// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

#![cfg(target_arch = "x86_64")]

//! Reference VMM built with rust-vmm components and minimal glue.
#![deny(missing_docs)]

use std::convert::TryFrom;
use std::ffi::CString;
use std::fs::File;
use std::io::{self, stdin, stdout};
use std::sync::{Arc, Mutex};
use std::thread;

use event_manager::SubscriberOps;
use kvm_bindings::{kvm_userspace_memory_region, CpuId, KVM_API_VERSION, KVM_MAX_CPUID_ENTRIES};
use kvm_ioctls::{
    Cap::{self, Ioeventfd, Irqchip, Irqfd, SetTssAddr, UserMemory},
    Kvm,
};
use linux_loader::bootparam::boot_params;
use linux_loader::cmdline::{self, Cmdline};
use linux_loader::configurator::{
    self, linux::LinuxBootConfigurator, BootConfigurator, BootParams,
};
use linux_loader::loader::{self, elf::Elf, load_cmdline, KernelLoader, KernelLoaderResult};
use vm_memory::{
    Address, GuestAddress, GuestMemory, GuestMemoryError, GuestMemoryMmap, GuestMemoryRegion,
};
use vm_superio::Serial;
use vmm_sys_util::{eventfd::EventFd, terminal::Terminal};

mod boot;
use boot::*;

mod config;
pub use config::*;

mod devices;
use devices::{DeviceManager, SerialWrapper};

mod vcpu;
mod vm;
use vcpu::{cpuid, mpspec, mptable, Vcpu};
use vm::KvmVm;

/// First address past 32 bits.
const FIRST_ADDR_PAST_32BITS: u64 = 1 << 32;
/// Size of the MMIO gap.
const MEM_32BIT_GAP_SIZE: u64 = 768 << 20;
/// The start of the memory area reserved for MMIO devices.
const MMIO_MEM_START: u64 = FIRST_ADDR_PAST_32BITS - MEM_32BIT_GAP_SIZE;
/// Address of the zeropage, where Linux kernel boot parameters are written.
const ZEROPG_START: u64 = 0x7000;
/// Address where the kernel command line is written.
const CMDLINE_START: u64 = 0x0002_0000;

/// VMM memory related errors.
#[derive(Debug)]
pub enum MemoryError {
    /// Failure during guest memory operation.
    GuestMemory(GuestMemoryError),
    /// Not enough memory slots.
    NotEnoughMemorySlots,
    /// Failed to configure guest memory.
    VmMemory(vm_memory::Error),
}

/// VMM errors.
#[derive(Debug)]
pub enum Error {
    /// Failed to write boot parameters to guest memory.
    BootConfigure(configurator::Error),
    /// Error configuring boot parameters.
    BootParam(boot::Error),
    /// Error configuring the kernel command line.
    Cmdline(cmdline::Error),
    /// Error setting up devices.
    Device(devices::Error),
    /// I/O error.
    IO(io::Error),
    /// Failed to load kernel.
    KernelLoad(loader::Error),
    /// Invalid KVM API version.
    KvmApiVersion(i32),
    /// Unsupported KVM capability.
    KvmCap(Cap),
    /// Error issuing an ioctl to KVM.
    KvmIoctl(kvm_ioctls::Error),
    /// Memory error.
    Memory(MemoryError),
    /// vCPU errors.
    Vcpu(vcpu::Error),
    /// VM errors.
    Vm(vm::Error),
}

impl std::convert::From<vm::Error> for Error {
    fn from(vm_error: vm::Error) -> Self {
        Self::Vm(vm_error)
    }
}

/// Dedicated [`Result`](https://doc.rust-lang.org/std/result/) type.
pub type Result<T> = std::result::Result<T, Error>;

/// A live VMM.
pub struct VMM {
    vm: KvmVm,
    kvm: Kvm,
    guest_memory: GuestMemoryMmap,
    device_mgr: DeviceManager,
}

impl VMM {
    /// Create a new VMM.
    pub fn new() -> Result<Self> {
        let kvm = Kvm::new().map_err(Error::KvmIoctl)?;

        // Check that KVM has the correct version.
        let kvm_api_ver = kvm.get_api_version();
        if kvm_api_ver != KVM_API_VERSION as i32 {
            return Err(Error::KvmApiVersion(kvm_api_ver));
        }

        // Create fd for interacting with kvm-vm specific functions.
        let vm = KvmVm::new(&kvm)?;

        let vmm = VMM {
            vm,
            kvm,
            guest_memory: GuestMemoryMmap::default(),
            device_mgr: DeviceManager::new().map_err(Error::Device)?,
        };

        vmm.check_kvm_capabilities()?;

        Ok(vmm)
    }

    /// Configure guest memory.
    ///
    /// # Arguments
    ///
    /// * `guest_mem_cfg` - [`MemoryConfig`](struct.MemoryConfig.html) struct containing guest
    ///                     memory configurations.
    pub fn configure_guest_memory(&mut self, guest_mem_cfg: MemoryConfig) -> Result<()> {
        let mem_size = ((guest_mem_cfg.mem_size_mib as u64) << 20) as usize;

        // Create guest memory regions.
        // On x86_64, they surround the MMIO gap (dedicated space for MMIO device slots) if the
        // configured memory size exceeds the latter's starting address.
        let mem_regions = match mem_size.checked_sub(MMIO_MEM_START as usize) {
            // Guest memory fits before the MMIO gap.
            None | Some(0) => vec![(GuestAddress(0), mem_size)],
            // Guest memory extends beyond the MMIO gap.
            Some(remaining) => vec![
                (GuestAddress(0), MMIO_MEM_START as usize),
                (GuestAddress(FIRST_ADDR_PAST_32BITS), remaining),
            ],
        };

        // Create guest memory from regions.
        let guest_memory = GuestMemoryMmap::from_ranges(&mem_regions)
            .map_err(|e| Error::Memory(MemoryError::VmMemory(e)))?;

        if guest_memory.num_regions() > self.kvm.get_nr_memslots() {
            return Err(Error::Memory(MemoryError::NotEnoughMemorySlots));
        }

        // Register guest memory regions with KVM.
        guest_memory.with_regions(|index, region| {
            let memory_region = kvm_userspace_memory_region {
                slot: index as u32,
                guest_phys_addr: region.start_addr().raw_value(),
                memory_size: region.len() as u64,
                // It's safe to unwrap because the guest address is valid.
                userspace_addr: guest_memory.get_host_address(region.start_addr()).unwrap() as u64,
                flags: 0,
            };
            // Safe because we mapped the memory region, we made sure that the regions
            // are not overlapping.
            unsafe { self.vm.set_user_memory_region(memory_region) }
        })?;

        self.guest_memory = guest_memory;

        Ok(())
    }

    /// Configure guest kernel.
    ///
    /// # Arguments
    ///
    /// * `kernel_cfg` - [`KernelConfig`](struct.KernelConfig.html) struct containing kernel
    ///                  configurations.
    pub fn configure_kernel(&mut self, kernel_cfg: KernelConfig) -> Result<KernelLoaderResult> {
        let mut kernel_image = File::open(kernel_cfg.path).map_err(Error::IO)?;
        let zero_page_addr = GuestAddress(ZEROPG_START);

        // Load the kernel into guest memory.
        let kernel_load = Elf::load(
            &self.guest_memory,
            None,
            &mut kernel_image,
            Some(GuestAddress(kernel_cfg.himem_start)),
        )
        .map_err(Error::KernelLoad)?;

        // Generate boot parameters.
        let mut bootparams = build_bootparams(
            &self.guest_memory,
            GuestAddress(kernel_cfg.himem_start),
            GuestAddress(MMIO_MEM_START),
            GuestAddress(FIRST_ADDR_PAST_32BITS),
        )
        .map_err(Error::BootParam)?;

        // Add the kernel command line to the boot parameters.
        bootparams.hdr.cmd_line_ptr = CMDLINE_START as u32;
        bootparams.hdr.cmdline_size = kernel_cfg.cmdline.len() as u32 + 1;

        // Load the kernel command line into guest memory.
        let mut cmdline = Cmdline::new(kernel_cfg.cmdline.len() + 1);
        cmdline
            .insert_str(kernel_cfg.cmdline)
            .map_err(Error::Cmdline)?;
        load_cmdline(
            &self.guest_memory,
            GuestAddress(CMDLINE_START),
            // Safe because we know the command line string doesn't contain any 0 bytes.
            unsafe { &CString::from_vec_unchecked(cmdline.into()) },
        )
        .map_err(Error::KernelLoad)?;

        // Write the boot parameters in the zeropage.
        LinuxBootConfigurator::write_bootparams::<GuestMemoryMmap>(
            &BootParams::new::<boot_params>(&bootparams, zero_page_addr),
            &self.guest_memory,
        )
        .map_err(Error::BootConfigure)?;

        Ok(kernel_load)
    }

    /// Configure PIO devices.
    ///
    /// This sets up the following PIO devices:
    /// * `x86_64`: serial console
    /// * `aarch64`: N/A
    pub fn configure_pio_devices(&mut self) -> Result<()> {
        self.vm.setup_irq_controller()?;
        // Create the serial console.
        let interrupt_evt = EventFd::new(libc::EFD_NONBLOCK).map_err(Error::IO)?;
        let serial = Arc::new(Mutex::new(SerialWrapper(Serial::new(
            interrupt_evt.try_clone().map_err(Error::IO)?,
            stdout(),
        ))));
        // Register its interrupt fd with KVM.
        self.vm.register_irqfd(&interrupt_evt, 4);

        // Configure event management for the serial console's events.
        self.device_mgr.serial_ev_mgr.add_subscriber(serial.clone());
        self.device_mgr.serial = Some(serial);

        Ok(())
    }

    /// Configure guest vCPUs.
    ///
    /// # Arguments
    ///
    /// * `vcpu_cfg` - [`VcpuConfig`](struct.VcpuConfig.html) struct containing vCPU configurations.
    /// * `kernel_load` - address where the kernel is loaded in guest memory.
    pub fn configure_vcpus(
        &mut self,
        vcpu_cfg: VcpuConfig,
        kernel_load: GuestAddress,
    ) -> Result<()> {
        mptable::setup_mptable(&self.guest_memory, vcpu_cfg.num_vcpus)
            .map_err(|e| Error::Vcpu(vcpu::Error::Mptable(e)))?;

        for index in 0..vcpu_cfg.num_vcpus {
            self.vm.create_vcpu(
                index,
                self.device_mgr
                    .serial
                    .clone()
                    .expect("Remove this `expect` when the serial console becomes optional"),
            )?;
        }
        // Set CPUID.
        let base_cpuid = self
            .kvm
            .get_supported_cpuid(KVM_MAX_CPUID_ENTRIES)
            .map_err(Error::KvmIoctl)?;
        for vcpu in self.vm.vcpu_handles.iter() {
            let mut vcpu_cpuid = base_cpuid.clone();
            cpuid::filter_cpuid(
                &self.kvm,
                vcpu.id() as usize,
                vcpu_cfg.num_vcpus as usize,
                &mut vcpu_cpuid,
            );

            self.configure_vcpu(&vcpu, &vcpu_cpuid, kernel_load)
                .map_err(Error::Vcpu)?;
        }

        Ok(())
    }

    /// Run the VMM.
    pub fn run(&mut self) {
        if stdin().lock().set_raw_mode().is_err() {
            eprintln!("Failed to set raw mode on terminal. Stdin will echo.");
        }

        for mut vcpu in self.vm.vcpu_handles.drain(..) {
            let _ = thread::Builder::new().spawn(move || loop {
                vcpu.run();
            });
        }
        loop {
            match self.device_mgr.serial_ev_mgr.run() {
                Ok(_) => (),
                Err(e) => eprintln!("Failed to handle events: {:?}", e),
            }
        }
    }

    fn check_kvm_capabilities(&self) -> Result<()> {
        let capabilities = vec![Irqchip, Ioeventfd, Irqfd, UserMemory, SetTssAddr];

        // Check that all desired capabilities are supported.
        if let Some(c) = capabilities
            .iter()
            .find(|&capability| !self.kvm.check_extension(*capability))
        {
            Err(Error::KvmCap(*c))
        } else {
            Ok(())
        }
    }

    fn configure_vcpu(
        &self,
        vcpu: &Vcpu,
        cpuid: &CpuId,
        kernel_load: GuestAddress,
    ) -> vcpu::Result<()> {
        // Configure CPUID.
        vcpu.configure_cpuid(cpuid)?;

        // Configure MSRs (model specific registers).
        vcpu.configure_msrs()?;

        // Configure regs, sregs and fpu.
        vcpu.configure_regs(kernel_load)?;
        vcpu.configure_sregs(&self.guest_memory)?;
        vcpu.configure_fpu()?;

        // Configure LAPICs.
        vcpu.configure_lapic()
    }
}

impl TryFrom<VMMConfig> for VMM {
    type Error = Error;

    fn try_from(config: VMMConfig) -> Result<Self> {
        let mut vmm = VMM::new()?;
        vmm.configure_guest_memory(config.memory_config)?;
        let kernel_load = vmm.configure_kernel(config.kernel_config)?;
        vmm.configure_pio_devices()?;
        vmm.configure_vcpus(config.vcpu_config, kernel_load.kernel_load)?;
        Ok(vmm)
    }
}
