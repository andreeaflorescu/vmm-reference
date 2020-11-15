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

use event_manager::{EventManager, MutEventSubscriber, SubscriberOps};
use kvm_bindings::{kvm_userspace_memory_region, KVM_API_VERSION, KVM_MAX_CPUID_ENTRIES};
use kvm_ioctls::{
    Cap::{self, Ioeventfd, Irqchip, Irqfd, UserMemory},
    Kvm,
};
use linux_loader::bootparam::boot_params;
use linux_loader::cmdline::{self, Cmdline};
use linux_loader::configurator::{
    self, linux::LinuxBootConfigurator, BootConfigurator, BootParams,
};
use linux_loader::loader::{self, elf::Elf, load_cmdline, KernelLoader, KernelLoaderResult};
use vm_device::device_manager::IoManager;
use vm_device::resources::Resource;
use vm_memory::{Address, GuestAddress, GuestMemory, GuestMemoryMmap, GuestMemoryRegion};
use vm_superio::Serial;
use vm_vcpu::vcpu::{self, cpuid::filter_cpuid, mptable, VcpuState};
use vm_vcpu::vm::{self, KvmVm};
use vmm_sys_util::{eventfd::EventFd, terminal::Terminal};

mod boot;
use boot::*;

mod config;
pub use config::*;

mod devices;
use devices::SerialWrapper;

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
    /// Event management error.
    EventManager(event_manager::Error),
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
    kvm: Kvm,
    vm: KvmVm,
    guest_memory: GuestMemoryMmap,
    // An Option, of all things, because it needs to be mutable while adding devices (so it can't
    // be in an Arc), then it needs to be packed in an Arc to share it across vCPUs. An Option
    // allows us to .take() it when starting the vCPUs.
    device_mgr: Option<IoManager>,
    // Arc<Mutex<>> because the same device (a dyn DevicePio/DeviceMmio from IoManager's
    // perspective, and a dyn MutEventSubscriber from EventManager's) is managed by the 2 entities,
    // and isn't Copy-able; so once one of them gets ownership, the other one can't anymore.
    event_mgr: EventManager<Arc<Mutex<dyn MutEventSubscriber>>>,
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
            device_mgr: Some(IoManager::new()),
            event_mgr: EventManager::new().map_err(Error::EventManager)?,
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

            // Safe because:
            // * userspace_addr is a valid address for a memory region, obtained by calling
            //   get_host_address() on a valid region's start address;
            // * the memory regions do not overlap - there's either a single region spanning
            //   the whole guest memory, or 2 regions with the MMIO gap in between.
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

        // Register its interrupt fd with KVM. IRQ line 4 is typically used for serial port 1.
        // See more IRQ assignments & info: https://tldp.org/HOWTO/Serial-HOWTO-8.html
        self.vm.register_irqfd(&interrupt_evt, 4)?;

        // Put it on the bus.
        // Safe to use expect() because the device manager is instantiated in new(), there's no
        // default implementation, and the field is private inside the VMM struct.
        self.device_mgr
            .as_mut()
            .expect("Missing device manager")
            .register_pio_resources(
                serial.clone(),
                &[Resource::PioAddressRange {
                    base: 0x3f8,
                    size: 0x8,
                }],
            )
            .unwrap();

        // Hook it to event management.
        self.event_mgr.add_subscriber(serial);

        Ok(())
    }

    /// Creates guest vCPUs.
    ///
    /// # Arguments
    ///
    /// * `vcpu_cfg` - [`VcpuConfig`](struct.VcpuConfig.html) struct containing vCPU configurations.
    /// * `kernel_load` - address where the kernel is loaded in guest memory.
    pub fn create_vcpus(&mut self, vcpu_cfg: VcpuConfig, kernel_load: GuestAddress) -> Result<()> {
        // TODO: Should we move this function call to the Vm module?
        mptable::setup_mptable(&self.guest_memory, vcpu_cfg.num_vcpus)
            .map_err(|e| Error::Vcpu(vcpu::Error::Mptable(e)))?;

        // Safe to use expect() because the device manager is instantiated in new(), there's no
        // default implementation, and the field is private inside the VMM struct.
        let shared_device_mgr = Arc::new(self.device_mgr.take().expect("Missing device manager"));
        let base_cpuid = self
            .kvm
            .get_supported_cpuid(KVM_MAX_CPUID_ENTRIES)
            .map_err(Error::KvmIoctl)?;

        for index in 0..vcpu_cfg.num_vcpus {
            // Set CPUID.
            let mut cpuid = base_cpuid.clone();
            filter_cpuid(
                &self.kvm,
                index as usize,
                vcpu_cfg.num_vcpus as usize,
                &mut cpuid,
            );

            let vcpu_state = VcpuState {
                kernel_load_addr: kernel_load,
                cpuid,
                id: index,
                zero_page_start: ZEROPG_START,
            };
            self.vm
                .create_vcpu(shared_device_mgr.clone(), vcpu_state, &self.guest_memory)?;
        }

        Ok(())
    }

    /// Run the VMM.
    pub fn run(&mut self) {
        if stdin().lock().set_raw_mode().is_err() {
            eprintln!("Failed to set raw mode on terminal. Stdin will echo.");
        }

        // TODO: should we handle this in another way rather than a panic?
        self.vm.run().expect("Cannot start vcpus.");

        loop {
            match self.event_mgr.run() {
                Ok(_) => (),
                Err(e) => eprintln!("Failed to handle events: {:?}", e),
            }
        }
    }

    fn check_kvm_capabilities(&self) -> Result<()> {
        let capabilities = vec![Irqchip, Ioeventfd, Irqfd, UserMemory];

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
}

impl TryFrom<VMMConfig> for VMM {
    type Error = Error;

    fn try_from(config: VMMConfig) -> Result<Self> {
        let mut vmm = VMM::new()?;
        vmm.configure_guest_memory(config.memory_config)?;
        let kernel_load = vmm.configure_kernel(config.kernel_config)?;
        vmm.configure_pio_devices()?;
        vmm.create_vcpus(config.vcpu_config, kernel_load.kernel_load)?;
        Ok(vmm)
    }
}
