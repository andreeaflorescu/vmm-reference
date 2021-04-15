// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// Copyright 2017 The Chromium OS Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

use std::io::{self, ErrorKind};
use std::sync::{Arc, Barrier, Mutex};
use std::thread::{self, JoinHandle};

use kvm_bindings::{kvm_pit_config, kvm_userspace_memory_region, KVM_PIT_SPEAKER_DUMMY};
#[cfg(target_arch = "aarch64")]
use kvm_bindings::{kvm_device_attr, kvm_device_type_KVM_DEV_TYPE_ARM_VGIC_V3, kvm_create_device, kvm_device_type_KVM_DEV_TYPE_ARM_VGIC_V2, KVM_DEV_ARM_VGIC_CTRL_INIT, KVM_VGIC_V3_ADDR_TYPE_REDIST, KVM_DEV_ARM_VGIC_GRP_CTRL, KVM_DEV_ARM_VGIC_GRP_NR_IRQS, KVM_VGIC_V3_ADDR_TYPE_DIST, KVM_VGIC_V2_ADDR_TYPE_CPU, KVM_VGIC_V2_ADDR_TYPE_DIST, KVM_DEV_ARM_VGIC_GRP_ADDR};

use arch::{AARCH64_GIC_CPUI_BASE, AARCH64_GIC_DIST_BASE, AARCH64_GIC_REDIST_SIZE, AARCH64_GIC_NR_IRQS};
use kvm_ioctls::{Kvm, VmFd, DeviceFd};
use vm_device::device_manager::IoManager;
use vm_memory::{Address, GuestAddress, GuestMemory, GuestMemoryRegion};
use vmm_sys_util::errno::Error as Errno;
use vmm_sys_util::eventfd::EventFd;
use vmm_sys_util::signal::{Killable, SIGRTMIN};

#[cfg(target_arch = "x86_64")]
use crate::vcpu::mptable;
use crate::vcpu::{self, KvmVcpu, VcpuRunState, VcpuState};

/// Defines the state from which a `KvmVm` is initialized.
pub struct VmState {
    pub num_vcpus: u8,
}

/// A KVM specific implementation of a Virtual Machine.
///
/// Provides abstractions for working with a VM. Once a generic Vm trait will be available,
/// this type will become on of the concrete implementations.
pub struct KvmVm<EH: ExitHandler + Send> {
    fd: Arc<VmFd>,
    state: VmState,
    // Only one of `vcpus` or `vcpu_handles` can be active at a time.
    // To create the `vcpu_handles` the `vcpu` vector is drained.
    // A better abstraction should be used to represent this behavior.
    vcpus: Vec<KvmVcpu>,
    vcpu_handles: Vec<JoinHandle<()>>,
    exit_handler: EH,
    vcpu_barrier: Arc<Barrier>,
    vcpu_run_state: Arc<VcpuRunState>,
    irq_initialized: bool,
}

#[derive(Debug)]
pub enum Error {
    /// Failed to create a VM.
    CreateVm(kvm_ioctls::Error),
    /// Failed to setup the user memory regions.
    SetupMemoryRegion(kvm_ioctls::Error),
    /// Not enough memory slots.
    NotEnoughMemorySlots,
    /// Failed to setup the interrupt controller.
    SetupInterruptController(kvm_ioctls::Error),
    /// Failed to create the vcpu.
    CreateVcpu(vcpu::Error),
    /// Failed to register IRQ event.
    RegisterIrqEvent(kvm_ioctls::Error),
    /// Failed to run the vcpus.
    RunVcpus(io::Error),
    /// Failed to configure mptables.
    #[cfg(target_arch = "x86_64")]
    Mptable(mptable::Error),
    /// Failed to pause the vcpus.
    PauseVcpus(Errno),
    /// Failed to resume vcpus.
    ResumeVcpus(Errno),
}

// TODO: Implement std::error::Error for Error.

/// Dedicated [`Result`](https://doc.rust-lang.org/std/result/) type.
pub type Result<T> = std::result::Result<T, Error>;

/// Trait that allows the VM to signal that the VCPUs have exited.
///
// This trait needs Clone because each VCPU needs to be able to call the `kick` function.
pub trait ExitHandler: Clone {
    fn kick(&self) -> io::Result<()>;
}

/// Represents the current state of the VM.
#[derive(Debug, PartialEq)]
pub enum VmRunState {
    Running,
    Suspending,
    Exiting,
}

impl Default for VmRunState {
    fn default() -> Self {
        Self::Running
    }
}

enum DeviceKind {
    ArmVgicV3,
    ArmVgicV2,
}

impl<EH: 'static + ExitHandler + Send> KvmVm<EH> {
    /// Create a new `KvmVm`.
    pub fn new<M: GuestMemory>(
        kvm: &Kvm,
        vm_state: VmState,
        guest_memory: &M,
        exit_handler: EH,
    ) -> Result<Self> {
        let vm_fd = Arc::new(kvm.create_vm().map_err(Error::CreateVm)?);

        let vcpu_run_state = Arc::new(VcpuRunState::default());

        let vm = KvmVm {
            vcpu_barrier: Arc::new(Barrier::new(vm_state.num_vcpus as usize)),
            state: vm_state,
            fd: vm_fd,
            vcpus: Vec::new(),
            vcpu_handles: Vec::new(),
            exit_handler,
            vcpu_run_state,
            // hack to be removed; just so we can quickly start an aarch64 vm for POC;
            irq_initialized: false,
        };

        vm.configure_memory_regions(guest_memory, kvm)?;

        #[cfg(target_arch = "x86_64")]
        mptable::setup_mptable(guest_memory, vm.state.num_vcpus).map_err(Error::Mptable)?;

        // TODO: reuse this for setting up the GIC.
        #[cfg(target_arch = "x86_64")]
        vm.setup_irq_controller()?;

        Ok(vm)
    }

    /// Retrieve the associated KVM VM file descriptor.
    pub fn vm_fd(&self) -> Arc<VmFd> {
        self.fd.clone()
    }

    // Create the kvm memory regions based on the configuration passed as `guest_memory`.
    fn configure_memory_regions<M: GuestMemory>(&self, guest_memory: &M, kvm: &Kvm) -> Result<()> {
        if guest_memory.num_regions() > kvm.get_nr_memslots() {
            return Err(Error::NotEnoughMemorySlots);
        }

        // Register guest memory regions with KVM.
        guest_memory
            .with_regions(|index, region| {
                let memory_region = kvm_userspace_memory_region {
                    slot: index as u32,
                    guest_phys_addr: region.start_addr().raw_value(),
                    memory_size: region.len() as u64,
                    // It's safe to unwrap because the guest address is valid.
                    userspace_addr: guest_memory.get_host_address(region.start_addr()).unwrap()
                        as u64,
                    flags: 0,
                };

                // Safe because:
                // * userspace_addr is a valid address for a memory region, obtained by calling
                //   get_host_address() on a valid region's start address;
                // * the memory regions do not overlap - there's either a single region spanning
                //   the whole guest memory, or 2 regions with the MMIO gap in between.
                unsafe { self.fd.set_user_memory_region(memory_region) }
            })
            .map_err(Error::SetupMemoryRegion)?;

        Ok(())
    }

    // Configures the in kernel interrupt controller.
    // This function should be reused to configure the aarch64 interrupt controller (GIC).
    #[cfg(target_arch = "x86_64")]
    fn setup_irq_controller(&self) -> Result<()> {
        // First, create the irqchip.
        // On `x86_64`, this _must_ be created _before_ the vCPUs.
        // It sets up the virtual IOAPIC, virtual PIC, and sets up the future vCPUs for local APIC.
        // When in doubt, look in the kernel for `KVM_CREATE_IRQCHIP`.
        // https://elixir.bootlin.com/linux/latest/source/arch/x86/kvm/x86.c
        self.fd
            .create_irq_chip()
            .map_err(Error::SetupInterruptController)?;

        // The PIT is used during boot to configure the frequency.
        // The output from PIT channel 0 is connected to the PIC chip, so that it
        // generates an "IRQ 0" (system timer).
        // https://wiki.osdev.org/Programmable_Interval_Timer
        let mut pit_config = kvm_pit_config::default();
        // Set up the speaker PIT, because some kernels are musical and access the speaker port
        // during boot. Without this, KVM would continuously exit to userspace.
        pit_config.flags = KVM_PIT_SPEAKER_DUMMY;
        self.fd
            .create_pit2(pit_config)
            .map_err(Error::SetupInterruptController)
    }

    #[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
    fn create_gic_device(vm: &VmFd, flags: u32) -> DeviceFd {
        let mut gic_device = kvm_bindings::kvm_create_device {
            type_: kvm_device_type_KVM_DEV_TYPE_ARM_VGIC_V3,
            fd: 0,
            flags,
        };
        let device_fd = match vm.create_device(&mut gic_device) {
            Ok(fd) => fd,
            Err(_) => {
                gic_device.type_ = kvm_device_type_KVM_DEV_TYPE_ARM_VGIC_V2;
                vm.create_device(&mut gic_device)
                    .expect("Cannot create KVM vGIC device")
            }
        };
        device_fd
    }

    #[cfg(target_arch = "aarch64")]
    fn setup_irq_controller(&self) -> Result<()> {
        let cpu_if_addr: u64 = AARCH64_GIC_CPUI_BASE;
        let dist_if_addr: u64 = AARCH64_GIC_DIST_BASE;
        let redist_addr: u64 = dist_if_addr - (AARCH64_GIC_REDIST_SIZE * self.state.num_vcpus as u64);
        let raw_cpu_if_addr = &cpu_if_addr as *const u64;
        let raw_dist_if_addr = &dist_if_addr as *const u64;
        let raw_redist_addr = &redist_addr as *const u64;

        let cpu_if_attr = kvm_device_attr {
            group: KVM_DEV_ARM_VGIC_GRP_ADDR,
            attr: KVM_VGIC_V2_ADDR_TYPE_CPU as u64,
            addr: raw_cpu_if_addr as u64,
            flags: 0,
        };
        let redist_attr = kvm_device_attr {
            group: KVM_DEV_ARM_VGIC_GRP_ADDR,
            attr: KVM_VGIC_V3_ADDR_TYPE_REDIST as u64,
            addr: raw_redist_addr as u64,
            flags: 0,
        };
        let mut dist_attr = kvm_device_attr {
            group: KVM_DEV_ARM_VGIC_GRP_ADDR,
            addr: raw_dist_if_addr as u64,
            attr: 0,
            flags: 0,
        };

        let mut gic_v3_device = kvm_create_device {
            type_: kvm_device_type_KVM_DEV_TYPE_ARM_VGIC_V3,
            ..Default::default()
        };

        let mut gic_v2_device = kvm_create_device {
            type_: kvm_device_type_KVM_DEV_TYPE_ARM_VGIC_V2,
            ..Default::default()
        };

        let (vgic, device_kind, cpu_redist_attr, dist_attr_attr) =
            match self.vm_fd().create_device(&mut gic_v3_device) {
                Err(_) => (
                    self.vm_fd().create_device(&mut gic_v2_device).map_err(Error::SetupInterruptController)?,
                    DeviceKind::ArmVgicV2,
                    cpu_if_attr,
                    KVM_VGIC_V2_ADDR_TYPE_DIST as u64,
                ),
                Ok(vgic) => (
                    vgic,
                    DeviceKind::ArmVgicV3,
                    redist_attr,
                    KVM_VGIC_V3_ADDR_TYPE_DIST as u64,
                ),
            };
        dist_attr.attr = dist_attr_attr;

        // Safe because we allocated the struct that's being passed in
        vgic.set_device_attr(&cpu_redist_attr).map_err(Error::SetupInterruptController)?;
        vgic.set_device_attr(&dist_attr).map_err(Error::SetupInterruptController)?;


        // We need to tell the kernel how many irqs to support with this vgic
        let nr_irqs: u32 = AARCH64_GIC_NR_IRQS;
        let nr_irqs_ptr = &nr_irqs as *const u32;
        let nr_irqs_attr = kvm_device_attr {
            group: KVM_DEV_ARM_VGIC_GRP_NR_IRQS,
            attr: 0,
            addr: nr_irqs_ptr as u64,
            flags: 0,
        };
        vgic.set_device_attr(&nr_irqs_attr).map_err(Error::SetupInterruptController)?;

        // Finalize the GIC
        let init_gic_attr = kvm_device_attr {
            group: KVM_DEV_ARM_VGIC_GRP_CTRL,
            attr: KVM_DEV_ARM_VGIC_CTRL_INIT as u64,
            addr: 0,
            flags: 0,
        };

        vgic.set_device_attr(&init_gic_attr).map_err(Error::SetupInterruptController)?;

        Ok(())
    }

    /// Create a Vcpu based on the passed configuration.
    pub fn create_vcpu<M: GuestMemory>(
        &mut self,
        bus: Arc<Mutex<IoManager>>,
        vcpu_state: VcpuState,
        memory: &M,
    ) -> Result<()> {
        let vcpu = KvmVcpu::new(
            &self.fd,
            bus,
            vcpu_state,
            self.vcpu_barrier.clone(),
            self.vcpu_run_state.clone(),
            memory,
        )
        .map_err(Error::CreateVcpu)?;
        self.vcpus.push(vcpu);
        #[cfg(target_arch = "aarch64")]
        if !self.irq_initialized {
            self.setup_irq_controller()?;
            self.irq_initialized = true;
        }
        Ok(())
    }

    /// Let KVM know that instead of triggering an actual interrupt for `irq_number`, we will
    /// just write on the specified `event`.
    pub fn register_irqfd(&self, event: &EventFd, irq_number: u32) -> Result<()> {
        self.fd
            .register_irqfd(&event, irq_number)
            .map_err(Error::RegisterIrqEvent)
    }

    /// Run the `Vm` based on the passed `vcpu` configuration.
    ///
    /// Returns an error when the number of configured vcpus is not the same as the number
    /// of created vcpus (using the `create_vcpu` function).
    ///
    /// # Arguments
    ///
    /// * `vcpu_run_addr`: address in guest memory where the vcpu run starts.
    pub fn run(&mut self, vcpu_run_addr: GuestAddress) -> Result<()> {
        if self.vcpus.len() != self.state.num_vcpus as usize {
            return Err(Error::RunVcpus(io::Error::from(ErrorKind::InvalidInput)));
        }

        KvmVcpu::setup_signal_handler().unwrap();

        for (id, mut vcpu) in self.vcpus.drain(..).enumerate() {
            let vcpu_exit_handler = self.exit_handler.clone();
            let vcpu_handle = thread::Builder::new()
                .name(format!("vcpu_{}", id))
                .spawn(move || {
                    // TODO: Check the result of both vcpu run & kick.
                    let _ = vcpu.run(vcpu_run_addr).unwrap();
                    let _ = vcpu_exit_handler.kick();
                    vcpu.run_state.set_and_notify(VmRunState::Exiting);
                })
                .map_err(Error::RunVcpus)?;
            self.vcpu_handles.push(vcpu_handle);
        }

        Ok(())
    }

    /// Shutdown a VM by signaling the running VCPUs.
    pub fn shutdown(&mut self) {
        self.vcpu_run_state.set_and_notify(VmRunState::Exiting);
        self.vcpu_handles.drain(..).for_each(|handle| {
            #[allow(clippy::identity_op)]
            let _ = handle.kill(SIGRTMIN() + 0);
            let _ = handle.join();
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::vcpu::cpuid::filter_cpuid;
    use crate::vcpu::mptable::MAX_SUPPORTED_CPUS;
    use crate::vm::{Error, KvmVm, VmState};

    use std::sync::atomic::{AtomicBool, Ordering};
    use std::thread::sleep;
    use std::time::Duration;

    use kvm_ioctls::Kvm;
    use vm_memory::{Bytes, GuestAddress, GuestMemoryMmap};

    #[derive(Clone, Default)]
    struct WrappedExitHandler(Arc<DummyExitHandler>);

    #[derive(Default)]
    struct DummyExitHandler {
        kicked: AtomicBool,
    }

    impl ExitHandler for WrappedExitHandler {
        fn kick(&self) -> io::Result<()> {
            self.0.kicked.store(true, Ordering::Release);
            Ok(())
        }
    }

    fn default_memory() -> GuestMemoryMmap {
        let mem_size = 1024 << 20;
        GuestMemoryMmap::from_ranges(&[(GuestAddress(0), mem_size)]).unwrap()
    }

    fn default_vm(
        kvm: &Kvm,
        guest_memory: &GuestMemoryMmap,
        num_vcpus: u8,
    ) -> Result<KvmVm<WrappedExitHandler>> {
        let vm_state = VmState { num_vcpus };

        let exit_handler = WrappedExitHandler::default();
        let vm = KvmVm::new(&kvm, vm_state, guest_memory, exit_handler)?;
        Ok(vm)
    }

    fn create_and_run(
        num_vcpus: u8,
        asm_code: &[u8],
        guest_memory: &mut GuestMemoryMmap,
    ) -> KvmVm<WrappedExitHandler> {
        let kvm = Kvm::new().unwrap();
        let mut vm = default_vm(&kvm, guest_memory, num_vcpus).unwrap();
        let io_manager = Arc::new(Mutex::new(IoManager::new()));

        let base_cpuid = kvm
            .get_supported_cpuid(kvm_bindings::KVM_MAX_CPUID_ENTRIES)
            .unwrap();
        for i in 0..vm.state.num_vcpus {
            let mut cpuid = base_cpuid.clone();
            filter_cpuid(&kvm, i as usize, vm.state.num_vcpus as usize, &mut cpuid);
            vm.create_vcpu(io_manager.clone(), VcpuState { cpuid, id: i }, guest_memory)
                .unwrap();
        }

        assert_eq!(vm.vcpus.len() as u8, num_vcpus);
        assert_eq!(vm.vcpu_handles.len() as u8, 0);

        let load_addr = GuestAddress(0x100_0000);
        guest_memory.write_slice(asm_code, load_addr).unwrap();
        vm.run(load_addr).unwrap();

        vm
    }

    #[test]
    fn test_failed_setup_mptable() {
        let num_vcpus = (MAX_SUPPORTED_CPUS + 1) as u8;
        let kvm = Kvm::new().unwrap();
        let guest_memory = default_memory();
        let res = default_vm(&kvm, &guest_memory, num_vcpus);
        assert!(matches!(res, Err(Error::Mptable(_))));
    }

    #[test]
    fn test_failed_setup_memory() {
        let kvm = Kvm::new().unwrap();
        let vm_state = VmState { num_vcpus: 1 };

        // Create nr_slots non overlapping regions of length 100.
        let nr_slots: u64 = (kvm.get_nr_memslots() + 1) as u64;
        let mut ranges = Vec::<(GuestAddress, usize)>::new();
        for i in 0..nr_slots {
            ranges.push((GuestAddress(i * 100), 100))
        }
        let guest_memory = GuestMemoryMmap::from_ranges(&ranges).unwrap();
        let res = KvmVm::new(&kvm, vm_state, &guest_memory, WrappedExitHandler::default());
        assert!(matches!(res, Err(Error::NotEnoughMemorySlots)));
    }

    #[test]
    fn test_failed_irqchip_setup() {
        let kvm = Kvm::new().unwrap();
        let vm_state = VmState { num_vcpus: 1 };

        let vm = KvmVm {
            vcpus: Vec::new(),
            vcpu_handles: Vec::new(),
            vcpu_barrier: Arc::new(Barrier::new(vm_state.num_vcpus as usize)),
            state: vm_state,
            fd: Arc::new(kvm.create_vm().unwrap()),
            exit_handler: WrappedExitHandler::default(),
            vcpu_run_state: Arc::new(VcpuRunState::default()),
            irq_initialized: false
        };

        // Setting up the irq_controller twice should return an error.
        vm.setup_irq_controller().unwrap();
        let res = vm.setup_irq_controller();
        assert!(matches!(res, Err(Error::SetupInterruptController(_))));
    }

    #[test]
    fn test_invalid_vcpu_run() {
        // We're specifying in the VmState that we want to run one vcpu, but we do not create
        // any. This should return an error.
        let kvm = Kvm::new().unwrap();
        let guest_memory = default_memory();
        let mut vm = default_vm(&kvm, &guest_memory, 1).unwrap();
        assert!(
            matches!(vm.run(GuestAddress(0x1000_0000)), Err(Error::RunVcpus(e)) if e.kind() == ErrorKind::InvalidInput)
        );
    }

    #[test]
    fn test_shutdown() {
        let num_vcpus = 4;
        let mut guest_memory = default_memory();
        let asm_code = &[
            0xba, 0xf8, 0x03, /* mov $0x3f8, %dx */
            0xf4, /* hlt */
        ];

        let mut vm = create_and_run(num_vcpus, asm_code, &mut guest_memory);
        sleep(Duration::new(2, 0));
        vm.shutdown();
        assert_eq!(vm.exit_handler.0.kicked.load(Ordering::Relaxed), true);
        assert_eq!(vm.vcpus.len(), 0);
        assert_eq!(
            *vm.vcpu_run_state.vm_state.lock().unwrap(),
            VmRunState::Exiting
        );
    }
}
