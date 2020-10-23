use crate::devices::SafeStdoutSerial;
use crate::vcpu::{self, Vcpu};
use crate::VcpuConfig;
use kvm_bindings::{kvm_pit_config, kvm_userspace_memory_region, KVM_PIT_SPEAKER_DUMMY};
use kvm_ioctls::{Kvm, VmFd};
use vmm_sys_util::eventfd::EventFd;

/// A KVM specific implementation of a Virtual Machine.
///
/// Provides abstractions for working with a VM. Once a generic Vm trait will be available,
/// this type will become on of the concrete implementations.
pub struct KvmVm {
    fd: VmFd,
    pub(crate) vcpu_handles: Vec<Vcpu>,
}

#[derive(Debug)]
pub enum Error {
    /// Failed to create a VM.
    CreateVm(kvm_ioctls::Error),
    /// Failed to setup the user memory regions.
    SetupMemoryRegion(kvm_ioctls::Error),
    /// Failed to setup the interrupt controller.
    SetupInterruptController(kvm_ioctls::Error),
    /// Failed to create the vcpu.
    CreateVcpu(vcpu::Error),
    /// Failed to register IRQ event.
    RegisterIrqEvent(kvm_ioctls::Error),
}

// TODO: Implement std::error::Error for Error.

/// Dedicated [`Result`](https://doc.rust-lang.org/std/result/) type.
pub type Result<T> = std::result::Result<T, Error>;

impl KvmVm {
    /// Create a new `KvmVm`.
    pub fn new(kvm: &Kvm) -> Result<Self> {
        let fd = kvm.create_vm().map_err(Error::CreateVm)?;
        Ok(KvmVm {
            fd,
            vcpu_handles: Vec::new(),
        })
    }
    /// Set the user memory region.
    // This function can be easily be part of the hypervisor agnostic interface once we
    // redefine `memory_region` such that it does not use KVM primitives.
    pub unsafe fn set_user_memory_region(
        &self,
        memory_region: kvm_userspace_memory_region,
    ) -> Result<()> {
        self.fd
            .set_user_memory_region(memory_region)
            .map_err(Error::SetupMemoryRegion)
    }

    /// Configures the in kernel interrupt controller.
    // This function should be reuse to configure the aarch64 interrupt controller (GIC).
    pub fn setup_irq_controller(&self) -> Result<()> {
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

    /// Create a Vcpu based on the passed configuration.
    // TODO: Should this return the Vcpu or just directly insert it in the vcpu_handles?
    // TODO: This should not be pub (crate). Make it pub after removing `serial_console` param.
    // Right now this is complicated to abstract because the Vcpu holds a reference to
    // the Serial Console. Waiting on the creation of a Bus before defining the implementation.
    pub(crate) fn create_vcpu(
        &mut self,
        index: u8,
        serial_console: SafeStdoutSerial,
    ) -> Result<()> {
        let vcpu = Vcpu::new(&self.fd, index, serial_console).map_err(Error::CreateVcpu)?;
        self.vcpu_handles.push(vcpu);
        Ok(())
    }

    /// Let KVM know that instead of triggering an actual interrupt for `irq_number`, we will
    /// just write on the specified `event`.
    // TODO: Add a check for `irq_number`. Since we are only supporting the in-kernel IRQ chip
    // right now, we shouldn't allow irq_number > 15 (I think?).
    pub fn register_irqfd(&self, event: &EventFd, irq_number: u32) -> Result<()> {
        self.fd
            .register_irqfd(&event, irq_number)
            .map_err(Error::RegisterIrqEvent)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_invalid_irqfd() {
        let kvm = Kvm::new().unwrap();
        let vm = KvmVm::new(&kvm).unwrap();

        let eventfd = EventFd::new(0).unwrap();
        // TODO: This should fail.
        vm.register_irqfd(&eventfd, 1430943);
    }
}
