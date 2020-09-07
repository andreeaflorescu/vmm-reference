// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

use std::result::Result;
use std::sync::{Arc, Mutex};

use kvm_bindings::CpuId;
use kvm_ioctls::{VcpuFd, VmFd};

use crate::devices::SafeStdoutSerial;

pub(crate) mod cpuid;
pub(crate) mod mpspec;
pub(crate) mod mptable;

/// Errors encountered during vCPU operation.
#[derive(Debug)]
pub enum Error {
    /// Error issuing an ioctl to KVM.
    KvmIoctl(kvm_ioctls::Error),
    /// Failed to configure mptables.
    Mptable(mptable::Error),
}

/// Struct for interacting with vCPUs.
///
/// This struct is a temporary (and quite terrible) placeholder until the
/// [`vmm-vcpu`](https://github.com/rust-vmm/vmm-vcpu) crate is stabilized.
pub(crate) struct Vcpu {
    /// Index.
    pub index: u8,
    /// KVM file descriptor for a vCPU.
    pub vcpu_fd: VcpuFd,
    /// Shared device.
    pub serial: SafeStdoutSerial,
}

impl Vcpu {
    /// Create a new vCPU.
    pub fn new(vm_fd: &VmFd, index: u8, serial: SafeStdoutSerial) -> Result<Self, Error> {
        Ok(Vcpu {
            index,
            vcpu_fd: vm_fd.create_vcpu(index).map_err(Error::KvmIoctl)?,
            serial,
        })
    }

    // Set CPUID.
    pub fn configure_cpuid(&self, cpuid: &CpuId) -> Result<(), Error> {
        self.vcpu_fd.set_cpuid2(cpuid).map_err(Error::KvmIoctl)
    }
}
