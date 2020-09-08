// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

extern crate cli;
extern crate vmm;

#[cfg(target_arch = "x86_64")]
use std::convert::TryFrom;
#[cfg(target_arch = "x86_64")]
use std::env;

#[cfg(target_arch = "x86_64")]
use cli::CLI;
#[cfg(target_arch = "x86_64")]
use vmm::VMM;

fn main() {
    #[cfg(target_arch = "x86_64")]
    {
        let vmm_config = CLI::launch(
            env::args()
                .collect::<Vec<String>>()
                .iter()
                .map(|s| s.as_str())
                .collect(),
        )
        .expect("Failed to parse command line options");
        let mut vmm = VMM::try_from(vmm_config).expect("Failed to create VMM from configurations");
        vmm.run();
    }
    #[cfg(target_arch = "aarch64")]
    println!("Reference VMM under construction!")
}
