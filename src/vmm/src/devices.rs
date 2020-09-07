// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

#![cfg(target_arch = "x86_64")]

use std::io::{stdin, Read, Stdin, Stdout, Write};
use std::result::Result;
use std::sync::{Arc, Mutex};

use event_manager::{EventManager, EventOps, Events, MutEventSubscriber};
use vm_superio::Serial;
use vmm_sys_util::{epoll::EventSet, eventfd::EventFd};

/// Newtype for implementing `event-manager` functionalities.
pub(crate) struct SerialWrapper<W: Write>(pub Serial<W>);

impl<W: Write> MutEventSubscriber for SerialWrapper<W> {
    fn process(&mut self, events: Events, ops: &mut EventOps) {
        // Respond to stdin events.
        // `EventSet::IN` => send what's coming from stdin to the guest.
        // `EventSet::HANG_UP` or `EventSet::ERROR` => deregister the serial input.
        let mut out = [0u8; 32];
        match stdin().read(&mut out) {
            Err(e) => {
                eprintln!("Error while reading stdin: {:?}", e);
            }
            Ok(count) => {
                let event_set = events.event_set();
                let unregister_condition =
                    event_set.contains(EventSet::ERROR) | event_set.contains(EventSet::HANG_UP);
                if count > 0 {
                    if let Err(_) = self.0.enqueue_raw_bytes(&out[..count]) {
                        eprintln!("Failed to send bytes to the guest via serial input");
                    }
                } else if unregister_condition {
                    // Got 0 bytes from serial input; is it a hang-up or error?
                    ops.remove(events)
                        .expect("Failed to unregister serial input");
                }
            }
        }
    }

    fn init(&mut self, ops: &mut EventOps) {
        // Hook to stdin events.
        ops.add(Events::new(&stdin(), EventSet::IN))
            .expect("Failed to register serial input event");
    }
}

/// Errors encountered during device operation.
#[derive(Debug)]
pub enum Error {
    /// Failed to create an event manager for device events.
    EventManager(event_manager::Error),
}

/// Shorthand for an otherwise long type name.
pub(crate) type SafeStdoutSerial = Arc<Mutex<SerialWrapper<Stdout>>>;

/// Device manager.
///
/// This struct is the likeliest candidate for change once
/// [`vm-device`](https://github.com/rust-vmm/vm-device/) interfaces are stabilized.
pub(crate) struct DeviceManager {
    /// Serial console.
    pub serial: Option<SafeStdoutSerial>,
    /// Event manager for the serial console.
    pub serial_ev_mgr: EventManager<SafeStdoutSerial>,
}

impl DeviceManager {
    /// Builds an empty device manager.
    pub fn new() -> Result<Self, Error> {
        Ok(DeviceManager {
            serial: None,
            serial_ev_mgr: EventManager::new().map_err(Error::EventManager)?,
        })
    }
}
