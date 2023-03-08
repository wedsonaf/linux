// SPDX-License-Identifier: GPL-2.0

//! Hyper-V interfaces.
//!
//! C header: [`include/linux/hyperv.h`](../../../../include/linux/hyperv.h)

pub mod vmbus;

/// Parses a string into a GUID.
///
/// This function is const, so it can convert string at compile time.
pub const fn guid(input: &[u8]) -> [u8; 16] {
    const fn hex(c: u8) -> u8 {
        c - if c >= b'0' && c <= b'9' {
            b'0'
        } else if c >= b'a' && c <= b'f' {
            b'a' - 10
        } else if c >= b'A' && c <= b'F' {
            b'A' - 10
        } else {
            panic!("Invalid guid");
        }
    }
    const INDICES: &[usize] = &[6, 4, 2, 0, 11, 9, 16, 14, 19, 21, 24, 26, 28, 30, 32, 34];
    let mut result = [0; 16];

    let mut i = 0;
    while i < INDICES.len() {
        result[i] = hex(input[INDICES[i]]) << 4 | hex(input[INDICES[i] + 1]);
        i += 1;
    }

    result
}
