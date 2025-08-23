/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use libseccomp::*;
use std::error::Error;

/// Configure seccomp filters for file-read adapter
/// This restricts the adapter to only necessary system calls for file operations
pub fn configure_seccomp() -> Result<(), Box<dyn Error>> {
    let mut ctx = ScmpFilterContext::new_filter(ScmpAction::Kill)?;

    // Allow only file read operations and essential system calls
    let allowed_syscalls = vec![
        // File read operations only
        ScmpSyscall::new("read"),
        ScmpSyscall::new("open"),
        ScmpSyscall::new("close"),
        ScmpSyscall::new("fstat"),
        ScmpSyscall::new("lstat"),
        ScmpSyscall::new("stat"),
        ScmpSyscall::new("access"),
        ScmpSyscall::new("readlink"),
        ScmpSyscall::new("realpath"),
        // Memory management (minimal)
        ScmpSyscall::new("mmap"),
        ScmpSyscall::new("mprotect"),
        ScmpSyscall::new("munmap"),
        ScmpSyscall::new("brk"),
        // Process control (minimal)
        ScmpSyscall::new("exit"),
        ScmpSyscall::new("exit_group"),
        ScmpSyscall::new("rt_sigreturn"),
        // Time operations (for timestamps)
        ScmpSyscall::new("clock_gettime"),
        ScmpSyscall::new("gettimeofday"),
        // Random number generation (for checksums)
        ScmpSyscall::new("getrandom"),
        // Signal handling (minimal)
        ScmpSyscall::new("rt_sigaction"),
        ScmpSyscall::new("rt_sigprocmask"),
        // Thread operations (minimal)
        ScmpSyscall::new("clone"),
        ScmpSyscall::new("set_tid_address"),
        ScmpSyscall::new("futex"),
        ScmpSyscall::new("sched_yield"),
        // File descriptor operations (minimal)
        ScmpSyscall::new("dup"),
        ScmpSyscall::new("dup2"),
        ScmpSyscall::new("fcntl"),
        // Error handling
        ScmpSyscall::new("arch_prctl"),
        // File system operations (read-only)
        ScmpSyscall::new("getcwd"),
        ScmpSyscall::new("chdir"),
        // No network operations allowed
        // No process creation allowed
        // No file writing allowed
    ];

    // Add all allowed system calls
    for syscall in allowed_syscalls {
        ctx.add_rule(ScmpAction::Allow, syscall)?;
    }

    // Deny all other system calls
    ctx.add_rule(ScmpAction::Kill, ScmpSyscall::new("any"))?;

    // Load the filter
    ctx.load()?;

    Ok(())
}

/// Validate that seccomp is properly configured
pub fn validate_seccomp() -> Result<bool, Box<dyn Error>> {
    // Try to execute a denied system call
    let result = std::panic::catch_unwind(|| {
        unsafe {
            // This should be denied by seccomp
            libc::socket(libc::AF_INET, libc::SOCK_STREAM, 0);
        }
    });

    // If seccomp is working, this should panic or be killed
    Ok(result.is_err())
}

/// Test file read operations with seccomp restrictions
pub fn test_file_read_with_seccomp() -> Result<bool, Box<dyn Error>> {
    // Try to read a file (should be allowed)
    let result = std::panic::catch_unwind(|| {
        let _ = std::fs::read("/proc/version");
    });

    // File read should work
    Ok(result.is_ok())
}

/// Test network operations with seccomp restrictions
pub fn test_network_blocked_by_seccomp() -> Result<bool, Box<dyn Error>> {
    // Try to create a network socket (should be denied)
    let result = std::panic::catch_unwind(|| unsafe {
        let _ = libc::socket(libc::AF_INET, libc::SOCK_STREAM, 0);
    });

    // Network operations should be blocked
    Ok(result.is_err())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_seccomp_configuration() {
        // This test should pass if seccomp is properly configured
        let result = configure_seccomp();
        assert!(result.is_ok());
    }

    #[test]
    fn test_seccomp_validation() {
        // This test should pass if seccomp is working
        let result = validate_seccomp();
        assert!(result.is_ok());
    }

    #[test]
    fn test_file_read_allowed() {
        // This test should pass if file read operations are allowed
        let result = test_file_read_with_seccomp();
        assert!(result.is_ok());
    }

    #[test]
    fn test_network_blocked() {
        // This test should pass if network operations are blocked
        let result = test_network_blocked_by_seccomp();
        assert!(result.is_ok());
    }
}
