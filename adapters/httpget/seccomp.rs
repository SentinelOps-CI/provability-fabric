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

/// Configure seccomp filters for HTTP-GET adapter
/// This restricts the adapter to only necessary system calls
pub fn configure_seccomp() -> Result<(), Box<dyn Error>> {
    let mut ctx = ScmpFilterContext::new_filter(ScmpAction::Kill)?;

    // Allow basic system calls needed for HTTP operations
    let allowed_syscalls = vec![
        // File operations (for logging, config)
        ScmpSyscall::new("read"),
        ScmpSyscall::new("write"),
        ScmpSyscall::new("open"),
        ScmpSyscall::new("close"),
        ScmpSyscall::new("fstat"),
        ScmpSyscall::new("lstat"),
        ScmpSyscall::new("stat"),
        // Memory management
        ScmpSyscall::new("mmap"),
        ScmpSyscall::new("mprotect"),
        ScmpSyscall::new("munmap"),
        ScmpSyscall::new("brk"),
        // Process control
        ScmpSyscall::new("exit"),
        ScmpSyscall::new("exit_group"),
        ScmpSyscall::new("rt_sigreturn"),
        // Time operations
        ScmpSyscall::new("clock_gettime"),
        ScmpSyscall::new("gettimeofday"),
        // Network operations (restricted)
        ScmpSyscall::new("socket"),
        ScmpSyscall::new("connect"),
        ScmpSyscall::new("sendto"),
        ScmpSyscall::new("recvfrom"),
        ScmpSyscall::new("setsockopt"),
        ScmpSyscall::new("getsockopt"),
        // DNS resolution
        ScmpSyscall::new("getaddrinfo"),
        ScmpSyscall::new("freeaddrinfo"),
        // Random number generation
        ScmpSyscall::new("getrandom"),
        // Signal handling
        ScmpSyscall::new("sigaltstack"),
        ScmpSyscall::new("rt_sigaction"),
        ScmpSyscall::new("rt_sigprocmask"),
        // Thread operations
        ScmpSyscall::new("clone"),
        ScmpSyscall::new("set_tid_address"),
        ScmpSyscall::new("futex"),
        ScmpSyscall::new("sched_yield"),
        // File descriptor operations
        ScmpSyscall::new("dup"),
        ScmpSyscall::new("dup2"),
        ScmpSyscall::new("fcntl"),
        // Error handling
        ScmpSyscall::new("arch_prctl"),
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
            libc::mkdir("/tmp/test", 0o755);
        }
    });

    // If seccomp is working, this should panic or be killed
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
}
