// SPDX-License-Identifier: Apache-2.0
//! Restricted Linux x86_64 syscall profiles for the adapter CLIs.
//!
//! This is a defense-in-depth syscall allowlist, not pathname or network
//! destination isolation. The deployment must separately constrain mounts,
//! credentials, inherited descriptors and network access.

use libseccomp::{ScmpAction, ScmpArgCompare, ScmpCompareOp, ScmpFilterContext, ScmpSyscall};
use std::error::Error;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Profile {
    FileRead,
    HttpGet,
}

pub fn configure(profile: Profile) -> Result<(), Box<dyn Error>> {
    let mut filter = ScmpFilterContext::new(ScmpAction::Errno(libc::EPERM))?;
    filter.set_ctl_nnp(true)?;
    filter.set_ctl_tsync(true)?;

    // libc, Rust allocator, file metadata, clocks and process termination.
    for name in [
        "read", "readv", "pread64", "close", "fstat", "newfstatat",
        "stat", "lstat", "statx", "lseek", "readlink", "readlinkat",
        "access", "faccessat", "faccessat2", "getcwd", "getdents64",
        "mmap", "mprotect", "munmap", "mremap", "madvise", "brk",
        "exit", "exit_group", "rt_sigreturn", "rt_sigaction",
        "rt_sigprocmask", "sigaltstack", "clock_gettime", "gettimeofday",
        "clock_nanosleep", "nanosleep", "getrandom", "futex",
        "getpid", "gettid", "getuid", "geteuid", "getgid", "getegid",
        "sched_yield", "sched_getaffinity", "prlimit64", "fcntl",
        "set_tid_address", "set_robust_list", "rseq", "restart_syscall",
    ] {
        filter.add_rule(ScmpAction::Allow, ScmpSyscall::from_name(name)?)?;
    }

    // Permit read-only opens, including TLS trust roots and NSS configuration.
    // openat2 is deliberately excluded because its flags are behind a pointer.
    let prohibited = (libc::O_ACCMODE | libc::O_CREAT | libc::O_TRUNC
        | libc::O_APPEND | (libc::O_TMPFILE & !libc::O_DIRECTORY)) as u64;
    for (name, arg) in [("open", 1), ("openat", 2)] {
        filter.add_rule_conditional(
            ScmpAction::Allow,
            ScmpSyscall::from_name(name)?,
            &[ScmpArgCompare::new(arg, ScmpCompareOp::MaskedEqual(prohibited), 0)],
        )?;
    }

    // Only allow the file adapter to write its normal CLI output descriptors.
    for name in ["write", "writev"] {
        let syscall = ScmpSyscall::from_name(name)?;
        if profile == Profile::HttpGet {
            // The HTTP client also needs to write to connected sockets.
            filter.add_rule(ScmpAction::Allow, syscall)?;
        } else {
            for fd in [1, 2] {
                filter.add_rule_conditional(
                    ScmpAction::Allow,
                    syscall,
                    &[ScmpArgCompare::new(0, ScmpCompareOp::Equal, fd)],
                )?;
            }
        }
    }

    if profile == Profile::HttpGet {
        for name in [
            "socket", "connect", "sendto", "recvfrom", "sendmsg", "recvmsg",
            "getsockname", "getpeername", "getsockopt", "setsockopt", "shutdown",
            "epoll_create1", "epoll_ctl", "epoll_wait", "epoll_pwait",
            "eventfd2", "poll", "ppoll", "select", "pselect6", "ioctl",
        ] {
            filter.add_rule(ScmpAction::Allow, ScmpSyscall::from_name(name)?)?;
        }
        // DNS resolution uses blocking worker threads. Do not permit
        // ordinary process creation or namespace creation through clone.
        let required = libc::CLONE_THREAD as u64;
        let forbidden = (libc::CLONE_NEWNS | libc::CLONE_NEWCGROUP
            | libc::CLONE_NEWUTS | libc::CLONE_NEWIPC | libc::CLONE_NEWUSER
            | libc::CLONE_NEWPID | libc::CLONE_NEWNET | libc::CLONE_VFORK
            | libc::CLONE_PTRACE | libc::CLONE_UNTRACED) as u64;
        filter.add_rule_conditional(
            ScmpAction::Allow,
            ScmpSyscall::from_name("clone")?,
            &[ScmpArgCompare::new(
                0, ScmpCompareOp::MaskedEqual(required | forbidden), required,
            )],
        )?;
        // glibc falls back to clone when clone3 is unavailable. Its pointer
        // argument cannot be inspected by classic seccomp.
        filter.add_rule(ScmpAction::Errno(libc::ENOSYS), ScmpSyscall::from_name("clone3")?)?;
    }

    filter.load()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{fs, process::Command};

    // Irreversible filters belong in disposable child processes, never the
    // parent test runner. The test also runs normally during unfiltered tests.
    #[test]
    fn seccomp_child_probe() {
        let Ok(profile) = std::env::var("PF_SECCOMP_CHILD_PROFILE") else {
            return;
        };
        let profile = match profile.as_str() {
            "file" => Profile::FileRead,
            "http" => Profile::HttpGet,
            _ => panic!("unknown test profile"),
        };
        let path = std::env::var("PF_SECCOMP_TEST_FILE").expect("fixture path");
        configure(profile).expect("kernel filter installation");
        assert_eq!(fs::read(&path).expect("permitted read"), b"seccomp fixture");
        let error = fs::OpenOptions::new().write(true).open(&path)
            .expect_err("write-open must be denied");
        assert_eq!(error.raw_os_error(), Some(libc::EPERM));
        // SAFETY: socket arguments are valid; close any returned descriptor.
        let fd = unsafe { libc::socket(libc::AF_INET, libc::SOCK_STREAM, 0) };
        if profile == Profile::FileRead {
            assert_eq!(fd, -1, "network socket must be denied");
            assert_eq!(std::io::Error::last_os_error().raw_os_error(), Some(libc::EPERM));
        } else {
            assert!(fd >= 0, "HTTP profile must permit sockets");
            assert_eq!(unsafe { libc::close(fd) }, 0);
        }
        // SAFETY: getppid has no arguments; it is deliberately absent from
        // the allowlist. This distinguishes a loaded filter from no filter.
        let denied = unsafe { libc::syscall(libc::SYS_getppid) };
        assert_eq!(denied, -1);
        assert_eq!(std::io::Error::last_os_error().raw_os_error(), Some(libc::EPERM));
        // Exit directly after the probe: the general test harness needs
        // additional syscalls and must not be used to infer policy coverage.
        println!("PF_SECCOMP_PROBE_OK");
        std::process::exit(0);
    }

    #[test]
    fn seccomp_profiles_enforce_in_children() {
        let path = std::env::temp_dir().join(format!("pf-seccomp-{}", std::process::id()));
        let mut fixture = fs::OpenOptions::new().write(true).create_new(true)
            .open(&path).expect("unique fixture");
        use std::io::Write;
        fixture.write_all(b"seccomp fixture").expect("write fixture");
        drop(fixture);
        let result = (|| {
            for profile in ["file", "http"] {
                let output = Command::new(std::env::current_exe().expect("test executable"))
                    .args(["--exact", "seccomp::tests::seccomp_child_probe", "--nocapture"])
                    .env("PF_SECCOMP_CHILD_PROFILE", profile)
                    .env("PF_SECCOMP_TEST_FILE", &path)
                    .output().expect("run isolated probe");
                assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
                assert!(String::from_utf8_lossy(&output.stdout).contains("PF_SECCOMP_PROBE_OK"));
            }
        })();
        fs::remove_file(path).expect("remove fixture");
        result
    }
}
