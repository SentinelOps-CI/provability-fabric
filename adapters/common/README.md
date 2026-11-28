# Adapter syscall restrictions

The optional `seccomp` feature for the Rust file-read and HTTP-GET CLIs is
restricted to Linux x86_64 with libseccomp installed. It installs a default-deny
syscall allowlist before adapter execution; the HTTP runtime is created after
filter installation. A filter installation failure terminates the CLI.

The file-read profile denies socket creation and restricts new file opens to
read-only access. The HTTP profile permits networking and DNS worker threads,
with new file opens restricted to read-only access. Neither profile grants
pathname confinement, network destination confinement, isolation from inherited
descriptors, or complete host resource bounds. Deploy separately constrained
mounts, credentials, descriptors and networking. Default builds do not install
these in-process filters. Kubernetes/container seccomp profiles are independent.

The validation workflow exercises filter installation in isolated subprocesses,
positive file and socket operations, denied write-open and socket operations,
and actual CLI invocations against a local file and loopback HTTP server.
These tests establish the observed controls, not an exhaustive security proof.
