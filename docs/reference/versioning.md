# Versioning

## Platform version

The root `VERSION` file holds the platform version (e.g. `1.0.0`). It is the single source of truth for the overall Provability Fabric release version. Release workflows and release notes may use this value.

## Crate and package versions

Rust crates in the workspace each define their own version in their `Cargo.toml` (e.g. `sidecar-watcher` 1.0.0, `attestor` 0.1.0). These are not automatically synced with `VERSION`. When cutting a release, consider:

- Bumping `VERSION` for the platform release.
- Bumping version fields in any crates that changed and are published or shipped as artifacts.

Go modules and Node packages also use their own version fields (e.g. `go.mod`, `package.json`). Align them with the release process as needed.

## Toolchain and workspace

- **Rust:** The repo root has a `rust-toolchain.toml` pinning `channel = "stable"` with `clippy` and `rustfmt`. All Rust workspace crates use this when building from the root.
- **Workspace:** Root `Cargo.toml` defines the Rust workspace; see that file and the main [README](https://github.com/SentinelOps-CI/provability-fabric/blob/main/README.md) "Rust workspace" section for the list of members and optional crates.

## Summary

- **VERSION**: platform/release version at repo root.
- **Crates and other packages**: independent version fields; update as part of release or when publishing.
