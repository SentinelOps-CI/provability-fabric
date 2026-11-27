# Financial MPC demonstration

This crate is an experimental scaffold for financial multi-party computation interfaces. It includes mock threshold signatures, simulated key shares, illustrative regulatory checks, process-local audit records and performance instrumentation.

**Do not use this crate for live financial transactions, production key custody, regulatory certification, or cryptographic audit evidence.** Its test and benchmark outputs characterize the demonstration, not a deployed cryptographic MPC protocol. No production latency, throughput, or compliance guarantee is established by the repository.

## Components

| Module | Implemented scope |
| --- | --- |
| `threshold_signature` | Simulated signature generation and verification, key-share and cache interfaces |
| `audit_trail` | Process-local audit entry creation and hashing; not a tamper-proof persistent log |
| `compliance` | Illustrative rule evaluation; not regulatory certification |
| `network` | Network management scaffold |
| `performance` | Instrumentation and performance data structures |

## Build and test

Run from the repository root with the pinned Rust toolchain:

```sh
cargo test --locked -p mpc-fintech --all-features
cargo build --locked -p mpc-fintech --all-features --bins
```

The demo and benchmark binaries are experimental workloads. Review their source and configuration before executing them. Their results must not be reported as production measurements.

## Timestamp contract

The public Rust timestamp type is now `mpc_fintech::UtcTimestamp`, replacing Chrono's `DateTime<Utc>`. Use `UtcTimestamp::now()` for current time and `UtcTimestamp::parse` for RFC 3339 input.

For supported values, JSON retains the previous UTC Z spelling with 0, 3, 6 or 9 fractional digits. The legacy explicit +00:00 spelling is preserved in audit hash inputs. Transaction signing payloads continue to use signed Unix seconds. Unsupported dates, leap seconds and fractional precision beyond nanoseconds are rejected.

The migration includes independently generated digest fixtures for transaction signing payloads and the audit hash input. Those tests address timestamp-byte compatibility in the existing encoding, not its cryptographic completeness. The legacy audit encoding includes unordered maps and is not a canonical cross-process hash format; the signing payload also omits transaction fields. Those protocol limitations need separate remediation.

## Production prerequisites

A production system would need an independently reviewed threshold cryptographic protocol, secure key lifecycle, authenticated transport, binding of complete transaction intent to authorization, durable audit evidence with independent integrity verification, and substantiated compliance evaluation. None is established by this scaffold.
