# Security policy

## Supported versions

Security updates are applied on the default development branch (`main`) and released as tagged versions when appropriate. Use the latest tag for production deployments.

## Reporting a vulnerability

Please report security issues **privately** so we can coordinate a fix before public disclosure.

1. **Preferred:** Use [GitHub Security Advisories](https://github.com/SentinelOps-CI/provability-fabric/security/advisories/new) for this repository (if enabled for your access).
2. **Alternative:** Email the maintainers with subject line `[SECURITY] provability-fabric` and include:
   - Description of the issue and impact
   - Steps to reproduce (proof-of-concept if possible)
   - Affected versions or components (e.g. `runtime/attestor`, `core/cli/pf`)

We aim to acknowledge reports within **5 business days** and to provide a substantive update within **30 days**, depending on severity and complexity.

## Scope

In scope: this repository’s code, default configurations, and documented build/release paths. Out of scope: third-party services without a documented integration path, social engineering, and physical attacks.

## Safe harbor

We support coordinated disclosure. If you act in good faith and avoid privacy violations, destruction of data, or service disruption, we will not pursue legal action for research conducted under this policy.

## Supply chain

- SBOM generation and dependency scanning run in CI (see `.github/workflows/sbom-diff.yaml`).
- CycloneDX SBOMs are attached to GitHub Releases (see `.github/workflows/release-sbom.yml`).
- OpenSSF Scorecard runs on a schedule and on pushes to `main` (see `.github/workflows/scorecards.yml`).
- Pull requests: **Dependency review** flags high-or-worse vulnerable dependency changes and enforces a license deny list (see `.github/workflows/dependency-review.yml`); enable the repository **dependency graph** where required.
- Rust: **cargo-deny** checks licenses and advisories against root `deny.toml` (see `.github/workflows/cargo-deny.yml`).
- Workflow YAML is linted when `.github/workflows/**` changes (see `.github/workflows/actionlint.yml`).
