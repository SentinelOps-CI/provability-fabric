# Lean Offline Build System

This document describes the offline Lean/mathlib dependency management system for Provability Fabric.

## Overview

The Provability Fabric project uses a vendored mathlib approach to ensure reproducible, offline builds of all Lean proofs. This eliminates network dependencies and ensures that all proofs compile consistently across different environments.

## Architecture

```
provability-fabric/
├── vendor/mathlib/          # Vendored mathlib4 repository
├── lean-toolchain          # Pinned Lean version (v4.7.0)
├── lakefile.lean           # Root-level Lake configuration
├── bundles/*/proofs/       # Agent-specific Lean proofs
├── core/lean-libs/         # Core Lean libraries
└── spec-templates/         # Template Lean specifications
```

## Key Components

### 1. Vendored Mathlib

- **Location**: `vendor/mathlib/`
- **Version**: v4.7.0
- **Commit**: `b5eba595428809e96f3ed113bc7ba776c5f801ac`
- **Purpose**: Eliminates network dependencies during build

### 2. Pinned Lean Version

- **Version**: v4.7.0
- **File**: `lean-toolchain`
- **Purpose**: Ensures consistent Lean version across all projects

### 3. Lake Configuration

All `lakefile.lean` files reference the vendored mathlib:

```lean
require mathlib from "../../../vendor/mathlib"
```

## Development Workflow

### Initial Setup

1. **Clone the repository**:
   ```bash
   git clone --recursive https://github.com/your-org/provability-fabric.git
   cd provability-fabric
   ```

2. **Vendor mathlib** (if not already done):
   ```bash
   chmod +x scripts/vendor-mathlib.sh
   ./scripts/vendor-mathlib.sh
   ```

3. **Verify setup**:
   ```bash
   make lean-offline
   ```

### Building Lean Proofs

#### Offline Build (Recommended)

```bash
make lean-offline
```

This target:
- Verifies `vendor/mathlib` exists and has correct commit
- Builds all Lean projects without network access
- Ensures reproducible builds

#### Individual Project Builds

```bash
# Core libraries
cd core/lean-libs && lake build

# Spec templates
cd spec-templates/v1/proofs && lake build

# Agent proofs
cd bundles/my-agent/proofs && lake build
cd bundles/test-new-user-agent/proofs && lake build
```

### Updating Mathlib

When updating to a new mathlib version:

1. **Update the vendor script**:
   ```bash
   # Edit scripts/vendor-mathlib.sh
   # Update MATHLIB_VERSION and MATHLIB_COMMIT
   ```

2. **Re-run vendor script**:
   ```bash
   ./scripts/vendor-mathlib.sh
   ```

3. **Update lean-toolchain** (if needed):
   ```bash
   # Edit lean-toolchain to match mathlib's Lean version
   ```

4. **Test offline build**:
   ```bash
   make lean-offline
   ```

## CI/CD Integration

### GitHub Actions

The `.github/workflows/lean-offline.yaml` workflow:

1. **Blocks network access** using `iptables`
2. **Verifies vendored mathlib** exists and has correct commit
3. **Builds all Lean projects** in offline mode
4. **Tests network blocking** by attempting git fetch
5. **Generates build report** with results

### Local CI Testing

Test the offline build locally:

```bash
# Simulate CI environment
sudo iptables -P OUTPUT DROP
make lean-offline
sudo iptables -P OUTPUT ACCEPT
```

## Troubleshooting

### Common Issues

#### 1. Mathlib Not Found

**Error**: `vendor/mathlib directory not found`

**Solution**:
```bash
./scripts/vendor-mathlib.sh
```

#### 2. Commit Mismatch

**Error**: `Mathlib commit mismatch!`

**Solution**:
```bash
cd vendor/mathlib
git fetch origin v4.7.0
git checkout b5eba595428809e96f3ed113bc7ba776c5f801ac
cd ../..
make lean-offline
```

#### 3. Network Access During Build

**Error**: Build succeeds with network blocked

**Solution**: Check that all `lakefile.lean` files use:
```lean
require mathlib from "../../../vendor/mathlib"
```

#### 4. Placeholder Proofs

**Error**: Found 'sorry' or 'by admit' statements

**Solution**: Complete all proofs by replacing placeholders with actual proofs.

### Debugging

#### Enable Lake Debug Output

```bash
LAKE_DEBUG=1 lake build
```

#### Check Mathlib Status

```bash
cd vendor/mathlib
git status
git log --oneline -5
```

#### Verify Offline Build

```bash
# Block network
sudo iptables -P OUTPUT DROP

# Test build
make lean-offline

# Restore network
sudo iptables -P OUTPUT ACCEPT
```

## Security Benefits

### Reproducible Builds

- All builds use identical mathlib version
- No network dependencies during build
- Consistent behavior across environments

### Supply Chain Security

- Mathlib commit is pinned and verified
- No external dependencies during build
- Audit trail of all dependencies

### Offline Capability

- Builds work without internet access
- Suitable for air-gapped environments
- Reduces attack surface

## Best Practices

### 1. Always Use `make lean-offline`

Instead of individual `lake build` commands, use:
```bash
make lean-offline
```

### 2. Verify Before Committing

Before committing Lean changes:
```bash
make lean-offline
```

### 3. Update Dependencies Carefully

When updating mathlib:
1. Test thoroughly in development
2. Update vendor script with new commit
3. Verify all proofs still compile
4. Update documentation

### 4. Monitor CI Results

Check the Lean Offline Build workflow results:
- All projects must build successfully
- No network access during build
- No placeholder proofs

## File Structure

```
docs/dev/lean-build.md          # This documentation
scripts/vendor-mathlib.sh       # Mathlib vendor script
.github/workflows/lean-offline.yaml  # CI workflow
Makefile                        # Build targets
lean-toolchain                  # Pinned Lean version
lakefile.lean                   # Root Lake configuration
vendor/mathlib/                 # Vendored mathlib4
```

## References

- [Lean 4 Documentation](https://leanprover-community.github.io/)
- [Mathlib4 Repository](https://github.com/leanprover-community/mathlib4)
- [Lake Build System](https://github.com/leanprover/lake)
- [Lean Project Management](https://leanprover-community.github.io/leanproject.html) 