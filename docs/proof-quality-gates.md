# Proof Quality Gates & Time-to-Fail

This document describes the proof quality gates and time-to-fail features implemented to ensure high-quality Lean proofs and fast feedback cycles.

## Overview

The proof quality gates enforce three key policies:

1. **No stale sorry/admit**: No `sorry` or `by admit` statements older than 48 hours
2. **Build time budgets**: Total `lake build` ≤ 6 min; per-file ≤ 90 s
3. **Time-to-fail (TTF)**: First failing lemma must surface in ≤ 20 s on CI

## Components

### 1. Lean Proof Quality Gate (`tools/lean_gate.py`)

Scans Lean proofs for sorry/admit statements and enforces time-based policies.

**Features:**
- Configurable maximum age for admits (default: 48 hours)
- Exception list for legitimate admits
- Clear error messages with file locations
- YAML configuration support

**Usage:**
```bash
# Basic scan
python tools/lean_gate.py --root .

# With custom config
python tools/lean_gate.py --root . --config tools/lean_gate_config.yaml

# With custom max age
python tools/lean_gate.py --root . --max-age 24
```

**Configuration (`tools/lean_gate_config.yaml`):**
```yaml
max_age_hours: 48
exceptions:
  - "vendor/"
  - "tests/"
  - "examples/"
```

### 2. Lean Time Budget Checker (`scripts/lean_time_budget.sh`)

Times per-file builds and enforces time budgets.

**Features:**
- Total build timeout: 6 minutes
- Per-file timeout: 90 seconds
- Warning threshold: 60 seconds
- Grace period: 30 seconds
- Cross-platform support (Windows batch file available)

**Usage:**
```bash
# Unix/Linux/macOS
./scripts/lean_time_budget.sh

# Windows
scripts\lean_time_budget.bat
```

**Output:**
```
🔧 Lean Time Budget Checker
📋 Total budget: 360s
📋 Per-file budget: 90s
📋 Warning threshold: 60s

🔨 Building core/lean-libs... ✅ 45s
🔨 Building spec-templates/v1/proofs... ⚠️ 75s

============================================================
📊 LEAN BUILD TIME RESULTS
============================================================
⏱️  Total build time: 120s / 360s
✅ Total time within budget

⚠️  Slow files (1):
   spec-templates/v1/proofs:75s
```

### 3. Time-to-Fail Check

Ensures first failing lemma surfaces quickly in CI.

**Features:**
- 20-second timeout per file
- Fast feedback on compilation issues
- Prevents long-running builds from blocking CI

### 4. Property-Based Testing (`core/lean-libs/GenTrace.lean`)

Generates and shrinks Action traces for fuzz testing.

**Features:**
- SmallCheck/QuickCheck-style generators
- Size-bounded trace generation
- Automatic counterexample shrinking
- Seeded generation for reproducibility

**Usage:**
```bash
# Run proofbench
lake exe proofbench

# Run tests
cd tests/lean
lean --run gentrace_spec.lean
```

## CI Integration

The quality gates are integrated into the CI workflow (`.github/workflows/ci.yaml`):

```yaml
- name: Lean proof quality gate
  run: |
    echo "🔍 Running Lean proof quality gate..."
    python tools/lean_gate.py --root . --config tools/lean_gate_config.yaml

- name: Lean build time budget check
  run: |
    echo "⏱️  Running Lean build time budget check..."
    chmod +x scripts/lean_time_budget.sh
    ./scripts/lean_time_budget.sh

- name: Time-to-fail check
  run: |
    echo "⚡ Checking time-to-fail for first failing lemma..."
    # ... timeout checks ...

- name: Run proofbench
  run: |
    echo "🧪 Running property-based testing with proofbench..."
    cd core/lean-libs
    lake build
    cd ../..
    lake exe proofbench
```

## Policies

### 1. No Stale Sorry/Admit

- **Policy**: No `sorry` or `by admit` statements older than 48 hours
- **Enforcement**: CI fails with clear error message
- **Exceptions**: Files in exception list (vendor/, tests/, etc.)
- **Resolution**: Replace with actual proofs or add to exceptions

### 2. Build Time Budgets

- **Total budget**: 6 minutes for all builds
- **Per-file budget**: 90 seconds per file
- **Warning threshold**: 60 seconds (warns but doesn't fail)
- **Grace period**: 30 seconds remaining triggers warning

### 3. Time-to-Fail

- **Policy**: First failing lemma must surface in ≤ 20 seconds
- **Enforcement**: CI fails if any file takes > 20s to compile
- **Purpose**: Fast feedback on compilation issues

## Troubleshooting

### Common Issues

1. **Stale sorry/admit detected**
   ```
   ❌ Found admits/sorry in files older than 48 hours:
   core/lean-libs/Example.lean
   ```
   **Fix**: Replace `sorry` with actual proof or add file to exceptions

2. **Build timeout**
   ```
   ⏰ TIMEOUT core/lean-libs (90s)
   ```
   **Fix**: Optimize proof complexity or split into smaller files

3. **Slow file warning**
   ```
   ⚠️  Slow files (1):
      spec-templates/v1/proofs:75s
   ```
   **Fix**: Optimize proofs or increase budget if legitimate

### Configuration

To customize the quality gates:

1. **Edit `tools/lean_gate_config.yaml`** for sorry/admit policies
2. **Modify `scripts/lean_time_budget.sh`** for time budgets
3. **Update CI workflow** for different thresholds

### Adding Exceptions

To add files to the sorry/admit exception list:

```yaml
# tools/lean_gate_config.yaml
exceptions:
  - "vendor/"
  - "tests/"
  - "examples/"
  - "your-new-exception/"  # Add here
```

## Benefits

1. **Quality Assurance**: Ensures proofs are complete and not left as admits
2. **Performance**: Prevents slow builds from blocking CI
3. **Developer Experience**: Fast feedback on compilation issues
4. **Maintainability**: Automated enforcement of quality standards
5. **Fuzz Testing**: Property-based testing catches edge cases

## Future Enhancements

1. **Incremental builds**: Only rebuild changed files
2. **Parallel builds**: Build multiple files simultaneously
3. **Caching**: Cache build artifacts for faster rebuilds
4. **Metrics**: Track build times over time
5. **Integration**: Hook into ART failures for automatic testing 