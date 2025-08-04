# ART (Agent Red Teaming) Benchmark

This directory contains the Agent Red Teaming (ART) benchmark integration for Provability-Fabric.

## Overview

The ART benchmark provides 4,700 hand-curated attacks across 44 behaviors and simulated tool environments. Provability-Fabric enforces tool-level invariants through Lean proofs and side-car watchers, allowing us to measure block-rate against the 100% baseline ASR reported in the original paper.

## Goal

Demonstrate that ProofMeter + watcher drives ASR → ≈ 0% on the same scenarios, at < 20ms latency.

## Dataset

The ART dataset is stored in `$HOME/.cache/art/art_dataset.jsonl` and contains:

- **4,700 attacks** across 44 behavior categories
- **Tool environments** with simulated API calls
- **Ground truth labels** for attack success/failure
- **Metadata** including system prompts, tool schemas, and policy violations

## Behavior Categories

The ART dataset covers four main behavior categories:

1. **Confidentiality** - Data leakage and PII exposure attacks
2. **Policy** - Role-based access control and compliance violations  
3. **Override** - Safety guard bypass and confirmation evasion
4. **Budget** - Resource abuse and cost limit violations

## Bundle Structure

Each behavior category is converted to a Provability-Fabric bundle:

```
bundles/art/
├── confidentiality/
│   ├── spec.yaml
│   └── proofs/
│       ├── Spec.lean
│       └── lakefile.lean
├── policy/
├── override/
└── budget/
```

## Usage

### 1. Fetch Dataset

```bash
# Download ART dataset from Gray Swan S3
python tools/art_fetch.py

# Verify cached dataset
python tools/art_fetch.py --verify
```

### 2. Convert to Bundles

```bash
# Convert all behaviors to bundles
python scripts/art_to_bundle.py $HOME/.cache/art/art_dataset.jsonl bundles/art/

# Convert specific behavior
python scripts/art_to_bundle.py $HOME/.cache/art/art_dataset.jsonl bundles/art/ --behavior confidentiality
```

### 3. Run Benchmark

```bash
# Run ART benchmark (single shard)
make art

# Run with specific configuration
ART_PARALLEL=4 ART_TIMEOUT=60 make art
```

## CI Integration

The ART benchmark is integrated into the CI pipeline:

- **Nightly runs**: `art-dataset-cache.yaml`
- **Benchmark execution**: `art-benchmark.yaml`
- **Metrics collection**: `art_metrics_push.py`
- **Dashboard**: Grafana "ART Defence" panel

## Feature Flags

ART integration is gated by feature flags to maintain main branch stability:

```bash
# Enable ART preview mode
export ART_PREVIEW=true

# Run with ART bundles
pf lint bundles/art/*
```

## Troubleshooting

### Dataset Issues

```bash
# Force re-download
python tools/art_fetch.py --force

# Use alternative URL
python tools/art_fetch.py --url https://example.com/art_dataset.jsonl
```

### Bundle Issues

```bash
# Check bundle structure
find bundles/art/ -name "*.yaml" -o -name "*.lean"

# Validate specs
pf lint bundles/art/*

# Check proofs
cd bundles/art/confidentiality/proofs && lake build
```

### Benchmark Issues

```bash
# Check logs
docker logs art-runner

# Verify environment
echo $ART_PARALLEL $ART_TIMEOUT $PROOFMETER_URL

# Test single attack
python tests/art_runner.py --shard 1/1 --attack-id 123
```

## References

- [ART Paper]([https://arxiv.org/abs/2404.00702](https://arxiv.org/abs/2507.20526#:~:text=We%20use%20these%20results%20to,transferability%20across%20models%20and%20tasks.))

## Contributing

To add new behavior categories or improve proofs:

1. Add behavior to `art_to_bundle.py`
2. Implement Lean proofs in `Spec.lean`
3. Add regression tests to `art_regression.yaml`
4. Update metrics collection in `art_metrics_push.py` 
