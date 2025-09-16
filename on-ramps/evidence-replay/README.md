# Evidence + Replay On-Ramp

The Evidence + Replay on-ramp adds TRACE-REPLAY-KIT for nightly builds, allowing teams to validate and replay traces with deterministic verification.

## Overview

This on-ramp extends Standards-Only with:
- **TRACE-REPLAY-KIT**: Deterministic trace replay capabilities
- **Nightly Builds**: Automated replay validation
- **Evidence Collection**: Comprehensive audit trails
- **Low-View Comparison**: Verify deterministic behavior

## Quick Start

### 1. Install Dependencies

```bash
# Install so CLI
go install github.com/provability-fabric/core/cli/cmd/so@latest

# Install Python dependencies for TRACE-REPLAY-KIT
pip install -r external/TRACE-REPLAY-KIT/requirements.txt
```

### 2. Set Up Nightly Builds

Create `.github/workflows/nightly-replay.yml`:

```yaml
name: Nightly Replay Validation
on:
  schedule:
    - cron: '0 2 * * *'  # 2 AM daily
  workflow_dispatch:

jobs:
  replay:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
        with:
          submodules: recursive
          
      - name: Setup Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.9'
          
      - name: Install Dependencies
        run: |
          pip install -r external/TRACE-REPLAY-KIT/requirements.txt
          go install github.com/provability-fabric/core/cli/cmd/so@latest
          
      - name: Compile Policy
        run: so policy compile --in policy.md --out build/
        
      - name: Run Replay Validation
        run: so trace run --trace fixtures/trace.json --fixtures fixtures/ --out replay-output/
        
      - name: Compare Low-View
        run: so trace compare-lowview --in replay-output/ --threshold 0.999999
        
      - name: Upload Evidence
        uses: actions/upload-artifact@v3
        with:
          name: replay-evidence
          path: replay-output/
```

### 3. Create Trace Fixtures

Create `fixtures/trace.json`:

```json
{
  "trace_id": "security-validation-001",
  "timestamp": "2025-01-27T14:00:00Z",
  "events": [
    {
      "type": "user_login",
      "timestamp": "2025-01-27T14:00:01Z",
      "data": {
        "user_id": "user123",
        "role": "admin"
      }
    },
    {
      "type": "api_call",
      "timestamp": "2025-01-27T14:00:02Z",
      "data": {
        "endpoint": "/api/sensitive",
        "method": "GET"
      }
    }
  ],
  "expected_outcome": "allowed"
}
```

### 4. Run Validation

```bash
# Run single trace validation
so trace run --trace fixtures/trace.json --fixtures fixtures/ --out replay-output/

# Compare with previous runs
so trace compare-lowview --in replay-output/ --threshold 0.999999

# Generate evidence report
so trace report --in replay-output/
```

## Features

### Trace Replay
- Deterministic execution environment
- Configurable fixtures and inputs
- Comprehensive logging and output capture

### Low-View Comparison
- Bit-perfect output verification
- Configurable similarity thresholds
- Drift detection and reporting

### Evidence Collection
- Complete audit trails
- Cryptographic hashes
- Timestamped artifacts

### Nightly Validation
- Automated replay scheduling
- Regression detection
- Historical trend analysis

## Configuration

### Trace Format

Traces define sequences of events for deterministic replay:

```json
{
  "trace_id": "unique-identifier",
  "timestamp": "ISO-8601-timestamp",
  "metadata": {
    "description": "Human readable description",
    "tags": ["security", "authentication"],
    "expected_duration_ms": 1000
  },
  "events": [
    {
      "type": "event_type",
      "timestamp": "ISO-8601-timestamp",
      "data": {
        "key": "value"
      }
    }
  ],
  "expected_outcome": "allowed|denied|error",
  "fixtures": {
    "input_file": "path/to/input.json",
    "expected_output": "path/to/expected.json"
  }
}
```

### Replay Configuration

Configure deterministic execution:

```yaml
# replay-config.yml
replay:
  seed: 42                    # Fixed random seed
  locale: "C"                 # Consistent locale
  timezone: "UTC"             # Fixed timezone
  chunk_size: 4096           # Consistent buffer sizes
  flush_cadence_ms: 100      # Fixed flush timing
  padding_policy: "fixed"    # Consistent padding
  drift_threshold: 0.001     # Drift detection threshold
```

## Integration Examples

### Docker Compose

```yaml
version: '3.8'
services:
  replay-runner:
    image: provability-fabric/trace-replay:latest
    volumes:
      - ./fixtures:/fixtures
      - ./replay-output:/output
    command: ["so", "trace", "run", "--trace", "/fixtures/trace.json", "--out", "/output"]
    
  evidence-collector:
    image: provability-fabric/evidence-service:latest
    volumes:
      - ./replay-output:/evidence
    environment:
      - EVIDENCE_STORAGE=/evidence
```

### Kubernetes CronJob

```yaml
apiVersion: batch/v1
kind: CronJob
metadata:
  name: nightly-replay
spec:
  schedule: "0 2 * * *"
  jobTemplate:
    spec:
      template:
        spec:
          containers:
          - name: replay-runner
            image: provability-fabric/trace-replay:latest
            command: ["so", "trace", "run", "--trace", "/fixtures/trace.json"]
            volumeMounts:
            - name: fixtures
              mountPath: /fixtures
            - name: output
              mountPath: /replay-output
          volumes:
          - name: fixtures
            configMap:
              name: trace-fixtures
          - name: output
            persistentVolumeClaim:
              claimName: replay-storage
```

## Monitoring and Alerting

### Drift Detection

```bash
# Check for drift in recent runs
so trace compare-lowview --in replay-output/ --threshold 0.999999 --alert-on-drift

# Generate drift report
so trace report --in replay-output/ --include-drift-analysis
```

### Performance Monitoring

```bash
# Track replay performance over time
so trace report --in replay-output/ --performance-metrics

# Compare execution times
so trace compare-lowview --in replay-output/ --execution-time-threshold 100ms
```

## Migration Path

From Evidence + Replay, teams can adopt:

1. **Full Platform**: Add sidecar integration with epochs and IFC
2. **Advanced Features**: Implement MPC fintech, privacy controls, and RAG guards

## Support

- Documentation: [docs/Evidence.md](../../docs/Evidence.md)
- TRACE-REPLAY-KIT: [external/TRACE-REPLAY-KIT/](../../external/TRACE-REPLAY-KIT/)
- Examples: [examples/evidence-replay/](../examples/)
- CLI Reference: [docs/cli-reference.md](../../docs/cli-reference.md)
