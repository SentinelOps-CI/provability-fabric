# Testing Guide

This guide covers testing strategies and best practices for Provability-Fabric applications, including unit testing, integration testing, and formal verification.

## Testing Strategy

### Testing Pyramid

```
    /\
   /  \     E2E Tests (Few)
  /____\    Integration Tests (Some)
 /______\   Unit Tests (Many)
```

### Test Types

1. **Unit Tests** - Test individual components in isolation
2. **Integration Tests** - Test component interactions
3. **End-to-End Tests** - Test complete workflows
4. **Formal Verification** - Mathematical proof of properties

## Unit Testing

### Go Testing

```go
package core

import (
    "testing"
    "github.com/stretchr/testify/assert"
)

func TestAgentCreation(t *testing.T) {
    spec := &AgentSpecification{
        Name: "test-agent",
        Version: "1.0.0",
    }
    
    agent, err := CreateAgent(spec)
    assert.NoError(t, err)
    assert.Equal(t, "test-agent", agent.Name)
    assert.Equal(t, "1.0.0", agent.Version)
}
```

### Rust Testing

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_agent_creation() {
        let spec = AgentSpecification {
            name: "test-agent".to_string(),
            version: "1.0.0".to_string(),
        };
        
        let agent = create_agent(spec).unwrap();
        assert_eq!(agent.name, "test-agent");
        assert_eq!(agent.version, "1.0.0");
    }
}
```

### Lean Testing

```lean
import Mathlib.Data.String.Basic

def test_agent_spec := {
  name := "test-agent"
  version := "1.0.0"
}

theorem test_agent_name : test_agent_spec.name = "test-agent" := by
  rfl

theorem test_agent_version : test_agent_spec.version = "1.0.0" := by
  rfl
```

### Rust workspace tests

The repository uses a Cargo workspace at the root. Typical commands from the repo root:

- `cargo test --workspace --exclude sidecar-watcher`
- `cargo test -p sidecar-watcher --lib` and `cargo test -p sidecar-watcher --tests` (explicit integration-test binaries only; see `runtime/sidecar-watcher/tests/README.md`)

Workspace crates with tests include `sidecar-watcher`, `labeler`, `http-get`, `file-read`, `attestor`, `kms-proxy`, `tool-broker`, and `wasm-sandbox`. **CI** mirrors this split via `.github/workflows/reusable-ci-rust.yml` (not a single blind `cargo test --workspace` that would pick up quarantined sidecar sources). For dependency license and advisory policy locally, run `cargo deny check` (see root `deny.toml`). See the [developer guide](developer-guide.md) and [CI reference](../reference/ci-reference.md).

### Benchmark SWE-bench smoke suite

The SWE-bench smoke suite runs in **deterministic mode** (no network, no model calls) to validate the bench pipeline and evidence formatting. Run from the repository root:

```bash
pytest tests/test_swebench_runner_smoke.py -q --tb=short
```

- **Fixtures**: `bench/swebench/fixtures/instances_smoke.jsonl` (placeholder instances for local/CI); tests use the runner with `--instances-file` and `--no-workspace` when using mock engine.
- **Behavior**: Invokes the runner with `--no-workspace` and local instances so the mock engine is used; no HuggingFace fetch and no OpenHands/LLM calls. On native Windows only `--engine mock` or `--mode deterministic` are allowed; real OpenHands runs and the SWE-bench harness require WSL or Linux. See `experiments/exp-step2-lite-smoke/env-checklist.md` and `experiments/scripts/check_wsl_env.py`.
- **Assertions**: Strict JSONL format for `predictions.jsonl` and `predictions.pfmeta.jsonl` (required keys, one valid JSON object per line); evidence dirs present with `run.log`, `model.patch`, `metadata.json`; when guarded, compliance summary and events.jsonl; two runs yield the same evidence structure.

### SWE-bench provider, eval cleanup, and compare gates (pytest)

Run from the repository root (no Docker or LLM required for these tests; Docker cleanup tests mock `subprocess.run`):

```bash
python -m pytest \
  tests/test_provider_env.py \
  tests/test_openhands_provider_env.py \
  tests/test_run_swebench_eval_cleanup.py \
  tests/test_experiments_compare_runs.py \
  tests/test_run_config.py \
  -v --tb=short
```

These cover **`provider_env`** (Prime default base URL, preflight messaging, credentials matrix), OpenHands engine credential helpers, **scoped** `sweb.eval.*.<run_id>` stale-container selection in `run_swebench_eval.py`, **`compare_runs.py`** strict flags (`--require-harness`, `--require-compliance`, `--require-patch-apply`, `--require-priced-models`), and **`RunConfig`** defaults including **`openhands_timeout` = 1200**. Manual WSL smoke steps and a budget drift table are in **`docs/internal/swebench-stabilization-regression-matrix.md`**.
- **CI**: `.github/workflows/bench-swebench-smoke.yaml` runs these tests on every PR (job `bench-smoke`). Optional `rust-tests` job; optional nightly with model calls gated by `BENCH_SWEBENCH_NIGHTLY_TOKEN`.

### Experiments and bench unit tests (synthetic fixtures)

Unit tests for experiments scripts and bench/swebench components run without Docker, OpenHands, or HuggingFace network. From the repository root:

```bash
# Matches `.github/workflows/bench-swebench-unit.yaml` (ubuntu + windows)
pytest tests/test_experiments_compare_runs.py tests/test_validate_predictions.py tests/test_check_no_stub.py tests/test_validate_pf_run.py tests/test_loader_from_file.py tests/test_workspace_plan.py tests/test_replay_roundtrip.py tests/test_swebench_runner_smoke.py tests/test_openhands_engine.py tests/test_policy_loader.py tests/test_cost_report.py tests/test_proof_hook.py tests/test_check_wsl_env.py tests/test_fill_manifest_from_run.py tests/test_list_delta_cases.py tests/test_bucket_pf_failures.py tests/test_policy_guard_deny_allow.py -v
```

Extended local run (adds modular runner and experiments helpers not all wired in that workflow yet):

```bash
pytest tests/test_run_config.py tests/test_runner_core.py tests/test_instance_processor.py tests/test_workspace_manager.py tests/test_evidence_writer.py tests/test_engine_interface.py tests/test_predictions_writer.py tests/test_summary_writer.py tests/test_runner_cost_reporter_facade.py tests/test_swebench_edge_cases.py tests/test_swebench_properties.py tests/test_error_recovery.py tests/test_summarize_stress_run.py -v
```

- **Fixture generator**: `tests/fixtures/gen_fake_runpair.py` builds a temporary tree (baseline/, pf/, predictions.jsonl, run_id/instance_id artifacts, eval reports) for tests. Used by compare_runs, validate_predictions, check_no_stub, and validate_pf_run tests.
- **Tests**: `test_experiments_compare_runs` (aggregate solve rates, patch_apply, empty_patch_reasons_topN, reproducibility fields, --require-harness run_id checks, stale-eval and predictions_sha256, --require-patch-apply gates, schema validation); `test_validate_predictions` (good predictions, empty file, pfmeta mismatch, non-diff with/without --allow-empty-patch, run_status partial with/without --allow-partial); `test_check_no_stub` (stub in model.patch fails, clean dirs pass); `test_validate_pf_run` (minimal PF dir passes, missing compliance fails); `test_loader_from_file` (load JSONL, max_instances, instance_ids filter); `test_workspace_plan` (WorkspaceManifest shape and hash, invalid repo raises, mocked git); `test_replay_roundtrip` (placeholder, skipped on Windows); `test_openhands_engine` (is_like_diff, timeout fallback [skipped on Windows], trajectory parse, path-restricted fallback); `test_policy_loader` (load swebench_safe_v1, hash determinism, required keys, unknown/missing pack); `test_cost_report` (build_cost_report, write_summary, load_summary with missing cost files); `test_proof_hook` (run_proof success writes proof.ok and proof_artifact_hash.txt, lake not found, write_proof_failure). **Contract tests:** `test_check_wsl_env` (fails with clear message when resource/fcntl missing, Docker unavailable or not found, datasets/swebench or openhands missing; passes when all mocked ok); `test_fill_manifest_from_run` (writes pf_commit and created_at, copies OPENHANDS_COMMIT/AGENT_COMMIT to agent_commit, writes experiment_manifest.json to run_dir when passed, not-in-git returns empty pf_commit); `test_list_delta_cases` (synthetic compare.csv produces baseline_solved_pf_failed.txt etc. with expected instance IDs); `test_bucket_pf_failures` (synthetic compare.csv and case bundles produce CSV with instance_id, bucket, pf_status, violations, reason_codes, notes); `test_policy_guard_deny_allow` (deny curl, wget, git clone https, pip install git+https; allow python -m pytest, pip install -e ., make test, grep, sed; allow writes under workspace; deny /tmp, -o to forbidden path). **Stress summary:** `test_summarize_stress_run` (synthetic runpair + compare.json produce stress_summary.json with timeout_rate_*, wall_clock_s median/p95, guard_overhead_s_median; second test asserts timeout_rate_pf from timing.json).
- **CI**: `.github/workflows/bench-swebench-unit.yaml` runs the first pytest command above on `ubuntu-latest` and `windows-latest` when relevant paths change (bench/swebench, experiments, tests). The extended list is recommended before large bench changes.
- **Golden cycle**: For the one trusted baseline+PF run (all gates pass, run-ids.md updated only via script), see `experiments/exp-step2-lite-smoke/golden-cycle.md` for the canonical pipeline command, required artifacts, and acceptance checks (solve rates numeric, patch_apply.applies_false == 0, validate_pf_run and check_no_stub exit 0).

## Integration Testing

### Test Environment Setup

```bash
# Start test environment
make test-env-up

# Run integration tests
make test-integration

# Clean up
make test-env-down
```

### Test Configuration

```yaml
# tests/config/test-config.yaml
test_environment:
  name: "integration-test"
  kubernetes_context: "kind-test"
  timeout_seconds: 300

test_data:
  agents:
    - name: "test-text-generator"
      specification: "fixtures/text-generator-spec.yaml"
    - name: "test-image-classifier"
      specification: "fixtures/image-classifier-spec.yaml"

verification:
  lean_timeout: 60
  marabou_timeout: 120
  dryvr_timeout: 180
```

## End-to-End Testing

### Complete Workflow Test

```python
import pytest
from provability_fabric import Client

class TestCompleteWorkflow:
    def test_agent_lifecycle(self):
        client = Client(api_key="test-key")
        
        # 1. Create agent
        agent = client.agents.create({
            "name": "e2e-test-agent",
            "version": "1.0.0",
            "specification": load_test_spec()
        })
        assert agent.status == "pending"
        
        # 2. Verify proofs
        proofs = client.proofs.list(agent_id=agent.id)
        for proof in proofs:
            result = client.proofs.verify(proof.id)
            assert result.status == "verified"
        
        # 3. Deploy agent
        deployment = client.deployments.create({
            "agent_id": agent.id,
            "environment": "test"
        })
        assert deployment.status == "running"
        
        # 4. Test functionality
        response = client.agents.generate_text(
            agent.id, 
            prompt="Hello, world!"
        )
        assert len(response.text) <= 1000
        
        # 5. Cleanup
        client.deployments.delete(deployment.id)
        client.agents.delete(agent.id)
```

## Formal Verification

### Lean Proof Verification

```bash
# Build and verify Lean proofs
lake build

# Check proof quality
make lean-gate

# Core libs (includes experimental ProofBench module when present)
cd core/lean-libs && lake build
```

### Neural Network Verification

```python
import marabou

def verify_neural_network(model_path, constraints):
    """Verify neural network properties using Marabou"""
    model = marabou.read_onnx(model_path)
    
    # Add verification constraints
    for constraint in constraints:
        model.addConstraint(constraint)
    
    # Solve verification problem
    status, vals = model.solve()
    
    if status == "sat":
        print("Property verification FAILED")
        return False
    else:
        print("Property verification PASSED")
        return True
```

## Performance Testing

### Load Testing

```python
import asyncio
import aiohttp
import time

async def load_test(agent_url, num_requests):
    """Perform load testing on agent endpoint"""
    async with aiohttp.ClientSession() as session:
        start_time = time.time()
        
        tasks = []
        for i in range(num_requests):
            task = session.post(
                f"{agent_url}/generate",
                json={"prompt": f"Request {i}"}
            )
            tasks.append(task)
        
        responses = await asyncio.gather(*tasks)
        total_time = time.time() - start_time
        
        success_count = sum(1 for r in responses if r.status == 200)
        rps = success_count / total_time
        
        print(f"Requests per second: {rps:.2f}")
        return rps
```

### Benchmarking

```bash
# Run Go benchmarks
go test -bench=. ./core/...

# Run Rust benchmarks
cargo bench

# Run Lean benchmarks
cd core/lean-libs && lake build
```

## Test Automation

### CI/CD Integration

```yaml
# .github/workflows/test.yml
name: Test

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3
    
    - name: Run unit tests
      run: make test-unit
    
    - name: Run integration tests
      run: make test-integration
    
    - name: Verify proofs
      run: make verify-proofs
    
    - name: Performance test
      run: make test-performance
```

### Test Reporting

```python
import json
import datetime

class TestReporter:
    def __init__(self):
        self.results = {
            "timestamp": datetime.datetime.now().isoformat(),
            "tests": []
        }
    
    def add_result(self, test_name, status, duration, details=None):
        self.results["tests"].append({
            "name": test_name,
            "status": status,
            "duration": duration,
            "details": details or {}
        })
    
    def save_report(self, filename):
        with open(filename, 'w') as f:
            json.dump(self.results, f, indent=2)
    
    def print_summary(self):
        total = len(self.results["tests"])
        passed = sum(1 for t in self.results["tests"] if t["status"] == "PASSED")
        failed = total - passed
        
        print(f"Test Summary: {passed}/{total} passed, {failed} failed")
```

## Best Practices

### Test Organization

1. **Group Related Tests** - Use test suites and classes
2. **Descriptive Names** - Test names should explain what they test
3. **Arrange-Act-Assert** - Structure tests clearly
4. **Test Data Management** - Use fixtures and factories

### Test Maintenance

1. **Keep Tests Fast** - Avoid slow operations in unit tests
2. **Isolate Tests** - Tests should not depend on each other
3. **Mock External Dependencies** - Use mocks for external services
4. **Update Tests with Code** - Keep tests current with implementation

### Test Coverage

```bash
# Generate coverage reports
go test -coverprofile=coverage.out ./...
go tool cover -html=coverage.out

# Rust coverage
cargo tarpaulin --out Html
```

## Troubleshooting

### Common Issues

1. **Test Timeouts** - Increase timeout values for slow tests
2. **Resource Conflicts** - Ensure tests use isolated resources
3. **Flaky Tests** - Add retry logic for timing-dependent tests
4. **Environment Issues** - Use consistent test environments

### Debug Tools

```bash
# Enable verbose output
go test -v ./...
cargo test -- --nocapture

# Run specific tests
go test -run TestSpecificFunction ./...
cargo test test_specific_function

# Debug with logging
RUST_LOG=debug cargo test
```

## Conclusion

Effective testing is crucial for maintaining quality in Provability-Fabric applications. Focus on:

- **Comprehensive Coverage** - Test all critical paths
- **Automation** - Integrate testing into CI/CD pipelines
- **Performance** - Include performance and load testing
- **Formal Verification** - Use mathematical proofs for critical properties
- **Maintenance** - Keep tests current and reliable

For more testing examples, see the [Examples](examples.md) document (in this folder).
