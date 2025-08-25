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

# Verify specific proofs
lake exe proofbench
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
lake exe proofbench --benchmark
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

For more testing examples, see the [Examples](examples.md) document.
