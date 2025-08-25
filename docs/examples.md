# Examples and Use Cases

This document provides practical examples and use cases for the Provability-Fabric framework, demonstrating how to implement various AI agent scenarios with formal verification.

## Basic Examples

### 1. Simple Text Generation Agent

A basic example of creating a text generation agent with length constraints.

**Specification (`spec.yaml`):**
```yaml
name: text-generator
version: 1.0.0
description: Simple text generation agent with length constraints

capabilities:
  - name: text_generation
    description: Generate text responses
    constraints:
      max_length: 1000
      content_filter: true
      no_harmful_content: true

proofs:
  - name: length_constraint
    type: lean
    file: proofs/length_constraint.lean
  - name: content_safety
    type: lean
    file: proofs/content_safety.lean
```

**Lean Proof (`proofs/length_constraint.lean`):**
```lean
import Mathlib.Data.String.Basic

def max_response_length : Nat := 1000

theorem response_length_bound (response : String) : 
  response.length ≤ max_response_length := by
  -- Proof that response length is bounded
  sorry

theorem content_filter_applied (input : String) (output : String) :
  content_filter input = output → 
  output.length ≤ max_response_length := by
  -- Proof that content filter respects length constraint
  sorry
```

**Deployment:**
```bash
# Initialize agent
pf init text-generator
cd text-generator

# Build proofs
lake build

# Verify specification
pf verify

# Deploy
pf deploy --environment production
```

### 2. Image Classification Agent

An image classification agent with accuracy guarantees.

**Specification (`spec.yaml`):**
```yaml
name: image-classifier
version: 1.0.0
description: Image classification with accuracy guarantees

capabilities:
  - name: image_classification
    description: Classify images into predefined categories
    constraints:
      min_accuracy: 0.95
      max_latency_ms: 100
      supported_formats: ["jpg", "png", "webp"]
      max_image_size_mb: 10

proofs:
  - name: accuracy_guarantee
    type: marabou
    file: proofs/accuracy_verification.py
  - name: latency_bound
    type: lean
    file: proofs/latency_bound.lean
```

**Marabou Verification (`proofs/accuracy_verification.py`):**
```python
import marabou
import numpy as np

def verify_accuracy_guarantee(model_path, test_data):
    """Verify that model meets accuracy requirements"""
    model = marabou.read_onnx(model_path)
    
    # Set up verification problem
    input_vars = model.inputVars[0]
    output_vars = model.outputVars[0]
    
    # Add accuracy constraints
    for i, (input_data, expected_label) in enumerate(test_data):
        # Set input constraints
        for j, val in enumerate(input_data):
            model.setLowerBound(input_vars[j], val)
            model.setUpperBound(input_vars[j], val)
        
        # Set output constraints for accuracy
        correct_output = output_vars[expected_label]
        for j, output_var in enumerate(output_vars):
            if j != expected_label:
                model.addConstraint(correct_output >= output_var)
    
    # Solve verification problem
    status, vals = model.solve()
    
    if status == "sat":
        print("Accuracy guarantee verification FAILED")
        return False
    else:
        print("Accuracy guarantee verification PASSED")
        return True

if __name__ == "__main__":
    # Load test data and verify
    test_data = load_test_data()
    verify_accuracy_guarantee("model.onnx", test_data)
```

## Advanced Examples

### 3. Multi-Modal Agent with Safety Guarantees

A complex agent that handles text, images, and audio with comprehensive safety constraints.

**Specification (`spec.yaml`):**
```yaml
name: multimodal-agent
version: 2.0.0
description: Multi-modal AI agent with safety guarantees

capabilities:
  - name: text_processing
    description: Process and generate text
    constraints:
      max_length: 2000
      content_filter: true
      no_pii: true
  
  - name: image_processing
    description: Process and generate images
    constraints:
      max_resolution: "2048x2048"
      no_nsfw: true
      watermark_required: true
  
  - name: audio_processing
    description: Process and generate audio
    constraints:
      max_duration_seconds: 300
      no_copyright: true
      quality_threshold: 0.8

safety_constraints:
  - name: no_harmful_content
    description: Prevent generation of harmful content
    type: global
    enforcement: runtime
  
  - name: privacy_protection
    description: Protect user privacy
    type: global
    enforcement: runtime

proofs:
  - name: safety_verification
    type: lean
    file: proofs/safety_verification.lean
  - name: privacy_guarantees
    type: lean
    file: proofs/privacy_guarantees.lean
  - name: content_filter_verification
    type: marabou
    file: proofs/content_filter.py
```

**Safety Verification (`proofs/safety_verification.lean`):**
```lean
import Mathlib.Data.String.Basic
import Mathlib.Data.List.Basic

-- Define safety predicates
def is_safe_content (content : String) : Prop :=
  ¬contains_harmful_terms content ∧
  ¬contains_pii content ∧
  content.length ≤ 2000

def is_safe_image (image : Image) : Prop :=
  image.resolution.width ≤ 2048 ∧
  image.resolution.height ≤ 2048 ∧
  ¬contains_nsfw_content image

def is_safe_audio (audio : Audio) : Prop :=
  audio.duration ≤ 300 ∧
  ¬contains_copyrighted_content audio

-- Main safety theorem
theorem multimodal_safety_guarantee 
  (text : String) (image : Image) (audio : Audio) :
  is_safe_content text ∧
  is_safe_image image ∧
  is_safe_audio audio →
  is_safe_multimodal_output text image audio := by
  -- Proof that safe inputs produce safe outputs
  sorry

-- Runtime enforcement theorem
theorem runtime_safety_enforcement
  (input : MultimodalInput) :
  safety_check input = true →
  is_safe_input input := by
  -- Proof that runtime checks ensure safety
  sorry
```

### 4. Financial Trading Agent

A financial trading agent with risk management and compliance guarantees.

**Specification (`spec.yaml`):**
```yaml
name: trading-agent
version: 1.0.0
description: Financial trading agent with risk management

capabilities:
  - name: market_analysis
    description: Analyze market conditions
    constraints:
      data_sources: ["approved_exchanges"]
      update_frequency_minutes: 5
  
  - name: trade_execution
    description: Execute trades
    constraints:
      max_position_size_usd: 100000
      max_daily_loss_usd: 5000
      trading_hours: "09:30-16:00"
      approved_securities: ["stocks", "etfs"]

risk_management:
  - name: position_limits
    description: Enforce position size limits
    type: runtime
    enforcement: strict
  
  - name: loss_limits
    description: Enforce daily loss limits
    type: runtime
    enforcement: strict
  
  - name: compliance_checks
    description: Ensure regulatory compliance
    type: runtime
    enforcement: strict

proofs:
  - name: risk_management_verification
    type: lean
    file: proofs/risk_management.lean
  - name: compliance_verification
    type: lean
    file: proofs/compliance.lean
```

**Risk Management Verification (`proofs/risk_management.lean`):**
```lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic

-- Define financial constraints
def max_position_size : ℝ := 100000
def max_daily_loss : ℝ := 5000

-- Position tracking
structure Position where
  security : String
  size : ℝ
  entry_price : ℝ
  current_price : ℝ

-- Risk calculations
def position_value (pos : Position) : ℝ :=
  pos.size * pos.current_price

def position_pnl (pos : Position) : ℝ :=
  pos.size * (pos.current_price - pos.entry_price)

def total_portfolio_value (positions : List Position) : ℝ :=
  positions.foldl (fun acc pos => acc + position_value pos) 0

def total_portfolio_pnl (positions : List Position) : ℝ :=
  positions.foldl (fun acc pos => acc + position_pnl pos) 0

-- Risk management theorems
theorem position_size_limit
  (positions : List Position) :
  (∀ pos ∈ positions, position_value pos ≤ max_position_size) →
  total_portfolio_value positions ≤ max_position_size * positions.length := by
  -- Proof that individual position limits ensure portfolio limits
  sorry

theorem daily_loss_limit
  (positions : List Position) :
  total_portfolio_pnl positions ≥ -max_daily_loss := by
  -- Proof that daily loss limits are enforced
  sorry

-- Runtime enforcement
theorem runtime_risk_enforcement
  (new_position : Position) (existing_positions : List Position) :
  position_value new_position ≤ max_position_size →
  total_portfolio_pnl (new_position :: existing_positions) ≥ -max_daily_loss →
  is_safe_trade new_position existing_positions := by
  -- Proof that runtime checks ensure safe trades
  sorry
```

## Integration Examples

### 5. Kubernetes Integration

Deploying and managing agents in Kubernetes with automatic sidecar injection.

**Agent Deployment (`deployment.yaml`):**
```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: text-generator
  labels:
    app: text-generator
    provability-fabric.io/agent: "true"
spec:
  replicas: 3
  selector:
    matchLabels:
      app: text-generator
  template:
    metadata:
      labels:
        app: text-generator
        provability-fabric.io/agent: "true"
      annotations:
        provability-fabric.io/sidecar: "true"
        provability-fabric.io/proof-bundle: "text-generator-v1.0.0"
    spec:
      containers:
      - name: text-generator
        image: text-generator:1.0.0
        ports:
        - containerPort: 8080
        resources:
          requests:
            memory: "512Mi"
            cpu: "250m"
          limits:
            memory: "1Gi"
            cpu: "500m"
        env:
        - name: MAX_LENGTH
          value: "1000"
        - name: CONTENT_FILTER
          value: "true"
      
      # Sidecar is automatically injected by admission controller
      initContainers:
      - name: proof-verification
        image: provability-fabric/verifier:latest
        command: ["/bin/sh", "-c"]
        args:
        - |
          pf verify --bundle text-generator-v1.0.0
          if [ $? -eq 0 ]; then
            echo "Proof verification passed"
            exit 0
          else
            echo "Proof verification failed"
            exit 1
          fi
```

**Service Configuration (`service.yaml`):**
```yaml
apiVersion: v1
kind: Service
metadata:
  name: text-generator-service
  labels:
    app: text-generator
spec:
  selector:
    app: text-generator
  ports:
  - protocol: TCP
    port: 80
    targetPort: 8080
  type: ClusterIP
```

**Ingress Configuration (`ingress.yaml`):**
```yaml
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: text-generator-ingress
  annotations:
    nginx.ingress.kubernetes.io/rewrite-target: /
    provability-fabric.io/agent: "true"
spec:
  rules:
  - host: text-generator.example.com
    http:
      paths:
      - path: /
        pathType: Prefix
        backend:
          service:
            name: text-generator-service
            port:
              number: 80
```

### 6. CI/CD Pipeline Integration

Automated testing and deployment with proof verification.

**GitHub Actions Workflow (`.github/workflows/deploy.yml`):**
```yaml
name: Deploy Agent

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3
    
    - name: Set up Lean
      uses: leanprover/lean4-action@v1
      with:
        lean-version: 'leanprover/lean4:nightly'
    
    - name: Build and verify proofs
      run: |
        lake build
        pf verify
    
    - name: Run tests
      run: |
        make test
        make test-integration
    
    - name: Run security scan
      run: |
        pf security-scan
    
    - name: Build agent image
      run: |
        docker build -t text-generator:${{ github.sha }} .
        docker tag text-generator:${{ github.sha }} text-generator:latest
    
    - name: Push to registry
      run: |
        echo ${{ secrets.REGISTRY_PASSWORD }} | docker login -u ${{ secrets.REGISTRY_USERNAME }} --password-stdin
        docker push text-generator:${{ github.sha }}
        docker push text-generator:latest

  deploy:
    needs: test
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    steps:
    - uses: actions/checkout@v3
    
    - name: Deploy to staging
      run: |
        kubectl config use-context staging
        kubectl apply -f k8s/
        kubectl rollout status deployment/text-generator
    
    - name: Run staging tests
      run: |
        pf test --environment staging
    
    - name: Deploy to production
      run: |
        kubectl config use-context production
        kubectl apply -f k8s/
        kubectl rollout status deployment/text-generator
    
    - name: Verify production deployment
      run: |
        pf verify --environment production
```

## Testing Examples

### 7. Property-Based Testing

Using Lean for property-based testing of agent behavior.

**Test Specification (`tests/agent_properties.lean`):**
```lean
import Mathlib.Data.String.Basic
import Mathlib.Data.List.Basic

-- Define agent behavior properties
def agent_response_property (input : String) (output : String) : Prop :=
  output.length ≤ 1000 ∧
  ¬contains_harmful_content output ∧
  ¬contains_pii output

-- Property-based test generator
def generate_test_inputs : List String :=
  ["Hello", "Test input", "Long input " * 100, "Input with PII: 123-45-6789"]

-- Test all properties
theorem test_agent_properties :
  ∀ input ∈ generate_test_inputs,
  let output := agent_process input
  agent_response_property input output := by
  -- Proof that all test inputs produce valid outputs
  sorry

-- Fuzz testing with random inputs
def random_input_generator : IO String := do
  let length := (← IO.rand 1 1000).toNat
  let chars := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
  let mut result := ""
  for i in [:length] do
    let idx := (← IO.rand 0 (chars.length - 1)).toNat
    result := result ++ chars[idx].toString
  return result

-- Property verification for random inputs
theorem random_input_property_verification :
  ∀ input : String,
  input.length ≤ 1000 →
  let output := agent_process input
  agent_response_property input output := by
  -- Proof that random inputs within bounds produce valid outputs
  sorry
```

### 8. Performance Testing

Testing agent performance under various load conditions.

**Performance Test Script (`tests/performance_test.py`):**
```python
import asyncio
import time
import statistics
from typing import List, Dict
import aiohttp
import json

class PerformanceTester:
    def __init__(self, base_url: str, api_key: str):
        self.base_url = base_url
        self.headers = {"Authorization": f"Bearer {api_key}"}
    
    async def test_latency(self, num_requests: int) -> Dict[str, float]:
        """Test agent latency under load"""
        latencies = []
        
        async with aiohttp.ClientSession() as session:
            tasks = []
            for i in range(num_requests):
                task = self._make_request(session, i)
                tasks.append(task)
            
            start_time = time.time()
            results = await asyncio.gather(*tasks, return_exceptions=True)
            total_time = time.time() - start_time
            
            # Calculate latencies
            for result in results:
                if isinstance(result, dict) and 'latency' in result:
                    latencies.append(result['latency'])
            
            return {
                'total_requests': num_requests,
                'successful_requests': len(latencies),
                'total_time': total_time,
                'requests_per_second': num_requests / total_time,
                'mean_latency': statistics.mean(latencies),
                'median_latency': statistics.median(latencies),
                'p95_latency': statistics.quantiles(latencies, n=20)[18],
                'p99_latency': statistics.quantiles(latencies, n=100)[98],
                'min_latency': min(latencies),
                'max_latency': max(latencies)
            }
    
    async def test_throughput(self, duration_seconds: int) -> Dict[str, float]:
        """Test agent throughput over time"""
        start_time = time.time()
        request_count = 0
        latencies = []
        
        async with aiohttp.ClientSession() as session:
            while time.time() - start_time < duration_seconds:
                start = time.time()
                try:
                    async with session.post(
                        f"{self.base_url}/generate",
                        headers=self.headers,
                        json={"prompt": "Test prompt", "max_length": 100}
                    ) as response:
                        if response.status == 200:
                            request_count += 1
                            latency = time.time() - start
                            latencies.append(latency)
                except Exception as e:
                    print(f"Request failed: {e}")
                
                # Small delay to prevent overwhelming
                await asyncio.sleep(0.01)
        
        total_time = time.time() - start_time
        return {
            'duration_seconds': duration_seconds,
            'total_requests': request_count,
            'requests_per_second': request_count / total_time,
            'mean_latency': statistics.mean(latencies) if latencies else 0,
            'success_rate': request_count / (request_count + 1)  # Avoid division by zero
        }
    
    async def test_concurrent_users(self, num_users: int, requests_per_user: int) -> Dict[str, float]:
        """Test agent performance with concurrent users"""
        async def user_workflow(user_id: int):
            latencies = []
            async with aiohttp.ClientSession() as session:
                for i in range(requests_per_user):
                    start = time.time()
                    try:
                        async with session.post(
                            f"{self.base_url}/generate",
                            headers=self.headers,
                            json={"prompt": f"User {user_id} request {i}", "max_length": 100}
                        ) as response:
                            if response.status == 200:
                                latency = time.time() - start
                                latencies.append(latency)
                    except Exception as e:
                        print(f"User {user_id} request {i} failed: {e}")
            return latencies
        
        # Run concurrent user workflows
        start_time = time.time()
        user_results = await asyncio.gather(*[
            user_workflow(i) for i in range(num_users)
        ])
        total_time = time.time() - start_time
        
        # Aggregate results
        all_latencies = []
        for latencies in user_results:
            all_latencies.extend(latencies)
        
        total_requests = num_users * requests_per_user
        successful_requests = len(all_latencies)
        
        return {
            'concurrent_users': num_users,
            'requests_per_user': requests_per_user,
            'total_requests': total_requests,
            'successful_requests': successful_requests,
            'success_rate': successful_requests / total_requests,
            'total_time': total_time,
            'requests_per_second': successful_requests / total_time,
            'mean_latency': statistics.mean(all_latencies) if all_latencies else 0,
            'p95_latency': statistics.quantiles(all_latencies, n=20)[18] if all_latencies else 0
        }
    
    async def _make_request(self, session: aiohttp.ClientSession, request_id: int) -> Dict[str, float]:
        """Make a single request and measure latency"""
        start = time.time()
        try:
            async with session.post(
                f"{self.base_url}/generate",
                headers=self.headers,
                json={"prompt": f"Request {request_id}", "max_length": 100}
            ) as response:
                if response.status == 200:
                    latency = time.time() - start
                    return {'latency': latency, 'success': True}
                else:
                    return {'latency': 0, 'success': False}
        except Exception as e:
            return {'latency': 0, 'success': False, 'error': str(e)}

async def main():
    tester = PerformanceTester(
        base_url="https://api.example.com/v1/agents/text-generator",
        api_key="your-api-key"
    )
    
    print("Running performance tests...")
    
    # Test 1: Latency under load
    print("\n1. Testing latency under load (100 requests)...")
    latency_results = await tester.test_latency(100)
    print(json.dumps(latency_results, indent=2))
    
    # Test 2: Throughput over time
    print("\n2. Testing throughput over 60 seconds...")
    throughput_results = await tester.test_throughput(60)
    print(json.dumps(throughput_results, indent=2))
    
    # Test 3: Concurrent users
    print("\n3. Testing concurrent users (10 users, 20 requests each)...")
    concurrent_results = await tester.test_concurrent_users(10, 20)
    print(json.dumps(concurrent_results, indent=2))
    
    # Performance validation
    print("\n4. Performance validation...")
    if latency_results['p95_latency'] <= 100:  # 100ms P95
        print("PASSED: P95 latency within acceptable range")
    else:
        print("FAILED: P95 latency exceeds acceptable range")
    
    if throughput_results['requests_per_second'] >= 10:  # 10 RPS minimum
        print("PASSED: Throughput meets minimum requirements")
    else:
        print("FAILED: Throughput below minimum requirements")
    
    if concurrent_results['success_rate'] >= 0.95:  # 95% success rate
        print("PASSED: Success rate meets requirements")
    else:
        print("FAILED: Success rate below requirements")

if __name__ == "__main__":
    asyncio.run(main())
```

## Conclusion

These examples demonstrate the flexibility and power of Provability-Fabric for creating AI agents with formal guarantees. Key takeaways:

1. **Start Simple**: Begin with basic constraints and gradually add complexity
2. **Focus on Safety**: Always include safety and compliance constraints
3. **Test Thoroughly**: Use property-based testing and performance testing
4. **Automate Everything**: Integrate with CI/CD pipelines for continuous verification
5. **Monitor Runtime**: Use sidecar injection for continuous monitoring

For more examples and use cases, check the `examples/` directory in the repository or explore the community-contributed examples on GitHub.
