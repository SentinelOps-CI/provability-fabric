# α-β-CROWN Adapter Documentation

## Overview

The α-β-CROWN adapter provides GPU-accelerated neural network verification for the Provability Fabric ecosystem. It integrates the α-β-CROWN verifier, which has won multiple VNN-COMP competitions, to provide complete verification guarantees for neural networks with improved scalability and performance.

## Features

### Core Capabilities

- **GPU Acceleration**: Utilizes CUDA for 10-100x faster verification compared to CPU-based methods
- **Complete Verification**: Provides provable robustness guarantees with no false positives
- **Multiple Architectures**: Supports CNNs, ResNets, and other complex neural network architectures
- **Efficient Bounds**: Per-neuron split constraints for tighter bound propagation
- **Scalable Verification**: Handles networks with millions of parameters

### Integration Features

- **Standardized Interface**: Compatible with existing Provability Fabric adapter patterns
- **Docker Support**: Containerized execution for isolation and reproducibility
- **JSON Output**: Generates standardized witness files compatible with other adapters
- **Error Handling**: Robust timeout and failure management
- **CLI Interface**: Command-line tool with comprehensive options

## Installation

### Prerequisites

- Python 3.8 or higher
- CUDA-compatible GPU (optional, falls back to CPU)
- Docker (for containerized execution)
- 8GB+ RAM recommended for large models

### Quick Installation

1. **Clone the repository** (if not already done):
   ```bash
   git clone https://github.com/provability-fabric/provability-fabric.git
   cd provability-fabric
   ```

2. **Install Python dependencies**:
   ```bash
   cd adapters/alpha-beta-crown
   pip install -r requirements.txt
   ```

3. **Build Docker image** (optional):
   ```bash
   docker build -t alpha-beta-crown:latest .
   ```

### Development Installation

For development and testing:

```bash
# Install in development mode
pip install -e .

# Install additional development dependencies
pip install pytest pytest-cov black isort
```

## Usage

### Command Line Interface

The adapter provides a comprehensive CLI for neural network verification:

```bash
# Basic usage
python adapter.py model.pt property.json --out witness.json

# With GPU acceleration
python adapter.py model.pt property.json --out witness.json --gpu

# With custom timeout
python adapter.py model.pt property.json --out witness.json --timeout 1200

# CPU-only mode
python adapter.py model.pt property.json --out witness.json --no-gpu
```

### Docker Usage

For containerized execution:

```bash
# Using the adapter script
./adapter.sh model.pt property.json witness.json --gpu --timeout 600

# Direct Docker execution
docker run --rm --gpus all \
  -v $(pwd)/model.pt:/input/model.pt \
  -v $(pwd)/property.json:/input/property.json \
  -v $(pwd):/output \
  alpha-beta-crown:latest \
  python3 /opt/adapter.py \
  /input/model.pt /input/property.json \
  --out /output/witness.json --gpu
```

### Integration with Provability Fabric

The adapter integrates seamlessly with the Provability Fabric proof service:

```yaml
# In specification bundle
verification:
  type: alpha_beta_crown
  model: models/classifier.pt
  property: properties/robustness.json
  gpu_enabled: true
  timeout: 600
  options:
    device: cuda
    precision: double
```

## Input Formats

### Model Files

The adapter supports multiple neural network formats:

- **PyTorch Models** (`.pt` files): Native PyTorch model files
- **ONNX Models** (`.onnx` files): Open Neural Network Exchange format

### Property Files

Properties are specified in JSON format:

```json
{
  "type": "robustness",
  "input_bounds": {
    "lower": [0.0, 0.0, 0.0, 0.0],
    "upper": [1.0, 1.0, 1.0, 1.0]
  },
  "output_bounds": {
    "lower": [0.0],
    "upper": [1.0]
  },
  "epsilon": 0.1,
  "property": "adversarial_robustness",
  "description": "Verify robustness against adversarial perturbations"
}
```

#### Property Types

1. **Robustness Properties**:
   ```json
   {
     "type": "robustness",
     "input_bounds": {"lower": [...], "upper": [...]},
     "output_bounds": {"lower": [...], "upper": [...]},
     "epsilon": 0.1
   }
   ```

2. **Safety Properties**:
   ```json
   {
     "type": "safety",
     "input_bounds": {"lower": [...], "upper": [...]},
     "output_bounds": {"lower": [...], "upper": [...]},
     "constraint": "output < threshold"
   }
   ```

3. **Reachability Properties**:
   ```json
   {
     "type": "reachability",
     "initial_set": {"lower": [...], "upper": [...]},
     "unsafe_set": {"lower": [...], "upper": [...]}
   }
   ```

## Output Format

The adapter generates JSON witness files with the following structure:

```json
{
  "type": "alpha_beta_crown",
  "hash": "sha256_hash_of_model",
  "proof": [
    {
      "type": "bound_constraint",
      "layer": "conv1",
      "lower_bound": 0.0,
      "upper_bound": 0.5,
      "method": "alpha_beta_crown"
    },
    {
      "type": "verification_constraint",
      "property": "robustness",
      "verified": true,
      "method": "alpha_beta_crown"
    }
  ],
  "verification_result": "verified",
  "bounds": {
    "conv1": {"lower": 0.0, "upper": 0.5},
    "fc1": {"lower": -1.0, "upper": 1.0}
  },
  "counter_example": null,
  "execution_time": 120.5,
  "gpu_utilized": true
}
```

### Output Fields

- **`type`**: Always "alpha_beta_crown" for identification
- **`hash`**: SHA256 hash of the input model for integrity verification
- **`proof`**: Array of proof constraints and verification results
- **`verification_result`**: One of "verified", "falsified", "timeout", "error"
- **`bounds`**: Layer-wise bound information from verification
- **`counter_example`**: Input that violates the property (if falsified)
- **`execution_time`**: Verification time in seconds
- **`gpu_utilized`**: Whether GPU acceleration was used

## Configuration

### Environment Variables

```bash
# GPU settings
export CUDA_VISIBLE_DEVICES=0
export ALPHA_BETA_CROWN_DEVICE=cuda

# Memory settings
export ALPHA_BETA_CROWN_MAX_MEMORY=8GB

# Timeout settings
export ALPHA_BETA_CROWN_TIMEOUT=600

# Debug settings
export ALPHA_BETA_CROWN_DEBUG=1
```

### Configuration File

Create a `config.json` file for persistent settings:

```json
{
  "device": "cuda",
  "timeout": 600,
  "max_memory": "8GB",
  "precision": "double",
  "debug": false,
  "log_level": "INFO"
}
```

## Performance Optimization

### GPU Optimization

1. **Memory Management**:
   ```bash
   # Set GPU memory fraction
   export CUDA_VISIBLE_DEVICES=0
   export PYTORCH_CUDA_ALLOC_CONF=max_split_size_mb:512
   ```

2. **Batch Processing**:
   ```python
   # Process multiple properties in batch
   python adapter.py model.pt property1.json --batch property2.json property3.json
   ```

### CPU Optimization

1. **Parallel Processing**:
   ```bash
   # Use multiple CPU cores
   export OMP_NUM_THREADS=8
   python adapter.py model.pt property.json --no-gpu --threads 8
   ```

2. **Memory Optimization**:
   ```bash
   # Reduce memory usage
   python adapter.py model.pt property.json --no-gpu --low-memory
   ```

## Testing

### Unit Tests

Run the comprehensive test suite:

```bash
# Run all tests
python -m pytest tests/ -v

# Run specific test categories
python -m pytest tests/test_adapter.py -v
python -m pytest tests/test_integration.py -v
```

### Integration Tests

Test integration with Provability Fabric:

```bash
# Run integration tests
python tests/test_integration.py

# Test with real models
python tests/test_with_models.py --models test_models/ --properties test_properties/
```

### Benchmark Tests

Performance testing and comparison:

```bash
# Run benchmarks
python benchmarks/run_benchmarks.py \
  --models test_models/ \
  --properties test_properties/ \
  --output results/ \
  --gpu

# Compare with other adapters
python benchmarks/compare_adapters.py \
  --adapters marabou,alpha_beta_crown \
  --models test_models/
```

## Troubleshooting

### Common Issues

1. **CUDA Not Available**:
   ```bash
   # Check CUDA installation
   nvidia-smi
   
   # Use CPU fallback
   python adapter.py model.pt property.json --no-gpu
   ```

2. **Memory Errors**:
   ```bash
   # Reduce batch size
   python adapter.py model.pt property.json --batch-size 1
   
   # Use CPU mode
   python adapter.py model.pt property.json --no-gpu
   ```

3. **Timeout Errors**:
   ```bash
   # Increase timeout
   python adapter.py model.pt property.json --timeout 1800
   
   # Use faster verification mode
   python adapter.py model.pt property.json --fast-mode
   ```

### Debug Mode

Enable verbose logging for troubleshooting:

```bash
# Enable debug output
export ALPHA_BETA_CROWN_DEBUG=1
python adapter.py model.pt property.json --out witness.json

# Save debug logs
python adapter.py model.pt property.json --out witness.json --debug-log debug.log
```

### Performance Issues

1. **Slow Verification**:
   - Ensure GPU is being used: `gpu_utilized: true` in output
   - Check GPU memory usage: `nvidia-smi`
   - Consider using smaller models for testing

2. **High Memory Usage**:
   - Use CPU mode for large models
   - Reduce batch size
   - Enable memory optimization flags

## API Reference

### AlphaBetaCrownAdapter Class

```python
class AlphaBetaCrownAdapter:
    def __init__(
        self,
        model_path: str,
        property_path: str,
        output_path: str,
        use_gpu: bool = True,
        timeout: int = 600,
    ):
        """Initialize the α-β-CROWN adapter."""
        
    def run(self) -> int:
        """Run verification and return exit code."""
        
    def calculate_hash(self) -> str:
        """Calculate SHA256 hash of the model."""
        
    def generate_witness(self, crown_result: Dict) -> AlphaBetaCrownOutput:
        """Generate witness output from verification results."""
```

### AlphaBetaCrownOutput Class

```python
class AlphaBetaCrownOutput(pydantic.BaseModel):
    type: str = "alpha_beta_crown"
    hash: str
    proof: List[Dict]
    verification_result: str
    bounds: Optional[Dict[str, Any]] = None
    counter_example: Optional[List[float]] = None
    execution_time: float
    gpu_utilized: bool
```

## Contributing

### Development Setup

1. **Fork the repository**
2. **Create a feature branch**:
   ```bash
   git checkout -b feature/alpha-beta-crown-improvements
   ```

3. **Install development dependencies**:
   ```bash
   pip install -r requirements-dev.txt
   ```

4. **Run tests**:
   ```bash
   python -m pytest tests/ -v --cov=adapter
   ```

5. **Format code**:
   ```bash
   black adapter.py tests/
   isort adapter.py tests/
   ```

### Code Style

Follow the project's coding standards:

- Use type hints for all function parameters and return values
- Follow PEP 8 style guidelines
- Write comprehensive docstrings
- Include unit tests for all new functionality
- Update documentation for any API changes

## License

This adapter is licensed under the Apache License 2.0. See the [LICENSE](../../LICENSE) file for details.

## Acknowledgments

- [α-β-CROWN](https://github.com/Verified-Intelligence/alpha-beta-CROWN) - The underlying verification engine
- [Provability Fabric](https://github.com/provability-fabric/provability-fabric) - The parent framework
- [VNN-COMP](https://sites.google.com/view/vnn20) - Neural network verification competition
