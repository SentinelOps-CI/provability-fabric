# α-β-CROWN Adapter for Provability Fabric

This adapter integrates α-β-CROWN, a GPU-accelerated neural network verifier, with the Provability Fabric framework.

**Status: unsupported / optional.** Requires an external α-β-CROWN install or Docker image. Not smoke-tested in Adapters CI — bring your own solver runtime.

## Features

- **GPU Acceleration**: Utilizes CUDA for faster verification
- **Complete Verification**: Provides provable robustness guarantees
- **Multiple Architectures**: Supports CNNs, ResNets, and other architectures
- **Standardized Output**: Generates JSON witness files compatible with Provability Fabric

## Installation

1. Build the Docker image:
```bash
docker build -t alpha-beta-crown:latest .
```

2. Install Python dependencies:
```bash
pip install -r requirements.txt
```

## Usage

### Command Line Interface

```bash
# Basic usage
python adapter.py model.pt property.json --out witness.json

# With GPU acceleration
python adapter.py model.pt property.json --out witness.json --gpu

# With custom timeout
python adapter.py model.pt property.json --out witness.json --timeout 1200
```

### Docker Usage

```bash
# Using the adapter script
./adapter.sh model.pt property.json witness.json --gpu --timeout 600
```

## Input Formats

### Model Files
- PyTorch models (`.pt` files)
- ONNX models (`.onnx` files)

### Property Files
JSON format specifying verification properties:

```json
{
  "type": "robustness",
  "input_bounds": {
    "lower": [0.0, 0.0, 0.0],
    "upper": [1.0, 1.0, 1.0]
  },
  "output_bounds": {
    "lower": [0.0],
    "upper": [1.0]
  },
  "epsilon": 0.1
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
      "layer": "layer_name",
      "lower_bound": 0.0,
      "upper_bound": 1.0,
      "method": "alpha_beta_crown"
    }
  ],
  "verification_result": "verified",
  "bounds": {
    "layer1": {"lower": 0.0, "upper": 1.0}
  },
  "execution_time": 120.5,
  "gpu_utilized": true
}
```

## Testing

Run the test suite:

```bash
python -m pytest tests/
```

Run benchmarks:

```bash
python benchmarks/run_benchmarks.py --models test_models/ --properties test_properties/ --output results/
```

## Integration with Provability Fabric

This adapter integrates seamlessly with the Provability Fabric proof service and specification bundles. It follows the same interface pattern as other adapters (Marabou, DryVR) and generates compatible witness files.

## Performance Characteristics

- **Speed**: 10-100x faster than CPU-based verification
- **Scalability**: Handles networks with millions of parameters
- **Memory**: Efficient GPU memory utilization
- **Accuracy**: Complete verification with no false positives

## Troubleshooting

### Common Issues

1. **CUDA not available**: Use `--no-gpu` flag to fall back to CPU
2. **Timeout errors**: Increase timeout with `--timeout` parameter
3. **Memory errors**: Reduce batch size or use CPU mode

### Debug Mode

Enable verbose output by setting environment variable:
```bash
export ALPHA_BETA_CROWN_DEBUG=1
python adapter.py model.pt property.json --out witness.json
```
