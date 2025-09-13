#!/usr/bin/env python3
"""
Benchmark suite for α-β-CROWN adapter performance testing.
"""

import time
import json
import subprocess
from pathlib import Path
import argparse


def run_benchmark(
    model_path: str,
    property_path: str,
    output_path: str,
    use_gpu: bool = True,
    timeout: int = 600,
):
    """Run a single benchmark test."""
    start_time = time.time()

    cmd = [
        "python",
        "adapter.py",
        model_path,
        property_path,
        "--out",
        output_path,
        "--timeout",
        str(timeout),
    ]

    if use_gpu:
        cmd.append("--gpu")
    else:
        cmd.append("--no-gpu")

    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        execution_time = time.time() - start_time

        return {
            "success": result.returncode == 0,
            "execution_time": execution_time,
            "stdout": result.stdout,
            "stderr": result.stderr,
        }
    except subprocess.TimeoutExpired:
        return {
            "success": False,
            "execution_time": timeout,
            "error": "Timeout exceeded",
        }


def main():
    parser = argparse.ArgumentParser(description="α-β-CROWN Adapter Benchmarks")
    parser.add_argument(
        "--models", required=True, help="Directory containing test models"
    )
    parser.add_argument(
        "--properties", required=True, help="Directory containing test properties"
    )
    parser.add_argument("--output", required=True, help="Output directory for results")
    parser.add_argument("--gpu", action="store_true", help="Use GPU acceleration")
    parser.add_argument("--timeout", type=int, default=600, help="Timeout in seconds")

    args = parser.parse_args()

    models_dir = Path(args.models)
    properties_dir = Path(args.properties)
    output_dir = Path(args.output)
    output_dir.mkdir(exist_ok=True)

    # Find all model files
    model_files = list(models_dir.glob("*.pt")) + list(models_dir.glob("*.onnx"))
    property_files = list(properties_dir.glob("*.json"))

    results = []

    for model_file in model_files:
        for property_file in property_files:
            print(f"Running benchmark: {model_file.name} + {property_file.name}")

            output_file = (
                output_dir / f"{model_file.stem}_{property_file.stem}_result.json"
            )

            result = run_benchmark(
                str(model_file),
                str(property_file),
                str(output_file),
                args.gpu,
                args.timeout,
            )

            results.append(
                {
                    "model": str(model_file),
                    "property": str(property_file),
                    "result": result,
                }
            )

    # Save benchmark results
    with open(output_dir / "benchmark_results.json", "w") as f:
        json.dump(results, f, indent=2)

    print(
        f"Benchmark completed. Results saved to {output_dir / 'benchmark_results.json'}"
    )


if __name__ == "__main__":
    main()
