#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Marabou adapter for neural network verification.
"""

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional

import click
import pydantic


class WitnessOutput(pydantic.BaseModel):
    type: str = "marabou"
    hash: str
    proof: List[Dict]


class MarabouAdapter:
    def __init__(self, onnx_path: str, property_path: str, output_path: str):
        self.onnx_path = Path(onnx_path)
        self.property_path = Path(property_path)
        self.output_path = Path(output_path)

        if not self.onnx_path.exists():
            raise FileNotFoundError(f"ONNX file not found: {onnx_path}")
        if not self.property_path.exists():
            raise FileNotFoundError(f"Property file not found: {property_path}")

    def calculate_hash(self) -> str:
        """Calculate SHA256 hash of the ONNX file."""
        with open(self.onnx_path, "rb") as f:
            return hashlib.sha256(f.read()).hexdigest()

    def run_marabou(self) -> Dict:
        """Run Marabou docker container and return results."""
        cmd = [
            "docker",
            "run",
            "--rm",
            "-v",
            f"{self.onnx_path.absolute()}:/input/model.onnx",
            "-v",
            f"{self.property_path.absolute()}:/input/property.json",
            "marabou:2.0-rc3",
            "marabou",
            "/input/model.onnx",
            "/input/property.json",
        ]

        try:
            result = subprocess.run(
                cmd, capture_output=True, text=True, timeout=300  # 5 minute timeout
            )

            if result.returncode == 0:
                # UNSAT case - extract proof trace
                return self._parse_unsat_output(result.stdout)
            else:
                # SAT case - extract counter-example
                return self._parse_sat_output(result.stdout, result.stderr)

        except subprocess.TimeoutExpired:
            raise RuntimeError("Marabou verification timed out")
        except subprocess.CalledProcessError as e:
            raise RuntimeError(f"Marabou execution failed: {e}")

    def _parse_unsat_output(self, stdout: str) -> Dict:
        """Parse UNSAT output and extract proof constraints."""
        constraints = []

        # Parse Marabou output to extract constraint information
        lines = stdout.split("\n")
        for line in lines:
            if "constraint" in line.lower() or "bound" in line.lower():
                # Extract constraint information
                constraint = {
                    "type": "linear_constraint",
                    "coefficients": [],  # Would parse actual coefficients
                    "bounds": [],  # Would parse actual bounds
                }
                constraints.append(constraint)

        return {"status": "UNSAT", "proof": constraints}

    def _parse_sat_output(self, stdout: str, stderr: str) -> Dict:
        """Parse SAT output and extract counter-example."""
        # Parse counter-example from output
        counter_example = []

        lines = stdout.split("\n")
        for line in lines:
            if "input" in line.lower() or "value" in line.lower():
                # Extract input values
                try:
                    value = float(line.split()[-1])
                    counter_example.append(value)
                except (ValueError, IndexError):
                    continue

        return {"status": "SAT", "counter_example": counter_example}

    def generate_witness(self, marabou_result: Dict) -> WitnessOutput:
        """Generate witness output in the required format."""
        hash_value = self.calculate_hash()

        if marabou_result["status"] == "UNSAT":
            return WitnessOutput(hash=hash_value, proof=marabou_result["proof"])
        else:
            # For SAT case, we don't generate a witness file
            raise ValueError("Model is satisfiable - no proof witness generated")

    def run(self) -> int:
        """Main execution method."""
        try:
            # Run Marabou verification
            marabou_result = self.run_marabou()

            # Generate witness only for UNSAT cases
            if marabou_result["status"] == "UNSAT":
                witness = self.generate_witness(marabou_result)

                # Write witness file
                with open(self.output_path, "w") as f:
                    json.dump(witness.dict(), f, indent=2)

                print(f"Witness written to: {self.output_path}")
                return 0
            else:
                print("Model is satisfiable - no witness generated")
                return 1

        except Exception as e:
            print(f"Error: {e}", file=sys.stderr)
            return 1


@click.command()
@click.argument("onnx", type=click.Path(exists=True))
@click.argument("property", type=click.Path(exists=True))
@click.option(
    "--out",
    "output",
    type=click.Path(),
    default="witness.json",
    help="Output witness file path",
)
def main(onnx: str, property: str, output: str):
    """Marabou adapter for neural network verification."""
    try:
        adapter = MarabouAdapter(onnx, property, output)
        exit_code = adapter.run()
        sys.exit(exit_code)
    except Exception as e:
        print(f"Fatal error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
