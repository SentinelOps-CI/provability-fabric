#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

α-β-CROWN adapter for GPU-accelerated neural network verification.
"""

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Dict, List, Optional, Any
import click
import pydantic


class AlphaBetaCrownOutput(pydantic.BaseModel):
    type: str = "alpha_beta_crown"
    hash: str
    proof: List[Dict]
    verification_result: str  # "verified", "falsified", "timeout", "error"
    bounds: Optional[Dict[str, Any]] = None
    counter_example: Optional[List[float]] = None
    execution_time: float
    gpu_utilized: bool


class AlphaBetaCrownAdapter:
    def __init__(
        self,
        model_path: str,
        property_path: str,
        output_path: str,
        use_gpu: bool = True,
        timeout: int = 600,
    ):
        self.model_path = Path(model_path)
        self.property_path = Path(property_path)
        self.output_path = Path(output_path)
        self.use_gpu = use_gpu
        self.timeout = timeout

        if not self.model_path.exists():
            raise FileNotFoundError(f"Model file not found: {model_path}")
        if not self.property_path.exists():
            raise FileNotFoundError(f"Property file not found: {property_path}")

    def calculate_hash(self) -> str:
        """Calculate SHA256 hash of the model file."""
        with open(self.model_path, "rb") as f:
            return hashlib.sha256(f.read()).hexdigest()

    def run_alpha_beta_crown(self) -> Dict:
        """Run α-β-CROWN verification and return results."""
        # Create temporary directory for α-β-CROWN execution
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)

            # Prepare command for α-β-CROWN
            cmd = [
                "python",
                "-m",
                "alpha_beta_crown.main",
                "--model",
                str(self.model_path),
                "--property",
                str(self.property_path),
                "--output_dir",
                str(temp_path),
                "--timeout",
                str(self.timeout),
            ]

            if self.use_gpu:
                cmd.extend(["--device", "cuda"])
            else:
                cmd.extend(["--device", "cpu"])

            try:
                result = subprocess.run(
                    cmd,
                    capture_output=True,
                    text=True,
                    timeout=self.timeout,
                    cwd="src/alpha-beta-crown",
                )

                if result.returncode == 0:
                    return self._parse_success_output(result.stdout, temp_path)
                else:
                    return self._parse_error_output(result.stdout, result.stderr)

            except subprocess.TimeoutExpired:
                return {
                    "status": "timeout",
                    "verification_result": "timeout",
                    "error": "Alpha-Beta-CROWN verification timed out",
                }
            except subprocess.CalledProcessError as e:
                return {
                    "status": "error",
                    "verification_result": "error",
                    "error": f"Alpha-Beta-CROWN execution failed: {e}",
                }

    def _parse_success_output(self, stdout: str, output_dir: Path) -> Dict:
        """Parse successful α-β-CROWN output."""
        # Look for result files in output directory
        result_files = list(output_dir.glob("*.json"))

        if not result_files:
            return {
                "status": "error",
                "verification_result": "error",
                "error": "No result files found",
            }

        # Parse the main result file
        with open(result_files[0], "r") as f:
            result_data = json.load(f)

        # Extract verification result
        verification_result = result_data.get("verification_result", "unknown")
        bounds = result_data.get("bounds", {})
        counter_example = result_data.get("counter_example")

        # Generate proof constraints
        proof_constraints = self._generate_proof_constraints(result_data)

        return {
            "status": "success",
            "verification_result": verification_result,
            "bounds": bounds,
            "counter_example": counter_example,
            "proof": proof_constraints,
            "execution_time": result_data.get("execution_time", 0.0),
        }

    def _parse_error_output(self, stdout: str, stderr: str) -> Dict:
        """Parse error output from α-β-CROWN."""
        error_msg = stderr if stderr else stdout
        return {"status": "error", "verification_result": "error", "error": error_msg}

    def _generate_proof_constraints(self, result_data: Dict) -> List[Dict]:
        """Generate proof constraints from α-β-CROWN results."""
        constraints = []

        # Extract bound constraints
        bounds = result_data.get("bounds", {})
        for layer, bound_info in bounds.items():
            constraint = {
                "type": "bound_constraint",
                "layer": layer,
                "lower_bound": bound_info.get("lower", 0.0),
                "upper_bound": bound_info.get("upper", 1.0),
                "method": "alpha_beta_crown",
            }
            constraints.append(constraint)

        # Add verification-specific constraints
        if result_data.get("verification_result") == "verified":
            constraint = {
                "type": "verification_constraint",
                "property": "robustness",
                "verified": True,
                "method": "alpha_beta_crown",
            }
            constraints.append(constraint)

        return constraints

    def generate_witness(self, crown_result: Dict) -> AlphaBetaCrownOutput:
        """Generate witness output in the required format."""
        hash_value = self.calculate_hash()

        return AlphaBetaCrownOutput(
            hash=hash_value,
            proof=crown_result.get("proof", []),
            verification_result=crown_result.get("verification_result", "error"),
            bounds=crown_result.get("bounds"),
            counter_example=crown_result.get("counter_example"),
            execution_time=crown_result.get("execution_time", 0.0),
            gpu_utilized=self.use_gpu,
        )

    def run(self) -> int:
        """Main execution method."""
        try:
            # Run α-β-CROWN verification
            crown_result = self.run_alpha_beta_crown()

            # Generate witness
            witness = self.generate_witness(crown_result)

            # Write witness file
            with open(self.output_path, "w") as f:
                json.dump(witness.model_dump(), f, indent=2)

            print(f"Alpha-Beta-CROWN witness written to: {self.output_path}")
            print(f"Verification result: {witness.verification_result}")

            return 0 if witness.verification_result in ["verified", "falsified"] else 1

        except Exception as e:
            print(f"Error: {e}", file=sys.stderr)
            return 1


@click.command()
@click.argument("model", type=click.Path(exists=True))
@click.argument("property", type=click.Path(exists=True))
@click.option(
    "--out",
    "output",
    type=click.Path(),
    default="witness.json",
    help="Output witness file path",
)
@click.option("--gpu/--no-gpu", default=True, help="Use GPU acceleration")
@click.option("--timeout", type=int, default=600, help="Timeout in seconds")
def main(model: str, property: str, output: str, gpu: bool, timeout: int):
    """Alpha-Beta-CROWN adapter for GPU-accelerated neural network verification."""
    try:
        adapter = AlphaBetaCrownAdapter(model, property, output, gpu, timeout)
        exit_code = adapter.run()
        sys.exit(exit_code)
    except Exception as e:
        print(f"Fatal error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
