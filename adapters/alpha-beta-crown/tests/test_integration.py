#!/usr/bin/env python3
"""
Integration tests for α-β-CROWN adapter with Provability Fabric.
"""

import subprocess
import json
import tempfile
from pathlib import Path
import sys
import os


def test_adapter_cli():
    """Test the adapter CLI interface."""
    # Create temporary files for testing
    with tempfile.NamedTemporaryFile(
        suffix=".pt", delete=False, mode="wb"
    ) as model_file:
        model_file.write(b"dummy model data")
        model_file.flush()
        model_path = model_file.name

    with tempfile.NamedTemporaryFile(
        suffix=".json", delete=False, mode="w"
    ) as property_file:
        property_data = {
            "type": "robustness",
            "input_bounds": {"lower": [0.0], "upper": [1.0]},
            "output_bounds": {"lower": [0.0], "upper": [1.0]},
            "epsilon": 0.1,
        }
        json.dump(property_data, property_file)
        property_file.flush()
        property_path = property_file.name

    with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as output_file:
        output_path = output_file.name

    try:
        # Test adapter help
        result = subprocess.run(
            [sys.executable, "adapter.py", "--help"],
            capture_output=True,
            text=True,
            cwd="adapters/alpha-beta-crown",
        )

        print(f"Return code: {result.returncode}")
        print(f"Stdout: {result.stdout}")
        print(f"Stderr: {result.stderr}")

        assert result.returncode == 0
        assert "adapter" in result.stdout.lower()

        print("✓ CLI help test passed")

        # Test adapter with mock files (will fail but should show proper error handling)
        result = subprocess.run(
            [
                sys.executable,
                "adapter.py",
                model_path,
                property_path,
                "--out",
                output_path,
                "--no-gpu",
                "--timeout",
                "10",
            ],
            capture_output=True,
            text=True,
            cwd="adapters/alpha-beta-crown",
        )

        # Should fail gracefully (no α-β-CROWN installed)
        assert result.returncode != 0
        print("✓ Error handling test passed")

    finally:
        # Clean up temporary files
        os.unlink(model_path)
        os.unlink(property_path)
        os.unlink(output_path)


def test_witness_format():
    """Test witness output format."""
    import sys
    from pathlib import Path

    sys.path.insert(0, str(Path(__file__).parent.parent))
    from adapter import AlphaBetaCrownAdapter, AlphaBetaCrownOutput

    # Test witness generation
    witness = AlphaBetaCrownOutput(
        hash="test_hash",
        proof=[{"type": "test_constraint"}],
        verification_result="verified",
        bounds={"layer1": {"lower": 0.0, "upper": 1.0}},
        execution_time=120.5,
        gpu_utilized=True,
    )

    # Test JSON serialization
    witness_json = witness.model_dump()
    assert witness_json["type"] == "alpha_beta_crown"
    assert witness_json["verification_result"] == "verified"
    assert witness_json["gpu_utilized"] == True

    print("✓ Witness format test passed")


def main():
    """Run all integration tests."""
    print("Running α-β-CROWN adapter integration tests...")

    test_adapter_cli()
    test_witness_format()

    print("All integration tests passed!")


if __name__ == "__main__":
    main()
