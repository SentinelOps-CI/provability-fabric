import pytest
import json
import tempfile
from pathlib import Path
import sys
import os

# Add the parent directory to the path so we can import the adapter
sys.path.insert(0, str(Path(__file__).parent.parent))
from adapter import AlphaBetaCrownAdapter


class TestAlphaBetaCrownAdapter:
    def test_adapter_initialization(self):
        """Test adapter initialization with valid inputs."""
        with tempfile.NamedTemporaryFile(suffix=".pt") as model_file:
            with tempfile.NamedTemporaryFile(suffix=".json") as property_file:
                with tempfile.NamedTemporaryFile(suffix=".json") as output_file:
                    adapter = AlphaBetaCrownAdapter(
                        model_file.name, property_file.name, output_file.name
                    )
                    assert adapter.model_path == Path(model_file.name)
                    assert adapter.property_path == Path(property_file.name)
                    assert adapter.output_path == Path(output_file.name)

    def test_hash_calculation(self):
        """Test model hash calculation."""
        with tempfile.NamedTemporaryFile(suffix=".pt") as model_file:
            model_file.write(b"test model data")
            model_file.flush()

            with tempfile.NamedTemporaryFile(suffix=".json") as property_file:
                with tempfile.NamedTemporaryFile(suffix=".json") as output_file:
                    adapter = AlphaBetaCrownAdapter(
                        model_file.name, property_file.name, output_file.name
                    )
                    hash_value = adapter.calculate_hash()
                    assert isinstance(hash_value, str)
                    assert len(hash_value) == 64  # SHA256 length

    def test_witness_generation(self):
        """Test witness generation from verification results."""
        with tempfile.NamedTemporaryFile(suffix=".pt") as model_file:
            with tempfile.NamedTemporaryFile(suffix=".json") as property_file:
                with tempfile.NamedTemporaryFile(suffix=".json") as output_file:
                    adapter = AlphaBetaCrownAdapter(
                        model_file.name, property_file.name, output_file.name
                    )

                    # Mock verification result
                    mock_result = {
                        "status": "success",
                        "verification_result": "verified",
                        "bounds": {"layer1": {"lower": 0.0, "upper": 1.0}},
                        "proof": [{"type": "bound_constraint", "layer": "layer1"}],
                        "execution_time": 120.5,
                    }

                    witness = adapter.generate_witness(mock_result)
                    assert witness.type == "alpha_beta_crown"
                    assert witness.verification_result == "verified"
                    assert witness.gpu_utilized is not None

    def test_proof_constraints_generation(self):
        """Test proof constraints generation from results."""
        with tempfile.NamedTemporaryFile(suffix=".pt") as model_file:
            with tempfile.NamedTemporaryFile(suffix=".json") as property_file:
                with tempfile.NamedTemporaryFile(suffix=".json") as output_file:
                    adapter = AlphaBetaCrownAdapter(
                        model_file.name, property_file.name, output_file.name
                    )

                    # Test data with bounds
                    result_data = {
                        "verification_result": "verified",
                        "bounds": {
                            "conv1": {"lower": 0.0, "upper": 0.5},
                            "fc1": {"lower": -1.0, "upper": 1.0},
                        },
                    }

                    constraints = adapter._generate_proof_constraints(result_data)

                    # Should have bound constraints for each layer
                    assert len(constraints) >= 2

                    # Check bound constraints
                    bound_constraints = [
                        c for c in constraints if c["type"] == "bound_constraint"
                    ]
                    assert len(bound_constraints) == 2

                    # Check verification constraint
                    verif_constraints = [
                        c for c in constraints if c["type"] == "verification_constraint"
                    ]
                    assert len(verif_constraints) == 1
                    assert verif_constraints[0]["verified"] == True

    def test_error_handling(self):
        """Test error handling for missing files."""
        with tempfile.NamedTemporaryFile(suffix=".pt") as model_file:
            with tempfile.NamedTemporaryFile(suffix=".json") as property_file:
                with tempfile.NamedTemporaryFile(suffix=".json") as output_file:
                    # Test missing model file
                    with pytest.raises(FileNotFoundError):
                        AlphaBetaCrownAdapter(
                            "nonexistent_model.pt", property_file.name, output_file.name
                        )

                    # Test missing property file
                    with pytest.raises(FileNotFoundError):
                        AlphaBetaCrownAdapter(
                            model_file.name,
                            "nonexistent_property.json",
                            output_file.name,
                        )


if __name__ == "__main__":
    pytest.main([__file__])
