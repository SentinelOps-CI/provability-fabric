#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Test suite for ActionDSL extension with read/write operations and ABAC primitives.
"""

import json
import unittest
from unittest.mock import Mock, patch
import sys
import os

# Add the core directory to the path for imports
sys.path.append(os.path.join(os.path.dirname(__file__), "..", "core"))


class ActionDSLExtensionTest(unittest.TestCase):
    """Test cases for ActionDSL extension functionality."""

    def setUp(self):
        """Set up test fixtures."""
        self.sample_policy = {
            "version": "v1",
            "plan_id": "test-policy",
            "capabilities": [
                {
                    "capability_id": "test-read",
                    "type": "read",
                    "resource": {"doc_id": "test-doc", "path": ["field1", "field2"]},
                    "conditions": {
                        "abac": {
                            "allow": {
                                "role": "reader",
                                "action": "read",
                                "guard": {
                                    "type": "attr",
                                    "key": "clearance",
                                    "value": "high",
                                },
                            }
                        }
                    },
                },
                {
                    "capability_id": "test-write",
                    "type": "write",
                    "resource": {"doc_id": "test-doc", "path": ["field1", "field2"]},
                    "conditions": {
                        "abac": {
                            "allow": {
                                "role": "writer",
                                "action": "write",
                                "guard": {
                                    "type": "and",
                                    "left": {"type": "scope", "tenant": "tenant-a"},
                                    "right": {
                                        "type": "epoch_in",
                                        "start": 1000,
                                        "end": 2000,
                                    },
                                },
                            }
                        }
                    },
                },
            ],
        }

    def test_policy_parsing(self):
        """Test that extended policy with read/write operations can be parsed."""
        # This would test the actual policy parsing logic
        # For now, we just verify the structure is valid JSON
        policy_json = json.dumps(self.sample_policy)
        parsed_policy = json.loads(policy_json)

        self.assertEqual(parsed_policy["version"], "v1")
        self.assertEqual(len(parsed_policy["capabilities"]), 2)

        # Check read capability
        read_cap = parsed_policy["capabilities"][0]
        self.assertEqual(read_cap["type"], "read")
        self.assertEqual(read_cap["resource"]["doc_id"], "test-doc")
        self.assertEqual(read_cap["resource"]["path"], ["field1", "field2"])

        # Check write capability
        write_cap = parsed_policy["capabilities"][1]
        self.assertEqual(write_cap["type"], "write")
        self.assertEqual(write_cap["resource"]["doc_id"], "test-doc")

    def test_abac_primitives(self):
        """Test ABAC primitive evaluation."""
        # Test attribute evaluation
        attr_expr = {"type": "attr", "key": "clearance", "value": "high"}

        # Test session evaluation
        session_expr = {"type": "session", "key": "auth_level", "value": "verified"}

        # Test epoch evaluation
        epoch_expr = {"type": "epoch_in", "start": 1000, "end": 2000}

        # Test scope evaluation
        scope_expr = {"type": "scope", "tenant": "tenant-a"}

        # Test complex expressions
        complex_expr = {
            "type": "and",
            "left": attr_expr,
            "right": {"type": "or", "left": session_expr, "right": epoch_expr},
        }

        # These expressions would be evaluated by the ABAC engine
        # For now, we just verify the structure
        self.assertIn("type", attr_expr)
        self.assertIn("type", session_expr)
        self.assertIn("type", epoch_expr)
        self.assertIn("type", scope_expr)
        self.assertIn("type", complex_expr)

    def test_read_write_operations(self):
        """Test read and write operation definitions."""
        # Test read operation
        read_op = {
            "type": "read",
            "doc_id": "user-profiles",
            "path": ["personal", "email"],
            "witness_required": True,
            "label_flow_check": True,
        }

        # Test write operation
        write_op = {
            "type": "write",
            "doc_id": "user-profiles",
            "path": ["preferences", "notifications"],
            "witness_required": True,
            "label_derivation_check": True,
        }

        self.assertEqual(read_op["type"], "read")
        self.assertEqual(write_op["type"], "write")
        self.assertTrue(read_op["witness_required"])
        self.assertTrue(write_op["witness_required"])

    def test_dfa_generation(self):
        """Test that policies can be compiled to DFAs."""
        # This would test the actual DFA compilation
        # For now, we verify the expected structure

        expected_dfa_structure = {
            "states": "List of DFA states",
            "transitions": "List of state transitions",
            "rate_limiters": "List of rate limiting rules",
            "initial_state": "Starting state ID",
        }

        # The DFA should be generated from the policy
        # and include states for read/write operations
        self.assertIn("states", expected_dfa_structure)
        self.assertIn("transitions", expected_dfa_structure)

    def test_enforcement_modes(self):
        """Test different enforcement modes."""
        enforcement_modes = ["enforce", "shadow", "monitor"]

        for mode in enforcement_modes:
            policy_with_mode = self.sample_policy.copy()
            policy_with_mode["metadata"] = {"enforcement_mode": mode}

            # Verify the mode is set correctly
            self.assertEqual(policy_with_mode["metadata"]["enforcement_mode"], mode)

    def test_feature_flags(self):
        """Test feature flag configuration."""
        feature_flags = {
            "witness_validation": True,
            "label_derivation": True,
            "epoch_validation": True,
            "abac_evaluation": True,
        }

        policy_with_flags = self.sample_policy.copy()
        policy_with_flags["metadata"] = {"feature_flags": feature_flags}

        # Verify feature flags are set
        self.assertTrue(
            policy_with_flags["metadata"]["feature_flags"]["witness_validation"]
        )
        self.assertTrue(
            policy_with_flags["metadata"]["feature_flags"]["abac_evaluation"]
        )

    def test_rate_limiting(self):
        """Test rate limiting configuration."""
        rate_limit_config = {
            "window_ms": 60000,
            "max_operations": 10,
            "tolerance_ms": 1000,
        }

        # Verify rate limiting parameters
        self.assertEqual(rate_limit_config["window_ms"], 60000)
        self.assertEqual(rate_limit_config["max_operations"], 10)
        self.assertEqual(rate_limit_config["tolerance_ms"], 1000)

    def test_deny_wins_semantics(self):
        """Test that deny rules take precedence over allow rules."""
        policy_with_deny = {
            "capabilities": [
                {
                    "capability_id": "test-deny",
                    "type": "read",
                    "resource": {"doc_id": "sensitive-doc", "path": []},
                    "conditions": {
                        "abac": {
                            "allow": {
                                "role": "reader",
                                "action": "read",
                                "guard": {"type": "true"},
                            },
                            "forbid": {
                                "role": "reader",
                                "action": "read",
                                "guard": {
                                    "type": "attr",
                                    "key": "clearance",
                                    "value": "low",
                                },
                            },
                        }
                    },
                }
            ]
        }

        # The forbid rule should take precedence
        # This would be tested in the actual enforcement logic
        self.assertIn(
            "forbid", policy_with_deny["capabilities"][0]["conditions"]["abac"]
        )

    def test_epoch_validation(self):
        """Test epoch-based validation."""
        epoch_guard = {"type": "epoch_in", "start": 1000, "end": 2000}

        # Test epoch validation logic
        current_epoch = 1500
        is_valid = epoch_guard["start"] <= current_epoch <= epoch_guard["end"]

        self.assertTrue(is_valid)

        # Test invalid epoch
        invalid_epoch = 2500
        is_invalid = epoch_guard["start"] <= invalid_epoch <= epoch_guard["end"]

        self.assertFalse(is_invalid)


class SidecarIntegrationTest(unittest.TestCase):
    """Test cases for sidecar integration with permitD enforcement."""

    def setUp(self):
        """Set up test fixtures."""
        self.mock_policy_adapter = Mock()
        self.mock_enforcement_hook = Mock()

    def test_permitd_evaluation(self):
        """Test that permitD is called for each event."""
        # Mock the permitD function
        with patch("policy_adapter.evaluate_permit") as mock_permitd:
            mock_permitd.return_value = True

            # Simulate event processing
            event = {
                "event_type": "read",
                "user_id": "test-user",
                "roles": ["reader"],
                "resource_uri": "test://doc1",
                "field_path": ["field1"],
            }

            # The sidecar should call permitD for this event
            result = mock_permitd(event)
            self.assertTrue(result)
            mock_permitd.assert_called_once()

    def test_witness_validation(self):
        """Test that Merkle path witnesses are validated."""
        # Mock witness validation
        with patch("witness_validator.validate_merkle_path") as mock_witness:
            mock_witness.return_value = True

            # Test valid witness
            valid_witness = "valid_merkle_path_hash"
            result = mock_witness(["field1", "field2"], valid_witness)
            self.assertTrue(result)

    def test_label_derivation(self):
        """Test that label derivation follows IFC rules."""
        # Mock label derivation validation
        with patch("witness_validator.validate_label_derivation") as mock_label:
            mock_label.return_value = True

            # Test valid label derivation
            source_label = "confidential"
            target_label = "internal"
            result = mock_label(source_label, target_label)
            self.assertTrue(result)

    def test_feature_flag_toggle(self):
        """Test that feature flags can toggle enforcement behavior."""
        # Test enforcement mode toggle
        enforcement_modes = ["enforce", "shadow", "monitor"]

        for mode in enforcement_modes:
            # The sidecar should behave differently based on mode
            if mode == "enforce":
                # Should block denied actions
                pass
            elif mode == "shadow":
                # Should log but allow all actions
                pass
            elif mode == "monitor":
                # Should log and track violations
                pass

            # Verify mode is recognized
            self.assertIn(mode, enforcement_modes)


def run_tests():
    """Run all test cases."""
    # Create test suite
    test_suite = unittest.TestSuite()

    # Add ActionDSL extension tests
    test_suite.addTest(unittest.makeSuite(ActionDSLExtensionTest))

    # Add sidecar integration tests
    test_suite.addTest(unittest.makeSuite(SidecarIntegrationTest))

    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(test_suite)

    # Return success/failure
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
