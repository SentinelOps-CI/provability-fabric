#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Mock policy adapter module for testing.
"""

from typing import Dict, Any, Optional


def evaluate_permit(
    principal: str,
    action: str,
    context: Dict[str, Any],
    resource: Optional[str] = None,
    field_path: Optional[list] = None
) -> Dict[str, Any]:
    """Mock permitD evaluation."""
    # In a real implementation, this would call the Lean permitD function
    return {
        "allowed": True,
        "reason": "Mock permitD evaluation - always allows",
        "epoch": context.get("epoch", 1),
        "path_witness_ok": True,
        "label_derivation_ok": True,
        "permit_decision": "accept"
    }


def validate_attributes(attributes: Dict[str, str], required: list) -> bool:
    """Mock attribute validation."""
    # In a real implementation, this would validate ABAC attributes
    return all(key in attributes for key in required)


def check_epoch_validity(epoch: int, current_epoch: int) -> bool:
    """Mock epoch validation."""
    # In a real implementation, this would check epoch validity
    return epoch <= current_epoch


def evaluate_abac_expression(expression: str, context: Dict[str, Any]) -> bool:
    """Mock ABAC expression evaluation."""
    # In a real implementation, this would evaluate ABAC expressions
    return True
