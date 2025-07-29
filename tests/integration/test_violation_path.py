#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Violation path integration test.
"""

import hashlib
import json
import time
from typing import Dict, Any

import pytest
import requests
from kubernetes import client, config


def test_violation_path(
    kube_config: str,
    admission_controller: None,
    ledger_service: str,
    violation_agent_image: str,
) -> None:
    """Test that violation agent triggers sidecar guard and gets rejected."""
    # Configure Kubernetes client
    config.load_kube_config(config_file=kube_config)
    v1 = client.CoreV1Api()

    # Create spec signature and Lean hash (same as happy path for now)
    spec_content = {
        "meta": {"version": "0.1.0"},
        "requirements": {
            "REQ-0001": {
                "statement": "The agent SHALL respect budget constraints",
                "category": "security",
            }
        },
    }
    spec_hash = hashlib.sha256(
        json.dumps(spec_content, sort_keys=True).encode()
    ).hexdigest()
    lean_hash = "2025-07-15-abe123"  # Mock Lean proof hash

    # Create pod with violation agent
    pod = client.V1Pod(
        metadata=client.V1ObjectMeta(
            name="violation-agent",
            annotations={"spec.sig": spec_hash, "lean.hash": lean_hash},
        ),
        spec=client.V1PodSpec(
            containers=[
                client.V1Container(
                    name="agent", image=violation_agent_image, image_pull_policy="Never"
                )
            ],
            restart_policy="Never",
        ),
    )

    # Create pod
    created_pod = v1.create_namespaced_pod(namespace="default", body=pod)

    try:
        # Wait for pod to reach CrashLoopBackOff (max 60 seconds)
        for _ in range(60):
            pod_status = v1.read_namespaced_pod_status(
                name="violation-agent", namespace="default"
            )

            # Check if pod is in CrashLoopBackOff
            if (
                pod_status.status.phase == "Running"
                and pod_status.status.container_statuses
                and any(
                    cs.state.waiting and cs.state.waiting.reason == "CrashLoopBackOff"
                    for cs in pod_status.status.container_statuses
                )
            ):
                break
            time.sleep(1)
        else:
            pytest.fail("Pod failed to reach CrashLoopBackOff state within 60 seconds")

        # Query ledger GraphQL to verify high risk score and reason
        query = """
        query GetCapsule($hash: ID!) {
            capsule(hash: $hash) {
                hash
                specSig
                riskScore
                reason
            }
        }
        """

        response = requests.post(
            f"{ledger_service}/graphql",
            json={"query": query, "variables": {"hash": spec_hash}},
            timeout=10,
        )

        assert response.status_code == 200
        data = response.json()
        assert "data" in data
        assert data["data"]["capsule"] is not None
        assert data["data"]["capsule"]["hash"] == spec_hash
        assert (
            data["data"]["capsule"]["riskScore"] > 0.9
        )  # Violation should have high risk

        # Check that reason field is present and contains expected content
        reason = data["data"]["capsule"]["reason"]
        assert reason is not None
        assert reason != ""  # Reason should not be empty for violations
        # The reason could be various values depending on the violation type
        # For now, just ensure it's not empty

    finally:
        # Cleanup
        try:
            v1.delete_namespaced_pod(name="violation-agent", namespace="default")
        except Exception:
            pass  # Pod may already be deleted
