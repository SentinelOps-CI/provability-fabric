#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Happy path integration test.
"""

import base64
import hashlib
import json
import subprocess
import time
from typing import Dict, Any

import pytest
import requests
from kubernetes import client, config


def test_happy_path(
    kube_config: str,
    admission_controller: None,
    ledger_service: str,
    demo_agent_image: str,
) -> None:
    """Test successful deployment of a valid agent."""
    # Configure Kubernetes client
    config.load_kube_config(config_file=kube_config)
    v1 = client.CoreV1Api()

    # Create valid spec signature and Lean hash
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

    # Create pod with valid annotations
    pod = client.V1Pod(
        metadata=client.V1ObjectMeta(
            name="demo-agent",
            annotations={"spec.sig": spec_hash, "lean.hash": lean_hash},
        ),
        spec=client.V1PodSpec(
            containers=[
                client.V1Container(
                    name="agent", image=demo_agent_image, image_pull_policy="Never"
                )
            ],
            restart_policy="Never",
        ),
    )

    # Create pod
    created_pod = v1.create_namespaced_pod(namespace="default", body=pod)

    try:
        # Wait for pod to be Running (max 30 seconds)
        for _ in range(30):
            pod_status = v1.read_namespaced_pod_status(
                name="demo-agent", namespace="default"
            )
            if pod_status.status.phase == "Running":
                break
            time.sleep(1)
        else:
            pytest.fail("Pod failed to reach Running state within 30 seconds")

        # Query ledger GraphQL to verify capsule hash is present
        query = """
        query GetCapsule($hash: ID!) {
            capsule(hash: $hash) {
                hash
                specSig
                riskScore
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
        assert data["data"]["capsule"]["riskScore"] == 0.0  # Valid agent has low risk

    finally:
        # Cleanup
        try:
            v1.delete_namespaced_pod(name="demo-agent", namespace="default")
        except Exception:
            pass  # Pod may already be deleted
