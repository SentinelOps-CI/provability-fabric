#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Integration test configuration and fixtures.
"""

import os
import subprocess
import tempfile
import time
import yaml
from pathlib import Path
from typing import Generator, Tuple

import pytest
import requests
from kubernetes import client, config


@pytest.fixture(scope="session")
def kind_cluster() -> Generator[str, None, None]:
    """Create and manage a Kind cluster for integration tests."""
    cluster_name = "provability-fabric-test"

    # Create Kind cluster
    subprocess.run(
        ["kind", "create", "cluster", "--name", cluster_name, "--config", "-"],
        input=yaml.dump(
            {
                "kind": "Cluster",
                "apiVersion": "kind.x-k8s.io/v1alpha4",
                "nodes": [
                    {
                        "role": "control-plane",
                        "extraPortMappings": [
                            {"containerPort": 80, "hostPort": 80},
                            {"containerPort": 443, "hostPort": 443},
                        ],
                    }
                ],
            }
        ).encode(),
        check=True,
    )

    try:
        yield cluster_name
    finally:
        # Cleanup
        subprocess.run(
            ["kind", "delete", "cluster", "--name", cluster_name], check=True
        )


@pytest.fixture(scope="session")
def kube_config(kind_cluster: str) -> Generator[str, None, None]:
    """Get kubeconfig for the test cluster."""
    result = subprocess.run(
        ["kind", "get", "kubeconfig", "--name", kind_cluster],
        capture_output=True,
        text=True,
        check=True,
    )

    # Write to temp file
    with tempfile.NamedTemporaryFile(mode="w", suffix=".yaml", delete=False) as f:
        f.write(result.stdout)
        kubeconfig_path = f.name

    try:
        yield kubeconfig_path
    finally:
        os.unlink(kubeconfig_path)


@pytest.fixture(scope="session")
def admission_controller(
    kind_cluster: str, kube_config: str
) -> Generator[None, None, None]:
    """Install admission controller Helm chart."""
    # Set kubeconfig
    os.environ["KUBECONFIG"] = kube_config

    # Build and load admission controller image
    subprocess.run(
        [
            "docker",
            "build",
            "-t",
            "provability-fabric/admission-controller:latest",
            "runtime/admission-controller",
        ],
        check=True,
    )

    subprocess.run(
        [
            "kind",
            "load",
            "docker-image",
            "provability-fabric/admission-controller:latest",
            "--name",
            kind_cluster,
        ],
        check=True,
    )

    # Install Helm chart
    subprocess.run(
        [
            "helm",
            "install",
            "admission-controller",
            "runtime/admission-controller/deploy/admission",
            "--set",
            "image.tag=latest",
            "--wait",
            "--timeout",
            "5m",
        ],
        check=True,
    )

    yield

    # Cleanup
    subprocess.run(["helm", "uninstall", "admission-controller"], check=True)


@pytest.fixture(scope="session")
def ledger_service() -> Generator[str, None, None]:
    """Start ledger service and return URL."""
    # Start ledger service
    subprocess.run(
        ["docker", "compose", "-f", "runtime/ledger/docker-compose.yml", "up", "-d"],
        check=True,
    )

    # Wait for service to be ready
    ledger_url = "http://localhost:4000"
    for _ in range(30):  # 30 second timeout
        try:
            response = requests.get(f"{ledger_url}/graphql", timeout=5)
            if response.status_code == 200:
                break
        except requests.RequestException:
            pass
        time.sleep(1)
    else:
        raise RuntimeError("Ledger service failed to start")

    try:
        yield ledger_url
    finally:
        # Cleanup
        subprocess.run(
            ["docker", "compose", "-f", "runtime/ledger/docker-compose.yml", "down"],
            check=True,
        )


@pytest.fixture(scope="session")
def demo_agent_image() -> Generator[str, None, None]:
    """Build demo agent container image."""
    # Create demo agent Dockerfile
    demo_dir = Path("demo/agent")
    demo_dir.mkdir(parents=True, exist_ok=True)

    (demo_dir / "Dockerfile").write_text(
        """
FROM busybox:latest
COPY agent.sh /agent.sh
RUN chmod +x /agent.sh
CMD ["/agent.sh"]
"""
    )

    (demo_dir / "agent.sh").write_text(
        """#!/bin/sh
# Demo agent that emits valid JSON actions
echo '{"action": "SendEmail", "score": 0.05, "payload": "test@example.com"}' >&1
echo '{"action": "LogSpend", "usd": 50.0, "payload": "test"}' >&1
sleep 3600  # Keep container running
"""
    )

    # Build image
    subprocess.run(
        [
            "docker",
            "build",
            "-t",
            "provability-fabric/demo-agent:latest",
            str(demo_dir),
        ],
        check=True,
    )

    yield "provability-fabric/demo-agent:latest"

    # Cleanup
    subprocess.run(
        ["docker", "rmi", "provability-fabric/demo-agent:latest"], check=True
    )


@pytest.fixture(scope="session")
def violation_agent_image() -> Generator[str, None, None]:
    """Build violation agent container image."""
    # Create violation agent Dockerfile
    demo_dir = Path("demo/violation-agent")
    demo_dir.mkdir(parents=True, exist_ok=True)

    (demo_dir / "Dockerfile").write_text(
        """
FROM busybox:latest
COPY agent.sh /agent.sh
RUN chmod +x /agent.sh
CMD ["/agent.sh"]
"""
    )

    (demo_dir / "agent.sh").write_text(
        """#!/bin/sh
# Demo agent that emits over-budget actions
echo '{"action": "LogSpend", "usd": 500.0, "payload": "violation"}' >&1
sleep 3600  # Keep container running
"""
    )

    # Build image
    subprocess.run(
        [
            "docker",
            "build",
            "-t",
            "provability-fabric/violation-agent:latest",
            str(demo_dir),
        ],
        check=True,
    )

    yield "provability-fabric/violation-agent:latest"

    # Cleanup
    subprocess.run(
        ["docker", "rmi", "provability-fabric/violation-agent:latest"], check=True
    )
