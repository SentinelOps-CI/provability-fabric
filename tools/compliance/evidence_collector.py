#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

"""
SOC 2 / ISO 42001 Evidence Collector Pipeline

Collects and stores compliance artifacts from GitHub CI/CD pipeline,
hashes them for integrity, and generates control mapping manifests.
"""

import os
import json
import hashlib
import boto3
import requests
from datetime import datetime
from typing import Dict, List, Optional
from dataclasses import dataclass
from pathlib import Path
import logging

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class ControlMapping:
    """Maps compliance controls to required artifacts"""

    control_id: str
    control_name: str
    required_artifacts: List[str]
    description: str


# SOC 2 and ISO 42001 control mappings
CONTROL_MAPPINGS = {
    "CC1.1": ControlMapping(
        control_id="CC1.1",
        control_name="Control Environment",
        required_artifacts=[
            "slsa-provenance.intoto.jsonl",
            "sbom.json",
            "security-scan-results.json",
        ],
        description="Entity demonstrates commitment to integrity and ethical values",
    ),
    "CC6.3": ControlMapping(
        control_id="CC6.3",
        control_name="Logical and Physical Access Controls",
        required_artifacts=[
            "access-logs.json",
            "rbac-policies.yaml",
            "network-security-config.yaml",
        ],
        description="Entity implements logical and physical access controls",
    ),
    "CC7.2": ControlMapping(
        control_id="CC7.2",
        control_name="System Operations",
        required_artifacts=[
            "deployment-logs.json",
            "monitoring-alerts.json",
            "incident-response-logs.json",
        ],
        description="Entity selects and develops control activities",
    ),
    "ISO42001-7.4b": ControlMapping(
        control_id="ISO42001-7.4b",
        control_name="AI System Risk Assessment",
        required_artifacts=[
            "risk-assessment-report.json",
            "proof-verification-results.json",
            "adversarial-testing-results.json",
        ],
        description="Organization shall establish, implement and maintain processes for AI system risk assessment",
    ),
}


@dataclass
class ArtifactManifest:
    """Represents a collected artifact with metadata"""

    artifact_name: str
    sha256: str
    control_id: str
    link: str
    collected_at: str
    size_bytes: int


class EvidenceCollector:
    """Collects and stores compliance evidence artifacts"""

    def __init__(self, github_token: str, s3_bucket: str, s3_prefix: str = "evidence"):
        self.github_token = github_token
        self.s3_bucket = s3_bucket
        self.s3_prefix = s3_prefix
        self.s3_client = boto3.client("s3")
        self.github_session = requests.Session()
        self.github_session.headers.update(
            {
                "Authorization": f"token {github_token}",
                "Accept": "application/vnd.github.v3+json",
            }
        )

    def get_github_artifacts(
        self, repo: str, run_id: Optional[str] = None
    ) -> List[Dict]:
        """Retrieve artifacts from GitHub Actions runs"""
        artifacts = []

        # Get latest run if no specific run_id
        if not run_id:
            runs_url = f"https://api.github.com/repos/{repo}/actions/runs"
            response = self.github_session.get(runs_url)
            response.raise_for_status()
            runs = response.json()["workflow_runs"]
            if runs:
                run_id = runs[0]["id"]

        if run_id:
            artifacts_url = (
                f"https://api.github.com/repos/{repo}/actions/runs/{run_id}/artifacts"
            )
            response = self.github_session.get(artifacts_url)
            response.raise_for_status()
            artifacts = response.json()["artifacts"]

        return artifacts

    def download_artifact(
        self, repo: str, artifact_id: int, artifact_name: str
    ) -> bytes:
        """Download artifact content from GitHub"""
        download_url = (
            f"https://api.github.com/repos/{repo}/actions/artifacts/{artifact_id}/zip"
        )
        response = self.github_session.get(download_url)
        response.raise_for_status()
        return response.content

    def calculate_sha256(self, content: bytes) -> str:
        """Calculate SHA256 hash of content"""
        return hashlib.sha256(content).hexdigest()

    def store_in_glacier(self, content: bytes, filename: str, date_str: str) -> str:
        """Store artifact in S3 Glacier Deep Archive"""
        key = f"{self.s3_prefix}/{date_str}/{filename}"

        self.s3_client.put_object(
            Bucket=self.s3_bucket,
            Key=key,
            Body=content,
            StorageClass="DEEP_ARCHIVE",
            Metadata={
                "collected_at": datetime.utcnow().isoformat(),
                "sha256": self.calculate_sha256(content),
            },
        )

        return key

    def map_artifact_to_controls(self, artifact_name: str) -> List[str]:
        """Map artifact name to applicable controls"""
        applicable_controls = []

        for control_id, mapping in CONTROL_MAPPINGS.items():
            if any(
                required in artifact_name for required in mapping.required_artifacts
            ):
                applicable_controls.append(control_id)

        return applicable_controls

    def collect_evidence(self, repo: str, run_id: Optional[str] = None) -> Dict:
        """Main evidence collection process"""
        date_str = datetime.now().strftime("%Y-%m-%d")
        manifest_entries = []

        # Get artifacts from GitHub
        artifacts = self.get_github_artifacts(repo, run_id)
        logger.info(f"Found {len(artifacts)} artifacts in run {run_id}")

        for artifact in artifacts:
            artifact_name = artifact["name"]
            artifact_id = artifact["id"]

            try:
                # Download artifact
                content = self.download_artifact(repo, artifact_id, artifact_name)
                sha256 = self.calculate_sha256(content)

                # Store in Glacier
                s3_key = self.store_in_glacier(
                    content, f"{artifact_name}.zip", date_str
                )

                # Map to controls
                applicable_controls = self.map_artifact_to_controls(artifact_name)

                # Create manifest entry
                for control_id in applicable_controls:
                    manifest_entry = ArtifactManifest(
                        artifact_name=artifact_name,
                        sha256=sha256,
                        control_id=control_id,
                        link=f"s3://{self.s3_bucket}/{s3_key}",
                        collected_at=datetime.utcnow().isoformat(),
                        size_bytes=len(content),
                    )
                    manifest_entries.append(manifest_entry)

                logger.info(
                    f"Processed artifact {artifact_name} -> {len(applicable_controls)} controls"
                )

            except Exception as e:
                logger.error(f"Failed to process artifact {artifact_name}: {e}")
                continue

        # Generate manifest
        manifest = {
            "collected_at": datetime.utcnow().isoformat(),
            "repo": repo,
            "run_id": run_id,
            "artifacts": [
                {
                    "artifact_name": entry.artifact_name,
                    "sha256": entry.sha256,
                    "control_id": entry.control_id,
                    "link": entry.link,
                    "collected_at": entry.collected_at,
                    "size_bytes": entry.size_bytes,
                }
                for entry in manifest_entries
            ],
        }

        # Store manifest
        manifest_key = f"{self.s3_prefix}/{date_str}/manifest.json"
        self.s3_client.put_object(
            Bucket=self.s3_bucket,
            Key=manifest_key,
            Body=json.dumps(manifest, indent=2),
            ContentType="application/json",
        )

        logger.info(f"Stored manifest at s3://{self.s3_bucket}/{manifest_key}")
        return manifest


def main():
    """Main entry point"""
    import argparse

    parser = argparse.ArgumentParser(description="Collect SOC 2 / ISO 42001 evidence")
    parser.add_argument("--repo", required=True, help="GitHub repo (owner/repo)")
    parser.add_argument("--run-id", help="Specific GitHub Actions run ID")
    parser.add_argument(
        "--github-token", required=True, help="GitHub personal access token"
    )
    parser.add_argument(
        "--s3-bucket", required=True, help="S3 bucket for evidence storage"
    )
    parser.add_argument("--output", help="Output manifest file path")

    args = parser.parse_args()

    collector = EvidenceCollector(args.github_token, args.s3_bucket)
    manifest = collector.collect_evidence(args.repo, args.run_id)

    if args.output:
        with open(args.output, "w") as f:
            json.dump(manifest, f, indent=2)
        logger.info(f"Manifest saved to {args.output}")

    # Print summary
    control_counts = {}
    for artifact in manifest["artifacts"]:
        control_id = artifact["control_id"]
        control_counts[control_id] = control_counts.get(control_id, 0) + 1

    logger.info("Evidence collection summary:")
    for control_id, count in control_counts.items():
        logger.info(f"  {control_id}: {count} artifacts")


if __name__ == "__main__":
    main()
