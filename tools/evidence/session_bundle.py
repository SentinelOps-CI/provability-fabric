#!/usr/bin/env python3
"""
Session Safety-Case Bundle Generator

Creates auditor-friendly evidence bundles per session containing:
- Access Receipts from retrieval gateway
- Capability Tokens (public parts)
- Kernel Decision Logs
- Attestation References
- Egress Certificates from firewall
- DSSE-signed manifests for tamper evidence
"""

import os
import sys
import json
import hashlib
import argparse
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Any, Tuple
import requests
import subprocess
import base64

try:
    import yaml
    import avro.schema
    import avro.io
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric import ed25519
    from cryptography.hazmat.primitives.serialization import load_pem_private_key
except ImportError as e:
    print(f"Required dependency missing: {e}")
    print("Install with: pip install pyyaml avro-python3 cryptography")
    sys.exit(1)


class SessionBundleGenerator:
    def __init__(self, config_path: str = None):
        self.config = self.load_config(config_path)
        self.schemas = self.load_schemas()
        self.signing_key = self.load_signing_key()
        self.ledger_client = self.setup_ledger_client()

    def load_config(self, config_path: str) -> Dict[str, Any]:
        """Load configuration from YAML file or use defaults."""
        if config_path and os.path.exists(config_path):
            with open(config_path, "r") as f:
                return yaml.safe_load(f)

        return {
            "ledger_endpoint": "http://localhost:3000",
            "retrieval_gateway": "http://localhost:8080",
            "egress_firewall": "http://localhost:8081",
            "attestor_endpoint": "http://localhost:8082",
            "evidence_dir": "./evidence/sessions",
            "signing_key_path": "./evidence/signing_key.pem",
            "glacier_bucket": "provability-evidence",
            "retention_days": 90,
            "bundle_format": "avro",
        }

    def load_schemas(self) -> Dict[str, Any]:
        """Load Avro schemas for evidence artifacts."""
        schema_dir = Path("./tools/evidence/schema")
        schemas = {}

        schema_files = [
            "receipt.avsc",
            "cap_token.avsc",
            "egress_cert.avsc",
            "decision_log.avsc",
        ]

        for schema_file in schema_files:
            schema_path = schema_dir / schema_file
            if schema_path.exists():
                with open(schema_path, "r") as f:
                    schema_name = schema_file.replace(".avsc", "")
                    schemas[schema_name] = avro.schema.parse(f.read())

        return schemas

    def load_signing_key(self) -> ed25519.Ed25519PrivateKey:
        """Load or generate signing key for DSSE."""
        key_path = Path(
            self.config.get("signing_key_path", "./evidence/signing_key.pem")
        )

        if key_path.exists():
            with open(key_path, "rb") as f:
                return load_pem_private_key(f.read(), password=None)
        else:
            # Generate new key
            private_key = ed25519.Ed25519PrivateKey.generate()
            key_path.parent.mkdir(exist_ok=True, parents=True)

            with open(key_path, "wb") as f:
                f.write(
                    private_key.private_bytes(
                        encoding=serialization.Encoding.PEM,
                        format=serialization.PrivateFormat.PKCS8,
                        encryption_algorithm=serialization.NoEncryption(),
                    )
                )

            print(f"Generated new signing key: {key_path}")
            return private_key

    def setup_ledger_client(self):
        """Setup ledger client for storing manifest hashes."""
        return {
            "endpoint": self.config["ledger_endpoint"],
            "headers": {"Content-Type": "application/json"},
        }

    def generate_session_id(self, session_data: Dict[str, Any]) -> str:
        """Generate unique session ID from session data."""
        session_str = json.dumps(session_data, sort_keys=True)
        return hashlib.sha256(session_str.encode()).hexdigest()[:16]

    def collect_session_receipts(
        self, session_id: str, start_time: datetime, end_time: datetime
    ) -> List[Dict[str, Any]]:
        """Collect access receipts for a specific session."""
        try:
            response = requests.get(
                f"{self.config['retrieval_gateway']}/api/receipts",
                params={
                    "session_id": session_id,
                    "start_time": start_time.isoformat(),
                    "end_time": end_time.isoformat(),
                },
                timeout=30,
            )
            response.raise_for_status()
            return response.json().get("receipts", [])
        except Exception as e:
            print(f"Warning: Failed to collect receipts for session {session_id}: {e}")
            return []

    def collect_capability_tokens(self, session_id: str) -> List[Dict[str, Any]]:
        """Collect capability tokens for a session."""
        try:
            response = requests.get(
                f"{self.config['ledger_endpoint']}/api/capabilities",
                params={"session_id": session_id},
                timeout=30,
            )
            response.raise_for_status()
            tokens = response.json().get("tokens", [])

            # Only include public parts for evidence
            public_tokens = []
            for token in tokens:
                public_token = {
                    "capability_id": token.get("capability_id"),
                    "session_id": token.get("session_id"),
                    "issued_at": token.get("issued_at"),
                    "expires_at": token.get("expires_at"),
                    "capability_type": token.get("capability_type"),
                    "resource_pattern": token.get("resource_pattern"),
                    "conditions": token.get("conditions", {}),
                }
                public_tokens.append(public_token)

            return public_tokens
        except Exception as e:
            print(
                f"Warning: Failed to collect capability tokens for session {session_id}: {e}"
            )
            return []

    def collect_kernel_decisions(
        self, session_id: str, start_time: datetime, end_time: datetime
    ) -> List[Dict[str, Any]]:
        """Collect kernel decision logs for a session."""
        try:
            response = requests.get(
                f"{self.config['ledger_endpoint']}/api/decisions",
                params={
                    "session_id": session_id,
                    "start_time": start_time.isoformat(),
                    "end_time": end_time.isoformat(),
                },
                timeout=30,
            )
            response.raise_for_status()
            return response.json().get("decisions", [])
        except Exception as e:
            print(
                f"Warning: Failed to collect kernel decisions for session {session_id}: {e}"
            )
            return []

    def collect_attestation_refs(self, session_id: str) -> List[Dict[str, Any]]:
        """Collect attestation references for a session."""
        try:
            response = requests.get(
                f"{self.config['attestor_endpoint']}/api/attestations",
                params={"session_id": session_id},
                timeout=30,
            )
            response.raise_for_status()
            attestations = response.json().get("attestations", [])

            # Convert to evidence format
            refs = []
            for att in attestations:
                ref = {
                    "attestation_id": att.get("attestation_id"),
                    "session_id": att.get("session_id"),
                    "attestation_type": att.get("attestation_type"),
                    "attested_at": att.get("attested_at"),
                    "attestation_hash": att.get("attestation_hash"),
                    "attester_id": att.get("attester_id"),
                }
                refs.append(ref)

            return refs
        except Exception as e:
            print(
                f"Warning: Failed to collect attestation refs for session {session_id}: {e}"
            )
            return []

    def collect_egress_certificates(
        self, session_id: str, start_time: datetime, end_time: datetime
    ) -> List[Dict[str, Any]]:
        """Collect egress certificates for a session."""
        try:
            response = requests.get(
                f"{self.config['egress_firewall']}/api/certificates",
                params={
                    "session_id": session_id,
                    "start_time": start_time.isoformat(),
                    "end_time": end_time.isoformat(),
                },
                timeout=30,
            )
            response.raise_for_status()
            return response.json().get("certificates", [])
        except Exception as e:
            print(
                f"Warning: Failed to collect egress certificates for session {session_id}: {e}"
            )
            return []

    def create_session_manifest(
        self,
        session_id: str,
        session_data: Dict[str, Any],
        receipts: List,
        tokens: List,
        decisions: List,
        attestations: List,
        certificates: List,
    ) -> Dict[str, Any]:
        """Create DSSE-signed manifest for session bundle."""
        manifest = {
            "session_id": session_id,
            "bundle_id": self.generate_bundle_id(),
            "created_at": datetime.utcnow().isoformat(),
            "session_data": session_data,
            "artifacts": {
                "receipts_count": len(receipts),
                "tokens_count": len(tokens),
                "decisions_count": len(decisions),
                "attestations_count": len(attestations),
                "certificates_count": len(certificates),
            },
            "evidence_hash": self.compute_evidence_hash(
                receipts, tokens, decisions, attestations, certificates
            ),
            "retention_policy": {
                "retention_days": self.config["retention_days"],
                "expires_at": (
                    datetime.utcnow() + timedelta(days=self.config["retention_days"])
                ).isoformat(),
            },
        }

        return self.sign_with_dsse(manifest)

    def generate_bundle_id(self) -> str:
        """Generate unique bundle ID."""
        timestamp = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
        random_suffix = os.urandom(4).hex()
        return f"session_bundle_{timestamp}_{random_suffix}"

    def compute_evidence_hash(
        self,
        receipts: List,
        tokens: List,
        decisions: List,
        attestations: List,
        certificates: List,
    ) -> str:
        """Compute SHA256 hash of all evidence artifacts."""
        evidence_data = {
            "receipts": receipts,
            "tokens": tokens,
            "decisions": decisions,
            "attestations": attestations,
            "certificates": certificates,
        }
        evidence_str = json.dumps(evidence_data, sort_keys=True)
        return hashlib.sha256(evidence_str.encode()).hexdigest()

    def sign_with_dsse(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Sign payload using DSSE (Dead Simple Signing Envelope)."""
        payload_str = json.dumps(payload, sort_keys=True)
        payload_hash = hashlib.sha256(payload_str.encode()).hexdigest()

        # Sign the hash
        signature = self.signing_key.sign(payload_str.encode())
        signature_b64 = base64.b64encode(signature).decode()

        # Get public key
        public_key = self.signing_key.public_key()
        public_key_bytes = public_key.public_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PublicFormat.SubjectPublicKeyInfo,
        )
        public_key_b64 = base64.b64encode(public_key_bytes).decode()

        return {
            "payload": payload,
            "payload_hash": payload_hash,
            "signature": signature_b64,
            "public_key": public_key_b64,
            "signing_algorithm": "ed25519",
        }

    def save_session_bundle(
        self,
        session_id: str,
        manifest: Dict[str, Any],
        receipts: List,
        tokens: List,
        decisions: List,
        attestations: List,
        certificates: List,
    ) -> Path:
        """Save session bundle to local storage."""
        bundle_dir = Path(self.config["evidence_dir"]) / session_id
        bundle_dir.mkdir(parents=True, exist_ok=True)

        # Save individual artifacts
        artifacts = {
            "manifest.json": manifest,
            "receipts.json": receipts,
            "tokens.json": tokens,
            "decisions.json": decisions,
            "attestations.json": attestations,
            "certificates.json": certificates,
        }

        for filename, data in artifacts.items():
            file_path = bundle_dir / filename
            with open(file_path, "w") as f:
                json.dump(data, f, indent=2)

        # Create archive
        archive_path = bundle_dir.parent / f"{session_id}_bundle.tar.gz"
        subprocess.run(
            [
                "tar",
                "-czf",
                str(archive_path),
                "-C",
                str(bundle_dir.parent),
                session_id,
            ],
            check=True,
        )

        return archive_path

    def upload_to_glacier(self, archive_path: Path) -> str:
        """Upload bundle to AWS Glacier for long-term storage."""
        try:
            import boto3

            glacier = boto3.client("glacier")

            with open(archive_path, "rb") as f:
                response = glacier.upload_archive(
                    vaultName=self.config["glacier_bucket"], body=f
                )

            return response["archiveId"]
        except Exception as e:
            print(f"Warning: Failed to upload to Glacier: {e}")
            return None

    def store_manifest_hash(self, session_id: str, manifest_hash: str) -> bool:
        """Store manifest hash in ledger for verification."""
        try:
            response = requests.post(
                f"{self.config['ledger_endpoint']}/api/manifests",
                json={
                    "session_id": session_id,
                    "manifest_hash": manifest_hash,
                    "stored_at": datetime.utcnow().isoformat(),
                },
                headers=self.ledger_client["headers"],
                timeout=30,
            )
            response.raise_for_status()
            return True
        except Exception as e:
            print(f"Warning: Failed to store manifest hash: {e}")
            return False

    def generate_session_bundle(
        self,
        session_id: str,
        session_data: Dict[str, Any],
        start_time: datetime,
        end_time: datetime,
    ) -> Tuple[str, Path]:
        """Generate complete session bundle with all evidence artifacts."""
        print(f"Generating session bundle for session: {session_id}")

        # Collect all evidence artifacts
        receipts = self.collect_session_receipts(session_id, start_time, end_time)
        tokens = self.collect_capability_tokens(session_id)
        decisions = self.collect_kernel_decisions(session_id, start_time, end_time)
        attestations = self.collect_attestation_refs(session_id)
        certificates = self.collect_egress_certificates(
            session_id, start_time, end_time
        )

        # Create DSSE-signed manifest
        manifest = self.create_session_manifest(
            session_id,
            session_data,
            receipts,
            tokens,
            decisions,
            attestations,
            certificates,
        )

        # Save bundle locally
        archive_path = self.save_session_bundle(
            session_id,
            manifest,
            receipts,
            tokens,
            decisions,
            attestations,
            certificates,
        )

        # Upload to Glacier
        archive_id = self.upload_to_glacier(archive_path)
        if archive_id:
            print(f"Uploaded to Glacier with archive ID: {archive_id}")

        # Store manifest hash in ledger
        manifest_hash = manifest["payload"]["evidence_hash"]
        if self.store_manifest_hash(session_id, manifest_hash):
            print(f"Stored manifest hash in ledger: {manifest_hash}")

        return session_id, archive_path

    def verify_session_bundle(self, session_id: str) -> bool:
        """Verify session bundle integrity and completeness."""
        bundle_dir = Path(self.config["evidence_dir"]) / session_id

        if not bundle_dir.exists():
            print(f"Session bundle not found: {session_id}")
            return False

        # Check all required files exist
        required_files = [
            "manifest.json",
            "receipts.json",
            "tokens.json",
            "decisions.json",
            "attestations.json",
            "certificates.json",
        ]

        for filename in required_files:
            if not (bundle_dir / filename).exists():
                print(f"Missing required file: {filename}")
                return False

        # Verify DSSE signature
        manifest_path = bundle_dir / "manifest.json"
        with open(manifest_path, "r") as f:
            manifest = json.load(f)

        try:
            # Verify signature
            payload_str = json.dumps(manifest["payload"], sort_keys=True)
            signature = base64.b64decode(manifest["signature"])
            public_key_bytes = base64.b64decode(manifest["public_key"])
            public_key = serialization.load_pem_public_key(public_key_bytes)

            public_key.verify(signature, payload_str.encode())
            print(f"Session bundle signature verified: {session_id}")
            return True
        except Exception as e:
            print(f"Signature verification failed: {e}")
            return False


def main():
    parser = argparse.ArgumentParser(description="Generate session safety-case bundles")
    parser.add_argument("--config", help="Configuration file path")
    parser.add_argument("--session-id", help="Specific session ID to bundle")
    parser.add_argument("--start-time", help="Session start time (ISO format)")
    parser.add_argument("--end-time", help="Session end time (ISO format)")
    parser.add_argument("--verify", action="store_true", help="Verify existing bundle")
    parser.add_argument(
        "--list-sessions", action="store_true", help="List available sessions"
    )

    args = parser.parse_args()

    generator = SessionBundleGenerator(args.config)

    if args.verify and args.session_id:
        success = generator.verify_session_bundle(args.session_id)
        sys.exit(0 if success else 1)

    if args.list_sessions:
        evidence_dir = Path(generator.config["evidence_dir"])
        if evidence_dir.exists():
            sessions = [d.name for d in evidence_dir.iterdir() if d.is_dir()]
            print("Available sessions:")
            for session in sessions:
                print(f"  - {session}")
        else:
            print("No sessions found")
        return

    if args.session_id:
        start_time = (
            datetime.fromisoformat(args.start_time)
            if args.start_time
            else datetime.utcnow() - timedelta(hours=1)
        )
        end_time = (
            datetime.fromisoformat(args.end_time)
            if args.end_time
            else datetime.utcnow()
        )

        session_data = {
            "session_id": args.session_id,
            "start_time": start_time.isoformat(),
            "end_time": end_time.isoformat(),
        }

        session_id, archive_path = generator.generate_session_bundle(
            args.session_id, session_data, start_time, end_time
        )
        print(f"Generated session bundle: {archive_path}")
    else:
        print(
            "Please specify --session-id or use --list-sessions to see available sessions"
        )


if __name__ == "__main__":
    main()
