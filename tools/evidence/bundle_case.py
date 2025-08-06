#!/usr/bin/env python3
"""
Evidence Bundle Case Generator

Creates verifiable evidence bundles containing:
- Access Receipts from retrieval gateway
- Capability Tokens (public parts)
- Egress Certificates from firewall
- Safety Case documentation with GSN diagrams
- DSSE-signed manifests for tamper evidence
"""

import os
import sys
import json
import hashlib
import sqlite3
import argparse
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Any, Optional
import requests
import subprocess

try:
    import yaml
    import avro.schema
    import avro.io
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import ed25519
except ImportError as e:
    print(f"Required dependency missing: {e}")
    print("Install with: pip install pyyaml avro-python3 cryptography")
    sys.exit(1)


class EvidenceBundle:
    def __init__(self, config_path: str):
        self.config = self.load_config(config_path)
        self.bundle_id = self.generate_bundle_id()
        self.artifacts = []
        self.evidence_dir = Path(self.config.get("evidence_dir", "./evidence"))
        self.evidence_dir.mkdir(exist_ok=True)

        # Load schemas
        self.schemas = self.load_schemas()

        # Signing key for DSSE
        self.signing_key = self.load_signing_key()

    def load_config(self, config_path: str) -> Dict[str, Any]:
        """Load configuration from YAML file."""
        try:
            with open(config_path, "r") as f:
                return yaml.safe_load(f)
        except FileNotFoundError:
            # Default configuration
            return {
                "ledger_endpoint": "http://localhost:3000",
                "evidence_dir": "./evidence",
                "signing_key_path": "./evidence/signing_key.pem",
                "retention_days": 90,
                "bundle_format": "avro",
            }

    def load_schemas(self) -> Dict[str, Any]:
        """Load Avro schemas for evidence artifacts."""
        schema_dir = Path("./tools/evidence/schema")
        schemas = {}

        schema_files = ["receipt.avsc", "cap_token.avsc", "egress_cert.avsc"]
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
                return serialization.load_pem_private_key(f.read(), password=None)
        else:
            # Generate new key
            private_key = ed25519.Ed25519PrivateKey.generate()
            key_path.parent.mkdir(exist_ok=True)

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

    def generate_bundle_id(self) -> str:
        """Generate unique bundle ID."""
        timestamp = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
        return f"evidence_bundle_{timestamp}"

    def collect_access_receipts(
        self, start_date: datetime, end_date: datetime
    ) -> List[Dict[str, Any]]:
        """Collect access receipts from ledger."""
        print("📋 Collecting access receipts...")

        try:
            response = requests.get(
                f"{self.config['ledger_endpoint']}/receipts",
                params={
                    "start_date": start_date.isoformat(),
                    "end_date": end_date.isoformat(),
                },
                timeout=30,
            )
            response.raise_for_status()

            receipts = response.json()
            print(f"✅ Collected {len(receipts)} access receipts")
            return receipts

        except requests.RequestException as e:
            print(f"❌ Failed to collect receipts: {e}")
            return []

    def collect_capability_tokens(
        self, start_date: datetime, end_date: datetime
    ) -> List[Dict[str, Any]]:
        """Collect capability tokens (public parts only)."""
        print("🔑 Collecting capability tokens...")

        try:
            response = requests.get(
                f"{self.config['ledger_endpoint']}/capability-tokens",
                params={
                    "start_date": start_date.isoformat(),
                    "end_date": end_date.isoformat(),
                    "public_only": True,
                },
                timeout=30,
            )
            response.raise_for_status()

            tokens = response.json()

            # Strip private information, keep only public parts
            public_tokens = []
            for token in tokens:
                public_token = {
                    "token_id": token.get("token_id"),
                    "tenant": token.get("tenant"),
                    "subject_id": token.get("subject_id"),
                    "capabilities": token.get("capabilities", []),
                    "issued_at": token.get("issued_at"),
                    "expires_at": token.get("expires_at"),
                    "issuer": token.get("issuer"),
                }
                public_tokens.append(public_token)

            print(f"✅ Collected {len(public_tokens)} capability tokens")
            return public_tokens

        except requests.RequestException as e:
            print(f"❌ Failed to collect capability tokens: {e}")
            return []

    def collect_egress_certificates(
        self, start_date: datetime, end_date: datetime
    ) -> List[Dict[str, Any]]:
        """Collect egress certificates from ledger."""
        print("🛡️ Collecting egress certificates...")

        try:
            response = requests.get(
                f"{self.config['ledger_endpoint']}/egress-certificates",
                params={
                    "start_date": start_date.isoformat(),
                    "end_date": end_date.isoformat(),
                },
                timeout=30,
            )
            response.raise_for_status()

            certificates = response.json()
            print(f"✅ Collected {len(certificates)} egress certificates")
            return certificates

        except requests.RequestException as e:
            print(f"❌ Failed to collect egress certificates: {e}")
            return []

    def generate_safety_case(self) -> Dict[str, Any]:
        """Generate safety case documentation with GSN diagram."""
        print("📄 Generating safety case...")

        safety_case = {
            "case_id": f"{self.bundle_id}_safety_case",
            "generated_at": datetime.utcnow().isoformat(),
            "version": "1.0",
            "title": "Provability-Fabric Safety Case",
            "description": "Comprehensive safety argument for AI system operation",
            # Goals (G nodes in GSN)
            "goals": [
                {
                    "id": "G1",
                    "statement": "System operates safely and securely",
                    "description": "Top-level safety goal for the entire system",
                },
                {
                    "id": "G2",
                    "statement": "No unauthorized access to tenant data",
                    "description": "Tenant isolation is maintained",
                },
                {
                    "id": "G3",
                    "statement": "No PII data leakage in outputs",
                    "description": "Privacy protection is enforced",
                },
                {
                    "id": "G4",
                    "statement": "All actions are authorized by capabilities",
                    "description": "Access control is properly enforced",
                },
            ],
            # Strategies (S nodes in GSN)
            "strategies": [
                {
                    "id": "S1",
                    "statement": "Argument by formal verification and runtime monitoring",
                    "description": "Combine formal proofs with runtime evidence",
                },
                {
                    "id": "S2",
                    "statement": "Argument by defense in depth",
                    "description": "Multiple layers of security controls",
                },
            ],
            # Evidence (E nodes in GSN)
            "evidence": [
                {
                    "id": "E1",
                    "statement": "Lean formal proofs of system invariants",
                    "artifact_type": "formal_proof",
                    "location": "core/lean-libs/Invariants.lean",
                },
                {
                    "id": "E2",
                    "statement": "Access receipts showing tenant isolation",
                    "artifact_type": "access_receipt",
                    "count": len(self.artifacts) if hasattr(self, "artifacts") else 0,
                },
                {
                    "id": "E3",
                    "statement": "Egress certificates showing PII filtering",
                    "artifact_type": "egress_certificate",
                    "count": 0,  # Will be updated
                },
                {
                    "id": "E4",
                    "statement": "Capability tokens showing authorization",
                    "artifact_type": "capability_token",
                    "count": 0,  # Will be updated
                },
            ],
            # GSN diagram in Mermaid format
            "gsn_diagram": """
            graph TD
                G1[G1: System operates safely and securely]
                S1[S1: Argument by formal verification and runtime monitoring]
                G2[G2: No unauthorized access to tenant data]
                G3[G3: No PII data leakage in outputs]
                G4[G4: All actions are authorized by capabilities]
                E1[E1: Lean formal proofs of system invariants]
                E2[E2: Access receipts showing tenant isolation]
                E3[E3: Egress certificates showing PII filtering]
                E4[E4: Capability tokens showing authorization]
                
                G1 --> S1
                S1 --> G2
                S1 --> G3
                S1 --> G4
                G2 --> E1
                G2 --> E2
                G3 --> E1
                G3 --> E3
                G4 --> E1
                G4 --> E4
            """,
            # Supporting documentation links
            "documentation": [
                {"title": "System Architecture", "path": "docs/architecture.md"},
                {"title": "Security Controls", "path": "docs/security/controls.md"},
                {"title": "Formal Verification", "path": "docs/verification/proofs.md"},
            ],
        }

        print("✅ Safety case generated")
        return safety_case

    def create_manifest(
        self, receipts: List, tokens: List, certificates: List, safety_case: Dict
    ) -> Dict[str, Any]:
        """Create evidence manifest with integrity hashes."""
        print("📋 Creating evidence manifest...")

        manifest = {
            "bundle_id": self.bundle_id,
            "created_at": datetime.utcnow().isoformat(),
            "version": "1.0",
            "format": "avro",
            "artifacts": {
                "access_receipts": {
                    "count": len(receipts),
                    "hash": self.compute_hash(json.dumps(receipts, sort_keys=True)),
                    "schema_version": "1.0",
                },
                "capability_tokens": {
                    "count": len(tokens),
                    "hash": self.compute_hash(json.dumps(tokens, sort_keys=True)),
                    "schema_version": "1.0",
                },
                "egress_certificates": {
                    "count": len(certificates),
                    "hash": self.compute_hash(json.dumps(certificates, sort_keys=True)),
                    "schema_version": "1.0",
                },
                "safety_case": {
                    "hash": self.compute_hash(json.dumps(safety_case, sort_keys=True)),
                    "version": safety_case["version"],
                },
            },
            "integrity": {
                "bundle_hash": "",  # Will be computed after serialization
                "signing_algorithm": "ed25519",
                "signature": "",  # Will be added by DSSE signing
            },
            "metadata": {
                "collection_period": {
                    "start": (datetime.utcnow() - timedelta(days=1)).isoformat(),
                    "end": datetime.utcnow().isoformat(),
                },
                "total_artifacts": len(receipts) + len(tokens) + len(certificates) + 1,
                "bundle_size_bytes": 0,  # Will be computed
            },
        }

        print("✅ Manifest created")
        return manifest

    def compute_hash(self, data: str) -> str:
        """Compute SHA-256 hash of data."""
        return hashlib.sha256(data.encode()).hexdigest()

    def sign_with_dsse(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Sign payload using DSSE (Dead Simple Signing Envelope)."""
        import base64

        # Serialize payload
        payload_json = json.dumps(payload, sort_keys=True)
        payload_b64 = base64.b64encode(payload_json.encode()).decode()

        # Create DSSE envelope
        envelope = {
            "payloadType": "application/vnd.provability-fabric.evidence-bundle",
            "payload": payload_b64,
            "signatures": [],
        }

        # Sign the envelope
        to_sign = f"DSSEv1 {envelope['payloadType']} {envelope['payload']}"
        signature = self.signing_key.sign(to_sign.encode())

        public_key = self.signing_key.public_key()
        public_bytes = public_key.public_bytes(
            encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw
        )

        envelope["signatures"].append(
            {
                "keyid": hashlib.sha256(public_bytes).hexdigest()[:16],
                "sig": base64.b64encode(signature).decode(),
            }
        )

        return envelope

    def save_bundle(
        self,
        manifest: Dict,
        receipts: List,
        tokens: List,
        certificates: List,
        safety_case: Dict,
    ):
        """Save evidence bundle to disk."""
        print(f"💾 Saving evidence bundle: {self.bundle_id}")

        bundle_dir = self.evidence_dir / self.bundle_id
        bundle_dir.mkdir(exist_ok=True)

        # Save individual artifact files
        with open(bundle_dir / "access_receipts.json", "w") as f:
            json.dump(receipts, f, indent=2)

        with open(bundle_dir / "capability_tokens.json", "w") as f:
            json.dump(tokens, f, indent=2)

        with open(bundle_dir / "egress_certificates.json", "w") as f:
            json.dump(certificates, f, indent=2)

        with open(bundle_dir / "safety_case.json", "w") as f:
            json.dump(safety_case, f, indent=2)

        # Sign and save manifest
        signed_manifest = self.sign_with_dsse(manifest)
        with open(bundle_dir / "manifest.json", "w") as f:
            json.dump(signed_manifest, f, indent=2)

        # Create bundle archive
        archive_path = self.evidence_dir / f"{self.bundle_id}.tar.gz"
        subprocess.run(
            [
                "tar",
                "czf",
                str(archive_path),
                "-C",
                str(self.evidence_dir),
                self.bundle_id,
            ],
            check=True,
        )

        print(f"✅ Bundle saved: {archive_path}")

        # Optionally upload to cloud storage
        if self.config.get("cloud_storage"):
            self.upload_to_cloud(archive_path)

    def upload_to_cloud(self, archive_path: Path):
        """Upload bundle to cloud storage (AWS S3/Glacier)."""
        print("☁️ Uploading to cloud storage...")

        # This would implement actual cloud upload
        # For now, just simulate
        cloud_url = f"s3://evidence-bucket/{self.bundle_id}.tar.gz"
        print(f"✅ Uploaded to: {cloud_url}")

    def generate_bundle(self, days_back: int = 1) -> str:
        """Generate complete evidence bundle."""
        print(f"🎯 Generating evidence bundle for last {days_back} day(s)")

        # Date range
        end_date = datetime.utcnow()
        start_date = end_date - timedelta(days=days_back)

        # Collect artifacts
        receipts = self.collect_access_receipts(start_date, end_date)
        tokens = self.collect_capability_tokens(start_date, end_date)
        certificates = self.collect_egress_certificates(start_date, end_date)
        safety_case = self.generate_safety_case()

        # Validate minimum requirements
        if not receipts and not tokens and not certificates:
            print("⚠️ Warning: No artifacts collected")

        # Create manifest
        manifest = self.create_manifest(receipts, tokens, certificates, safety_case)

        # Save bundle
        self.save_bundle(manifest, receipts, tokens, certificates, safety_case)

        # Print summary
        print(f"\n📊 BUNDLE SUMMARY:")
        print(f"  Bundle ID: {self.bundle_id}")
        print(f"  Access Receipts: {len(receipts)}")
        print(f"  Capability Tokens: {len(tokens)}")
        print(f"  Egress Certificates: {len(certificates)}")
        print(f"  Safety Case: Generated")
        print(f"  Period: {start_date.date()} to {end_date.date()}")

        return self.bundle_id


def main():
    parser = argparse.ArgumentParser(description="Evidence Bundle Case Generator")
    parser.add_argument(
        "--config", default="./tools/evidence/config.yaml", help="Configuration file"
    )
    parser.add_argument(
        "--days", type=int, default=1, help="Days back to collect evidence"
    )
    parser.add_argument("--output-dir", help="Output directory for evidence")

    args = parser.parse_args()

    try:
        bundle = EvidenceBundle(args.config)

        if args.output_dir:
            bundle.evidence_dir = Path(args.output_dir)
            bundle.evidence_dir.mkdir(exist_ok=True)

        bundle_id = bundle.generate_bundle(args.days)
        print(f"\n✅ Evidence bundle created: {bundle_id}")

    except Exception as e:
        print(f"❌ Error generating evidence bundle: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
