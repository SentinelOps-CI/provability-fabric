"""Independent negative controls for the decrypted synthetic DSAR verifier."""

from __future__ import annotations

import json
import tempfile
import unittest
import zipfile
from pathlib import Path

from verify_dsar_archive import InvalidDSAR, validate_archive, validate_payload


def sample_payload() -> dict:
    """Produce a minimal valid counterpart to the exporter's mock schema."""
    return {
        "tenant_id": "test-tenant-1",
        "export_date": "2026-11-19T11:00:00Z",
        "usage_events": [
            {"id": f"e{i}", "tenant_id": "test-tenant-1", "cpu_ms": 1,
             "net_bytes": 2, "timestamp": "2026-11-19T10:00:00Z"}
            for i in range(2)
        ],
        "capsules": [
            {"id": f"c{i}", "tenant_id": "test-tenant-1", "hash": "hash",
             "spec_sig": "signature", "risk_score": 0.2,
             "created_at": "2026-11-18T10:00:00Z",
             "updated_at": "2026-11-19T10:00:00Z"}
            for i in range(2)
        ],
        "metadata": {"export_version": "1.0", "pii_redacted": True, "encrypted": True,
                     "after_date": "2024-01-01T00:00:00Z"},
    }


class DSARArchiveContractTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = sample_payload()

    def verify(self, value: dict) -> dict:
        return validate_payload(
            json.dumps(value).encode("utf-8"),
            expected_tenant="test-tenant-1",
            after_date="2024-01-01",
        )

    def test_valid_synthetic_payload(self) -> None:
        self.assertEqual(self.verify(self.data)["tenant_id"], "test-tenant-1")

    def test_export_tenant_mismatch(self) -> None:
        self.data["tenant_id"] = "other"
        with self.assertRaises(InvalidDSAR):
            self.verify(self.data)

    def test_cross_tenant_event(self) -> None:
        self.data["usage_events"][0]["tenant_id"] = "other"
        with self.assertRaises(InvalidDSAR):
            self.verify(self.data)

    def test_unexpected_pii_field(self) -> None:
        self.data["capsules"][0]["email"] = "secret@example.invalid"
        with self.assertRaises(InvalidDSAR):
            self.verify(self.data)

    def test_false_encryption_claim(self) -> None:
        self.data["metadata"]["encrypted"] = False
        with self.assertRaises(InvalidDSAR):
            self.verify(self.data)

    def test_date_filter_violation(self) -> None:
        self.data["usage_events"][0]["timestamp"] = "2023-12-31T23:59:59Z"
        with self.assertRaises(InvalidDSAR):
            self.verify(self.data)

    def test_nonfinite_risk(self) -> None:
        self.data["capsules"][0]["risk_score"] = float("nan")
        with self.assertRaises(InvalidDSAR):
            self.verify(self.data)

    def test_duplicate_json_key(self) -> None:
        raw = json.dumps(self.data).replace(
            '"tenant_id": "test-tenant-1",',
            '"tenant_id": "test-tenant-1", "tenant_id": "other",',
            1,
        )
        with self.assertRaises(InvalidDSAR):
            validate_payload(raw.encode(), expected_tenant="test-tenant-1", after_date="2024-01-01")

    def test_zip_member_contract(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            filename = Path(root) / "export.zip"
            with zipfile.ZipFile(filename, "w") as archive:
                archive.writestr("dsar-data.json", json.dumps(self.data))
            verified = validate_archive(filename, expected_tenant="test-tenant-1", after_date="2024-01-01")
            self.assertEqual(verified["tenant_id"], "test-tenant-1")
            with zipfile.ZipFile(filename, "w") as archive:
                archive.writestr("wrong-name.json", json.dumps(self.data))
            with self.assertRaises(InvalidDSAR):
                validate_archive(filename, expected_tenant="test-tenant-1", after_date="2024-01-01")

    def test_invalid_archive(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            filename = Path(root) / "export.zip"
            filename.write_bytes(b"not a ZIP")
            with self.assertRaises(InvalidDSAR):
                validate_archive(filename, expected_tenant="test-tenant-1", after_date="2024-01-01")


if __name__ == "__main__":
    unittest.main()
