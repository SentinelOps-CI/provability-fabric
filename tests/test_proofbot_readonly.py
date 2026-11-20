"""Negative controls for the read-only APOLLO proposal inspection boundary."""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("apollo_readonly", ROOT / "tools/proofbot/run.py")
assert SPEC is not None and SPEC.loader is not None
bot = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(bot)


class FakeResponse:
    """Minimal streaming HTTP response for offline transport testing."""

    def __init__(self, data: bytes, status: int = 200, content_type: str = "application/json"):
        self.data = data
        self.status_code = status
        self.headers = {"Content-Type": content_type}

    def __enter__(self):
        return self

    def __exit__(self, *args):
        return False

    def iter_content(self, chunk_size: int):
        for start in range(0, len(self.data), chunk_size):
            yield self.data[start:start + chunk_size]


class ReadOnlyProofBotTests(unittest.TestCase):
    def setUp(self):
        self.root_tmp = tempfile.TemporaryDirectory()
        self.output_tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.root_tmp.cleanup)
        self.addCleanup(self.output_tmp.cleanup)
        self.root = Path(self.root_tmp.name)
        self.report = Path(self.output_tmp.name) / "inspection.json"
        self.lean = self.root / "Formal" / "Example.lean"
        self.lean.parent.mkdir(parents=True)
        self.lean.write_text("theorem sample : True := by\n  sorry\n", encoding="utf-8")
        self.original = self.lean.read_bytes()

    def valid_response(self):
        return FakeResponse(json.dumps({"proof_patch": "by exact True.intro"}).encode())

    def test_local_inventory_never_calls_network(self):
        with patch.object(bot.requests, "post") as post:
            status = bot.main(["--root", str(self.root), "--dry-run", "--report", str(self.report)])
        self.assertEqual(status, 0)
        post.assert_not_called()
        data = json.loads(self.report.read_text())
        self.assertEqual(data["status"], "INVENTORY_ONLY")
        self.assertFalse(data["proofs_verified"])
        self.assertEqual(data["candidate_count"], 1)
        self.assertEqual(data["records"][0]["source_sha256"], hashlib.sha256(self.original).hexdigest())
        self.assertEqual(self.lean.read_bytes(), self.original)

    def test_candidate_response_is_hashed_and_never_applied(self):
        with patch.object(bot.requests, "post", return_value=self.valid_response()) as post:
            status = bot.main([
                "--root", str(self.root), "--api-url", "https://proofs.example.test/api",
                "--report", str(self.report),
            ])
        self.assertEqual(status, 0)
        post.assert_called_once()
        args, kwargs = post.call_args
        self.assertEqual(args[0], "https://proofs.example.test/api/prove")
        self.assertEqual(kwargs["timeout"], (5, 30))
        self.assertIs(kwargs["allow_redirects"], False)
        result = json.loads(self.report.read_text())
        self.assertEqual(result["status"], "UNVERIFIED_PROPOSALS")
        self.assertFalse(result["proofs_verified"])
        self.assertEqual(
            result["records"][0]["proposal_sha256"],
            hashlib.sha256(b"by exact True.intro").hexdigest(),
        )
        self.assertNotIn("proof_patch", self.report.read_text())
        self.assertEqual(self.lean.read_bytes(), self.original)
        self.assertEqual(list(self.root.rglob("*")), [self.root / "Formal", self.lean])

    def test_invalid_endpoints_fail_closed(self):
        for url in (
            "", "https://user:password@host.example", "file:///tmp/input",
            "http://proofs.example.test", "https://proofs.example.test?token=secret",
            "https://proofs.example.test/#frag",
        ):
            with self.subTest(url=url), self.assertRaises(bot.ProposalError):
                bot.validate_endpoint(url)
        self.assertEqual(
            bot.validate_endpoint("http://127.0.0.1:8080"),
            "http://127.0.0.1:8080/prove",
        )

    def test_http_errors_and_redirects_fail_closed(self):
        for status in (301, 302, 401, 403, 404, 500):
            with self.subTest(status=status), patch.object(
                bot.requests, "post", return_value=FakeResponse(b"{}", status=status)
            ):
                data, code = bot.inspect(self.root, api_url="https://proofs.example.test")
                self.assertEqual(code, 1)
                self.assertEqual(data["status"], "INCOMPLETE")
                self.assertEqual(data["records"][0]["error_code"], f"api_http_{status}")

    def test_invalid_and_oversized_responses_fail_closed(self):
        responses = (
            (b'{"proof_patch":""}', "missing_proof_patch"),
            (b'{"proof_patch":10}', "missing_proof_patch"),
            (b'{"proof_patch":"ok","proof_patch":"duplicate"}', "duplicate_api_json_field"),
            (b'{"proof_patch":NaN}', "nonfinite_api_json_number"),
            (b'{"proof_patch":', "invalid_api_json"),
            (json.dumps({"proof_patch": "X" * (bot.MAX_PATCH_BYTES + 1)}).encode(),
             "oversized_proof_patch"),
            (b" " * (bot.MAX_RESPONSE_BYTES + 1), "oversized_api_response"),
        )
        for response, expected in responses:
            with self.subTest(expected=expected), patch.object(
                bot.requests, "post", return_value=FakeResponse(response)
            ):
                data, code = bot.inspect(self.root, api_url="https://proofs.example.test")
                self.assertEqual(code, 1)
                self.assertEqual(data["records"][0]["error_code"], expected)
                self.assertEqual(self.lean.read_bytes(), self.original)

    def test_transport_failure_is_failure_not_no_proofs(self):
        with patch.object(
            bot.requests, "post", side_effect=bot.requests.Timeout("offline")
        ):
            data, code = bot.inspect(self.root, api_url="https://proofs.example.test")
        self.assertEqual(code, 1)
        self.assertEqual(data["records"][0]["error_code"], "api_transport_failure")

    def test_source_changed_during_api_call_is_detected(self):
        def mutate(*args, **kwargs):
            self.lean.write_text("theorem sample : True := by\n  trivial\n")
            return self.valid_response()

        with patch.object(bot.requests, "post", side_effect=mutate):
            data, code = bot.inspect(self.root, api_url="https://proofs.example.test")
        self.assertEqual(code, 1)
        self.assertEqual(data["records"][0]["error_code"], "source_changed_during_inspection")
        self.assertNotIn("proposal_sha256", data["records"][0])

    def test_symlinked_sources_and_build_directories_are_excluded(self):
        (self.root / ".lake").mkdir()
        (self.root / ".lake" / "Generated.lean").write_text("by sorry\n")
        (self.root / "Symlink.lean").symlink_to(self.lean)
        items = bot.discover(self.root)
        self.assertEqual([item["path"] for item in items], ["Formal/Example.lean"])

    def test_report_cannot_modify_repository_worktree(self):
        with self.assertRaises(bot.ProposalError):
            bot.write_report(
                {"status": "UNVERIFIED"}, self.root / "report.json", self.root
            )
        self.assertFalse((self.root / "report.json").exists())

    def test_workflow_is_read_only_and_retains_configuration_failure(self):
        workflow = (ROOT / ".github/workflows/proof-bot.yaml").read_text()
        self.assertIn("contents: read", workflow)
        self.assertIn("persist-credentials: false", workflow)
        self.assertIn("APOLLO_API_URL unset", workflow)
        self.assertNotIn("contents: write", workflow)
        self.assertNotIn("pull-requests: write", workflow)
        self.assertNotIn("create-pull-request@", workflow)
        self.assertNotIn("git config --global", workflow)


if __name__ == "__main__":
    unittest.main()
