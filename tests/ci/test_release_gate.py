"""Synthetic GitHub API controls for the exact-SHA governance preflight."""

from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import unittest

SCRIPT = Path(__file__).resolve().parents[2] / "tools" / "ci" / "release_gate.py"
spec = importlib.util.spec_from_file_location("release_gate", SCRIPT)
assert spec and spec.loader
release_gate = importlib.util.module_from_spec(spec)
import sys
sys.modules[spec.name] = release_gate
spec.loader.exec_module(release_gate)

HEAD = "a" * 40
BASE = "b" * 40
ROOT = "/repos/SentinelOps-CI/provability-fabric"


def fixture() -> tuple[release_gate.ReleaseTarget, dict[str, object]]:
    t = release_gate.ReleaseTarget("SentinelOps-CI/provability-fabric", 300, HEAD, BASE, "fraware")
    p = {
        "/user": {"login": "fraware"},
        f"{ROOT}/pulls/300": {
            "state": "open", "merged_at": None, "draft": False,
            "head": {"sha": HEAD}, "base": {"sha": BASE, "ref": "main"},
            "user": {"login": "fraware"}, "mergeable": True, "mergeable_state": "clean",
        },
        f"{ROOT}/branches/main": {"commit": {"sha": BASE}, "protected": True},
        f"{ROOT}/commits/{HEAD}": {
            "author": {"login": "fraware"}, "committer": {"login": "fraware"}
        },
        f"{ROOT}/pulls/300/reviews?per_page=100&page=1": [
            {"id": 1, "user": {"login": "reviewer"}, "state": "APPROVED", "commit_id": HEAD}
        ],
        f"{ROOT}/commits/{HEAD}/check-runs?per_page=100&page=1": {
            "total_count": len(t.required),
            "check_runs": [
                {"name": name, "app": {"slug": app}, "status": "completed",
                 "conclusion": "success", "head_sha": HEAD}
                for name, app in t.required
            ],
        },
    }
    return t, p


def assess(t, p):
    return release_gate.evaluate(t, lambda endpoint: copy.deepcopy(p[endpoint]))


class ReleaseGateTests(unittest.TestCase):
    def test_valid_snapshot(self):
        self.assertEqual(assess(*fixture()), [])

    def test_refuses_wrong_authenticated_account(self):
        t, p = fixture(); p["/user"]["login"] = "different"
        self.assertTrue(any("authenticated GitHub account" in s for s in assess(t, p)))

    def test_refuses_unprotected_main(self):
        t, p = fixture(); p[f"{ROOT}/branches/main"]["protected"] = False
        self.assertIn("production main is not protected", assess(t, p))

    def test_refuses_main_drift(self):
        t, p = fixture(); p[f"{ROOT}/branches/main"]["commit"]["sha"] = "c" * 40
        self.assertTrue(any("advanced" in s for s in assess(t, p)))

    def test_refuses_draft_and_unreviewed(self):
        t, p = fixture(); p[f"{ROOT}/pulls/300"]["draft"] = True
        p[f"{ROOT}/pulls/300/reviews?per_page=100&page=1"] = []
        r = assess(t, p)
        self.assertTrue(any("draft" in s for s in r))
        self.assertTrue(any("independent approval" in s for s in r))

    def test_refuses_self_review_and_stale_review(self):
        t, p = fixture()
        p[f"{ROOT}/pulls/300/reviews?per_page=100&page=1"] = [
            {"id": 1, "user": {"login": "fraware"}, "state": "APPROVED", "commit_id": HEAD},
            {"id": 2, "user": {"login": "reviewer"}, "state": "APPROVED", "commit_id": BASE},
        ]
        self.assertTrue(any("independent" in s for s in assess(t, p)))

    def test_refuses_changes_requested_after_approval(self):
        t, p = fixture()
        p[f"{ROOT}/pulls/300/reviews?per_page=100&page=1"] += [
            {"id": 2, "user": {"login": "reviewer"}, "state": "CHANGES_REQUESTED", "commit_id": HEAD}
        ]
        self.assertTrue(any("changes-requested" in s for s in assess(t, p)))

    def test_refuses_wrong_commit_author_and_committer(self):
        t, p = fixture(); p[f"{ROOT}/commits/{HEAD}"]["committer"] = {"login": "other"}
        self.assertTrue(any("committer" in s for s in assess(t, p)))

    def test_refuses_wrong_pr_user(self):
        t, p = fixture(); p[f"{ROOT}/pulls/300"]["user"]["login"] = "other"
        self.assertTrue(any("PR author" in s for s in assess(t, p)))

    def test_refuses_wrong_check_app(self):
        t, p = fixture()
        p[f"{ROOT}/commits/{HEAD}/check-runs?per_page=100&page=1"]["check_runs"][0]["app"]["slug"] = "random"
        self.assertTrue(any("missing or ambiguous" in s for s in assess(t, p)))

    def test_refuses_skipped_required_check(self):
        t, p = fixture()
        p[f"{ROOT}/commits/{HEAD}/check-runs?per_page=100&page=1"]["check_runs"][0].update(
            {"status": "completed", "conclusion": "skipped"}
        )
        self.assertTrue(any("did not pass" in s for s in assess(t, p)))

    def test_refuses_check_with_wrong_sha(self):
        t, p = fixture()
        p[f"{ROOT}/commits/{HEAD}/check-runs?per_page=100&page=1"]["check_runs"][0]["head_sha"] = BASE
        self.assertTrue(any("not tied" in s for s in assess(t, p)))

    def test_refuses_ambiguous_check(self):
        t, p = fixture(); k=f"{ROOT}/commits/{HEAD}/check-runs?per_page=100&page=1"
        p[k]["check_runs"].append(copy.deepcopy(p[k]["check_runs"][0])); p[k]["total_count"] += 1
        self.assertTrue(any("ambiguous" in s for s in assess(t, p)))

    def test_refuses_changed_check_count_during_pagination(self):
        t, p = fixture(); k=f"{ROOT}/commits/{HEAD}/check-runs?per_page=100&page=1"
        p[k]["total_count"] += 1
        p[f"{ROOT}/commits/{HEAD}/check-runs?per_page=100&page=2"] = {"total_count":len(t.required),"check_runs":[]}
        with self.assertRaises(release_gate.GateError): assess(t, p)

    def test_refuses_bad_syntax(self):
        for bad in ("g", "1" * 39, "A" * 40):
            with self.subTest(bad=bad), self.assertRaises(release_gate.GateError):
                release_gate.ReleaseTarget("SentinelOps-CI/provability-fabric", 1, bad, BASE, "fraware")

    def test_refuses_missing_or_duplicate_required_checks(self):
        with self.assertRaises(release_gate.GateError):
            release_gate.ReleaseTarget("SentinelOps-CI/provability-fabric", 1, HEAD, BASE, "fraware", ())
        with self.assertRaises(release_gate.GateError):
            release_gate.ReleaseTarget("SentinelOps-CI/provability-fabric", 1, HEAD, BASE, "fraware", (("x","app"),("x","app")))

    def test_refuses_repeated_review_id(self):
        t, p = fixture()
        p[f"{ROOT}/pulls/300/reviews?per_page=100&page=1"].append(
            {"id": 1, "user": {"login": "reviewer-2"}, "state": "APPROVED", "commit_id": HEAD}
        )
        with self.assertRaises(release_gate.GateError): assess(t, p)

    def test_refuses_malformed_response(self):
        t, p = fixture(); p[f"{ROOT}/pulls/300"] = []
        with self.assertRaises(release_gate.GateError): assess(t, p)


if __name__ == "__main__":
    unittest.main()
