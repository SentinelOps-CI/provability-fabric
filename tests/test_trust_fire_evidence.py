"""Adversarial tests for TRUST-FIRE CI execution-evidence reporting."""

from __future__ import annotations

import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("trust_fire_evidence", ROOT / "tools/ci/trust_fire_evidence.py")
assert SPEC and SPEC.loader
mod = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(mod)

CONTEXT = {"repository": "SentinelOps-CI/provability-fabric",
           "commit_sha": "a" * 40, "run_id": 1234567, "run_attempt": 2}
START = "2026-11-18T11:00:00Z"
STEP_START = "2026-11-18T11:00:10Z"
STEP_END = "2026-11-18T11:00:20Z"
END = "2026-11-18T11:00:30Z"


def steps(overrides=None):
    base = {p: {"outcome": "success", "started_at": STEP_START, "completed_at": STEP_END}
            for p in mod.PHASES}
    if overrides:
        for p, changes in overrides.items():
            base[p].update(changes)
    return base


def report(raw="2,3,6", modifications=None):
    return mod.build_report(
        raw_selection=raw, context=CONTEXT, selection_started_at=START,
        step_data=modifications if modifications is not None else steps(),
        completed_at=END,
    )


class PhaseSelectionTests(unittest.TestCase):
    def test_canonical_and_permutation(self):
        for raw in ("2,3,6", "3, 6, 2", " 2 ,3,6 "):
            with self.subTest(raw=raw):
                self.assertEqual(mod.parse_phases(raw), ("2", "3", "6"))

    def test_explicit_partial_selection(self):
        self.assertEqual(mod.parse_phases("6,2"), ("2", "6"))

    def test_reject_invalid_inputs(self):
        for raw in ("", " ", "2,", ",2", "2,,3", "2,2,3", "2,3,6,6", "12", "23", "4",
                    "2;3", "2,3,0", "2,3\n6", "[2,3,6]", "__import__('os')"):
            with self.subTest(raw=raw), self.assertRaises(mod.EvidenceError):
                mod.parse_phases(raw)

    def test_writes_safe_exact_action_output(self):
        with tempfile.TemporaryDirectory() as d:
            output = Path(d) / "output"
            rc = mod.main(["select", "--output", str(output)],
                          env={"TRUST_FIRE_PHASES": "3, 6,2"})
            self.assertEqual(rc, 0)
            lines = dict(line.split("=", 1) for line in output.read_text().strip().splitlines())
            self.assertEqual(json.loads(lines["phase_ids"]), ["2", "3", "6"])
            mod.parse_timestamp(lines["started_at"], field="started_at")

    def test_invalid_selection_does_not_append_output(self):
        with tempfile.TemporaryDirectory() as d:
            output = Path(d) / "output"
            output.write_text("existing\n")
            self.assertEqual(mod.main(["select", "--output", str(output)],
                                      env={"TRUST_FIRE_PHASES": "2,2"}), 1)
            self.assertEqual(output.read_text(), "existing\n")


class ReportTests(unittest.TestCase):
    def test_full_suite_pass(self):
        x = report()
        self.assertEqual(x["overall_status"], "PASS")
        self.assertEqual(x["duration_seconds"], 30)
        self.assertEqual(set(x["phase_results"]), {"phase_2", "phase_3", "phase_6"})
        mod.validate_report(x, expected_context=CONTEXT, expected_selection="2,3,6")

    def test_failed_phase_fails_entire_gate(self):
        for phase in mod.PHASES:
            with self.subTest(phase=phase):
                x = report(modifications=steps({phase: {"outcome": "failure"}}))
                self.assertEqual(x["phase_results"][f"phase_{phase}"]["status"], "FAIL")
                self.assertEqual(x["overall_status"], "FAIL")
                with self.assertRaises(mod.EvidenceError):
                    mod.validate_report(x, expected_context=CONTEXT, expected_selection="2,3,6")

    def test_missing_or_skipped_requested_step_fails(self):
        for outcome in ("", "skipped", "cancelled", "timed_out"):
            with self.subTest(outcome=outcome):
                x = report(modifications=steps({"3": {"outcome": outcome,
                                                        "started_at": "", "completed_at": ""}}))
                self.assertEqual(x["overall_status"], "FAIL")
                with self.assertRaises(mod.EvidenceError):
                    mod.validate_report(x, expected_context=CONTEXT, expected_selection="2,3,6")

    def test_missing_finish_timestamp_fails_even_with_success_outcome(self):
        x = report(modifications=steps({"2": {"completed_at": ""}}))
        self.assertEqual(x["phase_results"]["phase_2"]["status"], "FAIL")

    def test_partial_is_explicitly_not_a_full_pass(self):
        partial_steps = steps({"3": {"outcome": "skipped", "started_at": "", "completed_at": ""}})
        x = report(raw="2,6", modifications=partial_steps)
        self.assertEqual(x["overall_status"], "PARTIAL")
        self.assertEqual(x["phase_results"]["phase_3"]["status"], "SKIP")
        with self.assertRaises(mod.EvidenceError):
            mod.validate_report(x, expected_context=CONTEXT, expected_selection="2,6")

    def test_unrequested_phase_executed_is_failure(self):
        x = report(raw="2,6", modifications=steps())
        self.assertEqual(x["overall_status"], "FAIL")
        self.assertEqual(x["phase_results"]["phase_3"]["status"], "FAIL")

    def test_tampered_verdict_is_rejected(self):
        x = report(modifications=steps({"6": {"outcome": "failure"}}))
        x["phase_results"]["phase_6"]["status"] = "PASS"
        x["overall_status"] = "PASS"
        with self.assertRaises(mod.EvidenceError):
            mod.validate_report(x, expected_context=CONTEXT, expected_selection="2,3,6")

    def test_omitted_phase_is_rejected(self):
        x = report()
        del x["phase_results"]["phase_3"]
        with self.assertRaises(mod.EvidenceError):
            mod.validate_report(x, expected_context=CONTEXT, expected_selection="2,3,6")

    def test_extra_phase_is_rejected(self):
        x = report()
        x["phase_results"]["phase_1"] = {"status": "PASS"}
        with self.assertRaises(mod.EvidenceError):
            mod.validate_report(x, expected_context=CONTEXT, expected_selection="2,3,6")

    def test_provenance_mismatches_are_rejected(self):
        for field, bad in (("repository", "attacker/repo"), ("commit_sha", "b" * 40),
                           ("run_id", 777), ("run_attempt", 1), ("run_id", "1234567")):
            with self.subTest(field=field, bad=bad):
                x = report()
                x[field] = bad
                with self.assertRaises(mod.EvidenceError):
                    mod.validate_report(x, expected_context=CONTEXT, expected_selection="2,3,6")

    def test_report_selection_mismatch_is_rejected(self):
        x = report()
        with self.assertRaises(mod.EvidenceError):
            mod.validate_report(x, expected_context=CONTEXT, expected_selection="2,6")

    def test_command_identity_tampering_is_rejected(self):
        x = report()
        x["phase_results"]["phase_6"]["command"] = "echo pass"
        with self.assertRaises(mod.EvidenceError):
            mod.validate_report(x, expected_context=CONTEXT, expected_selection="2,3,6")

    def test_schema_and_source_mismatch(self):
        for key, value in (("schema_version", 2), ("schema_version", True),
                           ("evidence_source", "hardcoded_pass"), ("test_suite", "other")):
            with self.subTest(key=key):
                x = report()
                x[key] = value
                with self.assertRaises(mod.EvidenceError):
                    mod.validate_report(x, expected_context=CONTEXT, expected_selection="2,3,6")

    def test_duration_and_time_tampering(self):
        for key, value in (("duration_seconds", 0), ("duration_seconds", "30"),
                           ("start_time", "2026-11-18T12:00:00Z"),
                           ("end_time", "2026-11-18T10:00:00Z")):
            with self.subTest(key=key):
                x = report()
                x[key] = value
                with self.assertRaises(mod.EvidenceError):
                    mod.validate_report(x, expected_context=CONTEXT, expected_selection="2,3,6")

    def test_invalid_or_backwards_phase_timestamps(self):
        bad = report(modifications=steps({"2": {"started_at": "2026-11-18T11:00:31Z"}}))
        self.assertEqual(bad["overall_status"], "FAIL")
        x = report(modifications=steps({"2": {"started_at": STEP_END, "completed_at": STEP_START}}))
        self.assertEqual(x["overall_status"], "FAIL")

    def test_strict_run_context(self):
        for key, bad in (("commit_sha", "a"*39), ("commit_sha", "A"*40),
                         ("run_id", 0), ("run_attempt", -1), ("repository", "x")):
            with self.subTest(key=key), self.assertRaises(mod.EvidenceError):
                mod.validate_context({**CONTEXT, key: bad})

    def test_report_cli_and_gate_cli(self):
        env = {
            "GITHUB_REPOSITORY": CONTEXT["repository"],
            "GITHUB_SHA": CONTEXT["commit_sha"],
            "GITHUB_RUN_ID": str(CONTEXT["run_id"]),
            "GITHUB_RUN_ATTEMPT": str(CONTEXT["run_attempt"]),
            "TRUST_FIRE_PHASES": "2,3,6",
            "TRUST_FIRE_STARTED_AT": START,
        }
        for phase in mod.PHASES:
            env[f"PHASE_{phase}_OUTCOME"] = "success"
            env[f"PHASE_{phase}_STARTED_AT"] = STEP_START
            env[f"PHASE_{phase}_COMPLETED_AT"] = STEP_END
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "trust-fire-report.json"
            self.assertEqual(mod.main(["report", "--output", str(path)], env=env), 0)
            self.assertEqual(mod.main(["gate", "--report", str(path)], env=env), 0)
            env["GITHUB_RUN_ATTEMPT"] = "3"
            self.assertEqual(mod.main(["gate", "--report", str(path)], env=env), 1)


class MalformedEvidenceTests(unittest.TestCase):
    def test_json_duplicate_keys_are_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            file = Path(d) / "report.json"
            file.write_text('{"overall_status":"PASS","overall_status":"FAIL"}')
            with self.assertRaises(mod.EvidenceError):
                mod.read_report(file)

    def test_nan_and_infinity_are_rejected(self):
        for literal in ("NaN", "Infinity", "-Infinity"):
            with self.subTest(literal=literal):
                with tempfile.TemporaryDirectory() as d:
                    file = Path(d) / "report.json"
                    file.write_text('{"duration_seconds":'+literal+'}')
                    with self.assertRaises(mod.EvidenceError):
                        mod.read_report(file)

    def test_large_or_nonobject_report_is_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            file = Path(d) / "report.json"
            file.write_bytes(b" " * 65537)
            with self.assertRaises(mod.EvidenceError):
                mod.read_report(file)
            file.write_text("[]")
            with self.assertRaises(mod.EvidenceError):
                mod.read_report(file)


if __name__ == "__main__":
    unittest.main()
