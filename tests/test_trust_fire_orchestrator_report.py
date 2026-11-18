"""Protect the reported scope and final verdict of the legacy TRUST-FIRE simulator."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest

SOURCE = Path(__file__).with_name("trust_fire_orchestrator.py")
if not SOURCE.is_file():
    SOURCE = Path(__file__).resolve().parents[1] / "tests" / "trust_fire_orchestrator.py"
SPEC = importlib.util.spec_from_file_location("trust_fire_orchestrator", SOURCE)
assert SPEC and SPEC.loader
module = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(module)


def make_orchestrator(statuses):
    obj = module.TrustFireOrchestrator({})
    obj.phase_results = {f"phase{i}": {"status": status}
                         for i, status in enumerate(statuses, start=1)}
    return obj


class LegacyOrchestratorReportTests(unittest.TestCase):
    def test_complete_success_is_only_a_simulation_pass(self):
        record = make_orchestrator(["PASS"] * 6).generate_report(suite_success=True)
        self.assertEqual(record["overall_status"], "PASS")
        self.assertTrue(record["simulation_only"])
        self.assertIs(record["safety_claim_validated"], False)
        self.assertEqual(record["test_suite"], "TRUST-FIRE Legacy Simulation Smoke")

    def test_zero_phases_cannot_vacuously_pass(self):
        record = make_orchestrator([]).generate_report(suite_success=True)
        self.assertEqual(record["overall_status"], "FAIL")

    def test_partial_execution_cannot_pass(self):
        for n in range(1, 6):
            with self.subTest(n=n):
                record = make_orchestrator(["PASS"] * n).generate_report(suite_success=True)
                self.assertEqual(record["overall_status"], "FAIL")

    def test_duplicate_or_unexpected_phase_keys_cannot_pass(self):
        obj = make_orchestrator(["PASS"] * 6)
        obj.phase_results["phase7"] = {"status": "PASS"}
        self.assertEqual(obj.generate_report(suite_success=True)["overall_status"], "FAIL")

    def test_phase_failure_fails_even_if_caller_claims_success(self):
        for i in range(6):
            with self.subTest(i=i):
                states = ["PASS"] * 6
                states[i] = "FAIL"
                self.assertEqual(
                    make_orchestrator(states).generate_report(suite_success=True)["overall_status"],
                    "FAIL",
                )

    def test_failed_final_criterion_fails_even_with_six_green_phases(self):
        report = make_orchestrator(["PASS"] * 6).generate_report(suite_success=False)
        self.assertEqual(report["overall_status"], "FAIL")

    def test_omitted_success_is_fail_closed(self):
        report = make_orchestrator(["PASS"] * 6).generate_report()
        self.assertEqual(report["overall_status"], "FAIL")


if __name__ == "__main__":
    unittest.main()
