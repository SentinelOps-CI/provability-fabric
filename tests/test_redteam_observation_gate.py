"""Offline negative controls for security harness execution accounting."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest

SOURCE = Path(__file__).resolve().parent / "redteam" / "observation_gate.py"
spec = importlib.util.spec_from_file_location("observation_gate", SOURCE)
assert spec is not None and spec.loader is not None
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class ObservationGateTests(unittest.TestCase):
    def verdict(self, **changes: int) -> list[str]:
        fields = dict(planned=12, recorded=12, valid_responses=12,
                      positive_controls=2, violations=0)
        fields.update(changes)
        return module.observation_failures(**fields)

    def test_complete_execution_with_positive_controls(self):
        self.assertEqual(self.verdict(), [])

    def test_no_planned_requests_never_passes(self):
        self.assertTrue(self.verdict(planned=0, recorded=0, valid_responses=0))

    def test_missing_results_fail(self):
        self.assertTrue(self.verdict(recorded=11, valid_responses=11))

    def test_http_or_transport_failures_fail(self):
        result = self.verdict(valid_responses=0)
        self.assertTrue(any("valid responses" in problem for problem in result))

    def test_no_positive_control_fails(self):
        self.assertTrue(self.verdict(positive_controls=0))

    def test_observed_violations_fail(self):
        self.assertTrue(self.verdict(violations=1))

    def test_overcount_and_negative_values_fail(self):
        self.assertTrue(self.verdict(valid_responses=13))
        self.assertTrue(self.verdict(valid_responses=-1))
        self.assertTrue(self.verdict(violations=-1))


if __name__ == "__main__":
    unittest.main()
