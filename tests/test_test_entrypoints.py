"""Guard local test selection against synthetic integration claims."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
INTEGRATION_MODULE = ROOT / "tests" / "integration" / "test_platform_integration.py"


@unittest.skipUnless(shutil.which("make"), "GNU Make is needed for entrypoint tests")
class TestEntrypointTests(unittest.TestCase):
    def dry_run(self, target: str) -> str:
        """Inspect Make's expanded commands without running services or tests."""
        result = subprocess.run(
            ["make", "--no-print-directory", "-n", target],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=20,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def test_default_test_runs_real_suites_and_excludes_simulators(self) -> None:
        output = self.dry_run("test")
        self.assertIn("test_record_criterion_baseline.py", output)
        self.assertIn("test_check_go_format.py", output)
        self.assertIn("test_trust_fire_orchestrator_report.py", output)
        self.assertIn("go test ./... -count=1", output)
        self.assertIn("cargo test --locked --workspace", output)
        self.assertIn("npm test -- --runInBand", output)
        self.assertNotIn("python3 tests/trust_fire_orchestrator.py", output)
        self.assertNotIn("python3 tests/integration/test_platform_integration.py", output)

    def test_synthetic_exercises_are_opt_in(self) -> None:
        output = self.dry_run("test-legacy-simulation")
        self.assertIn("python3 tests/trust_fire_orchestrator.py", output)
        self.assertIn("python3 tests/integration/test_platform_integration.py", output)
        self.assertIn("synthetic", output.lower())

    def test_security_target_uses_offline_contract_tests(self) -> None:
        output = self.dry_run("security")
        self.assertIn("test_redteam_observation_gate.py", output)
        self.assertIn("test_redteam_egress_contract.py", output)
        self.assertIn("test_redteam_retrieval_*.py", output)
        self.assertNotIn("tests/redteam/abac_fuzz.py --queries", output)
        self.assertNotIn("tests/redteam/pii_leak.py --vectors", output)
        self.assertNotIn("tests/security/malicious_adapter_test.py", output)

    def test_live_security_target_needs_reference_fixture(self) -> None:
        output = self.dry_run("security-live")
        self.assertIn("ABAC_FIXTURE_MANIFEST", output)
        self.assertIn("--fixture-manifest", output)
        self.assertIn("tests/redteam/pii_leak.py --vectors", output)
        with_fixture = subprocess.run(
            [
                "make", "--no-print-directory", "-n", "security-live",
                "ABAC_FIXTURE_MANIFEST=tests/redteam/fixtures/abac-reference.example.json",
            ],
            cwd=ROOT, capture_output=True, text=True, timeout=20, check=False,
        )
        self.assertEqual(with_fixture.returncode, 0, with_fixture.stderr)
        self.assertIn(
            '--fixture-manifest "tests/redteam/fixtures/abac-reference.example.json"',
            with_fixture.stdout,
        )

    def test_live_security_without_fixture_fails_before_running_probes(self) -> None:
        result = subprocess.run(
            ["make", "--no-print-directory", "security-live", "ABAC_FIXTURE_MANIFEST="],
            cwd=ROOT, capture_output=True, text=True, timeout=20, check=False,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Set ABAC_FIXTURE_MANIFEST", result.stdout + result.stderr)
        self.assertNotIn("Running probes with", result.stdout + result.stderr)

    def test_legacy_sandbox_simulator_is_opt_in(self) -> None:
        output = self.dry_run("security-legacy-simulation")
        self.assertIn("tests/security/malicious_adapter_test.py", output)
        self.assertIn("synthetic", output.lower())

    def test_aggregate_target_does_not_claim_exhaustiveness(self) -> None:
        output = self.dry_run("test-all")
        self.assertNotIn("All tests completed successfully", output)
        self.assertIn("selected local checks", output.lower())


class IntegrationReportClassificationTests(unittest.TestCase):
    def test_stub_integration_report_is_classified_as_simulation(self) -> None:
        spec = importlib.util.spec_from_file_location(
            "legacy_integration_simulation", INTEGRATION_MODULE
        )
        self.assertIsNotNone(spec)
        self.assertIsNotNone(spec.loader)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        with tempfile.TemporaryDirectory() as dirname:
            tester = module.PlatformIntegrationTester.__new__(module.PlatformIntegrationTester)
            tester.test_workspace = Path(dirname)
            tester.test_results = {
                "core_services": True,
                "runtime_components": True,
                "api_gateway": True,
                "evidence_replay": True,
                "security": True,
            }
            tester.generate_integration_report()
            report = json.loads(
                (tester.test_workspace / "platform_integration_report.json").read_text(
                    encoding="utf-8"
                )
            )
        self.assertTrue(report["simulation_only"])
        self.assertIs(report["operational_claim_validated"], False)
        self.assertEqual(report["summary"]["total_tests"], 5)
        self.assertEqual(report["test_suite"], "Legacy Platform Integration Simulation")


if __name__ == "__main__":
    unittest.main()
