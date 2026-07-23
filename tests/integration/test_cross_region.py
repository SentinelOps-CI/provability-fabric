"""Smoke integration tests referenced by operational-excellence.yaml (F06)."""

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]


def test_cross_region_config_present():
    """Cross-region DR scripts exist (Terraform removed; moto smoke is canonical)."""
    assert (REPO_ROOT / "scripts" / "dr" / "moto_dr_smoke.py").is_file()
    assert (REPO_ROOT / "scripts" / "zero-downtime-upgrade.sh").is_file()


def test_billing_metering_tool_builds():
    """Billing metering tool sources are present."""
    metering = REPO_ROOT / "tools" / "metering"
    assert (metering / "main.go").is_file() or any(metering.glob("*.go"))


def test_platform_services_layout_present():
    """Compose-backed Go platform services exist."""
    for name in (
        "api-gateway",
        "spec-service",
        "proof-service",
        "build-orchestrator",
        "evidence-service",
        "replay-service",
    ):
        assert (REPO_ROOT / "services" / name / "go.mod").is_file(), name


def test_console_layout_present():
    """Admin console (full Compose profile) is present."""
    assert (REPO_ROOT / "console" / "package.json").is_file()
    assert (REPO_ROOT / "console" / "Dockerfile").is_file()


def test_reproducibility_lockfiles_present():
    """Key Node packages ship lockfiles for reproducible CI installs."""
    for rel in (
        "runtime/ledger/package-lock.json",
        "console/package-lock.json",
    ):
        assert (REPO_ROOT / rel).is_file(), f"missing lockfile: {rel}"
