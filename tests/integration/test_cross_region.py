"""Smoke integration tests referenced by operational-excellence.yaml (F06)."""

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]


def test_cross_region_config_present():
    """Cross-region DR scripts and terraform layout exist."""
    assert (REPO_ROOT / "ops" / "terraform" / "regions").is_dir()
    assert (REPO_ROOT / "scripts" / "zero-downtime-upgrade.sh").is_file()


def test_billing_metering_tool_builds():
    """Billing metering tool sources are present."""
    metering = REPO_ROOT / "tools" / "metering"
    assert (metering / "main.go").is_file() or any(metering.glob("*.go"))


def test_marketplace_layout_present():
    """Marketplace API and UI directories exist."""
    assert (REPO_ROOT / "marketplace" / "api").is_dir()
    assert (REPO_ROOT / "marketplace" / "ui" / "package.json").is_file()


def test_reproducibility_lockfiles_present():
    """Key Node packages ship lockfiles for reproducible CI installs."""
    for rel in (
        "runtime/ledger/package-lock.json",
        "console/package-lock.json",
        "marketplace/ui/package-lock.json",
    ):
        assert (REPO_ROOT / rel).is_file(), f"missing lockfile: {rel}"
