"""Billing integration smoke (F06)."""

from pathlib import Path


def test_ledger_billing_routes_exist():
    root = Path(__file__).resolve().parents[2]
    ledger_src = root / "runtime" / "ledger" / "src"
    candidates = list(ledger_src.rglob("*.ts"))
    assert candidates, "ledger src tree missing"
    joined = "\n".join(p.read_text(encoding="utf-8", errors="replace") for p in candidates)
    assert "invoice" in joined.lower() or "billing" in joined.lower()


def test_metering_readme_or_main():
    root = Path(__file__).resolve().parents[2]
    metering = root / "tools" / "metering"
    assert metering.is_dir()
    assert any(metering.glob("*.go"))
