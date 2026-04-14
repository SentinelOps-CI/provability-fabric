# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Build policy compliance summary from the event stream.

from __future__ import annotations

import json
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, List


@dataclass
class PolicyComplianceSummary:
    """Final policy compliance summary for a run (pass/fail, reason codes)."""

    run_id: str
    total_events: int
    total_tool_calls: int
    violations: int
    compliant: bool
    violation_details: List[Dict[str, Any]] = field(default_factory=list)
    reason_codes: List[str] = field(default_factory=list)
    chain_tail_hash: str = ""

    def to_dict(self) -> dict:
        return {
            "run_id": self.run_id,
            "total_events": self.total_events,
            "total_tool_calls": self.total_tool_calls,
            "violations": self.violations,
            "compliant": self.compliant,
            "violation_details": self.violation_details,
            "reason_codes": self.reason_codes,
            "chain_tail_hash": self.chain_tail_hash,
        }


def build_compliance_summary(ledger) -> PolicyComplianceSummary:
    """Build policy compliance summary from a LedgerStream."""
    events = ledger.get_events()
    violations = [e for e in events if e.event_type == "violation"]
    tool_calls = [e for e in events if e.event_type in ("tool_call", "violation")]
    details = []
    reason_codes = []
    for e in violations:
        details.append({
            "event_id": e.event_id,
            "timestamp": e.timestamp,
            "payload": e.payload,
        })
        rc = (e.payload or {}).get("reason_code")
        if rc:
            reason_codes.append(rc)
    return PolicyComplianceSummary(
        run_id=ledger.run_id,
        total_events=len(events),
        total_tool_calls=len(tool_calls),
        violations=len(violations),
        compliant=len(violations) == 0,
        violation_details=details,
        reason_codes=reason_codes,
        chain_tail_hash=ledger.get_chain_tail_hash(),
    )


def write_compliance_summary(output_path: Path, summary: PolicyComplianceSummary) -> None:
    """Write policy_compliance_summary.json."""
    output_path = Path(output_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(
        json.dumps(summary.to_dict(), indent=2),
        encoding="utf-8",
    )


def build_compliance_summary_from_events_file(events_path: Path, run_id: str = "") -> PolicyComplianceSummary:
    """Build policy compliance summary from an existing events.jsonl file."""
    events_path = Path(events_path)
    if not events_path.exists():
        return PolicyComplianceSummary(
            run_id=run_id or "unknown",
            total_events=0,
            total_tool_calls=0,
            violations=0,
            compliant=True,
            violation_details=[],
            reason_codes=[],
            chain_tail_hash="",
        )
    events = []
    chain_tail = "0"
    with open(events_path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                ev = json.loads(line)
                events.append(ev)
                chain_tail = ev.get("event_hash", chain_tail)
            except json.JSONDecodeError:
                continue
    violations = [e for e in events if e.get("event_type") == "violation"]
    tool_calls = [e for e in events if e.get("event_type") in ("tool_call", "violation")]
    details = []
    reason_codes = []
    for e in violations:
        payload = e.get("payload", {})
        details.append({"event_id": e.get("event_id"), "timestamp": e.get("timestamp"), "payload": payload})
        rc = payload.get("reason_code")
        if rc:
            reason_codes.append(rc)
    return PolicyComplianceSummary(
        run_id=run_id or "unknown",
        total_events=len(events),
        total_tool_calls=len(tool_calls),
        violations=len(violations),
        compliant=len(violations) == 0,
        violation_details=details,
        reason_codes=reason_codes,
        chain_tail_hash=chain_tail,
    )
