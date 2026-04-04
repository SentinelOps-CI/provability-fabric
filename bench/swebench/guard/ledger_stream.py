# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Append-only hash-chained event stream for PF evidence (events.jsonl).

from __future__ import annotations

import hashlib
import json
import os
import urllib.request
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional


def _push_event_to_ledger_api(ledger_url: str, event: dict) -> None:
    """Optional: POST event to PF ledger API (minimal server pattern). No-op on failure."""
    try:
        req = urllib.request.Request(
            ledger_url.rstrip("/") + "/events",
            data=json.dumps(event).encode("utf-8"),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        urllib.request.urlopen(req, timeout=5)
    except Exception:
        pass


@dataclass
class LedgerEvent:
    """Single event in the ledger stream."""

    event_id: str
    event_type: str
    timestamp: str
    payload: Dict[str, Any]
    previous_hash: str
    event_hash: str
    sequence: int

    def to_dict(self) -> dict:
        return asdict(self)


def _compute_hash(prev: str, payload_json: str) -> str:
    return hashlib.sha256((prev + "\n" + payload_json).encode("utf-8")).hexdigest()


class LedgerStream:
    """Append-only hash-chained event stream. Writes to events.jsonl."""

    def __init__(self, output_path: Path, run_id: str = ""):
        self.output_path = Path(output_path)
        self.run_id = run_id or "default"
        self._sequence = 0
        self._previous_hash = "0"
        self._events: List[LedgerEvent] = []
        self.output_path.parent.mkdir(parents=True, exist_ok=True)
        self._file_handle: Optional[Any] = None
        self._load_tail()

    def _load_tail(self) -> None:
        """Load last event hash and sequence from existing file so chain continues across invocations."""
        if not self.output_path.exists():
            return
        try:
            with open(self.output_path, "r", encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        ev = json.loads(line)
                        self._previous_hash = ev.get("event_hash", self._previous_hash)
                        self._sequence = max(self._sequence, ev.get("sequence", 0))
                    except json.JSONDecodeError:
                        continue
        except OSError:
            pass

    def _next_id(self) -> str:
        self._sequence += 1
        return f"{self.run_id}_{self._sequence}"

    def append(
        self,
        event_type: str,
        payload: Dict[str, Any],
    ) -> LedgerEvent:
        event_id = self._next_id()
        ts = datetime.now(timezone.utc).isoformat()
        payload_json = json.dumps(payload, sort_keys=True, separators=(",", ":"))
        event_hash = _compute_hash(self._previous_hash, payload_json)
        event = LedgerEvent(
            event_id=event_id,
            event_type=event_type,
            timestamp=ts,
            payload=payload,
            previous_hash=self._previous_hash,
            event_hash=event_hash,
            sequence=self._sequence,
        )
        self._previous_hash = event_hash
        self._events.append(event)
        ev_dict = event.to_dict()
        line = json.dumps(ev_dict, ensure_ascii=False) + "\n"
        with open(self.output_path, "a", encoding="utf-8") as f:
            f.write(line)
        ledger_url = os.environ.get("PF_LEDGER_URL", "")
        if ledger_url:
            _push_event_to_ledger_api(ledger_url, ev_dict)
        return event

    def append_tool_call(
        self,
        tool: str,
        allowed: bool,
        command_or_path: str,
        exit_code: Optional[int] = None,
        stdout_redacted: Optional[str] = None,
        stderr_redacted: Optional[str] = None,
        violation: Optional[str] = None,
        reason_code: Optional[str] = None,
    ) -> LedgerEvent:
        payload = {
            "tool": tool,
            "allowed": allowed,
            "command_or_path": command_or_path,
        }
        if exit_code is not None:
            payload["exit_code"] = exit_code
        if stdout_redacted is not None:
            payload["stdout_redacted"] = stdout_redacted
        if stderr_redacted is not None:
            payload["stderr_redacted"] = stderr_redacted
        if violation:
            payload["violation"] = violation
        if reason_code:
            payload["reason_code"] = reason_code
        return self.append(
            "tool_call" if allowed else "violation",
            payload,
        )

    def get_events(self) -> List[LedgerEvent]:
        return list(self._events)

    def get_chain_tail_hash(self) -> str:
        return self._previous_hash
