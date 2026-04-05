# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# OpenHands engine adapter: PF calls OpenHands as a library (or subprocess fallback)
# to solve one workspace and return a patch string. Emits structured trace:
# prompts sent, tool calls, files modified.

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.request
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, List, Optional

try:
    from ..constants import (
        DEFAULT_PRIME_INTELLECT_INFERENCE_BASE_URL,
        GIT_DIFF_TIMEOUT,
        MAX_PATCH_BYTES,
        DIFF_STAT_TIMEOUT,
        NAME_ONLY_QUICK_TIMEOUT,
        NO_EDIT_FAST_CHECK_TIMEOUT,
        DIFF_STAT_FILE_THRESHOLD,
        PATH_DIFF_TIMEOUT,
        PATH_RESTRICTED_MAX_PATHS_FALLBACK,
    )
except ImportError:
    try:
        from bench.swebench.constants import (
            DEFAULT_PRIME_INTELLECT_INFERENCE_BASE_URL,
            GIT_DIFF_TIMEOUT,
            MAX_PATCH_BYTES,
            DIFF_STAT_TIMEOUT,
            NAME_ONLY_QUICK_TIMEOUT,
            NO_EDIT_FAST_CHECK_TIMEOUT,
            DIFF_STAT_FILE_THRESHOLD,
            PATH_DIFF_TIMEOUT,
            PATH_RESTRICTED_MAX_PATHS_FALLBACK,
        )
    except ImportError:
        DEFAULT_PRIME_INTELLECT_INFERENCE_BASE_URL = "https://api.pinference.ai/api/v1"
        GIT_DIFF_TIMEOUT = 120
        MAX_PATCH_BYTES = 2 * 1024 * 1024
        DIFF_STAT_TIMEOUT = 20
        NAME_ONLY_QUICK_TIMEOUT = 30
        NO_EDIT_FAST_CHECK_TIMEOUT = 5
        DIFF_STAT_FILE_THRESHOLD = 200
        PATH_DIFF_TIMEOUT = 60
        PATH_RESTRICTED_MAX_PATHS_FALLBACK = 50

_ENGINE_LOG_PREFIX = "[openhands-engine]"


def _log_engine(msg: str) -> None:
    """Log to stderr unless PF_SWEBENCH_QUIET=1."""
    if os.environ.get("PF_SWEBENCH_QUIET", "").lower() in ("1", "true", "yes"):
        return
    print(f"{_ENGINE_LOG_PREFIX} {msg}", file=sys.stderr, flush=True)


@dataclass
class OpenHandsConfig:
    """Minimal configuration for OpenHands solver."""

    model_name: str = "gpt-4o-mini"
    max_iterations: int = 25
    temperature: float = 0.0
    timeout_seconds: Optional[int] = 300
    llm_config_name: str = "llm"
    agent_class: str = "CodeActAgent"


@dataclass
class EngineTrace:
    """Structured trace: prompts sent, tool calls, files modified; optional token usage."""

    prompts_sent: List[str] = field(default_factory=list)
    tool_calls: List[dict] = field(default_factory=list)
    files_modified: List[str] = field(default_factory=list)
    raw_events: List[dict] = field(default_factory=list)
    # Execution/capability metadata (useful when the environment is CLI-first).
    execution_mode: str = ""  # e.g. "prime_subprocess" | "library" | "cli_subprocess"
    cli_mode_forced: bool = False
    mode_reason: str = ""
    openhands_library_core_available: bool = False
    # Timeout attribution.
    timeout_origin: Optional[str] = None  # e.g. "subprocess_wall_timeout"
    subprocess_timeout_seconds: Optional[int] = None
    # Phased timeout accounting (best-effort attribution from event timestamps).
    startup_budget_s: Optional[float] = None
    action_budget_s: Optional[float] = None
    finalization_budget_s: Optional[float] = None
    first_action_latency_s: Optional[float] = None
    first_file_edit_latency_s: Optional[float] = None
    # Timeout-specific diagnostics snapshot (for postmortems and regression gating).
    timeout_snapshot: Optional[dict[str, Any]] = None
    # Prime compatibility proxy flags/counters (populated when enabled).
    prime_proxy_enabled: bool = False
    prime_payload_normalizations_applied: int = 0
    # Heuristic: normalization applications that did not result in an upstream 422.
    prime_422_avoided: int = 0
    # Prompt/task delivery report (helps diagnose truncation/fidelity regressions).
    task_delivery_report: Optional[dict[str, Any]] = None
    # Direct-agent patch quality instrumentation.
    patch_sanitize_applied: bool = False
    patch_apply_check_passed: Optional[bool] = None
    patch_repair_attempted: bool = False
    patch_repair_success: bool = False
    patch_failure_type: str = ""

    def token_usage(self) -> tuple[int, int]:
        """Sum prompt_tokens and completion_tokens from raw_events (usage / input_tokens / output_tokens)."""
        prompt_total = 0
        completion_total = 0
        for ev in self.raw_events:
            if not isinstance(ev, dict):
                continue
            usage = ev.get("usage") or ev.get("token_usage")
            if isinstance(usage, dict):
                prompt_total += int(usage.get("prompt_tokens") or usage.get("input_tokens") or 0)
                completion_total += int(usage.get("completion_tokens") or usage.get("output_tokens") or 0)
            prompt_total += int(ev.get("prompt_tokens") or 0)
            completion_total += int(ev.get("completion_tokens") or 0)
        return prompt_total, completion_total

    def to_dict(self) -> dict:
        d = {
            "prompts_sent": self.prompts_sent,
            "tool_calls": self.tool_calls,
            "files_modified": self.files_modified,
            "raw_events": self.raw_events,
            "execution_mode": self.execution_mode,
            "cli_mode_forced": self.cli_mode_forced,
            "mode_reason": self.mode_reason,
            "openhands_library_core_available": self.openhands_library_core_available,
            "timeout_origin": self.timeout_origin,
            "subprocess_timeout_seconds": self.subprocess_timeout_seconds,
            "startup_budget_s": self.startup_budget_s,
            "action_budget_s": self.action_budget_s,
            "finalization_budget_s": self.finalization_budget_s,
            "first_action_latency_s": self.first_action_latency_s,
            "first_file_edit_latency_s": self.first_file_edit_latency_s,
            "timeout_snapshot": self.timeout_snapshot,
            "prime_proxy_enabled": self.prime_proxy_enabled,
            "prime_payload_normalizations_applied": self.prime_payload_normalizations_applied,
            "prime_422_avoided": self.prime_422_avoided,
            "task_delivery_report": self.task_delivery_report,
            "patch_sanitize_applied": self.patch_sanitize_applied,
            "patch_apply_check_passed": self.patch_apply_check_passed,
            "patch_repair_attempted": self.patch_repair_attempted,
            "patch_repair_success": self.patch_repair_success,
            "patch_failure_type": self.patch_failure_type,
        }
        pt, ct = self.token_usage()
        if pt or ct:
            d["prompt_tokens"] = pt
            d["completion_tokens"] = ct
        return d


@dataclass
class SolveResult:
    """Result of running OpenHands on a workspace."""

    patch_diff_str: str
    trace: EngineTrace
    success: bool
    error: Optional[str] = None
    stdout: str = ""
    stderr: str = ""

    def to_dict(self) -> dict:
        return {
            "patch_diff_str_length": len(self.patch_diff_str),
            "success": self.success,
            "error": self.error,
            "trace": self.trace.to_dict(),
        }


def _get_repo_dir(workspace_path: Path) -> Path:
    """Return the repo directory inside the PF workspace (workspace_path/repo)."""
    repo = workspace_path / "repo"
    if not repo.is_dir():
        raise ValueError(f"Workspace repo directory not found: {repo}")
    return repo


def _get_patch_from_repo(repo_dir: Path, timeout: Optional[int] = None) -> str:
    """Run git diff HEAD in repo and return patch string (unstaged + staged)."""
    t = timeout if timeout is not None else GIT_DIFF_TIMEOUT
    try:
        out = subprocess.run(
            ["git", "diff", "HEAD"],
            cwd=repo_dir,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=t,
        )
        return out.stdout or ""
    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        return f"# git diff failed: {e}\n"


def _get_diff_stat_file_count(repo_dir: Path, timeout: int = DIFF_STAT_TIMEOUT) -> int:
    """Run git diff HEAD --stat and return number of files changed (from summary line). Returns 9999 on timeout/parse failure."""
    try:
        out = subprocess.run(
            ["git", "diff", "HEAD", "--stat"],
            cwd=repo_dir,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
        )
        lines = (out.stdout or "").strip().splitlines()
        if not lines:
            return 0
        # Last line is " n files changed, x insertions(+), y deletions(-)" or " n files changed"
        last = lines[-1].strip()
        m = re.search(r"(\d+)\s+files?\s+changed", last, re.IGNORECASE)
        if m:
            return int(m.group(1))
        return len(lines) - 1  # exclude summary if no match
    except (subprocess.TimeoutExpired, FileNotFoundError, ValueError):
        return 9999


def _normalize_paths_to_repo_relative(repo_dir: Path, paths: List[str]) -> List[str]:
    """Convert absolute paths under repo_dir to relative paths; pass through already-relative; drop others."""
    repo_abs = repo_dir.resolve()
    out: List[str] = []
    for p in paths:
        p = (p or "").strip()
        if not p:
            continue
        path_obj = Path(p)
        if path_obj.is_absolute():
            try:
                rel = path_obj.resolve().relative_to(repo_abs)
                out.append(str(rel).replace("\\", "/"))
            except ValueError:
                continue
        elif ".." not in p:
            out.append(p.replace("\\", "/"))
    return list(dict.fromkeys(out))


def _get_patch_from_repo_for_paths(repo_dir: Path, paths: List[str], timeout: int = PATH_DIFF_TIMEOUT) -> str:
    """Run git diff HEAD -- <paths> and return patch string. Paths are relative to repo_dir. Empty paths = full diff not used."""
    if not paths:
        return ""
    # Normalize absolute paths to repo-relative; then sanitize (no "..").
    paths = _normalize_paths_to_repo_relative(repo_dir, paths)
    safe = []
    for p in paths:
        p = (p or "").strip()
        if p and ".." not in p and not Path(p).is_absolute():
            safe.append(p)
    if not safe:
        return ""
    try:
        out = subprocess.run(
            ["git", "diff", "HEAD", "--"] + safe,
            cwd=repo_dir,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
        )
        return out.stdout or ""
    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        return f"# git diff (paths) failed: {e}\n"


def _get_files_modified_from_repo(repo_dir: Path, timeout: Optional[int] = None) -> List[str]:
    """Run git diff --name-only in repo and return list of modified paths."""
    t = timeout if timeout is not None else GIT_DIFF_TIMEOUT
    try:
        out = subprocess.run(
            ["git", "diff", "HEAD", "--name-only"],
            cwd=repo_dir,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=t,
        )
        if out.returncode != 0:
            return []
        return [p.strip() for p in (out.stdout or "").splitlines() if p.strip()]
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return []


def _parse_openhands_cli_stdout_events(stdout: str) -> List[dict]:
    """Parse OpenHands CLI --json stdout: '--JSON Event--' followed by multi-line pretty-printed JSON.
    Returns list of event dicts. CLI does not emit one-JSON-per-line; it uses this delimiter + indented JSON.
    """
    events: List[dict] = []
    if "--JSON Event--" not in stdout:
        return events
    parts = stdout.split("--JSON Event--")
    for i, block in enumerate(parts):
        if i == 0:
            continue
        block = block.strip()
        if not block:
            continue
        # Find first { and then consume until matching }
        start = block.find("{")
        if start < 0:
            continue
        depth = 0
        end = -1
        for j, ch in enumerate(block[start:], start=start):
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    end = j
                    break
        if end < 0:
            continue
        try:
            obj = json.loads(block[start : end + 1])
            if isinstance(obj, dict):
                events.append(obj)
        except json.JSONDecodeError:
            continue
    return events


def _is_file_edit_tool(name: Optional[str]) -> bool:
    """True if tool name indicates a file write/edit (not read-only view/grep)."""
    if not name:
        return False
    n = (name or "").lower()
    return "edit" in n or "write" in n or "file_editor" in n or "fileeditor" in n


def _fill_trace_from_events(trace: EngineTrace) -> None:
    """Populate tool_calls, files_modified, prompts_sent from trace.raw_events.
    Handles both legacy (type/action) and OpenHands SDK (kind=ActionEvent, action=dict) shapes.
    Only adds to files_modified for actions that edit/write files, so path-restricted diff uses actual edited paths.
    """
    for ev in trace.raw_events:
        if not isinstance(ev, dict):
            continue
        kind = ev.get("kind") or ev.get("type")
        if kind == "ActionEvent" or ev.get("type") == "action":
            action_obj = ev.get("action")
            name = ev.get("tool_name") or (action_obj.get("name") if isinstance(action_obj, dict) else None) or ev.get("action") or ev.get("name")
            path_val = (
                ev.get("path")
                or (action_obj.get("path") if isinstance(action_obj, dict) else None)
                or (action_obj.get("filename") if isinstance(action_obj, dict) else None)
                or ev.get("file_path") or ev.get("filename")
            )
            if name:
                trace.tool_calls.append({"name": name, "args": {"path": path_val} if path_val else {}})
            if path_val and _is_file_edit_tool(name):
                trace.files_modified.append(str(path_val))
        else:
            action = ev.get("action") or ev
            if isinstance(action, dict):
                msg = action.get("message") or action.get("content") or action.get("content_str")
                if msg and isinstance(msg, str) and len(msg.strip()) > 0:
                    trace.prompts_sent.append(msg.strip()[:2000])
            llm_msg = ev.get("llm_message")
            if isinstance(llm_msg, dict):
                content = llm_msg.get("content")
                if isinstance(content, list):
                    for c in content:
                        if isinstance(c, dict) and c.get("type") == "text" and c.get("text"):
                            trace.prompts_sent.append(str(c["text"]).strip()[:2000])
            name = ev.get("name") or (action.get("name") or action.get("tool") if isinstance(action, dict) else None)
            if name:
                trace.tool_calls.append({
                    "name": name,
                    "args": (action.get("args") or action.get("arguments") or {}) if isinstance(action, dict) else {},
                })
    for tc in trace.tool_calls:
        if not _is_file_edit_tool(tc.get("name")):
            continue
        args = tc.get("args") or {}
        for key in ("path", "filename", "file_path"):
            if key in args and args[key]:
                trace.files_modified.append(str(args[key]))
    trace.files_modified = list(dict.fromkeys(trace.files_modified))


def _event_kinds_summary(raw_events: List[dict]) -> str:
    """One-line summary of event kinds for diagnostics (e.g. 'ActionEvent: 2, Message: 1')."""
    if not raw_events:
        return "none"
    counts: dict[str, int] = {}
    for ev in raw_events:
        if not isinstance(ev, dict):
            continue
        kind = ev.get("kind") or ev.get("type") or "unknown"
        counts[kind] = counts.get(kind, 0) + 1
    return ", ".join("%s: %d" % (k, v) for k, v in sorted(counts.items()))


def _parse_event_timestamp_s(ev: dict[str, Any]) -> Optional[float]:
    """Best-effort parse timestamp to epoch seconds for latency metrics."""
    for key in ("timestamp", "time", "ts"):
        v = ev.get(key)
        if v is None:
            continue
        if isinstance(v, (int, float)):
            return float(v)
        if isinstance(v, str):
            s = v.strip()
            if not s:
                continue
            # Handle common ISO formats ending with 'Z'.
            if s.endswith("Z"):
                s = s[:-1] + "+00:00"
            try:
                dt = datetime.fromisoformat(s)
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=timezone.utc)
                return dt.timestamp()
            except Exception:
                try:
                    return float(s)
                except Exception:
                    continue
    return None


def _compute_timeout_budget_phases(timeout_seconds: Optional[int]) -> tuple[Optional[float], Optional[float], Optional[float]]:
    """Derive phased budgets to attribute where wall time was spent (best-effort)."""
    if not timeout_seconds or timeout_seconds <= 0:
        return None, None, None
    t = float(timeout_seconds)
    startup = max(10.0, t * 0.25)
    action = max(20.0, t * 0.55)
    finalization = max(5.0, t - startup - action)
    # Normalize rounding errors.
    total = startup + action + finalization
    if total > 0:
        scale = t / total
        startup *= scale
        action *= scale
        finalization *= scale
    return round(startup, 3), round(action, 3), round(finalization, 3)


def _extract_latency_metrics_from_events(raw_events: List[dict[str, Any]]) -> tuple[Optional[float], Optional[float]]:
    """Extract first-action and first-file-edit latencies from event stream timestamps."""
    ts_list: List[float] = []
    action_ts: List[float] = []
    edit_ts: List[float] = []

    def _event_action_name(ev: dict[str, Any]) -> Optional[str]:
        kind = ev.get("kind") or ev.get("type")
        if kind != "ActionEvent" and ev.get("type") != "action":
            return None
        action_obj = ev.get("action")
        name = ev.get("tool_name")
        if not name and isinstance(action_obj, dict):
            name = action_obj.get("name") or action_obj.get("tool")
        if not name:
            # Fallbacks (legacy shapes).
            name = ev.get("action") or ev.get("name")
        return str(name) if name else None

    for ev in raw_events:
        if not isinstance(ev, dict):
            continue
        ts = _parse_event_timestamp_s(ev)
        if ts is not None:
            ts_list.append(ts)
        name = _event_action_name(ev)
        if name is not None and ts is not None:
            action_ts.append(ts)
            if _is_file_edit_tool(name):
                edit_ts.append(ts)

    if not ts_list:
        return None, None
    start_ts = min(ts_list)
    first_action_ts = min(action_ts) if action_ts else None
    first_edit_ts = min(edit_ts) if edit_ts else None
    first_action_latency = (first_action_ts - start_ts) if first_action_ts is not None else None
    first_file_edit_latency = (first_edit_ts - start_ts) if first_edit_ts is not None else None
    return first_action_latency, first_file_edit_latency


def _extract_timeout_snapshot(trace: EngineTrace, last_n: int = 25) -> dict[str, Any]:
    """Best-effort structured timeout diagnostics for postmortems/regression gates."""
    raw_events = trace.raw_events or []
    tail = raw_events[-last_n:] if raw_events else []
    snapshot: dict[str, Any] = {
        "event_kinds_tail": _event_kinds_summary(tail),
        "tail_event_count": len(tail),
    }

    # Last action tool name, when present.
    last_tool_name: Optional[str] = None
    for ev in reversed(tail):
        if not isinstance(ev, dict):
            continue
        kind = ev.get("kind") or ev.get("type")
        if kind != "ActionEvent" and ev.get("type") != "action":
            continue
        action_obj = ev.get("action")
        name = ev.get("tool_name")
        if not name and isinstance(action_obj, dict):
            name = action_obj.get("name") or action_obj.get("tool")
        if not name:
            name = ev.get("action") or ev.get("name")
        if name:
            last_tool_name = str(name)
            break
    snapshot["last_tool_name"] = last_tool_name

    # Last observation/message snippet if present.
    last_obs: Optional[str] = None
    for ev in reversed(tail):
        if not isinstance(ev, dict):
            continue
        for k in ("observation", "message", "content", "content_str"):
            v = ev.get(k)
            if isinstance(v, str) and v.strip():
                last_obs = v.strip()[:300]
                break
        if last_obs:
            break
    snapshot["last_observation"] = last_obs
    return snapshot


def _parse_trajectory_for_trace(trajectory_path: Path) -> EngineTrace:
    """Extract prompts_sent, tool_calls, files_modified from OpenHands trajectory JSON or JSONL."""
    trace = EngineTrace()
    path = trajectory_path
    if not path.exists():
        path = path.parent / (path.name.replace(".json", ".jsonl"))
    if not path.exists():
        return trace
    try:
        raw = path.read_text(encoding="utf-8", errors="replace").strip()
    except OSError:
        return trace
    events: List[dict] = []
    if raw.startswith("["):
        data = json.loads(raw)
        events = data if isinstance(data, list) else data.get("history", data.get("events", []))
    else:
        for line in raw.splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                ev = json.loads(line)
                if isinstance(ev, dict):
                    events.append(ev)
            except json.JSONDecodeError:
                continue
    trace.raw_events = [e for e in events if isinstance(e, dict)]
    _fill_trace_from_events(trace)
    return trace


try:
    from ..provider_env import (
        llm_credentials as _llm_credentials,
        normalize_openhands_provider as _normalize_provider,
        openhands_litellm_model as _openhands_litellm_model,
    )
except ImportError:
    try:
        from bench.swebench.provider_env import (
            llm_credentials as _llm_credentials,
            normalize_openhands_provider as _normalize_provider,
            openhands_litellm_model as _openhands_litellm_model,
        )
    except ImportError:
        from provider_env import (
            llm_credentials as _llm_credentials,
            normalize_openhands_provider as _normalize_provider,
            openhands_litellm_model as _openhands_litellm_model,
        )


_PRIME_PROXY_UPSTREAM_TIMEOUT_S = int(os.environ.get("PF_PRIME_PROXY_UPSTREAM_TIMEOUT_S", "180"))


def _normalize_openai_payload_for_strict_servers(payload: Any) -> Any:
    """
    Some OpenAI-compatible endpoints reject assistant tool-call messages without `content`.
    Normalize that shape to keep OpenHands tool loops compatible.

    Returns:
      (normalized_payload, changed)
    """
    if not isinstance(payload, dict):
        return payload, False
    msgs = payload.get("messages")
    if not isinstance(msgs, list):
        return payload, False
    changed = False
    for msg in msgs:
        if not isinstance(msg, dict):
            continue
        if msg.get("role") != "assistant":
            continue

        has_tool_calls = "tool_calls" in msg
        content = msg.get("content", "__MISSING__")

        # Strict servers may require *assistant* messages that contain tool_calls to also have
        # a `content` field (can be empty string).
        if has_tool_calls and (content == "__MISSING__" or content is None or content == []):
            msg["content"] = ""
            changed = True
    return payload, changed


class _PrimeStrictCompatProxy:
    """Local HTTP proxy that normalizes OpenAI payloads before forwarding to Prime."""

    def __init__(self, upstream_base_url: str, extra_headers: Optional[dict[str, str]] = None) -> None:
        self.upstream_base_url = upstream_base_url.rstrip("/")
        self.extra_headers = extra_headers or {}
        self.normalizations_applied: int = 0
        self.prime_422_count: int = 0
        self._server: Optional[ThreadingHTTPServer] = None
        self._thread: Optional[threading.Thread] = None
        self.base_url: Optional[str] = None

    def start(self) -> str:
        outer = self

        class _Handler(BaseHTTPRequestHandler):
            def log_message(self, fmt: str, *args: Any) -> None:  # noqa: D401
                return

            def _forward(self) -> None:
                path = self.path or "/"
                url = outer.upstream_base_url + path
                length = int(self.headers.get("Content-Length", "0") or "0")
                body = self.rfile.read(length) if length > 0 else b""
                ctype = (self.headers.get("Content-Type") or "").lower()
                if body and "application/json" in ctype:
                    try:
                        data = json.loads(body.decode("utf-8", errors="replace"))
                        data, changed = _normalize_openai_payload_for_strict_servers(data)
                        if changed:
                            outer.normalizations_applied += 1
                        body = json.dumps(data, separators=(",", ":")).encode("utf-8")
                    except (json.JSONDecodeError, OSError, TypeError, ValueError):
                        pass

                fwd_headers: dict[str, str] = {}
                for k in self.headers.keys():
                    lk = k.lower()
                    if lk in ("host", "content-length", "connection"):
                        continue
                    v = self.headers.get(k)
                    if v is not None:
                        fwd_headers[k] = v
                for k, v in outer.extra_headers.items():
                    if v and not fwd_headers.get(k):
                        fwd_headers[k] = v
                # Keep upstream responses uncompressed for simpler local relay semantics.
                if not fwd_headers.get("Accept-Encoding"):
                    fwd_headers["Accept-Encoding"] = "identity"

                req = urllib.request.Request(url=url, data=body, headers=fwd_headers, method=self.command)
                try:
                    with urllib.request.urlopen(req, timeout=_PRIME_PROXY_UPSTREAM_TIMEOUT_S) as resp:
                        status = int(resp.status)
                        resp_body = resp.read()
                        resp_headers = dict(resp.headers.items())
                except urllib.error.HTTPError as e:
                    status = int(e.code)
                    if int(e.code) == 422:
                        outer.prime_422_count += 1
                    resp_body = e.read() if hasattr(e, "read") else b""
                    resp_headers = dict(e.headers.items()) if e.headers else {}

                try:
                    self.send_response(status)
                    ct = resp_headers.get("Content-Type")
                    if ct:
                        self.send_header("Content-Type", ct)
                    ce = resp_headers.get("Content-Encoding")
                    if ce:
                        self.send_header("Content-Encoding", ce)
                    self.send_header("Content-Length", str(len(resp_body)))
                    self.end_headers()
                    if resp_body:
                        self.wfile.write(resp_body)
                except (BrokenPipeError, ConnectionResetError):
                    # Client closed connection (e.g. OpenHands timeout); ignore.
                    pass

            def do_POST(self) -> None:  # noqa: N802
                self._forward()

            def do_GET(self) -> None:  # noqa: N802
                self._forward()

        self._server = ThreadingHTTPServer(("127.0.0.1", 0), _Handler)
        host, port = self._server.server_address
        self.base_url = f"http://{host}:{port}"
        self._thread = threading.Thread(target=self._server.serve_forever, name="prime-compat-proxy", daemon=True)
        self._thread.start()
        return self.base_url

    def close(self) -> None:
        if self._server:
            self._server.shutdown()
            self._server.server_close()
            self._server = None
        if self._thread and self._thread.is_alive():
            self._thread.join(timeout=2)
        self._thread = None


def _write_openhands_config_toml(persistence_dir: Path) -> None:
    """Write a minimal config.toml for headless so CLI finds 'existing settings'."""
    api_key, base_url, _prov = _llm_credentials()
    model_raw = (os.environ.get("OPENHANDS_MODEL") or "gpt-4o-mini").strip()
    model = _openhands_litellm_model(_prov, model_raw)

    def esc(s: str) -> str:
        return s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\r", "\\r")

    persistence_dir.mkdir(parents=True, exist_ok=True)
    config_path = persistence_dir / "config.toml"
    lines = [
        "# Minimal config for headless (engine-generated)",
        "[core]",
        'runtime = "process"',
        "[llm]",
        'api_key = "%s"' % esc(api_key),
        'model = "%s"' % esc(model),
    ]
    if base_url:
        lines.append('base_url = "%s"' % esc(base_url))
    config_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _compact_task_text_for_openhands(
    task_text: str,
    *,
    scratch_dir: Path,
    max_task_chars: int,
) -> tuple[str, dict[str, Any]]:
    """
    Deterministically compact the SWE-bench prompt to fit OpenHands/tooling limits.

    The SWE-bench prompt created by bench/swebench/workspace.py is a concatenation of:
      - instruction header + problem statement (+ optional hints section)
      - fixed Reminder block
      - fixed Efficiency block

    We preserve the fixed Reminder block whenever compaction is applied, and we try to keep
    as much of the instruction+problem+constraints block as possible (head/tail) when needed.
    """
    original = task_text or ""
    original_len = len(original)
    had_constraints_marker = "# Constraints / Hints" in original

    sidecar_path = scratch_dir / "pf_task_full.md"
    try:
        sidecar_path.write_text(original, encoding="utf-8", errors="replace")
    except OSError:
        # If we cannot write the sidecar, fall back to in-place compaction only.
        sidecar_path = scratch_dir / "pf_task_full.md"

    # Markers from bench/swebench/workspace.py.
    reminder_marker = "\n**Reminder:**"
    efficiency_marker = "\n**Efficiency:**"
    had_reminder_marker = reminder_marker in original

    rem_start = original.find(reminder_marker)
    if rem_start < 0:
        # Unknown prompt shape; use minimal deterministic head truncation.
        effective = original[:max_task_chars]
        report = {
            "compaction_applied": original_len > max_task_chars,
            "original_len": original_len,
            "max_task_chars": max_task_chars,
            "strategy": "unknown_prompt_head_truncation",
            "reminder_preserved": False,
            "critical_drop": True,
            "sidecar_path": str(sidecar_path.resolve()),
        }
        return effective, report

    eff_start = original.find(efficiency_marker, rem_start + len(reminder_marker))
    instruction_and_problem = original[:rem_start].rstrip()
    reminder_block = original[rem_start : eff_start if eff_start >= 0 else len(original)].rstrip()
    efficiency_block = original[eff_start:].rstrip() if eff_start >= 0 else ""

    # If it already fits, do not add extra wrapper text (avoid changing prompt semantics).
    if original_len <= max_task_chars:
        report = {
            "compaction_applied": False,
            "original_len": original_len,
            "max_task_chars": max_task_chars,
            "strategy": "no_compaction",
            "reminder_preserved": True,
            "sidecar_path": str(sidecar_path.resolve()),
            "kept_blocks": ["instruction_and_problem", "reminder", "efficiency"],
            "critical_drop": False if (not had_constraints_marker) else ("# Constraints / Hints" not in original),
        }
        return original, report

    compaction_overhead = "\n\n[pf-swebench note] Task compacted to fit OpenHands limits. Reminder kept; if needed, open the full task sidecar with file_editor.\n"
    sidecar_ref = (
        "\n\n[pf-swebench sidecar] Full task saved at:\n"
        f"{str(sidecar_path.resolve())}\n"
    )

    fixed_tail = "\n".join([reminder_block, compaction_overhead.strip(), sidecar_ref.strip()]).strip()

    # Budget for instruction/problem portion.
    allowed_for_instruction = max_task_chars - len(fixed_tail)
    if allowed_for_instruction < 0:
        # Even fixed_tail alone doesn't fit; hard truncate fixed_tail deterministically.
        effective = fixed_tail[:max_task_chars]
        report = {
            "compaction_applied": True,
            "original_len": original_len,
            "max_task_chars": max_task_chars,
            "strategy": "fixed_tail_hard_truncation",
            "reminder_preserved": True,
            "sidecar_path": str(sidecar_path.resolve()),
            "critical_drop": (
                (had_constraints_marker and "# Constraints / Hints" not in effective)
                or (had_reminder_marker and "**Reminder:**" not in effective)
            ),
        }
        return effective, report

    if len(instruction_and_problem) <= allowed_for_instruction:
        effective_instruction = instruction_and_problem
        kept_blocks = ["instruction_and_problem", "reminder", "sidecar_ref", "compaction_overhead"]
    else:
        # Keep head and tail to preserve both issue framing and key constraints near the end.
        head_len = int(allowed_for_instruction * 0.7)
        tail_len = allowed_for_instruction - head_len
        head = instruction_and_problem[:head_len].rstrip()
        tail = instruction_and_problem[-tail_len:].lstrip()
        joiner = "\n\n[pf-swebench note] Dropped middle portion of instruction/problem to fit prompt budget.\n"
        effective_instruction = (head + joiner + tail).strip()
        # Ensure hard bound.
        if len(effective_instruction) > allowed_for_instruction:
            effective_instruction = effective_instruction[:allowed_for_instruction].rstrip()
        kept_blocks = ["instruction_and_problem_head_tail", "reminder", "sidecar_ref", "compaction_overhead"]

    effective = (effective_instruction + "\n\n" + fixed_tail).strip()
    if len(effective) > max_task_chars:
        effective = effective[:max_task_chars].rstrip()

    critical_drop = (
        (had_constraints_marker and "# Constraints / Hints" not in effective)
        or (had_reminder_marker and reminder_marker not in effective)
    )
    report = {
        "compaction_applied": True,
        "original_len": original_len,
        "max_task_chars": max_task_chars,
        "strategy": "preserve_reminder_head_tail_instruction_problem",
        "reminder_preserved": True,
        "sidecar_path": str(sidecar_path.resolve()),
        "kept_blocks": kept_blocks,
        "instruction_and_problem_len": len(instruction_and_problem),
        "reminder_len": len(reminder_block),
        "efficiency_kept": bool(efficiency_block) and len(instruction_and_problem) + len(reminder_block) + len(efficiency_block) <= max_task_chars,
        "critical_drop": critical_drop,
    }
    return effective, report


def _run_openhands_subprocess(
    repo_dir: Path,
    task_text: str,
    config: OpenHandsConfig,
    scratch_dir: Path,
    extra_env: Optional[dict] = None,
) -> tuple[str, EngineTrace, bool, Optional[str], str, str]:
    """
    Run OpenHands via CLI (subprocess). Returns (patch_str, trace, success, error, stdout, stderr).
    Uses RUNTIME=process so the agent runs in repo_dir. extra_env is merged in (e.g. for PF guard SHELL).
    """
    trajectory_path = scratch_dir / "openhands_trajectory.json"
    trajectory_jsonl_path = scratch_dir / "openhands_trajectory.jsonl"
    stdout_debug_path = scratch_dir / "openhands_stdout.txt"
    stderr_debug_path = scratch_dir / "openhands_stderr.txt"
    for stale in (stdout_debug_path, stderr_debug_path):
        try:
            if stale.exists():
                stale.unlink()
        except OSError:
            pass
    # Keep subprocess environment intentionally small: newer OpenHands CLI uses tmux internally
    # and very large inherited environments can trigger "tmux set-environment ... command too long".
    passthrough_keys = (
        "PATH",
        "HOME",
        "USER",
        "LOGNAME",
        "SHELL",
        "LANG",
        "LC_ALL",
        "TERM",
        "TMPDIR",
        "TMP",
        "TEMP",
        "SYSTEMROOT",
        "WINDIR",
        "WSL_DISTRO_NAME",
        "WSL_INTEROP",
        "WSLENV",
    )
    env = {k: os.environ[k] for k in passthrough_keys if os.environ.get(k) is not None}
    env["RUNTIME"] = "process"
    # Prepend this interpreter's bin (venv) to PATH so "openhands" CLI is found when run via venv Python
    _bin = str(Path(sys.executable).resolve().parent)
    env["PATH"] = _bin + os.pathsep + env.get("PATH", "")
    # Force OpenHands terminal backend to subprocess by shadowing `tmux -V` probe.
    # The current OpenHands CLI stack can fail in tmux with "set-environment ... command too long".
    # A shim that returns non-zero makes auto-detection choose subprocess terminal.
    try:
        no_tmux_dir = Path("/tmp") / ("pf_no_tmux_%d" % os.getpid())
        no_tmux_dir.mkdir(parents=True, exist_ok=True)
        shim = no_tmux_dir / "tmux"
        shim.write_text("#!/bin/sh\nexit 127\n", encoding="utf-8")
        shim.chmod(0o755)
        env["PATH"] = str(no_tmux_dir.resolve()) + os.pathsep + env["PATH"]
    except OSError:
        pass

    def _sanitize_key(val: str) -> str:
        """Strip CR/LF, whitespace, and optional surrounding quotes so .env keys work in subprocess."""
        if not val:
            return ""
        s = val.replace("\r", "").replace("\n", "").strip()
        if len(s) >= 2 and s[0] == s[-1] and s[0] in ("'", '"'):
            s = s[1:-1]
        return s.strip()

    # Ensure API keys reach the subprocess; sanitize so .env quirks (CRLF, quotes) do not break auth
    for _k in (
        "OPENAI_API_KEY",
        "ANTHROPIC_API_KEY",
        "PRIME_INTELLECT_API_KEY",
        "OPENAI_BASE_URL",
        "ANTHROPIC_BASE_URL",
        "PRIME_INTELLECT_BASE_URL",
        # So the OpenHands CLI / LiteLLM stack agrees with PF routing (do not rely on inherited env alone).
        "OPENHANDS_PROVIDER",
        "OPENHANDS_MODEL",
        "PRIME_TEAM_ID",
    ):
        _v = os.environ.get(_k)
        if _v is not None:
            env[_k] = _sanitize_key(_v)
    if extra_env:
        env.update(extra_env)
    # Explicitly disable OpenHands Cloud key path for local SWE-bench runs.
    env.pop("OPENHANDS_API_KEY", None)

    # OpenHands headless: --override-with-envs + LLM_API_KEY + LLM_MODEL (+ LLM_BASE_URL for custom endpoints).
    ak, bu, prov = _llm_credentials()
    api_key = _sanitize_key(ak)
    if api_key:
        env["LLM_API_KEY"] = api_key
    model_raw = (os.environ.get("OPENHANDS_MODEL") or config.model_name or "gpt-4o-mini").strip()
    model = _openhands_litellm_model(prov, model_raw)
    env["LLM_MODEL"] = model
    if model != model_raw:
        _log_engine("subprocess: normalized model for %s: %s -> %s" % (prov, model_raw, model))
    compat_proxy: Optional[_PrimeStrictCompatProxy] = None
    prime_proxy_enabled = False
    if bu:
        base_url = bu.strip()
        if prov == "prime_intellect":
            team_id = (os.environ.get("PRIME_TEAM_ID") or "").strip()
            extra = {"X-Prime-Team-ID": team_id} if team_id else {}
            compat_proxy = _PrimeStrictCompatProxy(base_url, extra_headers=extra)
            env["LLM_BASE_URL"] = compat_proxy.start()
            _log_engine("subprocess: enabled Prime strict-compat proxy at %s -> upstream %s" % (env["LLM_BASE_URL"], base_url))
            prime_proxy_enabled = True
        else:
            env["LLM_BASE_URL"] = base_url
    # Normalized provider for downstream stacks that read OPENHANDS_PROVIDER.
    env["OPENHANDS_PROVIDER"] = prov
    env["OPENHANDS_PROVIDER_EFFECTIVE"] = prov

    def _cleanup_proxy() -> None:
        if compat_proxy is not None:
            try:
                compat_proxy.close()
            except Exception:
                pass

    if not env.get("LLM_API_KEY"):
        _log_engine(
            "subprocess: WARNING LLM_API_KEY not set (OPENHANDS_PROVIDER=%s; set the matching API key env)"
            % _normalize_provider()
        )

    # Optional: persistence dir with config.toml as fallback; primary path is --override-with-envs + LLM_*.
    # Newer OpenHands CLI reads OPENHANDS_PERSISTENCE_DIR (not OH_PERSISTENCE_DIR).
    oh_persistence = scratch_dir / "openhands_persistence"
    _write_openhands_config_toml(oh_persistence)
    env["OH_PERSISTENCE_DIR"] = str(oh_persistence.resolve())
    env["OPENHANDS_PERSISTENCE_DIR"] = str(oh_persistence.resolve())
    env["OPENHANDS_CONVERSATIONS_DIR"] = str((oh_persistence / "conversations").resolve())

    # Force the CLI to use repo_dir as the agent workspace (get_work_dir() reads OPENHANDS_WORK_DIR or cwd)
    env["OPENHANDS_WORK_DIR"] = str(repo_dir.resolve())

    # Pass task via --file.
    # Older/newer OpenHands CLI stacks can still fail in tmux with "set-environment ... command too long"
    # depending on how the toolchain serializes payloads. We therefore apply deterministic compaction.
    # Default matches direct_agent (12000); set PF_OPENHANDS_MAX_TASK_CHARS lower only if you hit env limits.
    max_task_chars = max(400, int(os.environ.get("PF_OPENHANDS_MAX_TASK_CHARS", "12000") or "12000"))
    task_text_effective, task_delivery_report = _compact_task_text_for_openhands(
        task_text,
        scratch_dir=scratch_dir,
        max_task_chars=max_task_chars,
    )
    # Persist delivery report for postmortem reproducibility.
    try:
        (scratch_dir / "pf_task_delivery_report.json").write_text(
            json.dumps(task_delivery_report, indent=2),
            encoding="utf-8",
            errors="replace",
        )
    except OSError:
        pass
    _log_engine(
        "subprocess: task delivery compaction=%s original_chars=%d effective_chars=%d strategy=%s"
        % (
            task_delivery_report.get("compaction_applied"),
            task_delivery_report.get("original_len", len(task_text)),
            len(task_text_effective),
            task_delivery_report.get("strategy", ""),
        )
    )

    task_file = scratch_dir / "openhands_task.txt"
    try:
        task_file.write_text(task_text_effective, encoding="utf-8", errors="replace")
    except OSError as e:
        _log_engine("subprocess: failed to write task file: %s" % (str(e)[:80],))
        _cleanup_proxy()
        return "", EngineTrace(), False, "Failed to write task file", "", ""

    # --override-with-envs: use LLM_API_KEY/LLM_MODEL so headless runs without "existing settings" or GUI.
    cmd = [
        "openhands",
        "--headless",
        "--override-with-envs",
        "--json",
        "--file", str(task_file.resolve()),
    ]
    timeout_s = config.timeout_seconds or 3600
    _log_engine("subprocess: openhands --headless --file <task> (timeout=%ds cwd=%s)" % (timeout_s, repo_dir.name))
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            cmd,
            cwd=repo_dir,
            env=env,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=config.timeout_seconds or 3600,
        )
        stdout, stderr = proc.stdout or "", proc.stderr or ""
        if stdout.strip():
            try:
                trajectory_jsonl_path.write_text(stdout, encoding="utf-8", errors="replace")
            except OSError:
                pass
    except FileNotFoundError:
        _log_engine("subprocess: OpenHands CLI not found")
        _cleanup_proxy()
        return "", EngineTrace(), False, "OpenHands CLI not found (install openhands package)", "", ""
    except subprocess.TimeoutExpired as e:
        _log_engine("subprocess: timed out after %.1fs" % (time.perf_counter() - t0))
        timeout_stdout = ""
        timeout_stderr = ""
        if getattr(e, "stdout", None):
            try:
                timeout_stdout = (
                    e.stdout.decode("utf-8", errors="replace")
                    if isinstance(e.stdout, (bytes, bytearray))
                    else str(e.stdout)
                )
            except Exception:
                timeout_stdout = str(e.stdout)
        if getattr(e, "stderr", None):
            try:
                timeout_stderr = (
                    e.stderr.decode("utf-8", errors="replace")
                    if isinstance(e.stderr, (bytes, bytearray))
                    else str(e.stderr)
                )
            except Exception:
                timeout_stderr = str(e.stderr)
        if timeout_stdout.strip():
            try:
                trajectory_jsonl_path.write_text(timeout_stdout, encoding="utf-8", errors="replace")
            except OSError:
                pass
        t_parse = time.perf_counter()
        trace = _parse_trajectory_for_trace(trajectory_path)
        trace.timeout_origin = "subprocess_wall_timeout"
        trace.subprocess_timeout_seconds = int(config.timeout_seconds or 0)
        trace.prime_proxy_enabled = prime_proxy_enabled
        if compat_proxy is not None:
            trace.prime_payload_normalizations_applied = compat_proxy.normalizations_applied
            trace.prime_422_avoided = max(
                0, compat_proxy.normalizations_applied - compat_proxy.prime_422_count
            )
        trace.task_delivery_report = task_delivery_report
        if not trace.raw_events and timeout_stdout.strip() and "--JSON Event--" in timeout_stdout:
            cli_events = _parse_openhands_cli_stdout_events(timeout_stdout)
            if cli_events:
                trace.raw_events = cli_events
                _fill_trace_from_events(trace)
                _log_engine("trajectory(timeout): parsed %d events from CLI --json" % len(trace.raw_events))
        _log_engine("trajectory(timeout): parse/fill in %.2fs" % (time.perf_counter() - t_parse))
        trace.prompts_sent.insert(0, task_text[:2000])
        trace.files_modified = trace.files_modified or _get_files_modified_from_repo(repo_dir, timeout=NAME_ONLY_QUICK_TIMEOUT)
        paths = trace.files_modified or []
        t_diff_timeout = time.perf_counter()
        if paths:
            patch_str = _get_patch_from_repo_for_paths(repo_dir, paths[:DIFF_STAT_FILE_THRESHOLD])
            _log_engine("git diff: path-restricted after timeout patch_len=%d" % len(patch_str))
        else:
            patch_str = _get_patch_from_repo(repo_dir)
        _log_engine("git diff(timeout path): done in %.2fs" % (time.perf_counter() - t_diff_timeout))
        try:
            stdout_debug_path.write_text((timeout_stdout[:50000] if timeout_stdout else "[no stdout captured]\n"), encoding="utf-8", errors="replace")
        except OSError:
            pass
        try:
            stderr_debug_path.write_text((timeout_stderr[:50000] if timeout_stderr else "[no stderr captured]\n"), encoding="utf-8", errors="replace")
        except OSError:
            pass
        _cleanup_proxy()
        return patch_str, trace, False, str(e), "", ""
    except Exception as e:
        _log_engine("subprocess: exception %s" % (str(e)[:100],))
        _cleanup_proxy()
        return "", EngineTrace(), False, str(e), "", ""

    elapsed = time.perf_counter() - t0
    _log_engine("subprocess: finished in %.1fs returncode=%d" % (elapsed, proc.returncode))
    t_parse = time.perf_counter()
    trace = _parse_trajectory_for_trace(trajectory_path)
    trace.prime_proxy_enabled = prime_proxy_enabled
    if compat_proxy is not None:
        trace.prime_payload_normalizations_applied = compat_proxy.normalizations_applied
        trace.prime_422_avoided = max(
            0, compat_proxy.normalizations_applied - compat_proxy.prime_422_count
        )
    trace.task_delivery_report = task_delivery_report
    # If no events yet, try OpenHands CLI --json format: '--JSON Event--' + multi-line JSON (not one-per-line)
    if not trace.raw_events and stdout.strip() and "--JSON Event--" in stdout:
        cli_events = _parse_openhands_cli_stdout_events(stdout)
        if cli_events:
            trace.raw_events = cli_events
            _fill_trace_from_events(trace)
            _log_engine("trajectory: parsed %d events from CLI --json (--JSON Event-- format)" % len(trace.raw_events))
    if not trace.raw_events and stdout.strip():
        # Fallback: strict one-JSON-per-line
        try:
            for line in stdout.strip().splitlines():
                line = line.strip()
                if not line:
                    continue
                try:
                    ev = json.loads(line)
                    if isinstance(ev, dict):
                        trace.raw_events.append(ev)
                except json.JSONDecodeError:
                    continue
            if trace.raw_events:
                _fill_trace_from_events(trace)
        except Exception:
            pass
    if not trace.raw_events:
        for candidate in (
            repo_dir / "trajectory.json",
            repo_dir / "openhands_trajectory.json",
            repo_dir / ".openhands" / "trajectory.json",
        ):
            if candidate.exists():
                trace = _parse_trajectory_for_trace(candidate)
                if trace.raw_events:
                    _log_engine("trajectory: read %d events from %s" % (len(trace.raw_events), candidate.name))
                    break
    _log_engine("trajectory: parse/fill in %.2fs" % (time.perf_counter() - t_parse))
    _log_engine("trajectory: %d events" % (len(trace.raw_events) if trace.raw_events else 0))
    if not trace.raw_events:
        _log_engine("trajectory: subprocess stdout_len=%d stderr_len=%d" % (len(stdout), len(stderr)))
        if "requires existing settings" in stdout or "requires existing settings" in stderr:
            _log_engine("trajectory: CLI still reports 'requires existing settings'. Ensure OPENAI_API_KEY and OPENHANDS_MODEL (or LLM_MODEL) are set; engine passes --override-with-envs.")
        else:
            _log_engine("trajectory: 0 events (set OPENAI_API_KEY and OPENHANDS_MODEL; or install openhands with openhands.core for library path)")
        # Save stdout/stderr for debugging
        try:
            stdout_debug_path.write_text(stdout[:50000], encoding="utf-8", errors="replace")
            stderr_debug_path.write_text(stderr[:50000], encoding="utf-8", errors="replace")
        except OSError:
            pass
    trace.prompts_sent.insert(0, task_text[:2000])
    if not trace.files_modified:
        trace.files_modified = _get_files_modified_from_repo(repo_dir, timeout=NAME_ONLY_QUICK_TIMEOUT)
    paths = trace.files_modified or []
    # Normalize absolute paths from trajectory (e.g. OpenHands file_editor) to repo-relative for git diff
    if paths:
        paths = _normalize_paths_to_repo_relative(repo_dir, paths)
        trace.files_modified = paths

    t_diff = time.perf_counter()
    # Fast path: trajectory had no file edits; quick name-only check to avoid 7–10s full diff
    if not paths and trace.raw_events:
        quick_names = _get_files_modified_from_repo(repo_dir, timeout=NO_EDIT_FAST_CHECK_TIMEOUT)
        if not quick_names:
            patch_str = ""
            kinds = _event_kinds_summary(trace.raw_events)
            _log_engine(
                "git diff: skipped (no modified files in repo, %.2fs); event kinds: %s"
                % (time.perf_counter() - t_diff, kinds)
            )
            has_action = any(
                (ev.get("kind") or ev.get("type") or "").lower().find("action") >= 0
                for ev in trace.raw_events
                if isinstance(ev, dict)
            )
            if not has_action:
                # ConversationErrorEvent uses code + detail (OpenHands SDK), not message/error
                for ev in trace.raw_events:
                    if isinstance(ev, dict) and (ev.get("kind") or ev.get("type") or "").find("ConversationError") >= 0:
                        code = ev.get("code") or ev.get("message") or ev.get("error") or ""
                        detail = ev.get("detail") or ev.get("content") or ""
                        if isinstance(detail, dict):
                            detail = detail.get("text", detail.get("message", detail.get("detail", "")))
                        _log_engine(
                            "ConversationErrorEvent: code=%s detail=%s"
                            % (
                                (str(code)[:80] if code else "(none)"),
                                (str(detail).strip()[:400] if detail else "(none)"),
                            )
                        )
                        if (code or "").find("Authentication") >= 0 or (str(detail) or "").find("API key") >= 0:
                            _prov = _normalize_provider()
                            det_s = str(detail)
                            _prime_k = _sanitize_key(os.environ.get("PRIME_INTELLECT_API_KEY") or "")
                            pit_like = _prime_k.startswith("pit_") or "pit_" in det_s
                            openai_upstream = (
                                "platform.openai.com" in det_s
                                or "OpenAIException" in det_s
                                or "api.openai.com" in det_s
                            )
                            if _prov == "prime_intellect" or pit_like or (openai_upstream and _prime_k.startswith("pit_")):
                                _log_engine(
                                    "Fix (prime_intellect / pit_* key): Ensure PRIME_INTELLECT_API_KEY is valid and inference "
                                    "is enabled. Use OPENHANDS_PROVIDER=prime_intellect. Base URL must be Prime Inference "
                                    "(default %s) or PRIME_INTELLECT_BASE_URL; if the error mentions OpenAI "
                                    "(platform.openai.com), LLM_BASE_URL inside OpenHands was wrong or unset—check "
                                    "runs/<run_id>/env.json llm_base_url_effective and subprocess logs for Prime compat proxy."
                                    % DEFAULT_PRIME_INTELLECT_INFERENCE_BASE_URL
                                )
                            else:
                                _log_engine(
                                    "Fix: Use a valid OpenAI API key in .env (OPENAI_API_KEY=sk-...). "
                                    "Create or rotate keys at https://platform.openai.com/account/api-keys"
                                )
                        break
                # Log first assistant message snippet to diagnose "suggest issue" vs real errors
                for ev in trace.raw_events:
                    if not isinstance(ev, dict):
                        continue
                    if (ev.get("source") or ev.get("role")) == "agent" or (ev.get("llm_message") or {}).get("role") == "assistant":
                        content = ev.get("llm_message") or ev
                        if isinstance(content, dict):
                            for c in (content.get("content") or []):
                                if isinstance(c, dict) and c.get("type") == "text" and c.get("text"):
                                    txt = (c.get("text") or "")[:250].replace("\n", " ")
                                    if txt.strip():
                                        _log_engine("assistant reply snippet: %s" % (txt.strip(),))
                                        break
                        break
                _hp = _normalize_provider()
                if _hp == "prime_intellect":
                    _log_engine(
                        "hint: only MessageEvent (no ActionEvent). For prime_intellect set PRIME_INTELLECT_API_KEY; "
                        "see experiments/exp-step2-lite-smoke/openhands-headless-troubleshooting.md (version, model, minimal headless test)."
                    )
                else:
                    _log_engine(
                        "hint: only MessageEvent (no ActionEvent). If OPENAI_API_KEY is set, see "
                        "experiments/exp-step2-lite-smoke/openhands-headless-troubleshooting.md (version, model, minimal headless test); "
                        "otherwise set OPENAI_API_KEY in the shell that started the runner."
                    )
            trace.raw_events.append({"source": "subprocess", "stdout_len": len(stdout), "stderr_len": len(stderr)})
            return patch_str, trace, proc.returncode == 0, None if proc.returncode == 0 else (stderr.strip() or "exit %d" % proc.returncode), stdout, stderr
        paths = quick_names
        trace.files_modified = paths
    file_count = _get_diff_stat_file_count(repo_dir)
    if file_count > DIFF_STAT_FILE_THRESHOLD and paths:
        patch_str = _get_patch_from_repo_for_paths(repo_dir, paths[:DIFF_STAT_FILE_THRESHOLD])
        _log_engine("git diff: skipped full (%d files), path-restricted %.2fs patch_len=%d" % (file_count, time.perf_counter() - t_diff, len(patch_str)))
        if len(patch_str) > MAX_PATCH_BYTES and len(paths) > PATH_RESTRICTED_MAX_PATHS_FALLBACK:
            patch_str = _get_patch_from_repo_for_paths(repo_dir, paths[:PATH_RESTRICTED_MAX_PATHS_FALLBACK])
            if patch_str and not patch_str.strip().startswith("# git diff") and len(patch_str) <= MAX_PATCH_BYTES:
                _log_engine("git diff: path-restricted with %d paths patch_len=%d" % (PATH_RESTRICTED_MAX_PATHS_FALLBACK, len(patch_str)))
    else:
        patch_str = _get_patch_from_repo(repo_dir)
        _log_engine("git diff: %.2fs patch_len=%d" % (time.perf_counter() - t_diff, len(patch_str)))
        if len(patch_str) == 0 and trace.raw_events:
            kinds = _event_kinds_summary(trace.raw_events)
            _log_engine("empty patch with events: kinds=%s paths_from_trajectory=%d" % (kinds, len(paths)))
            if paths:
                path_preview = ", ".join(paths[:3]) + (" ..." if len(paths) > 3 else "")
                _log_engine("trajectory paths (edit tools only): %s" % path_preview)
                try:
                    st = subprocess.run(
                        ["git", "status", "--short"],
                        cwd=repo_dir,
                        capture_output=True,
                        text=True,
                        encoding="utf-8",
                        errors="replace",
                        timeout=30,
                    )
                    status_out = (st.stdout or "").strip() or "(clean)"
                    _log_engine("git status --short: %s" % (status_out[:200] if len(status_out) > 200 else status_out))
                except subprocess.TimeoutExpired:
                    _log_engine("git status timed out (repo large or slow fs); working tree may have changes")
                except Exception as e:
                    _log_engine("git status failed: %s" % (str(e)[:80],))
        if (len(patch_str) > MAX_PATCH_BYTES or patch_str.strip().startswith("# git diff failed")) and paths:
            restricted = _get_patch_from_repo_for_paths(repo_dir, paths[:DIFF_STAT_FILE_THRESHOLD])
            if restricted and not restricted.strip().startswith("# git diff"):
                if len(restricted) <= MAX_PATCH_BYTES:
                    patch_str = restricted
                    _log_engine("git diff: using path-restricted fallback patch_len=%d" % len(patch_str))
                elif len(paths) > PATH_RESTRICTED_MAX_PATHS_FALLBACK:
                    restricted = _get_patch_from_repo_for_paths(repo_dir, paths[:PATH_RESTRICTED_MAX_PATHS_FALLBACK])
                    if restricted and not restricted.strip().startswith("# git diff") and len(restricted) <= MAX_PATCH_BYTES:
                        patch_str = restricted
                        _log_engine("git diff: using path-restricted fallback (%d paths) patch_len=%d" % (PATH_RESTRICTED_MAX_PATHS_FALLBACK, len(patch_str)))
    trace.raw_events.append({"source": "subprocess", "stdout_len": len(stdout), "stderr_len": len(stderr)})
    # Non-zero CLI exit can still leave a valid working tree; do not drop a good patch.
    patch_ok = bool((patch_str or "").strip()) and not (
        patch_str or ""
    ).strip().startswith("# git diff failed")
    success = proc.returncode == 0 or patch_ok
    err = None if success else (stderr.strip() or f"exit code {proc.returncode}")
    if patch_ok and proc.returncode != 0:
        _log_engine(
            "subprocess: treating as success (non-zero exit %d but non-empty patch)"
            % proc.returncode
        )
    _cleanup_proxy()
    return patch_str, trace, success, err, stdout, stderr


def _run_openhands_library(
    repo_dir: Path,
    task_text: str,
    config: OpenHandsConfig,
    scratch_dir: Path,
) -> tuple[str, EngineTrace, bool, Optional[str], str, str]:
    """
    Run OpenHands as a library (create_runtime, run_controller). Returns same tuple as subprocess.
    """
    try:
        from openhands.controller.state.state import State
        from openhands.core.config import AppConfig, parse_arguments
        from openhands.core.main import run_controller
        from openhands.core.setup import create_runtime
        from openhands.events.action import MessageAction
        from openhands.utils.async_utils import call_async_from_sync
    except ImportError as e:
        return "", EngineTrace(), False, f"OpenHands library not available: {e}", "", ""

    trajectory_path = scratch_dir / "openhands_trajectory.json"
    try:
        from openhands.core.config import OpenHandsConfig as OHConfig
        from openhands.core.config.sandbox_config import SandboxConfig
    except ImportError:
        return "", EngineTrace(), False, "OpenHands config types not available", "", ""

    # Build minimal config for process runtime and our repo as workspace
    try:
        app_config = AppConfig(
            default_agent=config.agent_class,
            max_iterations=config.max_iterations,
            llm_config=config.llm_config_name,
        )
        app_config.runtime = "process"
        app_config.sandbox = SandboxConfig()
        app_config.sandbox.workspace_dir = str(repo_dir)
        app_config.save_trajectory_path = str(trajectory_path)
    except Exception as e:
        return "", EngineTrace(), False, f"OpenHands config build failed: {e}", "", ""

    try:
        runtime = create_runtime(app_config, agent=None)
        call_async_from_sync(runtime.connect)
        action = MessageAction(content=task_text)
        state = call_async_from_sync(
            run_controller,
            config=app_config,
            initial_user_action=action,
            runtime=runtime,
            fake_user_response_fn=lambda s: "Please continue. If done, finish the task.",
        )
        runtime.close()
    except Exception as e:
        trace = _parse_trajectory_for_trace(trajectory_path)
        trace.files_modified = trace.files_modified or _get_files_modified_from_repo(repo_dir, timeout=NAME_ONLY_QUICK_TIMEOUT)
        paths = trace.files_modified or []
        if paths:
            patch_str = _get_patch_from_repo_for_paths(repo_dir, paths[:DIFF_STAT_FILE_THRESHOLD])
        else:
            patch_str = _get_patch_from_repo(repo_dir)
        return patch_str, trace, False, str(e), "", ""

    trace = _parse_trajectory_for_trace(trajectory_path)
    if state and hasattr(state, "history"):
        for ev in (state.history or []):
            if hasattr(ev, "content") and ev.content:
                trace.prompts_sent.append(str(ev.content)[:2000])
    if not trace.files_modified:
        trace.files_modified = _get_files_modified_from_repo(repo_dir, timeout=NAME_ONLY_QUICK_TIMEOUT)
    paths = trace.files_modified or []
    file_count = _get_diff_stat_file_count(repo_dir)
    if file_count > DIFF_STAT_FILE_THRESHOLD and paths:
        patch_str = _get_patch_from_repo_for_paths(repo_dir, paths[:DIFF_STAT_FILE_THRESHOLD])
        if len(patch_str) > MAX_PATCH_BYTES and len(paths) > PATH_RESTRICTED_MAX_PATHS_FALLBACK:
            patch_str = _get_patch_from_repo_for_paths(repo_dir, paths[:PATH_RESTRICTED_MAX_PATHS_FALLBACK])
    else:
        patch_str = _get_patch_from_repo(repo_dir)
        if (len(patch_str) > MAX_PATCH_BYTES or patch_str.strip().startswith("# git diff failed")) and paths:
            restricted = _get_patch_from_repo_for_paths(repo_dir, paths[:DIFF_STAT_FILE_THRESHOLD])
            if restricted and not restricted.strip().startswith("# git diff"):
                if len(restricted) <= MAX_PATCH_BYTES:
                    patch_str = restricted
                elif len(paths) > PATH_RESTRICTED_MAX_PATHS_FALLBACK:
                    restricted = _get_patch_from_repo_for_paths(repo_dir, paths[:PATH_RESTRICTED_MAX_PATHS_FALLBACK])
                    if restricted and not restricted.strip().startswith("# git diff") and len(restricted) <= MAX_PATCH_BYTES:
                        patch_str = restricted
    return patch_str, trace, True, None, "", ""


def solve(
    workspace_path: str | Path,
    task_text: str,
    config: Optional[OpenHandsConfig] = None,
    extra_env: Optional[dict] = None,
) -> SolveResult:
    """
    Solve a task in the given PF workspace using OpenHands. Returns patch diff and structured trace.

    workspace_path: PF workspace root (contains repo/, task_prompt.md, scratch/).
    task_text: Task description (e.g. issue + constraints).
    config: OpenHands config; defaults to OpenHandsConfig().

    Returns SolveResult with patch_diff_str (git diff from repo), trace (prompts, tool calls,
    files modified), and success/error.
    """
    workspace_path = Path(workspace_path)
    config = config or OpenHandsConfig()
    repo_dir = _get_repo_dir(workspace_path)
    scratch_dir = workspace_path / "scratch"
    scratch_dir.mkdir(parents=True, exist_ok=True)

    # Capability probe: openhands.core is optional in the installed distribution.
    openhands_core_available = False
    try:
        # Only used as a capability probe (no execution).
        from openhands.core.main import run_controller as _  # noqa: F401

        openhands_core_available = True
    except Exception:
        openhands_core_available = False

    # Prime needs subprocess path: local compat proxy + LLM_* env are only wired there.
    if _normalize_provider() == "prime_intellect":
        _log_engine("provider=prime_intellect: using subprocess path (LLM proxy/env wiring)")
        patch_str, trace, success, err, stdout, stderr = _run_openhands_subprocess(
            repo_dir, task_text, config, scratch_dir, extra_env=extra_env
        )
        trace.execution_mode = "prime_subprocess"
        trace.cli_mode_forced = True
        trace.mode_reason = "prime_intellect: strict-compat proxy + subprocess env wiring"
        trace.openhands_library_core_available = openhands_core_available
    else:
        # Prefer library path if available (extra_env not applied in library path).
        # On UnicodeDecodeError (e.g. OpenHands output with non-UTF-8), fall back to subprocess.
        try:
            from openhands.core.main import run_controller  # noqa: F401
        except ImportError as e:
            _log_engine("library path unavailable (%s); using subprocess (openhands CLI)" % (str(e)[:60],))
            patch_str, trace, success, err, stdout, stderr = _run_openhands_subprocess(
                repo_dir, task_text, config, scratch_dir, extra_env=extra_env
            )
            trace.execution_mode = "cli_subprocess"
            trace.cli_mode_forced = True
            trace.mode_reason = "openhands.core missing: forced CLI/subprocess"
            trace.openhands_library_core_available = openhands_core_available
        else:
            try:
                _log_engine("using library path")
                t0 = time.perf_counter()
                patch_str, trace, success, err, stdout, stderr = _run_openhands_library(
                    repo_dir, task_text, config, scratch_dir
                )
                _log_engine("library path done in %.1fs success=%s" % (time.perf_counter() - t0, success))
                trace.execution_mode = "library"
                trace.cli_mode_forced = False
                trace.mode_reason = "openhands.core available"
                trace.openhands_library_core_available = openhands_core_available
            except UnicodeDecodeError as e:
                _log_engine("fallback to subprocess (UnicodeDecodeError: %s)" % (str(e)[:80],))
                patch_str, trace, success, err, stdout, stderr = _run_openhands_subprocess(
                    repo_dir, task_text, config, scratch_dir, extra_env=extra_env
                )
                trace.execution_mode = "cli_subprocess"
                trace.cli_mode_forced = True
                trace.mode_reason = "UnicodeDecodeError: fallback to subprocess"
                trace.openhands_library_core_available = openhands_core_available

    # Best-effort latency and phased budget attribution from event timestamps.
    sb, ab, fb = _compute_timeout_budget_phases(config.timeout_seconds)
    trace.startup_budget_s = sb
    trace.action_budget_s = ab
    trace.finalization_budget_s = fb
    la, le = _extract_latency_metrics_from_events(trace.raw_events or [])
    trace.first_action_latency_s = la
    trace.first_file_edit_latency_s = le
    if trace.timeout_origin:
        trace.timeout_snapshot = _extract_timeout_snapshot(trace)

    return SolveResult(
        patch_diff_str=patch_str,
        trace=trace,
        success=success,
        error=err,
        stdout=stdout,
        stderr=stderr,
    )
