#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# SWE-bench bench runner: single entry point to run SWE-bench instances and emit
# predictions.jsonl plus PF evidence bundles (runs/<run_id>/<instance_id>/).

import errno
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import uuid
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

_LOG_PREFIX = "[pf-swebench]"


def _stderr_write_safe(text: str) -> None:
    """Write to stderr; ignore EPIPE when stderr is piped (e.g. 2>&1 | tee) and the reader exits."""
    try:
        sys.stderr.write(text)
        sys.stderr.flush()
    except BrokenPipeError:
        return
    except OSError as e:
        if getattr(e, "errno", None) == errno.EPIPE:
            return
        raise


def _log(msg: str) -> None:
    """Print a log line to stderr with prefix and optional timestamp."""
    if os.environ.get("PF_SWEBENCH_QUIET", "").lower() in ("1", "true", "yes"):
        return
    ts = datetime.now(timezone.utc).strftime("%H:%M:%S")
    _stderr_write_safe(f"{_LOG_PREFIX} {ts} {msg}\n")


def _eprint(msg: str) -> None:
    """Print one line to stderr without raising if the pipe is broken."""
    _stderr_write_safe(msg + "\n")


def _stdout_line_safe(*parts: object) -> None:
    """Print to stdout; ignore EPIPE when stdout is piped and the reader exits early."""
    try:
        print(*parts)
        sys.stdout.flush()
    except BrokenPipeError:
        return
    except OSError as e:
        if getattr(e, "errno", None) == errno.EPIPE:
            return
        raise


def _verbose_instance_logs_enabled() -> bool:
    """Enable detailed per-instance phase timing logs."""
    return os.environ.get("PF_SWEBENCH_VERBOSE_INSTANCE_LOGS", "").strip().lower() in (
        "1",
        "true",
        "yes",
        "on",
    )

from loader import load_dataset as loader_load_dataset
from loader import load_from_file as loader_load_from_file
from loader import SWEbenchInstance
from util import sanitize_instance_id
from workspace import (
    GUARDED_SHELL_APPENDIX,
    _build_task_prompt,
)

try:
    from provider_env import (
        effective_llm_model,
        llm_env_diagnostics,
        normalize_openhands_provider,
        openhands_litellm_model,
        openhands_preflight_log_line,
        resolve_openhands_model,
    )
except ImportError:
    try:
        from bench.swebench.provider_env import (
            effective_llm_model,
            llm_env_diagnostics,
            normalize_openhands_provider,
            openhands_litellm_model,
            openhands_preflight_log_line,
            resolve_openhands_model,
        )
    except ImportError:
        effective_llm_model = None  # type: ignore[misc, assignment]
        llm_env_diagnostics = None  # type: ignore[misc, assignment]
        normalize_openhands_provider = None  # type: ignore[misc, assignment]
        openhands_litellm_model = None  # type: ignore[misc, assignment]
        openhands_preflight_log_line = None  # type: ignore[misc, assignment]
        resolve_openhands_model = None  # type: ignore[misc, assignment]

try:
    from constants import (
        COST_REPORT_FILENAME,
        PATCH_APPLY_CHECK_FILENAME,
        MAX_PATCH_BYTES,
        SUMMARY_JSON_FILENAME,
        TIMING_JSON_FILENAME,
        DIAGNOSTIC_DIFF_STAT_TIMEOUT,
        GIT_APPLY_CHECK_TIMEOUT,
        GIT_VERSION_MAX_LEN,
        PATCH_APPLY_CHECK_STDERR_MAX,
        DIFF_STAT_DISPLAY_HEAD,
        DIFF_STAT_DISPLAY_TAIL,
        DIFF_STAT_DISPLAY_LINES_THRESHOLD,
        PIP_FREEZE_TIMEOUT,
        PREFLIGHT_DIFF_TIMEOUT,
        PREFLIGHT_REV_LIST_TIMEOUT,
        PREFLIGHT_DIFF_RISK_FILE_THRESHOLD,
    )
except ImportError:
    COST_REPORT_FILENAME = "cost_report.json"
    PATCH_APPLY_CHECK_FILENAME = "patch_apply_check.json"
    MAX_PATCH_BYTES = 2 * 1024 * 1024
    SUMMARY_JSON_FILENAME = "summary.json"
    TIMING_JSON_FILENAME = "timing.json"
    DIAGNOSTIC_DIFF_STAT_TIMEOUT = 30
    GIT_APPLY_CHECK_TIMEOUT = 30
    GIT_VERSION_MAX_LEN = 200
    PATCH_APPLY_CHECK_STDERR_MAX = 2000
    DIFF_STAT_DISPLAY_HEAD = 80
    DIFF_STAT_DISPLAY_TAIL = 200
    DIFF_STAT_DISPLAY_LINES_THRESHOLD = 300
    PIP_FREEZE_TIMEOUT = 30
    PREFLIGHT_DIFF_TIMEOUT = 5
    PREFLIGHT_REV_LIST_TIMEOUT = 10
    PREFLIGHT_DIFF_RISK_FILE_THRESHOLD = 200

try:
    from engines.openhands_engine import OpenHandsConfig, solve as openhands_solve, SolveResult
    from engines.direct_agent_engine import solve as direct_agent_solve
except ImportError:
    OpenHandsConfig = None
    openhands_solve = None
    direct_agent_solve = None
    SolveResult = None

try:
    from guard.compliance import (
        PolicyComplianceSummary,
        build_compliance_summary_from_events_file,
        write_compliance_summary,
    )
    from guard.ledger_stream import LedgerStream
except ImportError:
    PolicyComplianceSummary = None  # type: ignore[misc, assignment]
    build_compliance_summary_from_events_file = None
    write_compliance_summary = None
    LedgerStream = None  # type: ignore[misc, assignment]

try:
    from policy.loader import load_pack
except ImportError:
    load_pack = None

try:
    from replay.capture import build_replay_bundle, write_replay_bundle
except ImportError:
    build_replay_bundle = None
    write_replay_bundle = None

try:
    from proof_hook import run_proof, write_proof_failure
except ImportError:
    run_proof = None
    write_proof_failure = None

try:
    from cost_report import (
        build_cost_report,
        write_cost_report,
        write_summary,
    )
except ImportError:
    build_cost_report = None
    write_cost_report = None
    write_summary = None

try:
    from evidence_writer import EvidenceWriter, write_instance_evidence as write_evidence
    from instance_processor import InstanceProcessor
    from predictions_writer import (
        append_raw_predictions_line,
        emit_predictions_line,
        pfmeta_path as _pfmeta_path,
        write_pfmeta_jsonl,
    )
    from run_config import RunConfig, build_argument_parser
    from summary_writer import SummaryWriter
    from workspace_manager import WorkspaceManager
except ImportError:
    from bench.swebench.evidence_writer import EvidenceWriter, write_instance_evidence as write_evidence
    from bench.swebench.instance_processor import InstanceProcessor
    from bench.swebench.predictions_writer import (
        append_raw_predictions_line,
        emit_predictions_line,
        pfmeta_path as _pfmeta_path,
        write_pfmeta_jsonl,
    )
    from bench.swebench.run_config import RunConfig, build_argument_parser
    from bench.swebench.summary_writer import SummaryWriter
    from bench.swebench.workspace_manager import WorkspaceManager

# Dataset name to HuggingFace dataset ID (optional dependency).
DATASET_IDS = {
    "Lite": "princeton-nlp/SWE-bench_Lite",
    "Verified": "princeton-nlp/SWE-bench_Verified",
    "Full": "princeton-nlp/SWE-bench",
}


def load_instances(
    dataset: str,
    split: str,
    instance_ids: Optional[List[str]] = None,
    max_instances: Optional[int] = None,
    instances_file: Optional[str] = None,
    dataset_cache_dir: Optional[str] = None,
) -> List[SWEbenchInstance]:
    """Load SWE-bench instances via loader (HuggingFace or local file)."""
    if instances_file:
        return loader_load_from_file(instances_file, instance_ids, max_instances)
    return loader_load_dataset(
        dataset, split, instance_ids, max_instances, cache_dir=dataset_cache_dir
    )


def assert_openhands_available(engine: str) -> None:
    """
    When engine is openhands, verify OpenHands is available (library or CLI).
    Exits with a clear error if not; does not return on failure.
    Call before creating run_dir so no valid-looking run dir is left on failure.
    """
    if engine != "openhands":
        return
    if openhands_solve is not None:
        return
    # Library import failed at module load. Try CLI to give a clearer message.
    try:
        proc = subprocess.run(
            ["openhands", "--version"],
            capture_output=True,
            timeout=10,
            text=True,
        )
        if proc.returncode == 0:
            print(
                "Error: OpenHands CLI is available but Python module 'engines.openhands_engine' could not be imported. "
                "Install the OpenHands Python package in this environment (e.g. pip install openhands), or use --engine mock for CI.",
                file=sys.stderr,
            )
        else:
            _print_openhands_not_available()
    except (FileNotFoundError, subprocess.TimeoutExpired, OSError):
        _print_openhands_not_available()
    sys.exit(1)


def _print_openhands_not_available() -> None:
    print(
        "Error: OpenHands is not available. Install it (e.g. pip install openhands) or use --engine mock for CI.",
        file=sys.stderr,
    )


def _write_guarded_run_started_event(evidence_dir: Path, run_id: str, instance_id: str) -> None:
    """Write initial run_started event to evidence/events.jsonl so guard engagement is auditable even if agent never issues commands."""
    if LedgerStream is None:
        return
    events_path = evidence_dir / "events.jsonl"
    try:
        ledger = LedgerStream(output_path=events_path, run_id=run_id)
        ledger.append("run_started", {"message": "guard_engaged", "instance_id": instance_id})
    except Exception:
        pass  # Best-effort; compliance summary will still be written with chain_tail_hash from later events


def _write_diff_stat_when_too_large(repo_dir: Path, inst_dir: Path, patch_len: int) -> None:
    """When patch was capped for size, write git diff --stat to evidence for debugging."""
    if not repo_dir.is_dir():
        return
    out_path = inst_dir / "diff_stat_when_too_large.txt"
    try:
        proc = subprocess.run(
            ["git", "diff", "HEAD", "--stat"],
            cwd=repo_dir,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=DIAGNOSTIC_DIFF_STAT_TIMEOUT,
        )
        lines = (proc.stdout or "").strip().splitlines()
        if len(lines) <= DIFF_STAT_DISPLAY_LINES_THRESHOLD:
            body = "\n".join(lines)
        else:
            body = "\n".join(
                lines[: DIFF_STAT_DISPLAY_HEAD]
                + [f"... ({len(lines)} lines total) ..."]
                + lines[-DIFF_STAT_DISPLAY_TAIL :]
            )
        out_path.write_text(
            f"# patch_len={patch_len} exceeded MAX_PATCH_BYTES; git diff HEAD --stat (diagnostic):\n\n{body}",
            encoding="utf-8",
        )
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError) as e:
        out_path.write_text(
            f"# patch_len={patch_len} exceeded MAX_PATCH_BYTES; git diff --stat failed: {e}\n",
            encoding="utf-8",
        )


def run_patch_apply_check(
    repo_dir: Path,
    patch_content: str,
    base_commit: str,
    resolved_commit: str,
) -> tuple[bool, dict]:
    """
    Run git apply --check --whitespace=nowarn in a temporary worktree. Returns (applies, report_dict).
    report_dict has: applies, stderr (truncated), base_commit, resolved_commit, git_version.

    Uses a temporary git worktree at HEAD so the main workspace is never mutated. The patch
    was produced from diff against HEAD; apply --check must run against that same clean tree.
    Callers (e.g. replay bundle capture) may rely on the workspace still containing the
    agent's edits after this returns.
    """
    git_version = ""
    try:
        v = subprocess.run(
            ["git", "--version"],
            cwd=repo_dir,
            capture_output=True,
            text=True,
            timeout=5,
        )
        git_version = (v.stdout or "").strip()[:GIT_VERSION_MAX_LEN]
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
        git_version = "unknown"

    if not patch_content.strip():
        return False, {
            "applies": False,
            "stderr": "empty patch",
            "base_commit": base_commit,
            "resolved_commit": resolved_commit,
            "git_version": git_version,
        }

    worktree_path = None
    try:
        worktree_path = tempfile.mkdtemp(prefix="pf_apply_check_")
        add_result = subprocess.run(
            ["git", "worktree", "add", worktree_path, "HEAD"],
            cwd=repo_dir,
            capture_output=True,
            text=True,
            timeout=30,
        )
        if add_result.returncode != 0:
            stderr = (add_result.stderr or "").strip()
            if len(stderr) > PATCH_APPLY_CHECK_STDERR_MAX:
                stderr = stderr[:PATCH_APPLY_CHECK_STDERR_MAX] + "\n... (truncated)"
            return False, {
                "applies": False,
                "stderr": f"git worktree add failed: {stderr}",
                "base_commit": base_commit,
                "resolved_commit": resolved_commit,
                "git_version": git_version,
            }
        proc = subprocess.run(
            ["git", "apply", "--check", "--whitespace=nowarn"],
            cwd=worktree_path,
            input=patch_content,
            capture_output=True,
            text=True,
            timeout=GIT_APPLY_CHECK_TIMEOUT,
        )
        stderr = (proc.stderr or "").strip()
        if len(stderr) > PATCH_APPLY_CHECK_STDERR_MAX:
            stderr = stderr[:PATCH_APPLY_CHECK_STDERR_MAX] + "\n... (truncated)"
        applies = proc.returncode == 0
        return applies, {
            "applies": applies,
            "stderr": stderr,
            "base_commit": base_commit,
            "resolved_commit": resolved_commit,
            "git_version": git_version,
        }
    except subprocess.TimeoutExpired:
        return False, {
            "applies": False,
            "stderr": "git apply --check timed out",
            "base_commit": base_commit,
            "resolved_commit": resolved_commit,
            "git_version": git_version,
        }
    except (FileNotFoundError, OSError) as e:
        return False, {
            "applies": False,
            "stderr": str(e)[:PATCH_APPLY_CHECK_STDERR_MAX],
            "base_commit": base_commit,
            "resolved_commit": resolved_commit,
            "git_version": git_version,
        }
    finally:
        if worktree_path and Path(worktree_path).exists():
            try:
                subprocess.run(
                    ["git", "worktree", "remove", "--force", worktree_path],
                    cwd=repo_dir,
                    capture_output=True,
                    timeout=15,
                )
            except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
                pass
            try:
                subprocess.run(
                    ["git", "worktree", "prune"],
                    cwd=repo_dir,
                    capture_output=True,
                    timeout=5,
                )
            except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
                pass
            if Path(worktree_path).exists():
                try:
                    shutil.rmtree(worktree_path, ignore_errors=True)
                except OSError:
                    pass


def _run_preflight(instances: List[Any], workspaces_dir: str) -> int:
    """
    Materialize workspaces (with clean on reuse), run quick git stats, print table. No OpenHands.
    Returns 0 on success. Lets you see repo size and cleanliness before a long run.
    """
    n = len(instances)
    print("Preflight: %d instances (materialize + clean + quick stats, no agent run)" % n, file=sys.stderr)
    print("%-45s %10s %8s %12s %s" % ("instance_id", "commits", "diff", "diff_risk", "note"), file=sys.stderr)
    print("-" * 95, file=sys.stderr)
    for idx, instance in enumerate(instances):
        iid = instance.instance_id
        repo_path: Optional[Path] = None
        commits_s = "?"
        diff_s = "?"
        diff_risk = ""
        note = ""
        try:
            workspace_root, _manifest, _sha = WorkspaceManager(workspaces_dir).materialize(instance)
            repo_path = workspace_root / "repo"
            if repo_path.is_dir():
                try:
                    r = subprocess.run(
                        ["git", "rev-list", "--count", "HEAD"],
                        cwd=repo_path,
                        capture_output=True,
                        text=True,
                        timeout=PREFLIGHT_REV_LIST_TIMEOUT,
                    )
                    commits_s = (r.stdout or "").strip() or "?"
                    try:
                        c = int(commits_s)
                        if c > 50000:
                            note = "large repo (full diff may timeout)"
                    except ValueError:
                        pass
                except (subprocess.TimeoutExpired, FileNotFoundError):
                    commits_s = "timeout"
                try:
                    r = subprocess.run(
                        ["git", "diff", "HEAD", "--stat"],
                        cwd=repo_path,
                        capture_output=True,
                        text=True,
                        timeout=PREFLIGHT_DIFF_TIMEOUT,
                    )
                    lines = (r.stdout or "").strip().splitlines()
                    if not lines:
                        diff_s = "0"
                    else:
                        last = lines[-1]
                        m = re.search(r"(\d+)\s+files?\s+changed", last, re.IGNORECASE)
                        diff_s = m.group(1) if m else str(len(lines) - 1)
                        if diff_s != "0":
                            note = (note + " " if note else "") + "was dirty (now reset)"
                        try:
                            fc = int(diff_s)
                            if fc > PREFLIGHT_DIFF_RISK_FILE_THRESHOLD:
                                diff_risk = "high"
                        except ValueError:
                            pass
                except subprocess.TimeoutExpired:
                    diff_s = "timeout"
                    diff_risk = "high"
                    note = (note + " " if note else "") + "diff slow"
                except FileNotFoundError:
                    diff_s = "?"
        except Exception as e:
            note = str(e)[:40]
        print("%-45s %10s %8s %12s %s" % (iid, commits_s, diff_s, diff_risk, note), file=sys.stderr)
    print("-" * 95, file=sys.stderr)
    print("Preflight done. Run without --preflight to execute OpenHands.", file=sys.stderr)
    return 0


def run_engine_for_instance(
    instance_dict: dict,
    engine: str,
    run_dir: Path,
    instance_id: str,
    workspace_path: Optional[Path] = None,
    task_text: Optional[str] = None,
    openhands_config: Optional[Any] = None,
    openhands_extra_env: Optional[dict] = None,
) -> tuple[str, str, Optional[dict]]:
    """
    Run the configured engine for one instance. Returns (model_patch, log_text, engine_trace_dict).
    When engine is openhands and workspace_path/task_text are set, invokes OpenHands and returns its patch and trace.
    """
    log_lines = [
        f"[{datetime.now(timezone.utc).isoformat()}] Engine={engine}",
        f"instance_id={instance_id}",
        f"repo={instance_dict.get('repo', '')}",
        f"base_commit={instance_dict.get('base_commit', '')}",
    ]
    trace_dict: Optional[dict] = None

    def _is_solve_result_like(obj: Any) -> bool:
        return (
            obj is not None
            and hasattr(obj, "patch_diff_str")
            and hasattr(obj, "trace")
            and hasattr(obj, "success")
        )

    def _fallback_reason_type(reason: str) -> str:
        if reason in ("provider_error", "runtime_fault"):
            return "runtime_or_provider"
        return "quality_or_policy"

    def _should_fallback_to_openhands(model_patch_val: str, trace_val: Optional[dict], err_text: str) -> tuple[bool, str]:
        low = (err_text or "").lower()
        provider_tokens = (
            "httperror",
            "connection",
            "429",
            "rate limit",
            "unauthorized",
            "forbidden",
            "timeout",
            "tls",
            "dns",
            "econnreset",
        )
        if any(tok in low for tok in provider_tokens):
            return True, "provider_error"
        # Structural runtime fault: no trace and no patch (engine likely failed before actioning).
        if (not trace_val or not _openhands_trace_has_content(trace_val)) and not (model_patch_val or "").strip():
            return True, "runtime_fault"
        # Do not fallback for quality-only failures (e.g., empty/weak patch) here.
        return False, ""
    if engine == "mock":
        try:
            from engines.mock_engine import solve as mock_solve
            result = mock_solve(
                workspace_path=workspace_path,
                task_text=task_text or "",
                config=openhands_config,
                extra_env=openhands_extra_env,
            )
            if isinstance(result, SolveResult):
                model_patch = result.patch_diff_str or ""
                trace_dict = result.trace.to_dict()
                trace_dict["success"] = result.success
                if result.error:
                    trace_dict["error"] = result.error
                log_lines.append("mock_success=%s" % result.success)
            else:
                model_patch = _solver_disabled_patch(instance_dict, engine)
                trace_dict = {"source": "mock", "prompts_sent": [], "tool_calls": [], "files_modified": []}
        except Exception as e:
            model_patch = _solver_disabled_patch(instance_dict, engine)
            trace_dict = {"error": str(e), "prompts_sent": [], "tool_calls": [], "files_modified": []}
            log_lines.append("mock_exception=%s" % str(e)[:500])
    elif engine == "openhands":
        # Stub is illegal for openhands: must produce non-empty patch or raise.
        if workspace_path is None or not task_text:
            raise RuntimeError(
                "OpenHands requires workspace_path and task_text; missing for instance_id=%s" % instance_id
            )
        if openhands_solve is None:
            raise RuntimeError("OpenHands solver not available (assert_openhands_available should have run earlier)")
        config = openhands_config or (OpenHandsConfig() if OpenHandsConfig else None)
        result = openhands_solve(
            workspace_path, task_text, config=config, extra_env=openhands_extra_env
        )
        if not _is_solve_result_like(result):
            raise RuntimeError("OpenHands did not return SolveResult for instance_id=%s" % instance_id)
        model_patch = result.patch_diff_str or ""
        trace_dict = result.trace.to_dict()
        trace_dict["success"] = result.success
        if result.error:
            trace_dict["error"] = result.error
        log_lines.append("openhands_success=%s" % result.success)
        if result.error:
            log_lines.append("openhands_error=%s" % result.error[:500])
        if not model_patch.strip():
            log_lines.append("openhands_empty_patch=1")
        # On failure or empty trace, save stderr tail to trace for run dir (openhands_stderr_tail.txt).
        if result.stderr and (not result.success or not _openhands_trace_has_content(trace_dict)):
            trace_dict["openhands_stderr_tail"] = result.stderr[-2000:] if len(result.stderr) > 2000 else result.stderr
    elif engine == "direct_agent":
        if workspace_path is None or not task_text:
            raise RuntimeError(
                "direct_agent requires workspace_path and task_text; missing for instance_id=%s" % instance_id
            )
        if direct_agent_solve is None:
            raise RuntimeError("direct_agent solver not available")
        config = openhands_config or (OpenHandsConfig() if OpenHandsConfig else None)
        result = direct_agent_solve(
            workspace_path, task_text, config=config, extra_env=openhands_extra_env
        )
        if not _is_solve_result_like(result):
            raise RuntimeError("direct_agent did not return SolveResult for instance_id=%s" % instance_id)
        model_patch = result.patch_diff_str or ""
        trace_dict = result.trace.to_dict()
        trace_dict["success"] = result.success
        if result.error:
            trace_dict["error"] = result.error
        log_lines.append("direct_agent_success=%s" % result.success)
        if result.error:
            log_lines.append("direct_agent_error=%s" % str(result.error)[:500])

        # Policy-driven fallback to OpenHands (secondary engine).
        fallback_enabled = (
            os.environ.get("PF_DIRECT_AGENT_FALLBACK_OPENHANDS", "1").strip().lower()
            in ("1", "true", "yes", "on")
        )
        fallback_needed, fallback_reason = _should_fallback_to_openhands(
            model_patch, trace_dict, str(result.error or "")
        )
        if fallback_enabled and fallback_needed:
            if openhands_solve is None:
                log_lines.append("fallback_openhands_unavailable=1")
            else:
                log_lines.append("fallback_openhands_invoked=1 reason=%s" % fallback_reason)
                trace_dict["fallback_invoked"] = True
                trace_dict["fallback_reason"] = fallback_reason
                trace_dict["fallback_reason_type"] = _fallback_reason_type(fallback_reason)
                trace_dict["fallback_from"] = "direct_agent"
                oh_result = openhands_solve(
                    workspace_path, task_text, config=config, extra_env=openhands_extra_env
                )
                if not _is_solve_result_like(oh_result):
                    raise RuntimeError("fallback openhands did not return SolveResult for instance_id=%s" % instance_id)
                model_patch = oh_result.patch_diff_str or ""
                oh_trace = oh_result.trace.to_dict()
                oh_trace["success"] = oh_result.success
                if oh_result.error:
                    oh_trace["error"] = oh_result.error
                oh_trace["fallback_invoked"] = True
                oh_trace["fallback_reason"] = fallback_reason
                oh_trace["fallback_reason_type"] = _fallback_reason_type(fallback_reason)
                oh_trace["fallback_from"] = "direct_agent"
                trace_dict = oh_trace
                log_lines.append("fallback_openhands_success=%s" % oh_result.success)
                if oh_result.error:
                    log_lines.append("fallback_openhands_error=%s" % str(oh_result.error)[:500])
    else:
        raise ValueError("Unknown engine: %s. Use openhands, direct_agent, or mock." % engine)
    log_lines.append("patch_length=%d" % len(model_patch))
    log_text = "\n".join(log_lines)
    return model_patch, log_text, trace_dict


def _solver_disabled_patch(instance: dict, engine: str) -> str:
    """Solver-disabled mode: no patch."""
    return f"""# solver_disabled engine={engine} instance_id={instance.get('instance_id', '')}
"""


def _openhands_trace_has_content(engine_trace: Optional[dict]) -> bool:
    """True iff trace has at least one of: non-empty tool_calls, non-empty files_modified, or raw_events length > 0."""
    if not engine_trace:
        return False
    tool_calls = engine_trace.get("tool_calls") or []
    files_modified = engine_trace.get("files_modified") or []
    raw_events = engine_trace.get("raw_events") or []
    return (
        len(tool_calls) > 0
        or len(files_modified) > 0
        or len(raw_events) > 0
    )


def _sha256_canonical_json(obj: Any) -> str:
    """SHA256 of canonical JSON (sort_keys) for deterministic hashes that match on-disk evidence."""
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _trace_hash(engine_trace_dict: Optional[dict]) -> str:
    """Hash of engine trace content; links to engine_trace.json on disk."""
    if not engine_trace_dict:
        return ""
    return _sha256_canonical_json(engine_trace_dict)


def _replay_bundle_hash(bundle: Optional[dict]) -> str:
    """Hash of replay bundle content; links to replay_bundle.json on disk."""
    if not bundle:
        return ""
    return _sha256_canonical_json(bundle)


def build_pfmeta_line(
    instance_id: str,
    run_id: str,
    policy_hash: Optional[str],
    trace_hash: str,
    replay_bundle_hash: str,
    proof_artifact_hash: Optional[str],
    cost_metrics: Optional[Dict[str, Any]],
    empty_patch_reason: Optional[str] = None,
) -> dict:
    """Build one PF metadata sidecar record (same instance_id as predictions.jsonl; links to evidence)."""
    out = {
        "instance_id": instance_id,
        "run_id": run_id,
        "policy_hash": policy_hash or "",
        "trace_hash": trace_hash,
        "replay_bundle_hash": replay_bundle_hash,
    }
    if proof_artifact_hash:
        out["proof_artifact_hash"] = proof_artifact_hash
    if empty_patch_reason:
        out["empty_patch_reason"] = empty_patch_reason
    out["cost_metrics"] = cost_metrics if cost_metrics is not None else {}
    return out


def _execute_run(config: RunConfig) -> int:
    if getattr(config, "verbose_instance_logs", False):
        os.environ["PF_SWEBENCH_VERBOSE_INSTANCE_LOGS"] = "1"
    t_load = time.perf_counter()
    try:
        instances = load_instances(
            dataset=config.dataset,
            split=config.split,
            instance_ids=config.instance_id_list,
            max_instances=config.max_instances,
            instances_file=config.instances_file or None,
            dataset_cache_dir=config.dataset_cache_dir or None,
        )
    except Exception as e:
        print("Error loading instances:", e, file=sys.stderr)
        return 1
    _log("Loaded %d instances in %.1fs" % (len(instances), time.perf_counter() - t_load))
    if _verbose_instance_logs_enabled():
        _log("Verbose instance logs enabled via PF_SWEBENCH_VERBOSE_INSTANCE_LOGS=1")

    if not instances:
        print("No instances to run.", file=sys.stderr)
        return 1

    if config.preflight:
        return _run_preflight(instances, config.workspaces_dir) or 0

    assert_openhands_available(config.engine)

    if config.seed is not None:
        os.environ["OPENHANDS_SEED"] = str(config.seed)
    run_id = config.run_id or datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S") + "-" + uuid.uuid4().hex[:8]
    run_dir = Path(config.runs_dir) / run_id
    run_dir.mkdir(parents=True, exist_ok=True)

    _repo_root = Path(__file__).resolve().parent.parent.parent
    env_info: Dict[str, Any] = {
        "python_version": sys.version.split()[0] if sys.version else "",
        "platform": sys.platform,
        "dataset": config.dataset,
        "split": config.split,
    }
    try:
        import openhands
        oh_ver = getattr(openhands, "__version__", None)
        if not oh_ver or str(oh_ver).strip().lower() == "unknown":
            try:
                from importlib.metadata import version as _pkg_version
                oh_ver = _pkg_version("openhands")
            except Exception:
                oh_ver = "unknown"
        env_info["openhands_version"] = oh_ver
    except ImportError:
        env_info["openhands_version"] = None
    try:
        import datasets
        env_info["datasets_version"] = getattr(datasets, "__version__", "unknown")
    except ImportError:
        env_info["datasets_version"] = None
    try:
        import swebench
        env_info["swebench_version"] = getattr(swebench, "__version__", "unknown")
    except ImportError:
        env_info["swebench_version"] = None
    provider_for_model = ""
    resolved_model_raw = config.openhands_model
    if config.engine in ("openhands", "direct_agent"):
        if normalize_openhands_provider is not None:
            provider_for_model = normalize_openhands_provider()
        else:
            provider_for_model = (os.environ.get("OPENHANDS_PROVIDER") or "openai").strip().lower()
        if resolve_openhands_model is not None:
            resolved_model_raw = resolve_openhands_model(config.openhands_model)
        else:
            resolved_model_raw = (os.environ.get("OPENHANDS_MODEL") or config.openhands_model or "").strip()
        env_info["openhands_model_config"] = config.openhands_model or None
        om = os.environ.get("OPENHANDS_MODEL", "").strip()
        if om:
            env_info["openhands_model_env"] = om
        env_info["openhands_model_resolved"] = resolved_model_raw or None
        env_info["openhands_model"] = resolved_model_raw or None
        if llm_env_diagnostics is not None:
            env_info.update(llm_env_diagnostics())
        else:
            _norm_prov = None
            try:
                from provider_env import normalize_openhands_provider as _norm_prov
            except ImportError:
                try:
                    from bench.swebench.provider_env import normalize_openhands_provider as _norm_prov
                except ImportError:
                    _norm_prov = None
            if _norm_prov is not None:
                env_info["openhands_provider"] = _norm_prov()
            else:
                env_info["openhands_provider"] = (os.environ.get("OPENHANDS_PROVIDER") or "openai").strip().lower()

        # Package capability probe: when openhands.core is absent, we must run CLI-first.
        cli_available = shutil.which("openhands") is not None
        library_core_available = False
        try:
            from openhands.core.main import run_controller as _  # noqa: F401

            library_core_available = True
        except Exception:
            library_core_available = False
        env_info["openhands_package_capabilities"] = {
            "cli_available": bool(cli_available),
            "library_core_available": bool(library_core_available),
        }
        # Expected execution mode based on provider + core availability.
        prov = str(env_info.get("openhands_provider") or "").strip().lower()
        if prov == "prime_intellect":
            env_info["openhands_execution_mode_expected"] = "prime_subprocess"
        elif library_core_available:
            env_info["openhands_execution_mode_expected"] = "library"
        else:
            env_info["openhands_execution_mode_expected"] = "cli_subprocess"
    else:
        env_info["openhands_model"] = None
    env_info["engine"] = config.engine
    try:
        pip_out = subprocess.run(
            [sys.executable, "-m", "pip", "freeze"],
            capture_output=True,
            text=True,
            timeout=PIP_FREEZE_TIMEOUT,
            cwd=str(_repo_root),
        )
        if pip_out.returncode == 0 and pip_out.stdout:
            pip_text = pip_out.stdout.strip()
            env_info["pip_freeze_hash"] = hashlib.sha256(pip_text.encode("utf-8")).hexdigest()
            (run_dir / "pip_freeze.txt").write_text(pip_text, encoding="utf-8")
    except Exception:
        env_info["pip_freeze_hash"] = None
    (run_dir / "env.json").write_text(json.dumps(env_info, indent=2), encoding="utf-8")

    policy_name: Optional[str] = None
    policy_hash_value: Optional[str] = None
    if config.policy and load_pack is not None:
        try:
            _pack_content, policy_hash_value = load_pack(config.policy)
            policy_name = config.policy
        except Exception as e:
            print(f"Policy pack load failed ({config.policy}): {e}", file=sys.stderr)

    # Write predictions to a temp file; rename to config.out only on full success (atomic).
    out_tmp = config.out + ".tmp"
    with open(out_tmp, "w", encoding="utf-8") as f:
        pass

    # For --skip-existing: load existing predictions and pfmeta so we can copy lines for already-done instances.
    existing_pred_line_by_id: Dict[str, str] = {}
    existing_pfmeta_by_id: Dict[str, dict] = {}
    if config.skip_existing and Path(config.out).exists():
        try:
            with open(config.out, "r", encoding="utf-8") as f:
                for line in f:
                    line = line.rstrip("\n")
                    if not line:
                        continue
                    obj = json.loads(line)
                    iid = obj.get("instance_id")
                    if iid:
                        existing_pred_line_by_id[iid] = line
        except (OSError, json.JSONDecodeError) as e:
            print(f"Warning: could not load existing predictions from {config.out}: {e}", file=sys.stderr)
            existing_pred_line_by_id = {}
        pfmeta_path_existing = _pfmeta_path(config.out)
        if pfmeta_path_existing.exists():
            try:
                with open(pfmeta_path_existing, "r", encoding="utf-8") as f:
                    for line in f:
                        line = line.rstrip("\n")
                        if not line:
                            continue
                        rec = json.loads(line)
                        iid = rec.get("instance_id")
                        if iid:
                            existing_pfmeta_by_id[iid] = rec
            except (OSError, json.JSONDecodeError) as e:
                print(f"Warning: could not load existing pfmeta from {pfmeta_path_existing}: {e}", file=sys.stderr)
                existing_pfmeta_by_id = {}
        if existing_pred_line_by_id:
            _log("Resume: %d instance(s) already in %s will be skipped" % (len(existing_pred_line_by_id), config.out))

    instances_planned = len(instances)
    instances_written = 0
    first_error: Optional[str] = None
    status = "failed"
    pfmeta_rows: List[dict] = []
    cost_reports: List[dict] = []
    model_name = f"pf-swebench-{config.engine}"
    effective_model_name = config.engine
    if config.engine in ("openhands", "direct_agent"):
        if openhands_litellm_model is not None and provider_for_model:
            effective_model_name = openhands_litellm_model(provider_for_model, resolved_model_raw)
        elif effective_llm_model is not None and provider_for_model:
            effective_model_name = effective_llm_model(provider_for_model, resolved_model_raw)
        else:
            effective_model_name = (resolved_model_raw or "").strip() or config.engine
    workspace_root = None
    repo_root = Path(__file__).resolve().parent.parent.parent
    guard_shell = Path(__file__).parent / "guard" / (
        "pf_guard_exec.bat" if sys.platform == "win32" else "pf_guard_exec.sh"
    )
    n_instances = len(instances)
    instance_ids_planned = [i.instance_id for i in instances]
    if config.engine in ("openhands", "direct_agent") and n_instances > 0:
        if openhands_preflight_log_line is not None:
            _log(openhands_preflight_log_line())
        else:
            api_key_set = bool(
                (os.environ.get("OPENAI_API_KEY") or os.environ.get("ANTHROPIC_API_KEY") or "").strip()
            )
            _log(
                "OpenHands: LLM_API_KEY will be set from env: %s"
                % ("yes" if api_key_set else "NO (set OPENAI_API_KEY or ANTHROPIC_API_KEY)")
            )
    workspace_mgr = WorkspaceManager(config.workspaces_dir)
    instance_processor = InstanceProcessor(workspace_mgr, run_engine_for_instance)
    evidence_writer_out = EvidenceWriter(run_dir)
    verbose_instance_logs = _verbose_instance_logs_enabled()
    try:
        for idx, instance in enumerate(instances):
            iid = instance.instance_id
            _log("Instance %d/%d: %s" % (idx + 1, n_instances, iid))
            t_instance_start = time.perf_counter()
            if config.skip_existing and iid in existing_pred_line_by_id:
                _log("  skipping (already in %s)" % config.out)
                append_raw_predictions_line(out_tmp, existing_pred_line_by_id[iid])
                pfmeta_rec = existing_pfmeta_by_id.get(iid)
                if pfmeta_rec is None:
                    pfmeta_rec = {"instance_id": iid, "run_id": "", "policy_hash": "", "trace_hash": "", "replay_bundle_hash": "", "cost_metrics": {}}
                pfmeta_rows.append(pfmeta_rec)
                instances_written += 1
                continue
            inst_dir = run_dir / sanitize_instance_id(iid)
            inst_dir.mkdir(parents=True, exist_ok=True)
            workspace_sha = None
            workspace_manifest_dict = None
            workspace_root = None
            task_text = None
            t_workspace = time.perf_counter()
            if not config.no_workspace and instance.repo and instance.base_commit:
                try:
                    if verbose_instance_logs:
                        _log("  workspace: materialize start repo=%s base=%s" % (instance.repo, instance.base_commit))
                    workspace_root, manifest, manifest_sha = workspace_mgr.materialize(instance)
                    workspace_sha = manifest_sha
                    workspace_manifest_dict = manifest.to_canonical_dict()
                    workspace_manifest_dict["workspace_manifest_sha256"] = manifest_sha
                    # Always use canonical task (implement-by-editing + tool instruction); do not rely on stale task_prompt.md
                    task_text = _build_task_prompt(instance)
                    _log("  workspace: ready in %.1fs" % (time.perf_counter() - t_workspace))
                except Exception as e:
                    _log("  workspace: failed in %.1fs - %s" % (time.perf_counter() - t_workspace, e))
                    _eprint("Workspace materialization failed for %s: %s" % (iid, e))
            elif not config.no_workspace:
                _log("  workspace: skipped (no repo/base_commit)")
            if config.effective_guarded and config.engine == "mock" and workspace_root is None:
                mock_ws = inst_dir / "mock_workspace"
                mock_ws.mkdir(parents=True, exist_ok=True)
                (mock_ws / "repo").mkdir(exist_ok=True)
                workspace_root = mock_ws
            openhands_config = config.openhands_config
            if openhands_config is None and OpenHandsConfig is not None:
                openhands_config = OpenHandsConfig(
                    model_name=resolved_model_raw,
                    max_iterations=config.openhands_max_iterations,
                    timeout_seconds=config.openhands_timeout,
                )
            openhands_extra_env = None
            evidence_dir = inst_dir / "evidence"
            if config.effective_guarded:
                evidence_dir.mkdir(parents=True, exist_ok=True)
                _write_guarded_run_started_event(evidence_dir, run_id, iid)
            else:
                evidence_dir.mkdir(parents=True, exist_ok=True)
            if config.effective_guarded and workspace_root and config.engine in ("openhands", "mock") and guard_shell.exists():
                pf_tmp = workspace_root / "scratch" / ".pf_tmp"
                try:
                    pf_tmp.mkdir(parents=True, exist_ok=True)
                except OSError:
                    pass
                tdir = str(pf_tmp.resolve()) if pf_tmp.is_dir() else ""
                openhands_extra_env = {
                    "SHELL": str(guard_shell.resolve()),
                    "PF_GUARD_WORKSPACE": str(workspace_root.resolve()),
                    "PF_GUARD_LEDGER_DIR": str(evidence_dir.resolve()),
                    "PF_GUARD_RUN_ID": run_id,
                    "PF_REPO_ROOT": str(repo_root),
                }
                if tdir:
                    openhands_extra_env["TMPDIR"] = tdir
                    openhands_extra_env["TMP"] = tdir
                    openhands_extra_env["TEMP"] = tdir
            else:
                openhands_extra_env = None
            if verbose_instance_logs:
                if workspace_root is not None:
                    _log(
                        "  workspace: paths root=%s repo=%s scratch=%s"
                        % (
                            str(workspace_root),
                            str(workspace_root / "repo"),
                            str(workspace_root / "scratch"),
                        )
                    )
                _log(
                    "  engine: config model=%s max_iterations=%s timeout=%ss guarded=%s"
                    % (
                        getattr(openhands_config, "model_name", resolved_model_raw),
                        getattr(openhands_config, "max_iterations", config.openhands_max_iterations),
                        getattr(openhands_config, "timeout_seconds", config.openhands_timeout),
                        str(config.effective_guarded).lower(),
                    )
                )
            t0 = time.perf_counter()
            engine_mode: Optional[str] = None
            engine_success: bool = True
            engine_error: Optional[str] = None
            model_patch = ""
            log_text = ""
            engine_trace: Optional[dict] = None
            try:
                if config.mode == "deterministic":
                    _log("  engine: deterministic (gold patch)")
                    model_patch = instance.patch or ""
                    log_text = (
                        f"[{datetime.now(timezone.utc).isoformat()}] Engine=deterministic (gold patch)\n"
                        f"instance_id={iid}\nrepo={instance.repo}\nbase_commit={instance.base_commit}\n"
                        f"patch_length={len(model_patch)}\n"
                    )
                    engine_trace = {"source": "deterministic", "prompts_sent": [], "tool_calls": [], "files_modified": []}
                    engine_mode = "deterministic"
                    engine_success = True
                    engine_error = None
                    events_path = evidence_dir / "events.jsonl"
                    if not events_path.exists():
                        events_path.write_text(
                            json.dumps({"mode": "deterministic", "instance_id": iid, "patch_from": "gold"}) + "\n",
                            encoding="utf-8",
                        )
                else:
                    _log("  engine: starting %s" % config.engine)
                    engine_mode = config.engine
                    try:
                        model_patch, log_text, engine_trace = instance_processor.run_engine(
                            instance.raw,
                            config.engine,
                            run_dir,
                            iid,
                            workspace_path=workspace_root,
                            task_text=task_text,
                            openhands_config=openhands_config,
                            openhands_extra_env=openhands_extra_env,
                        )
                        if config.engine == "openhands" and not (model_patch or "").strip():
                            engine_success = False
                            engine_error = (engine_trace.get("error") if engine_trace else None) or "empty patch"
                            _log("  engine: empty patch (recording engine_error)")
                        elif config.engine == "direct_agent" and not (model_patch or "").strip():
                            engine_success = False
                            engine_error = (engine_trace.get("error") if engine_trace else None) or "empty patch"
                            _log("  engine: direct_agent empty patch (engine_error=%s)" % (engine_error or "")[:240])
                        elif config.engine == "openhands" and not _openhands_trace_has_content(engine_trace):
                            model_patch = ""
                            engine_success = False
                            engine_error = "empty trace: no tool_calls, files_modified, or raw_events"
                            log_text = log_text + "\nengine_trace_empty=1"
                            _log("  engine: empty trace (treating as failure)")
                        elif engine_trace and engine_trace.get("error"):
                            engine_success = False
                            engine_error = (engine_error or str(engine_trace.get("error", "")))[:500]
                        else:
                            engine_success = True
                            engine_error = None
                    except Exception as e:
                        model_patch = ""
                        log_text = (
                            "[%s] Engine=%s raised: %s\ninstance_id=%s\n"
                            % (datetime.now(timezone.utc).isoformat(), config.engine, str(e)[:500], iid)
                        )
                        engine_trace = {
                            "error": str(e)[:500],
                            "prompts_sent": [],
                            "tool_calls": [],
                            "files_modified": [],
                        }
                        engine_success = False
                        engine_error = str(e)[:500]
                        _log("  engine: exception (recording engine_error)")
                        _eprint("Error: %s" % e)
            finally:
                wall_clock_s = time.perf_counter() - t0
                _log("  engine: done in %.1fs (patch_len=%d)" % (wall_clock_s, len(model_patch)))
                if verbose_instance_logs and isinstance(engine_trace, dict):
                    _log(
                        "  engine_trace: events=%d tool_calls=%d files_modified=%d timeout_origin=%s first_action_latency_s=%s first_file_edit_latency_s=%s"
                        % (
                            len(engine_trace.get("raw_events") or []),
                            len(engine_trace.get("tool_calls") or []),
                            len(engine_trace.get("files_modified") or []),
                            str(engine_trace.get("timeout_origin")),
                            str(engine_trace.get("first_action_latency_s")),
                            str(engine_trace.get("first_file_edit_latency_s")),
                        )
                    )
                    tdr = engine_trace.get("task_delivery_report") or {}
                    if tdr:
                        _log(
                            "  task_delivery: compaction=%s strategy=%s original=%s effective=%s critical_drop=%s"
                            % (
                                str(tdr.get("compaction_applied")),
                                str(tdr.get("strategy")),
                                str(tdr.get("original_len")),
                                str(tdr.get("max_task_chars")),
                                str(tdr.get("critical_drop")),
                            )
                        )
                if config.effective_guarded and write_compliance_summary is not None:
                    events_file = evidence_dir / "events.jsonl"
                    if events_file.exists() and build_compliance_summary_from_events_file is not None:
                        summary = build_compliance_summary_from_events_file(events_file, run_id=run_id)
                    elif PolicyComplianceSummary is not None:
                        summary = PolicyComplianceSummary(
                            run_id=run_id,
                            total_events=0,
                            total_tool_calls=0,
                            violations=0,
                            compliant=False,
                            violation_details=[],
                            reason_codes=[],
                            chain_tail_hash="",
                        )
                    else:
                        summary = None
                    if summary is not None:
                        write_compliance_summary(inst_dir / "policy_compliance_summary.json", summary)
                        log_text = log_text + "\npolicy_compliant=" + str(summary.compliant) + " violations=" + str(summary.violations)
            base_commit = (workspace_manifest_dict or {}).get("base_commit", "") or getattr(instance, "base_commit", "")
            resolved_commit = (workspace_manifest_dict or {}).get("resolved_commit", "")
            repo_dir = (workspace_root / "repo") if workspace_root else None
            is_timeout_fallback = bool(
                model_patch.strip().startswith("# git diff failed") and "TimeoutExpired" in model_patch
            )
            patch_capped_reason = None
            diff_stat_file = None
            empty_patch_reason: Optional[str] = None
            if not (model_patch or "").strip() and engine_error:
                if "empty trace" in (engine_error or "").lower() or "empty patch" in (engine_error or "").lower():
                    empty_patch_reason = "agent_no_changes"
            if len(model_patch) > MAX_PATCH_BYTES:
                _log("  patch: too large (%d bytes, max %d), emitting empty" % (len(model_patch), MAX_PATCH_BYTES))
                if repo_dir is not None:
                    _write_diff_stat_when_too_large(repo_dir, inst_dir, len(model_patch))
                    diff_stat_file = "diff_stat_when_too_large.txt"
                patch_capped_reason = "size"
                empty_patch_reason = "patch_too_large"
                model_patch = ""
                log_text = log_text + "\npatch_too_large=1"
            # Apply check runs in a temporary worktree; main workspace is unchanged so replay capture (below) sees agent edits.
            if repo_dir is not None and repo_dir.is_dir():
                t_apply = time.perf_counter()
                applies, apply_report = run_patch_apply_check(
                    repo_dir, model_patch, base_commit, resolved_commit
                )
                if patch_capped_reason is not None:
                    apply_report["patch_capped_reason"] = patch_capped_reason
                if patch_capped_reason is None and is_timeout_fallback:
                    apply_report["patch_capped_reason"] = "timeout"
                    empty_patch_reason = empty_patch_reason or "diff_timeout"
                if diff_stat_file is not None:
                    apply_report["diff_stat_file"] = diff_stat_file
                if not applies:
                    if empty_patch_reason is None:
                        # Empty engine patch + apply check fails with "empty patch" is not a merge conflict.
                        if not (model_patch or "").strip():
                            empty_patch_reason = "agent_no_changes"
                        else:
                            empty_patch_reason = "apply_check_failed"
                    model_patch = ""
                    log_text = log_text + "\npatch_apply_check=failed"
                    _log("  patch_apply_check: failed (emitting empty patch)")
                if empty_patch_reason is not None:
                    apply_report["empty_patch_reason"] = empty_patch_reason
                (inst_dir / PATCH_APPLY_CHECK_FILENAME).write_text(
                    json.dumps(apply_report, indent=2), encoding="utf-8"
                )
                if verbose_instance_logs:
                    _log(
                        "  patch_apply_check: done in %.2fs applies=%s empty_patch_reason=%s"
                        % (
                            time.perf_counter() - t_apply,
                            str(applies).lower(),
                            str(empty_patch_reason),
                        )
                    )
            else:
                applies = False
                empty_patch_reason = empty_patch_reason or "workspace_missing_or_failed"
                apply_report = {
                    "applies": False,
                    "stderr": "no workspace repo for apply check",
                    "base_commit": base_commit,
                    "resolved_commit": resolved_commit,
                    "git_version": "",
                    "empty_patch_reason": empty_patch_reason,
                }
                try:
                    v = subprocess.run(
                        ["git", "--version"],
                        capture_output=True,
                        text=True,
                        timeout=5,
                    )
                    apply_report["git_version"] = (v.stdout or "").strip()[:GIT_VERSION_MAX_LEN]
                except Exception:
                    apply_report["git_version"] = "unknown"
                (inst_dir / PATCH_APPLY_CHECK_FILENAME).write_text(
                    json.dumps(apply_report, indent=2), encoding="utf-8"
                )
            if (model_patch or "").strip() == "" and config.effective_guarded and summary is not None and getattr(summary, "violations", 0) > 0 and empty_patch_reason is None:
                empty_patch_reason = "guard_denial_prevented_writes"
                try:
                    pac = json.loads((inst_dir / PATCH_APPLY_CHECK_FILENAME).read_text(encoding="utf-8"))
                    pac["empty_patch_reason"] = empty_patch_reason
                    (inst_dir / PATCH_APPLY_CHECK_FILENAME).write_text(json.dumps(pac, indent=2), encoding="utf-8")
                except (OSError, json.JSONDecodeError):
                    pass
            if empty_patch_reason is not None:
                (inst_dir / "empty_patch_reason.txt").write_text(empty_patch_reason + "\n", encoding="utf-8")
            evidence_writer_out.write(
                iid,
                model_patch,
                log_text,
                workspace_manifest_sha256=workspace_sha,
                workspace_manifest_dict=workspace_manifest_dict,
                engine_trace_dict=engine_trace,
                policy_name=policy_name,
                policy_hash=policy_hash_value,
                engine_mode=engine_mode,
                engine_success=engine_success,
                engine_error=engine_error,
            )
            if verbose_instance_logs:
                _log("  evidence: wrote instance bundle to %s" % str(inst_dir))
            if engine_trace and engine_trace.get("openhands_stderr_tail"):
                (inst_dir / "openhands_stderr_tail.txt").write_text(
                    engine_trace["openhands_stderr_tail"], encoding="utf-8"
                )
            replay_bundle_hash = ""
            if (
                build_replay_bundle is not None
                and write_replay_bundle is not None
                and workspace_root is not None
                and engine_trace is not None
            ):
                repo_dir = workspace_root / "repo"
                if repo_dir.is_dir():
                    try:
                        bundle = build_replay_bundle(
                            inst_dir,
                            repo_path=repo_dir,
                            engine_trace_dict=engine_trace,
                            model_patch=model_patch,
                        )
                        write_replay_bundle(inst_dir, bundle)
                        replay_bundle_hash = _replay_bundle_hash(bundle)
                    except Exception as _e:
                        pass  # Replay capture is best-effort
            if build_cost_report is not None and write_cost_report is not None:
                tool_calls_list = (engine_trace or {}).get("tool_calls") or []
                prompts_list = (engine_trace or {}).get("prompts_sent") or []
                cost_rec = build_cost_report(
                    instance_id=iid,
                    model_name=effective_model_name,
                    prompt_tokens=int((engine_trace or {}).get("prompt_tokens", 0)),
                    completion_tokens=int((engine_trace or {}).get("completion_tokens", 0)),
                    iterations=len(prompts_list),
                    tool_calls=len(tool_calls_list),
                    wall_clock_s=wall_clock_s,
                    replay_s=0.0,
                    proof_s=0.0,
                    guarded=config.effective_guarded,
                    run_id=run_id,
                    engine_error=engine_error,
                )
                cost_reports.append(cost_rec)
                write_cost_report(inst_dir, cost_rec)
                # Per-instance timing and termination for stress summary and regression detection.
                max_steps_reached = (
                    config.openhands_max_iterations > 0
                    and len(prompts_list) >= config.openhands_max_iterations
                )
                timeout_origin = None
                if isinstance(engine_trace, dict):
                    timeout_origin = engine_trace.get("timeout_origin")
                timeout_reached = bool(
                    (timeout_origin == "subprocess_wall_timeout")
                    or (
                        engine_error
                        and (
                            "timeout" in (engine_error or "").lower()
                            or "timed out" in (engine_error or "").lower()
                            or "TimeoutExpired" in (engine_error or "")
                        )
                    )
                )
                if timeout_reached:
                    termination_reason = "timeout"
                elif max_steps_reached:
                    termination_reason = "max_steps"
                elif empty_patch_reason == "guard_denial_prevented_writes":
                    termination_reason = "guard_denial"
                elif empty_patch_reason:
                    termination_reason = "empty_patch"
                elif engine_error:
                    termination_reason = "error"
                else:
                    termination_reason = "success"
                timing = {
                    "wall_clock_s": round(wall_clock_s, 4),
                    "tool_calls": len(tool_calls_list),
                    "max_steps_reached": max_steps_reached,
                    "timeout_reached": timeout_reached,
                    "termination_reason": termination_reason,
                }
                (inst_dir / TIMING_JSON_FILENAME).write_text(
                    json.dumps(timing, indent=2), encoding="utf-8"
                )
                cost_metrics = {k: v for k, v in cost_rec.items() if k != "instance_id"}
            else:
                cost_metrics = {}
            emit_predictions_line(out_tmp, iid, model_patch, model_name)
            instances_written += 1
            if verbose_instance_logs:
                _log(
                    "  instance done: total_elapsed=%.1fs termination=%s empty_patch_reason=%s"
                    % (
                        time.perf_counter() - t_instance_start,
                        termination_reason if "termination_reason" in locals() else "unknown",
                        str(empty_patch_reason),
                    )
                )
            pfmeta_rows.append(build_pfmeta_line(
                iid,
                run_id,
                policy_hash_value,
                _trace_hash(engine_trace),
                replay_bundle_hash,
                None,
                cost_metrics,
                empty_patch_reason=empty_patch_reason,
            ))

        os.replace(out_tmp, config.out)
        status = "complete"
    except Exception as e:
        first_error = str(e)
        status = "partial" if instances_written > 0 else "failed"
        raise
    finally:
        run_status = {
            "run_id": run_id,
            "status": status,
            "instances_planned": instances_planned,
            "instances_written": instances_written,
            "first_error": first_error,
            "created_at": datetime.now(timezone.utc).isoformat(),
        }
        out_dir = Path(config.out).parent
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / "run_status.json").write_text(json.dumps(run_status, indent=2), encoding="utf-8")
        pred_path = Path(config.out)
        if pred_path.exists():
            (out_dir / "predictions.sha256").write_text(
                hashlib.sha256(pred_path.read_bytes()).hexdigest() + "\n",
                encoding="utf-8",
            )

    proof_time_s = 0.0
    if config.prove and run_proof is not None and write_proof_failure is not None:
        repo_root = Path(__file__).resolve().parent.parent.parent
        proofs_dir = Path(config.proofs_dir) if config.proofs_dir else (repo_root / "spec-templates" / "v1" / "proofs")
        t_proof0 = time.perf_counter()
        success, artifact_hash, failure = run_proof(proofs_dir, run_dir)
        proof_time_s = time.perf_counter() - t_proof0
        if success:
            _stdout_line_safe("Proof:", "ok", f"artifact_hash={artifact_hash}")
        else:
            if failure is not None:
                write_proof_failure(run_dir, failure)
            _eprint("Proof: failed see %s" % (run_dir / "proof_failure.json",))

    replay_time_s = 0.0  # Replay is run separately (pf bench swebench replay); optional future: time it here
    for rec in cost_reports:
        rec["proof_s"] = round(proof_time_s, 4)
        rec["replay_s"] = round(replay_time_s, 4)
    # Backfill cost_report for any instance that has patch_apply_check but missed cost_rec (e.g. exception mid-loop).
    if build_cost_report is not None and write_cost_report is not None:
        cost_report_iids = {rec["instance_id"] for rec in cost_reports}
        for iid in instance_ids_planned:
            if iid in cost_report_iids:
                continue
            inst_dir = run_dir / sanitize_instance_id(iid)
            if not (inst_dir / PATCH_APPLY_CHECK_FILENAME).exists():
                continue
            backfill_rec = build_cost_report(
                instance_id=iid,
                model_name=effective_model_name,
                prompt_tokens=0,
                completion_tokens=0,
                iterations=0,
                tool_calls=0,
                wall_clock_s=0.0,
                replay_s=round(replay_time_s, 4),
                proof_s=round(proof_time_s, 4),
                guarded=config.effective_guarded,
                run_id=run_id,
                engine_error=None,
            )
            cost_reports.append(backfill_rec)
    if write_cost_report is not None:
        for rec in cost_reports:
            inst_dir = run_dir / sanitize_instance_id(rec["instance_id"])
            write_cost_report(inst_dir, rec)
    SummaryWriter(write_summary).write_run_summary(
        run_dir,
        cost_reports,
        run_id,
        config.effective_guarded,
        instance_ids_planned=instance_ids_planned,
        effective_model_name=effective_model_name,
    )

    proof_artifact_hash_value: Optional[str] = None
    proof_hash_file = run_dir / "proof_artifact_hash.txt"
    if proof_hash_file.exists():
        try:
            proof_artifact_hash_value = proof_hash_file.read_text(encoding="utf-8").strip()
        except OSError:
            pass
    for rec in pfmeta_rows:
        if proof_artifact_hash_value:
            rec["proof_artifact_hash"] = proof_artifact_hash_value

    pfmeta_path = _pfmeta_path(config.out)
    write_pfmeta_jsonl(pfmeta_path, pfmeta_rows)

    _stdout_line_safe("Run ID:", run_id)
    _stdout_line_safe("Predictions:", config.out)
    _stdout_line_safe("PF metadata:", str(pfmeta_path))
    _stdout_line_safe("Evidence:", str(run_dir))
    _stdout_line_safe("Instances:", len(instances))
    return 0


def main() -> int:
    """Parse CLI, validate RunConfig, delegate to `_execute_run`."""
    parser = build_argument_parser()
    args = parser.parse_args()
    try:
        config = RunConfig.from_args(args)
    except ValueError as e:
        print(str(e), file=sys.stderr)
        return 1
    errors = config.validate()
    if errors:
        for err in errors:
            print(err, file=sys.stderr)
        return 1
    return _execute_run(config)

if __name__ == "__main__":
    try:
        sys.exit(main())
    except BrokenPipeError:
        # Stdout/stderr closed (e.g. `runner 2>&1 | head`); artifacts are already on disk.
        sys.exit(0)
