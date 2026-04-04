# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Direct agent engine: lightweight OpenAI-compatible loop without OpenHands runtime.

from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Optional

try:
    from .openhands_engine import (
        EngineTrace,
        SolveResult,
        _PrimeStrictCompatProxy,
        _compact_task_text_for_openhands,
        _extract_latency_metrics_from_events,
        _compute_timeout_budget_phases,
        _get_patch_from_repo,
        _get_patch_from_repo_for_paths,
        _get_files_modified_from_repo,
        DIFF_STAT_FILE_THRESHOLD,
        NAME_ONLY_QUICK_TIMEOUT,
    )
except ImportError:
    from engines.openhands_engine import (  # type: ignore[no-redef]
        EngineTrace,
        SolveResult,
        _PrimeStrictCompatProxy,
        _compact_task_text_for_openhands,
        _extract_latency_metrics_from_events,
        _compute_timeout_budget_phases,
        _get_patch_from_repo,
        _get_patch_from_repo_for_paths,
        _get_files_modified_from_repo,
        DIFF_STAT_FILE_THRESHOLD,
        NAME_ONLY_QUICK_TIMEOUT,
    )

try:
    from ..provider_env import (
        effective_llm_model as _effective_llm_model,
        llm_credentials as _llm_credentials,
        normalize_openhands_provider as _normalize_provider,
        prime_team_id as _prime_team_id,
    )
except ImportError:
    try:
        from bench.swebench.provider_env import (  # type: ignore[no-redef]
            effective_llm_model as _effective_llm_model,
            llm_credentials as _llm_credentials,
            normalize_openhands_provider as _normalize_provider,
            prime_team_id as _prime_team_id,
        )
    except ImportError:
        from provider_env import (  # type: ignore[no-redef]
            effective_llm_model as _effective_llm_model,
            llm_credentials as _llm_credentials,
            normalize_openhands_provider as _normalize_provider,
            prime_team_id as _prime_team_id,
        )


@dataclass
class DirectAgentConfig:
    model_name: str = "gpt-4o-mini"
    max_iterations: int = 3
    temperature: float = 0.0
    timeout_seconds: Optional[int] = 480


def _safe_repo_path(repo_dir: Path, rel_path: str) -> Optional[Path]:
    p = (repo_dir / rel_path).resolve()
    try:
        p.relative_to(repo_dir.resolve())
    except ValueError:
        return None
    return p


def _repo_file_excerpt(repo_dir: Path, max_files: int = 60) -> str:
    try:
        proc = subprocess.run(
            ["git", "ls-files"],
            cwd=repo_dir,
            capture_output=True,
            text=True,
            timeout=20,
        )
        files = [ln.strip() for ln in (proc.stdout or "").splitlines() if ln.strip()]
        if not files:
            return ""
        return "\n".join(files[:max_files])
    except Exception:
        return ""


def _build_system_prompt() -> str:
    return (
        "You are a coding agent operating on a local git repository.\n"
        "Return STRICT JSON only with an 'actions' array.\n"
        "Allowed actions:\n"
        "1) {\"type\":\"edit_file\",\"path\":\"relative/path\",\"old_string\":\"...\",\"new_string\":\"...\"}\n"
        "2) {\"type\":\"write_file\",\"path\":\"relative/path\",\"content\":\"...\"}\n"
        "3) {\"type\":\"finish\",\"summary\":\"...\"}\n"
        "Rules:\n"
        "- Use exact old_string for edit_file.\n"
        "- Keep edits minimal and targeted to the issue.\n"
        "- Prefer one or few precise edits over broad refactors.\n"
        "- If no further edits are needed, return finish.\n"
    )


def _call_openai_compatible_chat(
    *,
    base_url: str,
    api_key: str,
    model: str,
    messages: list[dict[str, Any]],
    timeout_s: int,
    temperature: float = 0.0,
    provider: str = "openai",
) -> tuple[str, dict[str, Any]]:
    url = base_url.rstrip("/") + "/chat/completions"
    payload = {
        "model": model,
        "messages": messages,
        "temperature": temperature,
    }
    body = json.dumps(payload).encode("utf-8")
    # Avoid default Python-urllib User-Agent; some CDNs (e.g. Cloudflare) return 403/1010 for it.
    _ua = (os.environ.get("PF_LLM_HTTP_USER_AGENT") or "").strip()
    if not _ua:
        _ua = "Mozilla/5.0 (compatible; ProvabilityFabric-SWE-bench/1.0)"
    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json",
        "Authorization": f"Bearer {api_key}",
        "User-Agent": _ua,
    }
    if provider == "prime_intellect":
        team_id = _prime_team_id()
        if team_id:
            headers["X-Prime-Team-ID"] = team_id
    req = urllib.request.Request(
        url=url,
        data=body,
        method="POST",
        headers=headers,
    )
    with urllib.request.urlopen(req, timeout=max(30, timeout_s)) as resp:
        raw = resp.read().decode("utf-8", errors="replace")
    data = json.loads(raw)
    choices = data.get("choices") or []
    if not choices:
        return "", data
    msg = choices[0].get("message") or {}
    content = msg.get("content") or ""
    if isinstance(content, list):
        parts: list[str] = []
        for item in content:
            if isinstance(item, dict) and item.get("type") == "text" and item.get("text"):
                parts.append(str(item["text"]))
        content = "\n".join(parts)
    return str(content), data


def _extract_json_blob(text: str) -> Optional[dict[str, Any]]:
    s = (text or "").strip()
    if not s:
        return None
    try:
        obj = json.loads(s)
        return obj if isinstance(obj, dict) else None
    except json.JSONDecodeError:
        pass
    start = s.find("{")
    end = s.rfind("}")
    if start >= 0 and end > start:
        try:
            obj = json.loads(s[start : end + 1])
            return obj if isinstance(obj, dict) else None
        except json.JSONDecodeError:
            return None
    return None


def _sanitize_patch_text(patch: str) -> tuple[str, bool]:
    """Normalize patch format and strip non-diff prelude text."""
    raw = (patch or "").replace("\r\n", "\n")
    lines = raw.splitlines()
    start_idx = 0
    for i, ln in enumerate(lines):
        if ln.startswith("diff --git "):
            start_idx = i
            break
    out = "\n".join(lines[start_idx:]).strip()
    changed = out != (patch or "").strip()
    if out and not out.endswith("\n"):
        out += "\n"
    return out, changed


def _patch_touched_paths(patch: str) -> list[str]:
    paths: list[str] = []
    for ln in (patch or "").splitlines():
        if not ln.startswith("diff --git "):
            continue
        m = re.match(r"^diff --git a/(.+?) b/(.+)$", ln.strip())
        if not m:
            continue
        paths.append(m.group(2))
    return list(dict.fromkeys(paths))


def _git_apply_check(repo_dir: Path, patch: str) -> tuple[bool, str]:
    if not (patch or "").strip():
        return False, "empty patch"
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", delete=False, suffix=".patch") as tf:
        tf.write(patch)
        p = tf.name
    try:
        proc = subprocess.run(
            ["git", "apply", "--check", p],
            cwd=repo_dir,
            capture_output=True,
            text=True,
            timeout=20,
        )
        if proc.returncode == 0:
            return True, ""
        # Patch was produced from current working tree state; reverse-check validates structure.
        rev = subprocess.run(
            ["git", "apply", "--check", "--reverse", p],
            cwd=repo_dir,
            capture_output=True,
            text=True,
            timeout=20,
        )
        if rev.returncode == 0:
            return True, ""
        msg = (proc.stderr or proc.stdout or rev.stderr or rev.stdout or "").strip()
        return False, msg
    finally:
        try:
            os.unlink(p)
        except OSError:
            pass


def _classify_patch_failure(patch: str, stderr_text: str, touched_paths: list[str], repo_dir: Path) -> str:
    if not (patch or "").strip():
        return "empty_patch"
    s = (stderr_text or "").lower()
    if "corrupt patch" in s or "malformed patch" in s:
        return "malformed_patch"
    if "patch failed" in s or "hunk" in s:
        return "context_drift"
    for rp in touched_paths:
        pp = _safe_repo_path(repo_dir, rp)
        if pp is None:
            return "invalid_path"
    missing = []
    for rp in touched_paths:
        pp = _safe_repo_path(repo_dir, rp)
        if pp is not None and not pp.exists():
            missing.append(rp)
    if missing:
        return "wrong_file_target"
    return "apply_check_failed"


def _attempt_one_repair_iteration(
    *,
    repo_dir: Path,
    messages: list[dict[str, Any]],
    base_url: str,
    api_key: str,
    model: str,
    remaining_s: int,
    temperature: float,
) -> tuple[bool, str]:
    """Constrained repair: request exactly one concrete edit action."""
    repair_messages = list(messages)
    repair_messages.append(
        {
            "role": "user",
            "content": (
                "Repair mode: produce STRICT JSON with exactly one action to create a valid, non-empty patch. "
                "Do not return finish unless one edit/write action has succeeded."
            ),
        }
    )
    content, _ = _call_openai_compatible_chat(
        base_url=base_url,
        api_key=api_key,
        model=model,
        messages=repair_messages,
        timeout_s=max(10, remaining_s),
        temperature=temperature,
        provider=_normalize_provider(),
    )
    parsed = _extract_json_blob(content)
    if not parsed:
        return False, "repair_json_invalid"
    actions = parsed.get("actions")
    if not isinstance(actions, list):
        return False, "repair_actions_missing"
    for action in actions:
        if not isinstance(action, dict):
            continue
        at = str(action.get("type") or "").strip().lower()
        if at == "edit_file":
            rel = str(action.get("path") or "").strip()
            old = str(action.get("old_string") or "")
            new = str(action.get("new_string") or "")
            pp = _safe_repo_path(repo_dir, rel)
            if pp is None or not pp.exists():
                continue
            cur = pp.read_text(encoding="utf-8", errors="replace")
            if old and old in cur:
                pp.write_text(cur.replace(old, new, 1), encoding="utf-8")
                return True, ""
        if at == "write_file":
            rel = str(action.get("path") or "").strip()
            body = str(action.get("content") or "")
            pp = _safe_repo_path(repo_dir, rel)
            if pp is None:
                continue
            pp.parent.mkdir(parents=True, exist_ok=True)
            pp.write_text(body, encoding="utf-8")
            return True, ""
    return False, "repair_no_applicable_action"


def solve(
    workspace_path: str | Path,
    task_text: str,
    config: Optional[Any] = None,
    extra_env: Optional[dict] = None,
) -> SolveResult:
    workspace_path = Path(workspace_path)
    repo_dir = workspace_path / "repo"
    scratch_dir = workspace_path / "scratch"
    scratch_dir.mkdir(parents=True, exist_ok=True)

    cfg = config if config is not None else DirectAgentConfig()
    model_raw = str(getattr(cfg, "model_name", "") or "").strip() or "gpt-4o-mini"
    max_iterations = int(getattr(cfg, "max_iterations", 3) or 3)
    timeout_seconds = int(getattr(cfg, "timeout_seconds", 480) or 480)
    temperature = float(getattr(cfg, "temperature", 0.0) or 0.0)

    trace = EngineTrace()
    trace.execution_mode = "direct_agent"
    trace.cli_mode_forced = False
    trace.mode_reason = "native direct agent runtime"
    trace.openhands_library_core_available = False
    trace.prime_proxy_enabled = _normalize_provider() == "prime_intellect"

    # Keep same compaction/diagnostic semantics as OpenHands for comparability.
    max_task_chars = max(400, int(os.environ.get("PF_OPENHANDS_MAX_TASK_CHARS", "12000") or "12000"))
    task_text_effective, task_delivery_report = _compact_task_text_for_openhands(
        task_text=task_text,
        scratch_dir=scratch_dir,
        max_task_chars=max_task_chars,
    )
    trace.task_delivery_report = task_delivery_report
    try:
        (scratch_dir / "pf_task_delivery_report.json").write_text(
            json.dumps(task_delivery_report, indent=2),
            encoding="utf-8",
        )
    except OSError:
        pass

    api_key, base_url, provider = _llm_credentials()
    if not api_key:
        trace.timeout_origin = None
        return SolveResult(
            patch_diff_str="",
            trace=trace,
            success=False,
            error="Missing provider API key for direct_agent",
        )
    if not base_url:
        trace.timeout_origin = None
        return SolveResult(
            patch_diff_str="",
            trace=trace,
            success=False,
            error="Missing base URL for direct_agent provider routing",
        )
    model = _effective_llm_model(provider, model_raw)

    # Prime: use the same local strict-compat proxy as OpenHands subprocess path.
    # Personal accounts do not require PRIME_TEAM_ID; optional header is only added when set.
    compat_proxy: Optional[_PrimeStrictCompatProxy] = None
    chat_base = base_url
    if provider == "prime_intellect":
        team_id = (os.environ.get("PRIME_TEAM_ID") or "").strip()
        extra = {"X-Prime-Team-ID": team_id} if team_id else {}
        compat_proxy = _PrimeStrictCompatProxy(base_url, extra_headers=extra)
        chat_base = compat_proxy.start()
        trace.prime_proxy_enabled = True

    repo_files = _repo_file_excerpt(repo_dir)
    messages: list[dict[str, Any]] = [
        {"role": "system", "content": _build_system_prompt()},
        {
            "role": "user",
            "content": (
                "Task:\n"
                + task_text_effective
                + "\n\nRepository files (subset):\n"
                + (repo_files or "(unavailable)")
                + "\n"
            ),
        },
    ]

    def _run_agent_loop() -> SolveResult:
        t0 = time.perf_counter()
        deadline = t0 + timeout_seconds
        edited_paths: list[str] = []
        finish_seen = False
        for it in range(max_iterations):
            if time.perf_counter() >= deadline:
                trace.timeout_origin = "agent_loop_timeout"
                break
            remaining = max(1, int(deadline - time.perf_counter()))
            step_t0 = time.perf_counter()
            try:
                content, raw_resp = _call_openai_compatible_chat(
                    base_url=chat_base,
                    api_key=api_key,
                    model=model,
                    messages=messages,
                    timeout_s=remaining,
                    temperature=temperature,
                    provider=provider,
                )
            except urllib.error.HTTPError as e:
                detail = str(e)[:400]
                try:
                    body = e.read().decode("utf-8", errors="replace")[:800]
                    if body:
                        detail = f"{detail} body={body}"
                except Exception:
                    pass
                trace.raw_events.append(
                    {
                        "kind": "AgentErrorEvent",
                        "iteration": it + 1,
                        "code": int(getattr(e, "code", 0) or 0),
                        "detail": detail,
                        "timestamp": time.time(),
                    }
                )
                return SolveResult("", trace, False, f"direct_agent HTTPError: {detail}")
            except Exception as e:
                trace.raw_events.append(
                    {
                        "kind": "AgentErrorEvent",
                        "iteration": it + 1,
                        "detail": str(e)[:400],
                        "timestamp": time.time(),
                    }
                )
                return SolveResult("", trace, False, f"direct_agent exception: {e}")

            trace.raw_events.append(
                {
                    "kind": "MessageEvent",
                    "iteration": it + 1,
                    "content": content[:4000],
                    "latency_s": round(time.perf_counter() - step_t0, 4),
                    "timestamp": time.time(),
                    "usage": (raw_resp.get("usage") or {}),
                }
            )
            parsed = _extract_json_blob(content)
            if not parsed:
                messages.append(
                    {
                        "role": "user",
                        "content": "Response was not valid JSON. Return STRICT JSON with an actions array.",
                    }
                )
                continue

            actions = parsed.get("actions")
            if not isinstance(actions, list):
                messages.append({"role": "user", "content": "Missing actions list. Return actions JSON only."})
                continue

            action_feedback: list[str] = []
            for action in actions:
                if not isinstance(action, dict):
                    continue
                at = str(action.get("type") or "").strip().lower()
                if at == "finish":
                    trace.tool_calls.append({"name": "finish", "args": {}})
                    trace.raw_events.append(
                        {"kind": "ActionEvent", "tool_name": "finish", "timestamp": time.time()}
                    )
                    finish_seen = True
                    action_feedback.append("finish acknowledged")
                    break

                if at == "edit_file":
                    rel = str(action.get("path") or "").strip()
                    old = str(action.get("old_string") or "")
                    new = str(action.get("new_string") or "")
                    p = _safe_repo_path(repo_dir, rel)
                    trace.tool_calls.append({"name": "edit_file", "args": {"path": rel}})
                    trace.raw_events.append(
                        {"kind": "ActionEvent", "tool_name": "edit_file", "path": rel, "timestamp": time.time()}
                    )
                    if p is None or not p.exists():
                        action_feedback.append(f"edit_file failed: invalid or missing path {rel}")
                        continue
                    try:
                        cur = p.read_text(encoding="utf-8", errors="replace")
                        if old and old in cur:
                            nxt = cur.replace(old, new, 1)
                            p.write_text(nxt, encoding="utf-8")
                            edited_paths.append(rel)
                            action_feedback.append(f"edit_file applied: {rel}")
                        else:
                            action_feedback.append(f"edit_file failed: old_string not found in {rel}")
                    except OSError as e:
                        action_feedback.append(f"edit_file failed: {rel}: {str(e)[:120]}")
                    continue

                if at == "write_file":
                    rel = str(action.get("path") or "").strip()
                    content_new = str(action.get("content") or "")
                    p = _safe_repo_path(repo_dir, rel)
                    trace.tool_calls.append({"name": "write_file", "args": {"path": rel}})
                    trace.raw_events.append(
                        {"kind": "ActionEvent", "tool_name": "write_file", "path": rel, "timestamp": time.time()}
                    )
                    if p is None:
                        action_feedback.append(f"write_file failed: invalid path {rel}")
                        continue
                    try:
                        p.parent.mkdir(parents=True, exist_ok=True)
                        p.write_text(content_new, encoding="utf-8")
                        edited_paths.append(rel)
                        action_feedback.append(f"write_file applied: {rel}")
                    except OSError as e:
                        action_feedback.append(f"write_file failed: {rel}: {str(e)[:120]}")
                    continue

                action_feedback.append(f"unsupported action type: {at}")

            if finish_seen:
                break
            messages.append(
                {
                    "role": "user",
                    "content": "Action results:\n- " + "\n- ".join(action_feedback) + "\nContinue with JSON actions.",
                }
            )

        trace.files_modified = list(dict.fromkeys(edited_paths))
        if not trace.files_modified:
            trace.files_modified = _get_files_modified_from_repo(repo_dir, timeout=NAME_ONLY_QUICK_TIMEOUT)
        paths = trace.files_modified or []
        if paths:
            patch = _get_patch_from_repo_for_paths(repo_dir, paths[:DIFF_STAT_FILE_THRESHOLD])
        else:
            patch = _get_patch_from_repo(repo_dir)

        patch, sanitized_changed = _sanitize_patch_text(patch)
        trace.patch_sanitize_applied = sanitized_changed
        touched_paths = _patch_touched_paths(patch)
        check_ok, check_stderr = _git_apply_check(repo_dir, patch)
        trace.patch_apply_check_passed = check_ok
        if not check_ok:
            trace.patch_failure_type = _classify_patch_failure(patch, check_stderr, touched_paths, repo_dir)
            # One constrained repair attempt (not a full re-solve).
            trace.patch_repair_attempted = True
            remaining = max(1, int(deadline - time.perf_counter()))
            if remaining > 0:
                try:
                    repaired, repair_err = _attempt_one_repair_iteration(
                        repo_dir=repo_dir,
                        messages=messages,
                        base_url=chat_base,
                        api_key=api_key,
                        model=model,
                        remaining_s=remaining,
                        temperature=temperature,
                    )
                    if repaired:
                        trace.files_modified = _get_files_modified_from_repo(repo_dir, timeout=NAME_ONLY_QUICK_TIMEOUT)
                        rpaths = trace.files_modified or []
                        if rpaths:
                            patch = _get_patch_from_repo_for_paths(repo_dir, rpaths[:DIFF_STAT_FILE_THRESHOLD])
                        else:
                            patch = _get_patch_from_repo(repo_dir)
                        patch, _ = _sanitize_patch_text(patch)
                        check_ok, check_stderr = _git_apply_check(repo_dir, patch)
                        trace.patch_apply_check_passed = check_ok
                        trace.patch_repair_success = check_ok
                        if check_ok:
                            trace.patch_failure_type = ""
                        else:
                            t2 = _patch_touched_paths(patch)
                            trace.patch_failure_type = _classify_patch_failure(patch, check_stderr, t2, repo_dir)
                    else:
                        trace.patch_repair_success = False
                        if not trace.patch_failure_type:
                            trace.patch_failure_type = repair_err
                except Exception as e:
                    trace.patch_repair_success = False
                    if not trace.patch_failure_type:
                        trace.patch_failure_type = f"repair_exception:{str(e)[:120]}"

        sb, ab, fb = _compute_timeout_budget_phases(timeout_seconds)
        trace.startup_budget_s = sb
        trace.action_budget_s = ab
        trace.finalization_budget_s = fb
        la, le = _extract_latency_metrics_from_events(trace.raw_events or [])
        trace.first_action_latency_s = la
        trace.first_file_edit_latency_s = le
        if trace.timeout_origin is None and time.perf_counter() >= deadline:
            trace.timeout_origin = "agent_loop_timeout"
        trace.subprocess_timeout_seconds = timeout_seconds

        success = bool(patch.strip()) and bool(trace.patch_apply_check_passed is not False)
        if success:
            err = None
        elif trace.patch_failure_type:
            err = f"patch_quality_failed:{trace.patch_failure_type}"
        else:
            err = "empty patch" if finish_seen else "no successful edit actions"
        return SolveResult(
            patch_diff_str=patch,
            trace=trace,
            success=success,
            error=err,
        )

    try:
        return _run_agent_loop()
    finally:
        if compat_proxy is not None:
            try:
                compat_proxy.close()
            except Exception:
                pass

