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
        "Return STRICT JSON only. The root object MUST have key \"actions\" whose value is a JSON array "
        "(possibly empty only if you then add finish in the same array).\n"
        "Example root: {\"actions\":[{\"type\":\"edit_file\",\"path\":\"src/x.py\",\"old_string\":\"a\",\"new_string\":\"b\"}]}\n"
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


def _assistant_text_from_completion(data: dict[str, Any]) -> str:
    """Extract assistant text from /chat/completions JSON (OpenAI + Gemini-compatible variants)."""
    choices = data.get("choices") or []
    if not choices or not isinstance(choices[0], dict):
        return ""
    ch0 = choices[0]
    msg = ch0.get("message") if isinstance(ch0.get("message"), dict) else {}
    content = msg.get("content")
    if isinstance(content, str) and content.strip():
        return content
    if isinstance(content, list):
        parts: list[str] = []
        for item in content:
            if not isinstance(item, dict):
                continue
            t = str(item.get("type") or "")
            if t in (
                "text",
                "output_text",
                "input_text",
                "reasoning",
                "thinking",
                "reasoning_content",
            ):
                txt = item.get("text")
                if txt is None and isinstance(item.get("content"), str):
                    txt = item.get("content")
                if txt:
                    parts.append(str(txt))
            elif item.get("text"):
                parts.append(str(item["text"]))
            elif isinstance(item.get("content"), str) and item["content"].strip():
                parts.append(str(item["content"]))
        if parts:
            return "\n".join(parts)
    for rk in ("reasoning_content", "reasoning"):
        rv = msg.get(rk)
        if isinstance(rv, str) and rv.strip():
            return rv
    ref = msg.get("refusal")
    if isinstance(ref, str) and ref.strip():
        return ref
    tx = ch0.get("text")
    if isinstance(tx, str) and tx.strip():
        return tx
    # Some gateways put the payload at the top level.
    ot = data.get("output_text")
    if isinstance(ot, str) and ot.strip():
        return ot
    return ""


def _coerce_actions_list(parsed: dict[str, Any]) -> Optional[list[Any]]:
    """
    Normalize model JSON into an actions list.
    Many models omit the top-level \"actions\" key or nest it; json_object mode still allows arbitrary keys.
    """
    if not isinstance(parsed, dict):
        return None
    a = parsed.get("actions")
    if isinstance(a, list):
        return a
    t = str(parsed.get("type") or "").strip().lower()
    if t in ("edit_file", "write_file", "finish"):
        return [parsed]
    single = parsed.get("action")
    if isinstance(single, dict):
        return [single]
    for k in ("result", "data", "output", "response", "tool_calls"):
        inner = parsed.get(k)
        if isinstance(inner, list) and inner and isinstance(inner[0], dict):
            # e.g. "tool_calls": [{"function": {...}}] — not our schema; skip
            continue
        if isinstance(inner, dict):
            ia = inner.get("actions")
            if isinstance(ia, list):
                return ia
            it = str(inner.get("type") or "").strip().lower()
            if it in ("edit_file", "write_file", "finish"):
                return [inner]
    return None


def _extract_actions_from_tool_calls(raw_resp: dict[str, Any]) -> Optional[list[Any]]:
    """When message.content is empty but the model emitted OpenAI-style tool_calls with JSON arguments."""
    choices = raw_resp.get("choices") or []
    if not choices or not isinstance(choices[0], dict):
        return None
    msg = choices[0].get("message")
    if not isinstance(msg, dict):
        return None
    tc = msg.get("tool_calls")
    if not isinstance(tc, list):
        return None
    for call in tc:
        if not isinstance(call, dict):
            continue
        fn = call.get("function")
        if not isinstance(fn, dict):
            continue
        raw = fn.get("arguments")
        if not isinstance(raw, str) or not raw.strip():
            continue
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if isinstance(obj, dict):
            al = _coerce_actions_list(obj)
            if al is not None:
                return al
    return None


def _completion_debug_excerpt(raw_resp: dict[str, Any], max_len: int = 4000) -> dict[str, Any]:
    """Structured hints when assistant text is empty (for engine_trace.json)."""
    out: dict[str, Any] = {}
    choices = raw_resp.get("choices")
    if isinstance(choices, list) and choices:
        ch0 = choices[0]
        if isinstance(ch0, dict):
            out["finish_reason"] = ch0.get("finish_reason")
            msg = ch0.get("message")
            if isinstance(msg, dict):
                out["message_keys"] = sorted(msg.keys())
                tc = msg.get("tool_calls")
                if isinstance(tc, list) and tc:
                    out["tool_calls_count"] = len(tc)
    try:
        raw = json.dumps(raw_resp, ensure_ascii=False)
    except (TypeError, ValueError):
        raw = str(raw_resp)
    out["raw_response_excerpt"] = raw[:max_len]
    return out


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
    payload: dict[str, Any] = {
        "model": model,
        "messages": messages,
        "temperature": temperature,
    }
    # OpenAI-compatible JSON mode (helps Gemini-style models return parseable objects).
    # Prime Inference: on by default; disable with PF_DIRECT_AGENT_JSON_OBJECT=0 if the API returns 400.
    # Other providers: opt-in with PF_DIRECT_AGENT_JSON_OBJECT=1.
    _jo = (os.environ.get("PF_DIRECT_AGENT_JSON_OBJECT") or "").strip().lower()
    if provider == "prime_intellect":
        if _jo not in ("0", "false", "no", "off"):
            payload["response_format"] = {"type": "json_object"}
    elif _jo in ("1", "true", "yes", "on"):
        payload["response_format"] = {"type": "json_object"}
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

    def _post(p: dict[str, Any]) -> dict[str, Any]:
        b = json.dumps(p).encode("utf-8")
        r = urllib.request.Request(url=url, data=b, method="POST", headers=headers)
        with urllib.request.urlopen(r, timeout=max(30, timeout_s)) as resp:
            raw_inner = resp.read().decode("utf-8", errors="replace")
        return json.loads(raw_inner)

    try:
        data = _post(payload)
    except urllib.error.HTTPError as e:
        if e.code == 400 and payload.pop("response_format", None) is not None:
            data = _post(payload)
        else:
            raise
    return _assistant_text_from_completion(data), data


def _strip_optional_markdown_fence(text: str) -> str:
    """Remove leading ``` / ```json and trailing ``` so chat models' JSON parses."""
    s = (text or "").strip()
    if not s.startswith("```"):
        return s
    lines = s.splitlines()
    if not lines:
        return s
    if not lines[0].lstrip().startswith("```"):
        return s
    body = lines[1:]
    while body and body[-1].strip() == "```":
        body = body[:-1]
    return "\n".join(body).strip()


def _extract_json_blob(text: str) -> Optional[dict[str, Any]]:
    s = _strip_optional_markdown_fence((text or "").strip())
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
            ["git", "apply", "--check", "--whitespace=nowarn", p],
            cwd=repo_dir,
            capture_output=True,
            text=True,
            timeout=20,
        )
        if proc.returncode == 0:
            return True, ""
        # Patch was produced from current working tree state; reverse-check validates structure.
        rev = subprocess.run(
            ["git", "apply", "--check", "--reverse", "--whitespace=nowarn", p],
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
    actions = _coerce_actions_list(parsed)
    if actions is None:
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

            msg_ev: dict[str, Any] = {
                "kind": "MessageEvent",
                "iteration": it + 1,
                "content": content[:4000],
                "latency_s": round(time.perf_counter() - step_t0, 4),
                "timestamp": time.time(),
                "usage": (raw_resp.get("usage") or {}),
            }
            if not (content or "").strip():
                msg_ev["empty_assistant_text"] = True
                msg_ev.update(_completion_debug_excerpt(raw_resp))
            trace.raw_events.append(msg_ev)
            parsed = _extract_json_blob(content)
            if not parsed and not (content or "").strip():
                tc_actions = _extract_actions_from_tool_calls(raw_resp)
                if tc_actions is not None:
                    parsed = {"actions": tc_actions}
            if not parsed:
                messages.append(
                    {
                        "role": "user",
                        "content": "Response was not valid JSON. Return STRICT JSON with an actions array.",
                    }
                )
                continue

            actions = _coerce_actions_list(parsed)
            if actions is None:
                messages.append(
                    {
                        "role": "user",
                        "content": (
                            "Invalid JSON shape. The root object must contain key \"actions\" (array), e.g. "
                            '{"actions":[{"type":"edit_file","path":"relative/path.py","old_string":"...","new_string":"..."}]} '
                            'or {"actions":[{"type":"finish","summary":"done"}]}.'
                        ),
                    }
                )
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

