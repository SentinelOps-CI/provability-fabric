# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import json
import os
import subprocess
import tempfile
import urllib.request
from pathlib import Path
from typing import Any
from unittest import mock


def _init_repo(repo_dir: Path) -> None:
    subprocess.run(["git", "init"], cwd=repo_dir, check=True, capture_output=True, text=True)
    subprocess.run(
        ["git", "config", "user.email", "test@example.com"],
        cwd=repo_dir,
        check=True,
        capture_output=True,
        text=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Test User"],
        cwd=repo_dir,
        check=True,
        capture_output=True,
        text=True,
    )
    (repo_dir / "a.txt").write_text("hello\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=repo_dir, check=True, capture_output=True, text=True)
    subprocess.run(["git", "commit", "-m", "init"], cwd=repo_dir, check=True, capture_output=True, text=True)


def test_coerce_actions_list_nested_and_single():
    from bench.swebench.engines import direct_agent_engine as dae

    assert dae._coerce_actions_list({"actions": [{"type": "finish"}]}) == [{"type": "finish"}]
    assert dae._coerce_actions_list({"type": "finish", "summary": "x"}) == [{"type": "finish", "summary": "x"}]
    assert dae._coerce_actions_list({"result": {"actions": [{"type": "finish"}]}}) == [{"type": "finish"}]
    assert dae._coerce_actions_list({"foo": 1}) is None


def test_extract_actions_from_tool_calls_arguments_json():
    from bench.swebench.engines import direct_agent_engine as dae

    raw = {
        "choices": [
            {
                "message": {
                    "role": "assistant",
                    "content": None,
                    "tool_calls": [
                        {
                            "id": "c1",
                            "type": "function",
                            "function": {
                                "name": "plan",
                                "arguments": '{"actions":[{"type":"finish","summary":"noop"}]}',
                            },
                        }
                    ],
                }
            }
        ]
    }
    al = dae._extract_actions_from_tool_calls(raw)
    assert al == [{"type": "finish", "summary": "noop"}]


def test_completion_debug_excerpt_shape():
    from bench.swebench.engines import direct_agent_engine as dae

    raw = {
        "choices": [
            {
                "finish_reason": "stop",
                "message": {"role": "assistant", "content": None, "tool_calls": [{"id": "1"}]},
            }
        ]
    }
    ex = dae._completion_debug_excerpt(raw, max_len=500)
    assert ex.get("finish_reason") == "stop"
    assert "tool_calls" in (ex.get("message_keys") or [])
    assert ex.get("tool_calls_count") == 1
    assert "raw_response_excerpt" in ex


def test_assistant_text_from_completion_gemini_style_parts():
    from bench.swebench.engines import direct_agent_engine as dae

    data = {
        "choices": [
            {
                "message": {
                    "content": [
                        {
                            "type": "output_text",
                            "text": '{"actions":[{"type":"finish","summary":"x"}]}',
                        },
                    ]
                }
            }
        ]
    }
    assert "actions" in dae._assistant_text_from_completion(data)


def test_extract_json_blob_strips_markdown_fence():
    from bench.swebench.engines import direct_agent_engine as dae

    fenced = '```json\n{"actions": [{"type": "finish", "summary": "x"}]}\n```'
    out = dae._extract_json_blob(fenced)
    assert out == {"actions": [{"type": "finish", "summary": "x"}]}
    bare = "```\n{\"actions\": []}\n```"
    assert dae._extract_json_blob(bare) == {"actions": []}


def test_direct_agent_engine_edits_file_and_returns_patch():
    from bench.swebench.engines import direct_agent_engine as dae

    with tempfile.TemporaryDirectory() as td:
        ws = Path(td)
        repo = ws / "repo"
        scratch = ws / "scratch"
        repo.mkdir()
        scratch.mkdir()
        _init_repo(repo)

        fake_content = json.dumps(
            {
                "actions": [
                    {
                        "type": "edit_file",
                        "path": "a.txt",
                        "old_string": "hello\n",
                        "new_string": "hello world\n",
                    },
                    {"type": "finish", "summary": "done"},
                ]
            }
        )

        with (
            mock.patch.object(dae, "_llm_credentials", return_value=("k", "https://api.example/v1", "openai")),
            mock.patch.object(dae, "_call_openai_compatible_chat", return_value=(fake_content, {"usage": {}})),
        ):
            res = dae.solve(
                workspace_path=ws,
                task_text="fix",
                config=dae.DirectAgentConfig(model_name="gpt-4o-mini", max_iterations=2, timeout_seconds=60),
            )

        assert res.success is True
        assert "hello world" in (repo / "a.txt").read_text(encoding="utf-8")
        assert "diff --git" in res.patch_diff_str
        assert res.trace.execution_mode == "direct_agent"


def test_direct_agent_engine_parses_fenced_json_from_model():
    from bench.swebench.engines import direct_agent_engine as dae

    with tempfile.TemporaryDirectory() as td:
        ws = Path(td)
        repo = ws / "repo"
        scratch = ws / "scratch"
        repo.mkdir()
        scratch.mkdir()
        _init_repo(repo)

        inner = json.dumps(
            {
                "actions": [
                    {
                        "type": "edit_file",
                        "path": "a.txt",
                        "old_string": "hello\n",
                        "new_string": "hello world\n",
                    },
                    {"type": "finish", "summary": "done"},
                ]
            }
        )
        fenced = f"Here is the plan:\n```json\n{inner}\n```"

        with (
            mock.patch.object(dae, "_llm_credentials", return_value=("k", "https://api.example/v1", "openai")),
            mock.patch.object(dae, "_call_openai_compatible_chat", return_value=(fenced, {"usage": {}})),
        ):
            res = dae.solve(
                workspace_path=ws,
                task_text="fix",
                config=dae.DirectAgentConfig(model_name="gpt-4o-mini", max_iterations=2, timeout_seconds=60),
            )

        assert res.success is True
        assert "hello world" in (repo / "a.txt").read_text(encoding="utf-8")


def test_direct_agent_patch_sanitize_and_apply_check():
    from bench.swebench.engines import direct_agent_engine as dae

    with tempfile.TemporaryDirectory() as td:
        repo = Path(td)
        _init_repo(repo)
        raw = "noise line\n\ndiff --git a/a.txt b/a.txt\n--- a/a.txt\n+++ b/a.txt\n@@ -1 +1 @@\n-hello\n+hi\n"
        sanitized, changed = dae._sanitize_patch_text(raw)
        assert changed is True
        assert sanitized.startswith("diff --git ")
        ok, _ = dae._git_apply_check(repo, sanitized)
        assert ok is True


def test_direct_agent_patch_failure_type_empty():
    from bench.swebench.engines import direct_agent_engine as dae

    with tempfile.TemporaryDirectory() as td:
        repo = Path(td)
        _init_repo(repo)
        ft = dae._classify_patch_failure("", "empty patch", [], repo)
        assert ft == "empty_patch"


def test_direct_agent_prime_uses_effective_model_for_chat_body_not_litellm_prefix():
    """Raw HTTP to Prime must use vendor ids (google/...); openai/ prefix is LiteLLM/OpenHands-only."""
    from bench.swebench.engines import direct_agent_engine as dae

    class _FakeProxy:
        def __init__(self, *args: Any, **kwargs: Any) -> None:
            pass

        def start(self) -> str:
            return "https://local-prime/v1"

        def close(self) -> None:
            pass

    fake_content = json.dumps(
        {
            "actions": [
                {
                    "type": "edit_file",
                    "path": "a.txt",
                    "old_string": "hello\n",
                    "new_string": "hello world\n",
                },
                {"type": "finish", "summary": "done"},
            ]
        }
    )
    captured: dict[str, str] = {}

    def _capture_chat(**kwargs: Any) -> tuple[str, dict[str, Any]]:
        captured["model"] = str(kwargs.get("model") or "")
        return fake_content, {}

    with tempfile.TemporaryDirectory() as td:
        ws = Path(td)
        repo = ws / "repo"
        scratch = ws / "scratch"
        repo.mkdir()
        scratch.mkdir()
        _init_repo(repo)

        with (
            mock.patch.object(
                dae,
                "_llm_credentials",
                return_value=("k", "https://api.pinference.ai/api/v1", "prime_intellect"),
            ),
            mock.patch.object(dae, "_PrimeStrictCompatProxy", _FakeProxy),
            mock.patch.object(dae, "_call_openai_compatible_chat", side_effect=_capture_chat),
        ):
            res = dae.solve(
                workspace_path=ws,
                task_text="fix",
                config=dae.DirectAgentConfig(
                    model_name="google/gemini-2.5-flash",
                    max_iterations=2,
                    timeout_seconds=60,
                ),
            )

    assert captured["model"] == "google/gemini-2.5-flash"
    starts = [e for e in res.trace.raw_events if e.get("kind") == "DirectAgentStartEvent"]
    assert starts and starts[0].get("llm_model_request") == "google/gemini-2.5-flash"
    assert res.success is True


def test_direct_agent_applies_edit_when_finish_listed_first_in_actions():
    """finish before edit_file in the same response must not skip the edit."""
    from bench.swebench.engines import direct_agent_engine as dae

    class _FakeProxy:
        def __init__(self, *args: Any, **kwargs: Any) -> None:
            pass

        def start(self) -> str:
            return "https://local-prime/v1"

        def close(self) -> None:
            pass

    fake_content = json.dumps(
        {
            "actions": [
                {"type": "finish", "summary": "done"},
                {
                    "type": "edit_file",
                    "path": "a.txt",
                    "old_string": "hello\n",
                    "new_string": "hello world\n",
                },
            ]
        }
    )

    with tempfile.TemporaryDirectory() as td:
        ws = Path(td)
        repo = ws / "repo"
        scratch = ws / "scratch"
        repo.mkdir()
        scratch.mkdir()
        _init_repo(repo)

        with (
            mock.patch.object(
                dae,
                "_llm_credentials",
                return_value=("k", "https://api.pinference.ai/api/v1", "prime_intellect"),
            ),
            mock.patch.object(dae, "_PrimeStrictCompatProxy", _FakeProxy),
            mock.patch.object(
                dae,
                "_call_openai_compatible_chat",
                return_value=(fake_content, {}),
            ),
        ):
            res = dae.solve(
                workspace_path=ws,
                task_text="fix",
                config=dae.DirectAgentConfig(
                    model_name="google/gemini-2.5-flash",
                    max_iterations=2,
                    timeout_seconds=60,
                ),
            )

        assert res.success is True
        assert "hello world" in (repo / "a.txt").read_text(encoding="utf-8")


def test_call_openai_compatible_chat_response_format_opt_in():
    from bench.swebench.engines import direct_agent_engine as dae

    class _FakeResp:
        def read(self) -> bytes:
            return (
                b'{"choices":[{"message":{"content":"{\\"actions\\":[{\\"type\\":\\"finish\\",'
                b'\\"summary\\":\\"x\\"}]}"}}]}'
            )

        def __enter__(self) -> "_FakeResp":
            return self

        def __exit__(self, *args: object) -> None:
            return None

    bodies: list[dict[str, Any]] = []

    def _fake_urlopen(req: urllib.request.Request, timeout: int = 0) -> _FakeResp:
        bodies.append(json.loads(req.data.decode("utf-8")))
        return _FakeResp()

    with mock.patch("urllib.request.urlopen", side_effect=_fake_urlopen):
        with mock.patch.dict(os.environ, {"PF_DIRECT_AGENT_JSON_OBJECT": "0"}):
            dae._call_openai_compatible_chat(
                base_url="https://example/v1",
                api_key="secret",
                model="openai/google/gemini-2.5-flash",
                messages=[{"role": "user", "content": "x"}],
                timeout_s=60,
                provider="prime_intellect",
            )
    assert bodies and "response_format" not in bodies[-1]

    with mock.patch("urllib.request.urlopen", side_effect=_fake_urlopen):
        with mock.patch.dict(os.environ, {"PF_DIRECT_AGENT_JSON_OBJECT": "1"}):
            dae._call_openai_compatible_chat(
                base_url="https://example/v1",
                api_key="secret",
                model="openai/google/gemini-2.5-flash",
                messages=[{"role": "user", "content": "x"}],
                timeout_s=60,
                provider="prime_intellect",
            )
    assert bodies[-1].get("response_format") == {"type": "json_object"}

    with mock.patch("urllib.request.urlopen", side_effect=_fake_urlopen):
        _saved = os.environ.pop("PF_DIRECT_AGENT_JSON_OBJECT", None)
        try:
            dae._call_openai_compatible_chat(
                base_url="https://example/v1",
                api_key="secret",
                model="openai/google/gemini-2.5-flash",
                messages=[{"role": "user", "content": "x"}],
                timeout_s=60,
                provider="prime_intellect",
            )
        finally:
            if _saved is not None:
                os.environ["PF_DIRECT_AGENT_JSON_OBJECT"] = _saved
    assert bodies[-1].get("response_format") == {"type": "json_object"}

    with mock.patch("urllib.request.urlopen", side_effect=_fake_urlopen):
        with mock.patch.dict(os.environ, {"PF_DIRECT_AGENT_JSON_OBJECT": ""}, clear=False):
            dae._call_openai_compatible_chat(
                base_url="https://example/v1",
                api_key="secret",
                model="gpt-4o-mini",
                messages=[{"role": "user", "content": "x"}],
                timeout_s=60,
                provider="openai",
            )
    assert "response_format" not in bodies[-1]

