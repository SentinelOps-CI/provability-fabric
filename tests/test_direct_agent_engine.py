# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import json
import subprocess
import tempfile
from pathlib import Path
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

