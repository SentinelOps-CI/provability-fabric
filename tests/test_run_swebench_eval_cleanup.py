# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from experiments.scripts.run_swebench_eval import (  # noqa: E402
    count_nonempty_prediction_patches,
    docker_rm_stale_eval_containers,
)


def test_docker_rm_stale_skips_empty_run_id() -> None:
    with patch("experiments.scripts.run_swebench_eval.subprocess.run") as m:
        docker_rm_stale_eval_containers("")
        docker_rm_stale_eval_containers("   ")
    m.assert_not_called()


def test_docker_rm_stale_removes_only_sweb_eval_suffix_match() -> None:
    """Only containers named like sweb.eval.*.<run_id> are removed (not arbitrary name=run_id)."""
    run_id = "20260319-234947-e276199d"
    ps_out = (
        "abc111\tsweb.eval.inst_a.%s\n"
        "def222\tother.%s\n"
        "ghi333\tsweb.eval.inst_b.wrong-suffix\n" % (run_id, run_id)
    )

    calls: list[list[str]] = []

    def fake_run(cmd, **kwargs):  # type: ignore[no-untyped-def]
        calls.append(list(cmd))
        class R:
            returncode = 0
            stdout = ps_out
            stderr = ""

        if cmd[:3] == ["docker", "ps", "-a"]:
            return R()
        if cmd[:3] == ["docker", "rm", "-f"]:
            r2 = R()
            r2.stdout = ""
            return r2
        raise AssertionError("unexpected cmd: %s" % cmd)

    with patch("experiments.scripts.run_swebench_eval.subprocess.run", side_effect=fake_run):
        docker_rm_stale_eval_containers(run_id)

    assert any("name=sweb.eval" in c for c in calls)
    rm_cmds = [c for c in calls if len(c) >= 3 and c[0] == "docker" and c[1] == "rm"]
    assert len(rm_cmds) == 1
    assert rm_cmds[0] == ["docker", "rm", "-f", "abc111"]


def test_docker_rm_stale_removes_multiple_suffix_matches() -> None:
    """Two sweb.eval lines ending with the same run_id both get rm -f."""
    run_id = "rid-abc"
    ps_out = "id1\tsweb.eval.inst1.%s\nid2\tsweb.eval.inst2.%s\n" % (run_id, run_id)
    rm_targets: list[str] = []

    def fake_run(cmd, **kwargs):  # type: ignore[no-untyped-def]
        class R:
            returncode = 0
            stdout = ps_out
            stderr = ""

        if cmd[:3] == ["docker", "ps", "-a"]:
            return R()
        if cmd[:3] == ["docker", "rm", "-f"]:
            rm_targets.append(cmd[3])
            r2 = R()
            r2.stdout = ""
            return r2
        raise AssertionError("unexpected cmd: %s" % cmd)

    with patch("experiments.scripts.run_swebench_eval.subprocess.run", side_effect=fake_run):
        docker_rm_stale_eval_containers(run_id)

    assert sorted(rm_targets) == ["id1", "id2"]


def test_docker_rm_stale_no_match_no_rm() -> None:
    run_id = "rid-only-here"

    def fake_run(cmd, **kwargs):  # type: ignore[no-untyped-def]
        class R:
            returncode = 0
            stdout = "zzz\tunrelated.name\n"

        return R()

    with patch("experiments.scripts.run_swebench_eval.subprocess.run", side_effect=fake_run) as m:
        docker_rm_stale_eval_containers(run_id)

    rm_calls = [
        c.args
        for c in m.call_args_list
        if len(c.args) >= 3 and c.args[0] == "docker" and c.args[1] == "rm" and c.args[2] == "-f"
    ]
    assert rm_calls == []


def test_count_nonempty_prediction_patches(tmp_path: Path) -> None:
    p = tmp_path / "p.jsonl"
    p.write_text(
        '{"instance_id":"a","model_patch":""}\n{"instance_id":"b","model_patch":"diff --git"}\n',
        encoding="utf-8",
    )
    ne, nt = count_nonempty_prediction_patches(p)
    assert nt == 2
    assert ne == 1


def test_count_nonempty_prediction_patches_accepts_patch_key(tmp_path: Path) -> None:
    p = tmp_path / "p.jsonl"
    p.write_text('{"instance_id":"x","patch":"x"}\n', encoding="utf-8")
    ne, nt = count_nonempty_prediction_patches(p)
    assert nt == 1
    assert ne == 1
