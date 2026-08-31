#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for the CERT write-path guard."""

from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
GUARD = REPO / "scripts" / "check_cert_write_paths.sh"


def _run(*args: str, cwd: Path, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        list(args),
        cwd=cwd,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )


def _fixture_repo(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    (root / "scripts").mkdir(parents=True)
    (root / "runtime" / "sidecar-watcher" / "src").mkdir(parents=True)
    shutil.copy2(GUARD, root / "scripts" / GUARD.name)
    (root / "runtime" / "sidecar-watcher" / "src" / "cert_v1.rs").write_text(
        "pub fn write_cert(cert: &CertV1, session: &str, seq: u64) -> Result<String> {\n"
        "    Ok(String::new())\n"
        "}\n"
        "pub fn write_cert_with_binding(cert: &CertV1, session: &str, seq: u64) -> Result<String> {\n"
        "    let path = write_cert(cert, session, seq)?;\n"
        "    Ok(path)\n"
        "}\n",
        encoding="utf-8",
    )
    assert _run("git", "init", "-q", cwd=root).returncode == 0
    assert _run("git", "config", "user.email", "guard-test@example.invalid", cwd=root).returncode == 0
    assert _run("git", "config", "user.name", "guard-test", cwd=root).returncode == 0
    assert _run("git", "add", ".", cwd=root).returncode == 0
    assert _run("git", "commit", "-qm", "fixture", cwd=root).returncode == 0
    return root


def test_guard_accepts_only_allowlisted_writer(tmp_path: Path) -> None:
    root = _fixture_repo(tmp_path)
    proc = _run("bash", "scripts/check_cert_write_paths.sh", cwd=root)
    assert proc.returncode == 0, proc.stderr + proc.stdout
    assert "check_cert_write_paths: OK" in proc.stdout


def test_guard_rejects_unbound_writer(tmp_path: Path) -> None:
    root = _fixture_repo(tmp_path)
    writer = root / "runtime" / "new" / "writer.rs"
    writer.parent.mkdir(parents=True)
    writer.write_text("fn x() { write_cert(); }\n", encoding="utf-8")
    assert _run("git", "add", str(writer.relative_to(root)), cwd=root).returncode == 0
    proc = _run("bash", "scripts/check_cert_write_paths.sh", cwd=root)
    assert proc.returncode != 0
    assert "CERT write without binding hook" in proc.stderr


def test_guard_rejects_spaced_unbound_writer(tmp_path: Path) -> None:
    root = _fixture_repo(tmp_path)
    writer = root / "runtime" / "new" / "spaced_writer.rs"
    writer.parent.mkdir(parents=True)
    writer.write_text("fn x() { write_cert (); }\n", encoding="utf-8")
    assert _run("git", "add", str(writer.relative_to(root)), cwd=root).returncode == 0
    proc = _run("bash", "scripts/check_cert_write_paths.sh", cwd=root)
    assert proc.returncode != 0
    assert "CERT write without binding hook" in proc.stderr


def test_guard_rejects_split_line_unbound_writer(tmp_path: Path) -> None:
    root = _fixture_repo(tmp_path)
    writer = root / "runtime" / "new" / "split_writer.rs"
    writer.parent.mkdir(parents=True)
    writer.write_text("fn x() {\n    write_cert\n        ();\n}\n", encoding="utf-8")
    assert _run("git", "add", str(writer.relative_to(root)), cwd=root).returncode == 0
    proc = _run("bash", "scripts/check_cert_write_paths.sh", cwd=root)
    assert proc.returncode != 0
    assert "CERT write without binding hook" in proc.stderr


def test_guard_rejects_direct_writer_even_with_bound_call_on_same_line(tmp_path: Path) -> None:
    root = _fixture_repo(tmp_path)
    writer = root / "runtime" / "new" / "mixed_writer.rs"
    writer.parent.mkdir(parents=True)
    writer.write_text(
        "fn x() { write_cert(); write_cert_with_binding(); }\n", encoding="utf-8"
    )
    assert _run("git", "add", str(writer.relative_to(root)), cwd=root).returncode == 0
    proc = _run("bash", "scripts/check_cert_write_paths.sh", cwd=root)
    assert proc.returncode != 0
    assert "CERT write without binding hook" in proc.stderr


def test_guard_rejects_extra_direct_writer_inside_bridge_file(tmp_path: Path) -> None:
    root = _fixture_repo(tmp_path)
    writer = root / "runtime" / "sidecar-watcher" / "src" / "cert_v1.rs"
    writer.write_text(
        writer.read_text(encoding="utf-8")
        + "fn bypass(cert: &CertV1, session: &str, seq: u64) -> Result<String> {\n"
        + "    write_cert(cert, session, seq)\n"
        + "}\n",
        encoding="utf-8",
    )
    assert _run("git", "add", str(writer.relative_to(root)), cwd=root).returncode == 0
    proc = _run("bash", "scripts/check_cert_write_paths.sh", cwd=root)
    assert proc.returncode != 0
    assert "CERT write without binding hook" in proc.stderr



def test_guard_rejects_missing_writer_definition(tmp_path: Path) -> None:
    root = _fixture_repo(tmp_path)
    writer = root / "runtime" / "sidecar-watcher" / "src" / "cert_v1.rs"
    text = writer.read_text(encoding="utf-8")
    start = text.index("pub fn write_cert(cert:")
    end = text.index("pub fn write_cert_with_binding", start)
    writer.write_text(text[:start] + text[end:], encoding="utf-8")
    assert _run("git", "add", str(writer.relative_to(root)), cwd=root).returncode == 0
    proc = _run("bash", "scripts/check_cert_write_paths.sh", cwd=root)
    assert proc.returncode != 0
    assert "expected exactly one write_cert definition, found 0" in proc.stderr


def test_guard_rejects_missing_bound_bridge_call(tmp_path: Path) -> None:
    root = _fixture_repo(tmp_path)
    writer = root / "runtime" / "sidecar-watcher" / "src" / "cert_v1.rs"
    text = writer.read_text(encoding="utf-8")
    writer.write_text(
        text.replace("    let path = write_cert(cert, session, seq)?;\n", "    let path = String::new();\n"),
        encoding="utf-8",
    )
    assert _run("git", "add", str(writer.relative_to(root)), cwd=root).returncode == 0
    proc = _run("bash", "scripts/check_cert_write_paths.sh", cwd=root)
    assert proc.returncode != 0
    assert "expected exactly one bound write_cert call, found 0" in proc.stderr

def test_guard_fails_closed_when_scanner_errors(tmp_path: Path) -> None:
    root = _fixture_repo(tmp_path)
    real_git = shutil.which("git")
    assert real_git is not None
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    fake_git = fake_bin / "git"
    fake_git.write_text(
        "#!/usr/bin/env bash\n"
        "if [[ \"${1:-}\" == \"grep\" ]]; then exit 2; fi\n"
        f'exec "{real_git}" "$@"\n',
        encoding="utf-8",
    )
    fake_git.chmod(0o755)
    env = os.environ.copy()
    env["PATH"] = f"{fake_bin}{os.pathsep}{env['PATH']}"
    proc = _run("bash", "scripts/check_cert_write_paths.sh", cwd=root, env=env)
    assert proc.returncode == 2
    assert "scan failed with status 2" in proc.stderr
