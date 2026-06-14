#!/usr/bin/env python3
import json
import os
import subprocess
import sys


REPO_MAP = {
    "CERT-V1": os.path.join("external", "CERT-V1"),
    "TRACE-REPLAY-KIT": os.path.join("external", "TRACE-REPLAY-KIT"),
}


def get_exact_tag(path: str) -> str | None:
    try:
        result = subprocess.run(
            [
                "git",
                "-C",
                path,
                "describe",
                "--tags",
                "--exact-match",
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        return result.stdout.strip()
    except subprocess.CalledProcessError:
        return None


def get_remote_url(path: str) -> str | None:
    try:
        result = subprocess.run(
            [
                "git",
                "-C",
                path,
                "config",
                "--get",
                "remote.origin.url",
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        return result.stdout.strip()
    except subprocess.CalledProcessError:
        return None


def get_head_commit(path: str) -> str | None:
    try:
        result = subprocess.run(
            ["git", "-C", path, "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            check=True,
        )
        return result.stdout.strip()
    except subprocess.CalledProcessError:
        return None


def main() -> int:
    versions_path = os.path.join("tools", "standards", "versions.json")
    if not os.path.exists(versions_path):
        print(f"Error: versions file not found at {versions_path}")
        return 2

    with open(versions_path, "r", encoding="utf-8") as f:
        versions = json.load(f)

    pin_commits = versions.get("pins", {})
    failures = 0
    for name, expected_tag in versions.items():
        if name == "pins":
            continue
        repo_path = REPO_MAP.get(name)
        if not repo_path:
            print(f"[WARN] Unknown repo mapping for {name}; skipping")
            continue

        if not os.path.isdir(repo_path):
            print(f"[FAIL] {name}: path missing: {repo_path}")
            failures += 1
            continue

        remote = get_remote_url(repo_path) or "(unknown)"
        tag = get_exact_tag(repo_path)
        expected_commit = pin_commits.get(name)

        if tag == expected_tag:
            ok_msg = f"[OK] {name}: pinned to {tag} (remote={remote})"
            print(ok_msg)
            continue

        head = get_head_commit(repo_path)
        if expected_commit and head and head.startswith(expected_commit):
            ok_msg = (
                f"[OK] {name}: commit {head[:12]} matches pin "
                f"(tag {expected_tag} not checked out; remote={remote})"
            )
            print(ok_msg)
            continue

        if tag is None:
            msg = (
                f"[FAIL] {name}: HEAD at {repo_path} is not at an exact tag "
                f"(remote={remote})."
            )
            print(msg)
            print(f"       Expected tag: {expected_tag}.")
            if expected_commit:
                print(f"       Expected commit prefix: {expected_commit}.")
            fix_str = (
                "       Fix: git -C {p} fetch --tags && git -C {p} " "checkout {tag}"
            )
            print(fix_str.format(p=repo_path, tag=expected_tag))
            failures += 1
            continue

        msg = f"[FAIL] {name}: tag mismatch at {repo_path} " f"(remote={remote})."
        print(msg)
        print(f"       Current: {tag}")
        print(f"       Expected: {expected_tag}")
        fix_str = (
            "       Fix: git -C {p} fetch --tags && git -C {p} " "checkout {tag}"
        )
        print(fix_str.format(p=repo_path, tag=expected_tag))
        failures += 1

    if failures:
        print(f"\nStandards pin check failed: {failures} issue(s)")
        return 1

    print("\nStandards pin check passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
