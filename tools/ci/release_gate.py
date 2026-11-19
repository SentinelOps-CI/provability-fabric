#!/usr/bin/env python3
"""Fail-closed GitHub release preflight for an exact pull-request commit.

This is a governance gate, not a security property verifier or deployment tool.
It never modifies GitHub state and never treats skipped checks as successful.

Usage:
    GITHUB_TOKEN=... python tools/ci/release_gate.py \
        --repo SentinelOps-CI/provability-fabric --pr 123 \
        --head-sha <full-40-character-sha> --base-sha <full-40-character-sha> \
        --actor fraware --required-check 'CI required checks@github-actions' \
        --required-check 'integration@github-actions'
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import os
import re
import sys
from typing import Any, Callable, Mapping
from urllib.error import HTTPError, URLError
from urllib.parse import quote
from urllib.request import Request, urlopen

SHA_RE = re.compile(r"^[0-9a-f]{40}$")
REPO_RE = re.compile(r"^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
USER_RE = re.compile(r"^[A-Za-z0-9-]{1,39}$")
MAX_PAGES = 20
API_ROOT = "https://api.github.com"
REQUIRED_DEFAULT = (
    ("CI required checks", "github-actions"),
    ("actionlint", "github-actions"),
    ("dependency-review", "github-actions"),
    ("integration", "github-actions"),
    ("Build and test retrieval-gateway", "github-actions"),
    ("GitGuardian Security Checks", "gitguardian"),
    ("semgrep-cloud-platform/scan", "semgrep-sentinelops-ci"),
)


class GateError(Exception):
    """Operational error that invalidates the entire release evaluation."""


@dataclass(frozen=True)
class ReleaseTarget:
    """Immutable target and identity constraints supplied by the operator."""

    repository: str
    pr_number: int
    head_sha: str
    base_sha: str
    actor: str
    required: tuple[tuple[str, str], ...] = REQUIRED_DEFAULT

    def __post_init__(self) -> None:
        if not REPO_RE.fullmatch(self.repository):
            raise GateError("invalid repository name")
        if self.pr_number <= 0:
            raise GateError("pull request number must be positive")
        if not SHA_RE.fullmatch(self.head_sha) or not SHA_RE.fullmatch(self.base_sha):
            raise GateError("full lowercase 40-character commit SHAs are required")
        if not USER_RE.fullmatch(self.actor):
            raise GateError("invalid GitHub login")
        if not self.required or len(self.required) != len(set(self.required)):
            raise GateError("required checks must be present and unique")
        for name, app in self.required:
            if not name.strip() or not app.strip():
                raise GateError("every required check must declare its exact app")


class GithubApi:
    """Read-only GitHub API with bounded pagination and no token logging."""

    def __init__(self, token: str, timeout: int = 15) -> None:
        if not token.strip():
            raise GateError("GITHUB_TOKEN is missing")
        self._token = token
        self._timeout = timeout

    def get(self, endpoint: str) -> Any:
        if not endpoint.startswith("/") or "//" in endpoint or ".." in endpoint:
            raise GateError("invalid API endpoint")
        req = Request(
            API_ROOT + endpoint,
            headers={
                "Authorization": f"Bearer {self._token}",
                "Accept": "application/vnd.github+json",
                "X-GitHub-Api-Version": "2022-11-28",
                "User-Agent": "provability-fabric-release-gate",
            },
            method="GET",
        )
        try:
            with urlopen(req, timeout=self._timeout) as response:
                if response.status != 200:
                    raise GateError("unexpected GitHub API response")
                # Bound memory consumption even if a server misbehaves.
                raw = response.read(2 * 1024 * 1024 + 1)
                if len(raw) > 2 * 1024 * 1024:
                    raise GateError("GitHub API response exceeded size limit")
                return json.loads(raw)
        except HTTPError as exc:
            # Do not include response bodies, which might disclose account details.
            raise GateError(f"GitHub API HTTP {exc.code}") from None
        except (URLError, OSError, ValueError, UnicodeError) as exc:
            raise GateError(f"GitHub API read failed: {type(exc).__name__}") from None


def _obj(value: Any, description: str) -> Mapping[str, Any]:
    if not isinstance(value, dict):
        raise GateError(f"malformed {description} response")
    return value


def _paged(client: GithubApi, base: str, key: str | None = None) -> list[dict[str, Any]]:
    """Fetch all entries; refuse incomplete results and malformed pages."""
    values: list[dict[str, Any]] = []
    total: int | None = None
    for page in range(1, MAX_PAGES + 1):
        response = client.get(f"{base}{'&' if '?' in base else '?'}per_page=100&page={page}")
        if key is not None:
            root = _obj(response, f"{key} page")
            count = root.get("total_count")
            if type(count) is not int or count < 0:
                raise GateError(f"malformed {key} count")
            if total is None:
                total = count
            elif count != total:
                raise GateError(f"{key} changed during pagination")
            response = root.get(key)
        if not isinstance(response, list) or any(not isinstance(x, dict) for x in response):
            raise GateError("malformed paginated response")
        values.extend(response)
        if total is not None:
            if len(values) >= total:
                if len(values) != total:
                    raise GateError(f"duplicate or inconsistent {key} entries")
                return values
        elif len(response) < 100:
            return values
    raise GateError("GitHub result pagination exceeds safety limit")


def evaluate(target: ReleaseTarget, get: Callable[[str], Any]) -> list[str]:
    """Return explicit blocking reasons. Unexpected API data always blocks."""
    errors: list[str] = []
    root = "/repos/" + quote(target.repository, safe="/")
    auth_user = _obj(get("/user"), "authenticated user")
    if auth_user.get("login") != target.actor:
        errors.append("authenticated GitHub account does not match release actor")
    pr = _obj(get(f"{root}/pulls/{target.pr_number}"), "pull request")
    head = _obj(pr.get("head"), "PR head")
    base = _obj(pr.get("base"), "PR base")
    user = _obj(pr.get("user"), "PR author")
    if pr.get("state") != "open" or pr.get("merged_at") is not None:
        errors.append("pull request is not open and unmerged")
    if pr.get("draft") is not False:
        errors.append("pull request has not exited draft review")
    if head.get("sha") != target.head_sha:
        errors.append("PR head differs from the exact approved commit")
    if base.get("sha") != target.base_sha or base.get("ref") != "main":
        errors.append("PR base differs from the audited main commit")
    if user.get("login") != target.actor:
        errors.append("PR author does not match the authenticated account")
    if pr.get("mergeable") is not True or pr.get("mergeable_state") != "clean":
        errors.append("GitHub has not established clean mergeability")

    branch = _obj(get(f"{root}/branches/main"), "protected branch")
    branch_commit = _obj(branch.get("commit"), "branch commit")
    if branch_commit.get("sha") != target.base_sha:
        errors.append("production main advanced since release review")
    if branch.get("protected") is not True:
        errors.append("production main is not protected")

    commit = _obj(get(f"{root}/commits/{target.head_sha}"), "commit")
    # GitHub account associations are essential; unassociated names/emails
    # alone do not establish author/committer attribution.
    for field in ("author", "committer"):
        value = commit.get(field)
        if not isinstance(value, dict) or value.get("login") != target.actor:
            errors.append(f"commit {field} is not associated with {target.actor}")

    # The PR endpoint describes commits introduced against the selected base.
    # Enforce GitHub account attribution for the entire introduced history;
    # a verified tip alone says nothing about the identities of prior commits.
    history = _paged_proxy(get, f"{root}/pulls/{target.pr_number}/commits", None)
    if not history or history[-1].get("sha") != target.head_sha:
        errors.append("PR commit history does not end at the audited head")
    seen: set[str] = set()
    for item in history:
        sha = item.get("sha")
        if not isinstance(sha, str) or not SHA_RE.fullmatch(sha) or sha in seen:
            raise GateError("malformed or duplicated PR commit")
        seen.add(sha)
        for field in ("author", "committer"):
            account = item.get(field)
            if not isinstance(account, dict) or account.get("login") != target.actor:
                errors.append(f"PR commit {sha} {field} is not associated with {target.actor}")

    # The repo's review state is needed in addition to GitHub's green checks.
    reviews = _paged_proxy(get, f"{root}/pulls/{target.pr_number}/reviews", None)
    by_author: dict[str, tuple[str, Any]] = {}
    latest_review_id = 0
    for review in reviews:
        review_id = review.get("id")
        if type(review_id) is not int or review_id <= latest_review_id:
            raise GateError("duplicate or nonmonotonic review identifiers")
        latest_review_id = review_id
        reviewer = review.get("user")
        if not isinstance(reviewer, dict) or not isinstance(reviewer.get("login"), str):
            raise GateError("malformed review author")
        who = reviewer["login"]
        state = review.get("state")
        # GitHub returns submissions in chronological order; check IDs to
        # reject accidental non-monotonic or duplicate pages.
        if state in ("APPROVED", "CHANGES_REQUESTED", "DISMISSED"):
            by_author[who] = (state, review.get("commit_id"))
    if not any(
        who != target.actor and state == "APPROVED" and commit_id == target.head_sha
        for who, (state, commit_id) in by_author.items()
    ):
        errors.append("no current independent approval on the exact PR head")
    if any(state == "CHANGES_REQUESTED" for state, _ in by_author.values()):
        errors.append("an outstanding changes-requested review exists")

    checks = _paged_proxy(get, f"{root}/commits/{target.head_sha}/check-runs", "check_runs")
    by_key: dict[tuple[str, str], list[dict[str, Any]]] = {}
    for c in checks:
        app = c.get("app")
        slug = app.get("slug") if isinstance(app, dict) else None
        name = c.get("name")
        if not isinstance(name, str) or not isinstance(slug, str):
            raise GateError("malformed check run identity")
        by_key.setdefault((name, slug), []).append(c)
    for required in target.required:
        matches = by_key.get(required, [])
        if len(matches) != 1:
            errors.append(f"check {required[0]}@{required[1]} missing or ambiguous")
            continue
        check = matches[0]
        if check.get("status") != "completed" or check.get("conclusion") != "success":
            errors.append(f"check {required[0]}@{required[1]} did not pass")
        if check.get("head_sha") != target.head_sha:
            errors.append(f"check {required[0]}@{required[1]} is not tied to the requested commit")

    # Refetch mutable refs to fail closed on a concurrent push/merge. This
    # guard reduces TOCTOU exposure; it is not a substitute for GitHub's
    # branch rulesets and required-status enforcement at merge time.
    final_pr = _obj(get(f"{root}/pulls/{target.pr_number}"), "final pull request")
    final_head = _obj(final_pr.get("head"), "final PR head")
    final_base = _obj(final_pr.get("base"), "final PR base")
    final_main = _obj(get(f"{root}/branches/main"), "final branch")
    final_main_commit = _obj(final_main.get("commit"), "final branch commit")
    if (final_head.get("sha") != target.head_sha
            or final_base.get("sha") != target.base_sha
            or final_base.get("ref") != "main"
            or final_pr.get("state") != "open"
            or final_pr.get("merged_at") is not None
            or final_pr.get("draft") is not False
            or final_pr.get("mergeable") is not True
            or final_pr.get("mergeable_state") != "clean"
            or final_main_commit.get("sha") != target.base_sha
            or final_main.get("protected") is not True):
        errors.append("release refs changed during evaluation")

    return errors


def _paged_proxy(get: Callable[[str], Any], base: str, key: str | None) -> list[dict[str, Any]]:
    """Bounded pagination over an injected GET implementation."""
    class Adapter:
        def get(self, endpoint: str) -> Any:
            return get(endpoint)

    return _paged(Adapter(), base, key)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default="SentinelOps-CI/provability-fabric")
    parser.add_argument("--pr", type=int, required=True)
    parser.add_argument("--head-sha", required=True)
    parser.add_argument("--base-sha", required=True)
    parser.add_argument("--actor", default="fraware")
    parser.add_argument("--required-check", action="append", default=[], metavar="NAME@APP")
    options = parser.parse_args(argv)
    try:
        if any("@" not in x for x in options.required_check):
            raise GateError("required checks need the NAME@APP form")
        required = tuple(
            tuple(x.rsplit("@", 1))  # checked against empty fields by ReleaseTarget
            for x in options.required_check
        ) if options.required_check else REQUIRED_DEFAULT
        target = ReleaseTarget(
            repository=options.repo,
            pr_number=options.pr,
            head_sha=options.head_sha,
            base_sha=options.base_sha,
            actor=options.actor,
            required=required,
        )
        api = GithubApi(os.environ.get("GITHUB_TOKEN", ""))
        reasons = evaluate(target, api.get)
    except (GateError, TypeError, KeyError) as exc:
        print(f"BLOCKED: {exc}", file=sys.stderr)
        return 2
    if reasons:
        for reason in reasons:
            print(f"BLOCKED: {reason}", file=sys.stderr)
        return 1
    print("Governance preflight passed for the exact commit; separate security and deployment approvals remain mandatory.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
