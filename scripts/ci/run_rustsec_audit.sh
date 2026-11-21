#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Run Cargo Audit against a fresh, identified upstream RustSec database snapshot.
# Do not treat a failed advisory-database download as a successful scan.
set -euo pipefail

if [[ $# -ne 1 || -z "$1" ]]; then
  echo "Usage: $0 OUTPUT_JSON" >&2
  exit 2
fi
if [[ -z "${GITHUB_TOKEN:-}" ]]; then
  echo "GITHUB_TOKEN is required to resolve the upstream RustSec revision" >&2
  exit 2
fi

output="$1"
directory="$(mktemp -d)"
trap 'rm -rf -- "$directory"' EXIT

# The Git smart-HTTP endpoint sometimes rejects requests from Actions with 403.
# Resolve upstream main through GitHub's authenticated REST API and fetch its
# corresponding source archive by immutable commit SHA over HTTPS.
curl --fail --silent --show-error --location \
  --retry 3 --retry-all-errors --retry-delay 2 --max-time 60 \
  --header "Authorization: Bearer ${GITHUB_TOKEN}" \
  --header "Accept: application/vnd.github+json" \
  "https://api.github.com/repos/RustSec/advisory-db/commits/main" \
  --output "$directory/upstream.json"

upstream_sha="$(python3 - "$directory/upstream.json" <<'PY'
import datetime
import json
import re
import sys

with open(sys.argv[1], encoding="utf-8") as handle:
    metadata = json.load(handle)
sha = metadata.get("sha")
if not isinstance(sha, str) or re.fullmatch(r"[a-f0-9]{40}", sha) is None:
    raise SystemExit("RustSec upstream metadata lacked a valid commit SHA")
committer = metadata.get("commit", {}).get("committer", {})
date = committer.get("date")
if not isinstance(date, str):
    raise SystemExit("RustSec upstream metadata lacked a commit date")
updated_at = datetime.datetime.fromisoformat(date.replace("Z", "+00:00"))
age = datetime.datetime.now(datetime.timezone.utc) - updated_at
if age > datetime.timedelta(days=90) or age < datetime.timedelta(days=-1):
    raise SystemExit(f"RustSec upstream snapshot is stale or future-dated: {date}")
print(sha)
PY
)"

curl --fail --silent --show-error --location \
  --retry 3 --retry-all-errors --retry-delay 2 --max-time 120 \
  "https://codeload.github.com/RustSec/advisory-db/tar.gz/${upstream_sha}" \
  --output "$directory/advisories.tar.gz"

mkdir -p "$directory/db"
tar -xzf "$directory/advisories.tar.gz" -C "$directory/db" --strip-components=1
if [[ ! -d "$directory/db/crates" ]] ||
   [[ -z "$(find "$directory/db/crates" -name 'RUSTSEC-*.toml' -print -quit)" ]]; then
  echo "The upstream RustSec snapshot contains no crate advisories" >&2
  exit 1
fi

# cargo-audit's database loader expects a Git repository. This is a locally
# materialized snapshot of the exact upstream commit, not the upstream Git
# history; the actual upstream SHA is recorded separately in the scan output.
git -C "$directory/db" init --quiet -b main
git -C "$directory/db" add -A
git -C "$directory/db" -c user.name="RustSec snapshot" \
  -c user.email="rustsec-snapshot@localhost" commit --quiet \
  -m "Materialize upstream RustSec ${upstream_sha}"

# Audit findings give cargo-audit a nonzero exit status. A database or tool
# failure must still fail this job, even when stdout contains partial JSON.
set +e
cargo audit --db "$directory/db" --no-fetch --file Cargo.lock --json > "$output"
audit_status=$?
set -e
if [[ "$audit_status" -gt 1 ]]; then
  echo "Cargo Audit exited unexpectedly with status ${audit_status}" >&2
  exit "$audit_status"
fi

python3 - "$output" "$upstream_sha" "$directory/upstream.json" <<'PY'
import json
import sys
from pathlib import Path

report_path = Path(sys.argv[1])
upstream_sha = sys.argv[2]
with report_path.open(encoding="utf-8") as handle:
    report = json.load(handle)
vulnerabilities = report.get("vulnerabilities")
database = report.get("database")
lockfile = report.get("lockfile")
if not isinstance(vulnerabilities, dict) or not isinstance(database, dict) or not isinstance(lockfile, dict):
    raise SystemExit("Cargo Audit did not produce a complete structured scan")
count = vulnerabilities.get("count")
items = vulnerabilities.get("list")
if not isinstance(count, int) or count < 0 or not isinstance(items, list) or count != len(items):
    raise SystemExit("Cargo Audit vulnerability count is inconsistent")
if database.get("advisory-count", 0) <= 0 or lockfile.get("dependency-count", 0) <= 0:
    raise SystemExit("Cargo Audit advisory database or lockfile is empty")
if vulnerabilities.get("found") != (count > 0):
    raise SystemExit("Cargo Audit reported inconsistent vulnerability metadata")
print(f"Cargo Audit completed using official RustSec revision {upstream_sha}; {count} vulnerability records.")
print("Findings are recorded, not waived or considered remediated.")
with open("rustsec-database-source.json", "w", encoding="utf-8") as handle:
    json.dump({
        "source": "https://github.com/RustSec/advisory-db",
        "upstream_commit": upstream_sha,
        "download": "GitHub codeload archive at the immutable upstream commit",
        "audit_fetch": "disabled after fetching the exact upstream snapshot",
        "vulnerability_records": count,
        "findings_remediated_by_scan": False,
    }, handle, indent=2)
    handle.write("\n")
PY
