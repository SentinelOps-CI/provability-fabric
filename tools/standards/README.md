# External standards pinning

Pinned copies of [CERT-V1](https://github.com/verifiable-ai-ci/CERT-V1) and
[TRACE-REPLAY-KIT](https://github.com/verifiable-ai-ci/TRACE-REPLAY-KIT) live under
`external/` as git submodules. This directory holds the **pin policy** and drift check.

## versions.json

| Field | Meaning |
|-------|---------|
| Top-level `"CERT-V1": "v1.0.0"` | **Intent** — the semver tag we expect upstream to publish |
| Top-level `"TRACE-REPLAY-KIT": "v1.0.0"` | Same for the replay kit |
| `pins.CERT-V1` | **Authoritative commit SHA** checked out until upstream tags exist |
| `pins.TRACE-REPLAY-KIT` | Authoritative commit SHA for the kit |

Upstream repos are private and may not have published `v1.0.0` tags yet. CI and local
development use commit SHAs in `pins.*` as the source of truth.

## check_pins.py

[`check_pins.py`](check_pins.py) verifies each submodule:

1. `remote.origin.url` matches the expected repository
2. `HEAD` equals the SHA in `pins.*` (prefix match allowed)
3. If an exact tag exists on `HEAD`, it must match the top-level semver intent

When no tag exists on the pinned commit, the script accepts a commit-prefix match only.

Run locally:

```bash
make submodules
make standards-pin-check
```

Or together: `make dev-standards`.

## Bumping pins

1. Clone or update the upstream repo and identify the target commit (or tag when published).
2. Test locally: `make dev-standards`, then Evidence/replay/cert workflows you touch.
3. Update `pins.*` in [`versions.json`](versions.json). Update top-level semver keys if intent changes.
4. Run `make standards-pin-check` and open a PR.
5. Ensure CI has repository secret **`STANDARDS_GITHUB_TOKEN`** (see [`external/README.md`](../../external/README.md)).

## CI checkout pattern

Workflows that need CERT-V1 or TRACE-REPLAY-KIT must **not** use `actions/checkout` with
`submodules: true` (stale gitlinks can fail). Use:

```yaml
- uses: actions/checkout@v4
- name: Init external standards
  env:
    STANDARDS_GITHUB_TOKEN: ${{ secrets.STANDARDS_GITHUB_TOKEN }}
  run: make submodules
```

Lean builds use `make vendor-mathlib` instead (see [`lean-offline.yaml`](../../.github/workflows/lean-offline.yaml)).
Workflows with no external dependency use plain checkout only.

See [`.github/WORKFLOWS.md`](../../.github/WORKFLOWS.md) for the workflow map.
