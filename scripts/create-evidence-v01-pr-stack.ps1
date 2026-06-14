# Create the 15 stacked Evidence v0.1 pull requests.
# REMOVE THIS SCRIPT after PR15 merges to main (see docs/roadmap/evidence-v0.1-delivery.md).
# Prerequisites: gh auth login (or GH_TOKEN with repo scope)
# Usage: pwsh -File scripts/create-evidence-v01-pr-stack.ps1

$ErrorActionPreference = "Stop"

gh auth status 2>&1 | Out-Null
if ($LASTEXITCODE -ne 0) {
    Write-Error "GitHub CLI is not authenticated. Run: gh auth login"
}

$labels = @()
foreach ($label in @("area:evidence", "release:evidence-v0.1")) {
    gh label list --search $label --json name -q ".[].name" 2>$null | ForEach-Object {
        if ($_ -eq $label) { $labels += $label }
    }
}

$prs = @(
    @{
        Num = 1
        Head = "evidence-v01/repo-hygiene"
        Base = "main"
        Title = "docs: prepare repository for Evidence v0.1 stabilization"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by establishing repository hygiene: roadmap, contributor pointers, placeholder allowlist updates, and removal of a committed `pf` binary so the stack can land cleanly.

## Scope
- Add `docs/roadmap/evidence-v0.1.md` with the 15-PR sequence and known limitations
- Update `README.md`, `CONTRIBUTING.md`, `docs/evidence/overview.md`, and `mkdocs.yml` for Evidence v0.1 navigation
- Extend `.gitignore` and remove tracked `core/cli/pf/pf` binary artifact
- Align placeholder-burn-down allowlist and `scripts/check_no_placeholder.py` paths

## Out of scope
- JSON schemas, CLI commands, runtime binding, replay workflow, and testbed scripts (later PRs)

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
mkdocs build
grep -n AGENTS.md README.md CONTRIBUTING.md
grep -n placeholder-burn-down docs/
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
    @{
        Num = 2
        Head = "evidence-v01/core-schemas"
        Base = "evidence-v01/repo-hygiene"
        Title = "specs: add Evidence v0.1 artifact schemas"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by publishing six draft-2020-12 JSON Schemas with stable `$id` URLs and a schema README under `specs/evidence/v0.1/`.

## Scope
- Add schemas: `claim`, `proof`, `attestation`, `execution-trace`, `evidence-bundle`, `validation-report`
- Document layout, required `schema_version: "0.1"`, and digest-bound artifact refs in `specs/evidence/v0.1/README.md`

## Out of scope
- Narrative specification docs, fixtures, CLI pack/validate/replay, and runtime integration

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
for f in specs/evidence/v0.1/schemas/*.schema.json; do
  python -m json.tool "$f" > /dev/null
done
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
    @{
        Num = 3
        Head = "evidence-v01/public-spec"
        Base = "evidence-v01/core-schemas"
        Title = "docs: publish Evidence v0.1 model specification"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by publishing the human-readable Evidence model and bundle format specifications that mirror the JSON Schemas.

## Scope
- Add `docs/specs/evidence-model-v0.1.md` (artifact roles, digests, composition rules)
- Add `docs/specs/evidence-bundle-v0.1.md` (manifest layout, packing expectations)

## Out of scope
- Example fixtures, compatibility matrix tests, CLI implementation, and runtime binding

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
mkdocs build
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
    @{
        Num = 4
        Head = "evidence-v01/fixtures"
        Base = "evidence-v01/public-spec"
        Title = "test: add Evidence v0.1 fixtures and compatibility matrix"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by adding valid and invalid JSON fixtures, a compatibility matrix, and pytest coverage that locks schema expectations before CLI work lands.

## Scope
- Add valid/invalid examples under `specs/evidence/v0.1/examples/`
- Add `docs/specs/evidence-compatibility.md` compatibility matrix
- Add `tests/evidence_schema/test_evidence_v01.py` schema conformance tests
- Add `.github/workflows/evidence-v01-smoke.yml` with `evidence-schema-only` job (progressive CI start)

## Out of scope
- `pf evidence` CLI commands, bundle digest packing, strict validation, and replay workflow

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
pytest tests/evidence_schema -q
mkdocs build
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
    @{
        Num = 5
        Head = "evidence-v01/bundle-format"
        Base = "evidence-v01/fixtures"
        Title = "cli: add Evidence v0.1 bundle packaging command"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by implementing `core/evidence` bundle packing with SHA-256 digests and exposing `pf evidence bundle pack` for reproducible artifact archives.

## Scope
- Add `core/evidence/bundle.go`, `digest.go`, and pack-only unit tests
- Wire `pf evidence bundle pack` in `core/cli/pf/evidence_commands.go`
- Add `tests/evidence_bundle/test_bundle_pack.py` pytest shim (shells out to Go pack tests)
- Note in `specs/evidence/v0.1/README.md`: primary pack tests are Go-native

## Out of scope
- Strict validation mode (`ValidateBundle` tests land in PR6), replay verification, runtime binding, and testbed CI

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
cd core/evidence && go test ./...
pytest tests/evidence_bundle -q
cd ../cli/pf && go build -o pf .
./pf evidence bundle pack --help
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
    @{
        Num = 6
        Head = "evidence-v01/validator"
        Base = "evidence-v01/bundle-format"
        Title = "cli: add strict validation for Evidence v0.1 bundles"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by adding fail-closed strict bundle validation via `pf evidence validate --strict` and tightening the CERT-V1 cert validator when schemas are missing.

## Scope
- Add `core/evidence/validator.go` with digest, schema, and manifest checks
- Extend `pf evidence validate --strict` CLI surface
- Add validation tests to `core/evidence/bundle_test.go` (ValidateBundle coverage)
- Expand `tests/evidence_validation/test_evidence_validate.py` (invalid JSON, missing schema, bad-bundle-digest)
- Deduplicate `.github/workflows/cert-validate.yml` to a single fail-closed workflow
- Update `tools/cert-validate/validate.py` to fail closed unless `--allow-missing-schema`
- Add progressive CI: `evidence-v01-smoke.yml` validator job on `core/evidence/**` paths

## Out of scope
- End-to-end walkthrough examples, runtime binding, replay workflow, and testbed scripts

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
cd core/cli/pf && go build -o pf .
./pf evidence validate --strict examples/evidence-basic/basic-evidence-bundle.json
pytest tests/evidence_validation -q
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
    @{
        Num = 7
        Head = "evidence-v01/e2e-example"
        Base = "evidence-v01/validator"
        Title = "examples: add end-to-end Evidence v0.1 bundle walkthrough"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by shipping a minimal `examples/evidence-basic` bundle, a step-by-step walkthrough guide, and e2e pytest coverage for pack-then-validate flows.

## Scope
- Add `examples/evidence-basic/` artifacts, manifest, bundle JSON, and `expected/` golden outputs
- Add `docs/guides/evidence-bundle-walkthrough.md`
- Extend `tests/e2e/test_evidence_bundle_basic.py` with golden report comparison
- Cross-platform temp dir notes in example README (no `/tmp`-only paths)

## Out of scope
- Runtime sidecar binding, replay verification, forensic tamper cases, and testbed automation

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
pytest tests/e2e/test_evidence_bundle_basic.py -q
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
    @{
        Num = 8
        Head = "evidence-v01/runtime-binding"
        Base = "evidence-v01/e2e-example"
        Title = "runtime: bind execution events to Evidence v0.1 artifacts"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by emitting additive `evidence_v01_binding` JSONL events from the sidecar watcher without breaking CERT-V1 permit enforcement.

## Scope
- Add `runtime/sidecar-watcher/src/evidence_v01.rs` binding event emitter
- Extend `cert_v1.rs` and `permit_enforcement.rs` for additive hooks
- Rust unit tests: JSONL binding output, `write_cert_with_binding` with CERT-V1 gate
- Expand `tests/runtime_evidence/test_runtime_evidence_binding.py` (bundle strict validate)
- Add `tests/runtime_evidence/test_runtime_evidence_sidecar.py` (Linux + CERT-V1 live test)
- Add `docs/guides/runtime-evidence-basic.md` (emit path, CI requirements)

## Out of scope
- Runtime boundaries documentation, constrained scenario fixtures, replay workflow, and forensic examples

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
cargo test -p sidecar-watcher -- write_evidence_binding write_cert_with_binding
pytest tests/runtime_evidence -q
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
    @{
        Num = 9
        Head = "evidence-v01/runtime-boundaries"
        Base = "evidence-v01/runtime-binding"
        Title = "docs: document runtime evidence boundaries"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by documenting what runtime binding guarantees, what remains out of band, and how CERT-V1 and TRACE-REPLAY-KIT relate to Evidence v0.1.

## Scope
- Add `docs/guides/runtime-evidence-boundaries.md` covering scope, non-goals, and failure modes

## Out of scope
- New runtime code paths, replay CLI, forensic examples, and testbed automation

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
mkdocs build
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
    @{
        Num = 10
        Head = "evidence-v01/runtime-scenario"
        Base = "evidence-v01/runtime-boundaries"
        Title = "examples: add constrained runtime evidence scenario"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by adding `examples/runtime-evidence-basic` with a binding event fixture and pytest coverage for the constrained runtime evidence scenario.

## Scope
- Add `examples/runtime-evidence-basic/` bundle artifacts, manifest, and `binding-event.json`
- Add `run_scenario.sh` (static validation + optional `--live` sidecar emit)
- Extend runtime evidence tests with `test_runtime_evidence_basic.py` (scenario script wiring)

## Out of scope
- Replay verification CLI, forensic tamper walkthrough, testbed scripts, and onboarding docs

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
bash examples/runtime-evidence-basic/run_scenario.sh
pytest tests/runtime_evidence/test_runtime_evidence_basic.py -q
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
    @{
        Num = 11
        Head = "evidence-v01/replay-workflow"
        Base = "evidence-v01/runtime-scenario"
        Title = "replay: add Evidence v0.1 replay verification workflow"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by implementing `core/evidence/replay.go` and `pf evidence replay` to verify bundle integrity and artifact digests after packaging.

## Scope
- Add `core/evidence/replay.go` and Go unit tests
- Wire `pf evidence replay` in `evidence_commands.go`
- Add `tests/evidence_replay/test_evidence_replay.py`

## Out of scope
- Replay guarantees documentation, forensic tamper examples, testbed CI, and onboarding release notes

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
pytest tests/evidence_replay -q
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
    @{
        Num = 12
        Head = "evidence-v01/replay-docs"
        Base = "evidence-v01/replay-workflow"
        Title = "docs: document replay guarantees and limitations"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by documenting replay guarantees, explicit non-goals, and platform limitations for `pf evidence replay`.

## Scope
- Add `docs/guides/replay-guarantees.md` with guarantees, limits, and reviewer checklist

## Out of scope
- Forensic tamper examples, testbed automation, and onboarding quickstart

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
mkdocs build
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
    @{
        Num = 13
        Head = "evidence-v01/forensic-example"
        Base = "evidence-v01/replay-docs"
        Title = "examples: add forensic replay example"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by adding a forensic replay walkthrough with pass and tampered bundles plus pytest coverage for digest mismatch detection.

## Scope
- Add `examples/forensic-replay-basic/` with valid and `tampered-bundle.json` fixtures
- Add `docs/guides/forensic-replay-basic.md`
- Add `tests/forensic_replay/test_forensic_replay_basic.py`

## Out of scope
- Testbed shell scripts, CI smoke workflow, and onboarding release notes

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
pytest tests/forensic_replay -q
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
    @{
        Num = 14
        Head = "evidence-v01/testbed"
        Base = "evidence-v01/forensic-example"
        Title = "testbed: add Evidence v0.1 reproducible workflows"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by adding reproducible testbed shell scripts and a CI smoke workflow that exercises happy-path pack/validate/replay and tamper detection.

## Scope
- Add `testbed/evidence-v0.1/run_happy_path.sh` and `run_tamper_case.sh`
- Add `tests/testbed/test_evidence_v01_testbed.py`
- Complete `.github/workflows/evidence-v01-smoke.yml`: full smoke + runtime sidecar step (builds on PR4/PR6 progressive jobs)

## Out of scope
- Onboarding quickstart, CHANGELOG release notes, and mkdocs nav finalization

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
bash testbed/evidence-v0.1/run_happy_path.sh
bash testbed/evidence-v0.1/run_tamper_case.sh
pytest tests/testbed -q
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
    @{
        Num = 15
        Head = "evidence-v01/onboarding-docs"
        Base = "evidence-v01/testbed"
        Title = "docs: add Evidence v0.1 onboarding and release notes"
        Body = @'
## Summary
This PR advances the Evidence v0.1 path by completing onboarding documentation: quickstart guide, status checklist, CHANGELOG entry, and mkdocs navigation for the full Evidence v0.1 lane.

## Scope
- Add `docs/guides/evidence-v0.1-quickstart.md`
- Add `docs/roadmap/evidence-v0.1-status.md` completion checklist
- Update `docs/CHANGELOG.md` and `mkdocs.yml` navigation

## Out of scope
- New schemas, CLI features, runtime changes, or additional testbed scripts

## Acceptance criteria
- [ ] Public artifact added or updated
- [ ] Tests or fixtures included
- [ ] Documentation updated
- [ ] Reproducible command included
- [ ] Known limitations documented

## Verification
```bash
mkdocs build
```

## Notes for reviewers
Please focus review on: schema stability, validation behavior, artifact compatibility, reproducibility, failure modes.
'@
    }
)

$created = @()
$existing = @()
$failed = @()

foreach ($pr in $prs) {
    $num = $pr.Num
    $head = $pr.Head
    $base = $pr.Base
    $title = $pr.Title

    $found = gh pr list --head $head --json number,url,title,baseRefName -q ".[0]" 2>$null
    if ($found -and $found -ne "null" -and $found -ne "") {
        $obj = $found | ConvertFrom-Json
        if ($obj.url) {
            Write-Host "PR${num} already exists: $($obj.url) (base: $($obj.baseRefName))"
            $existing += [PSCustomObject]@{ Num = $num; Url = $obj.url; Head = $head }
            continue
        }
    }

    $bodyFile = [System.IO.Path]::GetTempFileName()
    try {
        [System.IO.File]::WriteAllText($bodyFile, $pr.Body.TrimEnd())

        $args = @(
            "pr", "create",
            "--base", $base,
            "--head", $head,
            "--title", $title,
            "--body-file", $bodyFile
        )
        $url = & gh @args 2>&1
        if ($LASTEXITCODE -ne 0) {
            Write-Host "FAILED PR${num} ($head): $url"
            $failed += [PSCustomObject]@{ Num = $num; Head = $head; Error = "$url" }
            continue
        }

        Write-Host "Created PR${num}: $url"
        $created += [PSCustomObject]@{ Num = $num; Url = $url.Trim(); Head = $head }

        if ($labels.Count -gt 0) {
            $prNum = ($url -replace '.*\/pull\/', '').Trim()
            & gh pr edit $prNum --add-label ($labels -join ",") 2>$null
        }
    }
    finally {
        Remove-Item -Force $bodyFile -ErrorAction SilentlyContinue
    }
}

Write-Host ""
Write-Host "=== Summary ==="
Write-Host "Created: $($created.Count)"
Write-Host "Already existed: $($existing.Count)"
Write-Host "Failed: $($failed.Count)"
$created + $existing | Sort-Object Num | ForEach-Object { Write-Host "PR$($_.Num): $($_.Url)" }
