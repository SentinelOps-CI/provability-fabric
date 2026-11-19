# Release governance preflight

`tools/ci/release_gate.py` is an additional, fail-closed check for an exact pull-request commit. It is read-only, uses GitHub's API, and cannot merge, publish, deploy, change rulesets, or approve code.

The script refuses a draft or nonmergeable PR, a changed baseline commit, an unprotected `main`, missing independent approval on the exact head commit, GitHub author/committer accounts other than the declared contributor, and missing, ambiguous, pending, skipped, or unsuccessful named CI checks. Check identities include the app slug, avoiding accidental matching of a status posted by an unrelated application.

With an authenticated, read-only-capable GitHub token, run:

```bash
python3 tools/ci/release_gate.py \
  --repo SentinelOps-CI/provability-fabric \
  --pr <PR_NUMBER> \
  --head-sha <FULL_PR_HEAD_SHA> \
  --base-sha <FULL_MAIN_SHA> \
  --actor fraware
```

To override the default check set, supply one `--required-check 'NAME@APP'` option per check. Overrides **replace** the defaults and need independent review. The default list is intentionally scoped to checks observed in this repository and does not claim exhaustive validation of all configured workflows.

Run unit tests with `python3 -m unittest discover -s tests/ci -p 'test_release_gate.py'` or `python3 -m pytest -q tests/ci/test_release_gate.py`.

A preflight success is **not** authorization to deploy. Keep separate gates for signed credential interoperability, access-control negative controls, image and configuration provenance, production secret rotation, genuine enforcement evidence, relevant scheduled and dispatch-only workflows, independent security signoff, staged rollout and rollback readiness. A successful CI job running simulated tests establishes only completion of the simulated commands. A branch-protection setting must be verified and enforced in GitHub before changing the default branch.

The preflight checks account attribution on every commit introduced by the pull request, including the tip. It also rechecks the base branch name and mergeability before completing its assessment. These checks do not replace enforced merge-time branch policies.

The program does not establish the identity of the actor who sent a Git push event; commit author/committer GitHub associations and PR author are distinct facts. Any requirement that the push actor itself be the contributor must be checked using the GitHub audit log or a contributor-authenticated Git CLI workflow.
