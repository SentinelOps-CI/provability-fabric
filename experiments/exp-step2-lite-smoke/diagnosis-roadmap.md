# Diagnosis (roadmap execution)

Generated during implementation of the SWE-bench full product roadmap.

## Bucketing

`categorize_pf_failures.py` on PF run `20260317-143046-340fb140` reported **no baseline-solved / PF-failed** instances because the referenced golden smoke run had **0% baseline solve rate** (no delta to analyze).

## Empty patches

Historical smoke runs show `empty_patch_reason=agent_no_changes`: the agent used tools (e.g. file_editor) but the working tree had **no net diff** at end of episode, or the model prioritized environment setup (e.g. pytest) over landing edits.

## Mitigations applied (code)

1. **Guarded runs:** `TMPDIR` / `TMP` / `TEMP` point under `workspace/scratch/.pf_tmp` so pip and subprocess temp files stay under the workspace and avoid `/tmp`-related policy friction.
2. **Task prompt:** PF-guarded denial-recovery text; general guidance to prioritize code edits over long test-env setup.
3. **Engine:** Non-zero OpenHands CLI exit with a **non-empty git patch** is treated as success so valid edits are not dropped.
4. **Budget:** Manifest `timeout_sec` raised symmetrically (baseline and PF).

## Operator follow-up

Re-run `bash experiments/scripts/run-baseline-pf-cycle.sh --update-run-ids` in WSL with Docker and API keys. For higher solve rates, set `OPENHANDS_MODEL=gpt-4o` (see `manifest.json` notes).
