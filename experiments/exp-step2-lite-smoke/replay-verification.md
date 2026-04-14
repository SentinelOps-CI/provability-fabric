# Replay verification (roadmap)

Replay samples **PF-resolved, compliant** instances to show tool traces reconstitute the same patch.

- When `compare.json` has `replay.sample_size == 0`, the last run had no such candidates (e.g. zero PF solves). This is expected until solve rates are non-zero.
- After a run with PF resolves, check `runs/exp-step2-lite-smoke/replay/replay_summary.json` and `replay/instance_results.jsonl`: each line should have `success`, `match`, and matching patch hashes when replay is healthy.
- Full pipeline: `run-baseline-pf-cycle.sh` runs `run_replay_sample.py` in Phase 4.2; `compare.json` merges the replay section.
