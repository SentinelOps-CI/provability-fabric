# SWE-bench Replay

Deterministic replay of SWE-bench agent runs: replay tool trace, reconstitute the final patch, and verify the patch hash matches the original. Aligns with PF replay posture (see `docs/evidence/replay.md` and TRACE-REPLAY-KIT).

## Usage

```bash
pf bench swebench replay --run_id <run_id> [--instance_id <id>] [--runs-dir runs] [--workspaces-dir workspaces] [--json]
```

- **replay** replays each instance in the run (or a single instance if `--instance_id` is set).
- Tool trace is replayed by applying captured **file_edits** to the repo at base commit, then `git diff HEAD` reconstitutes the patch.
- The reconstituted patch hash is compared to the original; exit 0 only if all match.

## Capture

When the runner runs with a workspace, it writes a **replay bundle** (`replay_bundle.json`) per instance:

- **original_patch_sha256**: SHA256 of `model.patch`.
- **tool_trace**: List of tool calls from the engine trace.
- **file_edits**: Final content of each modified file (read from the repo at capture time).

Replay uses `file_edits` to reconstitute the patch without calling the model.

## Requirements

- The workspace (repo at base commit) must still exist at the path recorded in `workspace_manifest.json` for each instance, or replay will report "Repo path not found".
- Run from repository root so `bench/swebench/run_replay.py` is found.
