# PF-Guarded Runtime for OpenHands

Tool gateway that mediates OpenHands execution through PF enforcement (not a passive logger). Every tool call is checked against policy; forbidden actions fail closed and are recorded as violations.

## Components

- **policy.py**: Guard policy (allowed/forbidden binaries, max command length, workspace path restrictions, network deny).
- **ledger_stream.py**: Append-only hash-chained event stream (`events.jsonl`). Optional `PF_LEDGER_URL` to POST events to a PF ledger API.
- **redact.py**: Redaction of secrets from tool outputs before writing to the ledger.
- **tool_gateway.py**: Mediates shell exec: checks command, executes if allowed, records to ledger; fails closed on violation.
- **executor.py**: CLI used as `SHELL` when running OpenHands with `--guarded`; receives `-c "command"`, runs through the gateway.
- **compliance.py**: Builds `policy_compliance_summary.json` from the event stream (total events, violations, compliant, chain_tail_hash).

## Enforcement

- **Network off**: Forbidden binaries (curl, wget, ssh, nc, etc.) are denied.
- **File writes restricted to workspace**: Paths in commands (e.g. `> file`, `-o file`) must be under the workspace; `/etc`, `/home`, etc. are denied.
- **Max command length** and **allowlist of binaries** (git, python, pytest, bash, grep, etc.).
- **Redaction**: Outputs are redacted for secrets before being stored in the ledger.

## Evidence

- **events.jsonl**: One JSON object per line (hash-chained: each event has `previous_hash`, `event_hash`).
- **policy_compliance_summary.json**: `run_id`, `total_events`, `total_tool_calls`, `violations`, `compliant`, `violation_details`, `reason_codes`, `chain_tail_hash`.

## Usage

From the runner, use `--guarded` or `--mode pf_guarded` so that OpenHands runs with `SHELL` set to `guard/pf_guard_exec.sh` (or `.bat` on Windows). Env: `PF_GUARD_WORKSPACE`, `PF_GUARD_LEDGER_DIR`, `PF_GUARD_RUN_ID`, `PF_REPO_ROOT`. The executor appends each command to the ledger and exits with the command exit code (or 125 on forbidden, 126 on no command, 127 on missing env). Denials are **recoverable** by default: only the denied command fails (exit 125); the agent can continue. Fail-fast is not implemented by default.

## Ledger API

If `PF_LEDGER_URL` is set, each event is also POSTed to `{PF_LEDGER_URL}/events`. Integrates with PF runtime/ledger minimal server pattern.
