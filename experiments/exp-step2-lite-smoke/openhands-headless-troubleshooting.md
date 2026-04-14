# OpenHands headless: empty patches and next steps

When the baseline or PF run completes but every instance has an empty patch, the PF pipeline is behaving correctly: it runs OpenHands in the workspace repo, parses the trajectory, and diffs the same repo. Empty patches occur when the **trajectory contains only MessageEvent (no ActionEvent)** — the agent sent messages but did not run tools (edit_file, run_terminal_cmd, etc.). The runner's task prompt (written to `task_prompt.md` in each workspace) now includes an explicit instruction to use the file_editor or edit_file tool so the agent is more likely to emit ActionEvents; use a fresh run (or re-materialize workspaces) to pick this up. If problems persist, follow the steps below (version, minimal test, model, GUI comparison).

## Confirm the diagnosis

From repo root, after a run that produced empty patches:

```bash
# Count event kinds in one instance's trajectory (expect only MessageEvent if no tools were used)
grep -o '"kind": "[^"]*"' workspaces/astropy__astropy-12907/scratch/openhands_trajectory.jsonl | sort | uniq -c
# Example output:       2 "kind": "MessageEvent"   -> no ActionEvent, so no tool calls
```

If you see only `MessageEvent`, the agent never took actions; next steps below apply.

If the log shows **ConversationErrorEvent: 1** alongside MessageEvent, the run hit a conversation-level error (exception or limit). The engine now logs `ConversationErrorEvent: code=... detail=...` in the same run output; check that line for the actual error (e.g. API/rate-limit, context length, or MaxIterationsReached). Fix the cause (API key, model, or OpenHands config) then re-run.

### AuthenticationError (Incorrect API key)

If the log shows `code=AuthenticationError` and "Incorrect API key provided" or "OpenAIException", determine whether you are using **OpenAI** or **Prime Intellect** (`pit_*` keys).

#### Prime Intellect (`pit_*` / `OPENHANDS_PROVIDER=prime_intellect`)

If your key starts with **`pit_`** or you set **`PRIME_INTELLECT_API_KEY`**, the error text may still say **OpenAI** or **platform.openai.com** because LiteLLM uses OpenAI-shaped errors. That usually means the request was routed to the **wrong base URL**, not that you need an **`sk-*`** key.

1. **Set provider explicitly:** `export OPENHANDS_PROVIDER=prime_intellect` (or set it in `.env` and source before the cycle). The bench engine forwards this to the OpenHands CLI subprocess.
2. **Check routing without secrets:** Open `runs/<run_id>/env.json` from the failing run. Expect `openhands_provider` = `prime_intellect`, `llm_base_url_source` = `DEFAULT_PRIME_INTELLECT_INFERENCE_BASE_URL` (or your explicit base), and `llm_base_url_effective` pointing at Prime Inference (or your override), not only OpenAI.
3. **Key and account:** Confirm **`PRIME_INTELLECT_API_KEY`** is valid and inference is enabled for that key. Optional **`PRIME_TEAM_ID`** may be required for your account; it is sent as **`X-Prime-Team-ID`** when set.
4. **Custom base URL:** If you must use a non-default endpoint, set **`PRIME_INTELLECT_BASE_URL`** or **`OPENAI_BASE_URL`** (see **`bench/swebench/provider_env.py`** and **`bench/swebench/README.md`**).

Re-run from a shell that loads `.env` (e.g. `bash experiments/scripts/run-baseline-pf-cycle.sh`).

#### OpenAI (`sk-*` / default provider)

If you use **`OPENAI_API_KEY`** with **`OPENHANDS_PROVIDER=openai`** (default):

1. **Create or rotate the key**: Go to https://platform.openai.com/account/api-keys and create a new key (or revoke the old one and create a new one).
2. **Update `.env`**: Set `OPENAI_API_KEY=sk-proj-...` (paste the new key; no quotes needed). Ensure the line has no trailing space or CRLF. On Windows, save the file with LF line endings or run `python experiments/scripts/fix_crlf.py .env`.
3. **Re-run from a shell that loads `.env`**: Run `bash experiments/scripts/run-baseline-pf-cycle.sh` from the repo root so the script sources `.env` before starting the runner.

The engine sanitizes keys (strips CRLF and surrounding quotes) before passing them to OpenHands; if the key is still rejected, the key itself is invalid or expired.

## 1. Check OpenHands version

Pin and record the version. The runner writes `runs/<run_id>/env.json` with `openhands_version` when available.

```bash
# From repo root (with venv activated if you use one)
pip show openhands
python -c "import openhands; print(getattr(openhands, '__version__', 'unknown'))"
```

If you installed from source (e.g. OpenHands GitHub repo), note the commit or tag. Try a known-good version or upgrade to the latest and re-run one instance.

## 2. Run a minimal headless test (must use tools)

Verify that headless mode can perform at least one file edit in the same environment the runner uses.

```bash
# From repo root; ensure .env is sourced or OPENAI_API_KEY is set
source .env 2>/dev/null || true
export LLM_API_KEY="${OPENAI_API_KEY}"
export LLM_MODEL="${OPENHANDS_MODEL:-gpt-4o-mini}"

cd workspaces/astropy__astropy-12907/repo
openhands --headless --override-with-envs --json -t "Create an empty file named test_edit.txt in the current directory. Use the write or edit_file tool."
```

Then check whether a file was created. When you run OpenHands **manually**, trajectory JSON is printed to the terminal only; `workspaces/.../scratch/openhands_trajectory.jsonl` is written by the **PF runner** when it invokes the subprocess, so it will not exist or will be from a previous run. Either redirect and grep, or inspect the terminal output:

```bash
ls -la test_edit.txt
git status
cd ../..   # back to repo root
# If you redirected: openhands ... > /tmp/oh_manual.jsonl 2>&1
# then: grep -o '"kind": "[^"]*"' /tmp/oh_manual.jsonl | sort | uniq -c
# Otherwise look in the terminal for "kind": "ActionEvent" and "File created successfully"
```

If the minimal task produces ActionEvent and creates the file, headless tool use works; the SWE-bench task prompt may need to explicitly ask for tool use (see below). If the minimal task also produces only MessageEvent and no file, the issue is OpenHands headless or the model in this environment.

**If the minimal test succeeded:** The runner's task prompt has been updated to include an explicit instruction to use the file_editor or edit_file tool (and run_terminal_cmd if needed). Re-run a baseline or PF run so new workspaces get the updated task_prompt.md; existing workspaces already have the old prompt, so either re-materialize (delete the workspace dir and re-run) or run with a fresh instance.

## 3. Try a different model

Some models are better at following tool-calling instructions. Override the model for one run:

```bash
# From repo root
export OPENHANDS_MODEL="gpt-4o"   # or another model your API supports
python bench/swebench/runner.py \
  --dataset Lite \
  --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt \
  --experiment-dir experiments/exp-step2-lite-smoke \
  --engine openhands \
  --max_instances 1 \
  --out runs/test-model/predictions.jsonl \
  --runs-dir runs/test-model
```

Check the trajectory again for that instance; if you see ActionEvent and a non-empty patch, the previous model was the likely cause.

## 4. Compare with GUI (interactive) run

If you have a desktop or VNC session, run OpenHands once in interactive (GUI/TUI) mode on the same task to see if the agent uses tools there:

```bash
cd workspaces/astropy__astropy-12907/repo
openhands -t "Create an empty file named test_edit_gui.txt."
# Interact as needed; then check:
ls -la test_edit_gui.txt
git status
```

If the agent edits files in GUI mode but not in headless, the difference is headless-specific (report or search OpenHands issues for headless tool execution).

## 5. OpenHands config and skills

The runner sets `RUNTIME=process`, `LLM_API_KEY`, `LLM_MODEL`, optional `LLM_BASE_URL`, and `OH_PERSISTENCE_DIR` to a scratch dir (see **`bench/swebench/engines/openhands_engine.py`**). For Prime runs, `OPENHANDS_PROVIDER` and related vars are also passed through to the CLI subprocess. OpenHands may load skills (e.g. github, gitlab) that add extra prompt text; that should not prevent tool use. To use a minimal config:

```bash
# Optional: inspect generated config
cat workspaces/astropy__astropy-12907/scratch/openhands_persistence/config.toml
```

Check OpenHands docs for any headless-only flags or config that enable tool use (e.g. agent class, sandbox settings).

## 6. References

- OpenHands headless: https://docs.openhands.dev/openhands/usage/run-openhands/headless-mode
- OpenHands CLI: https://docs.openhands.dev/openhands/usage/cli/command-reference
- Event types (MessageEvent vs ActionEvent): https://docs.openhands.dev/sdk/arch/events
- PF runner and trajectory: **bench/swebench/README.md** (Prerequisites, "Trajectory events but no modified files", "Viewing trajectory and running OpenHands manually")
