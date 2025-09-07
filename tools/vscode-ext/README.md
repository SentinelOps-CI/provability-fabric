# SentinelOps VS Code Extension (v0)

Features:

- DSL Preview Pane (virtual document): Command compiles with `so policy compile` and opens a read‑only ActionDSL preview via a custom `dsl-preview:` URI.
- Hover Diagnostics: On markdown/plaintext policies, hover shows compiled rule ID and a docs link using `build/ir.json` source map.
- CERT Viewer UX: Context actions to validate CERTs, run replay, and copy hashes (proof/automata/policy/bundle).

Commands:

- "SentinelOps: Open DSL Preview"
- "SentinelOps: Validate CERT"
- "SentinelOps: Run Replay from CERT"
- "SentinelOps: Copy CERT Hash"

Settings:

- `sentinelops.cliPath` — default `so`.
- `sentinelops.compileOutDir` — default `build`.

Notes:

- The extension shells out to your local CLI and respects the configured path.
- Ensure A1–B2 are implemented (they are in this repo) for full functionality.

Packaging:

1. Install deps and build:
   - `npm i`
   - `npm run compile`
2. Package the extension:
   - `npx vsce package`
   - This generates a `.vsix` file you can install in VS Code.
3. Publish (optional):
   - Create a publisher and Personal Access Token.
   - `npx vsce publish patch|minor|major`

Configuration:

- Point `sentinelops.cliPath` at your CLI binary if not on PATH (e.g., `C:\\bin\\so.exe` on Windows).
- Change `sentinelops.compileOutDir` if your workflow writes build outputs elsewhere.
- The CERT viewer expects CERT-V1 JSON files; use the context menu or title bar actions.

Troubleshooting:

- If compile fails, check the Output panel channel “sentinelops” for CLI stderr/stdout.
- Ensure `so` commands run from your shell with the same environment as VS Code.


