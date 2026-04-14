## Demos

### MCP Sidecar Demo (Permissions / Epochs / IFC)

Repo: https://github.com/SentinelOps-CI/mcp-sidecar-demo

What it shows:
- Permission epochs with runtime bumps
- Field-level witnesses (Merkle path) for reads/writes
- Sidecar logs: permit/deny decisions and mini-CERTs (per emission)

How to run:
1) Follow the demo repo README to start the sidecar + MCP server.
2) Point your client (Claude Desktop / Cursor) to the SSE endpoints exposed by the demo (see demo docs):
   - SSE stream: `http://localhost:8787/sse`
   - Control: `http://localhost:8787/epoch` to bump epochs
3) Run sample tool calls in the client; observe sidecar logs and permit/deny decisions.
4) Check `evidence/` for emitted mini-CERTs.

Notes:
- Ensure witness mode is enabled in the policy to require Merkle path proofs on reads/writes.
- Bump epochs via the control endpoint to force policy transitions.

See also: `examples/edge-middleware/perm/epoch.yaml` for a minimal policy aligned with the demo.


