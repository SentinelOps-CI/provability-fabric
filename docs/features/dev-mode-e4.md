# Dev Mode (E4): Live Stream & DFA State

This document describes the Dev Mode live stream, per-decision latency, DFA state, and chunk/flush ticks visualization.

## Backend (Replay Service)

New endpoints (via API Gateway routing to Replay Service):

- `GET /api/v1/replay/:jobId/stream` Server-Sent Events stream of live dev-mode events
- `GET /api/v1/replay/:jobId/dfa_state` Returns the last known DFA state for a job

Event types emitted on the stream:

- `hello`: initial handshake
- `progress`: `{ progress }`
- `dfa_state`: `{ state_id }`
- `chunk_tick`: `{ sequence }`
- `flush_tick`: `{ sequence }`
- `decision_latency`: `{ latencies_ms: { permission_check, tool_call, egress } }`
- `job_started`, `job_completed`

## Console UI

A new `Dev Mode` page is available at `/dev`:

- Start a replay by entering a decision ID and clicking `Start Replay`
- Click `Connect Stream` to attach to the job's dev-mode event stream
- The page displays:
  - Current DFA state (auto-updated via events and manually refreshable)
  - Per-decision latency (ms)
  - Chunk and flush ticks with mini progress bars
  - Live events panel (latest first)

## API Client

Added helpers in `console/src/services/api.ts`:

- `getDevModeStreamUrl(jobId: string)` → EventSource URL
- `getDFAState(jobId: string)` → `{ job_id, state_id }`

## Notes

- SSE is used for low-latency updates with wide compatibility
- Event payloads are JSON; clients should parse `event.data`
- In production, decision latencies and DFA state should be produced by the runtime-sidecar instrumentation rather than simulated ticks
