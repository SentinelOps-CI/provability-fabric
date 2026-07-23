# Dev Mode (E4): live stream and DFA state

Console Dev Mode visualizes replay job progress, per-decision latency, DFA state, and chunk/flush ticks.

## Backend (replay service)

Routed via the API gateway to the replay service:

| Method | Path | Purpose |
|--------|------|---------|
| `GET` | `/api/v1/replay/:jobId/stream` | SSE stream of live Dev Mode events |
| `GET` | `/api/v1/replay/:jobId/dfa_state` | Last known DFA state for a job |

Event types on the stream: `hello`, `progress`, `dfa_state`, `chunk_tick`, `flush_tick`, `decision_latency`, `job_started`, `job_completed`.

Implementation: `services/replay-service/main.go` (`getDFAStateHandler`, stream routes).

## Console UI

Page at `/dev` (`console/src/pages/DevModePage.tsx`):

- Start a replay by decision ID, then connect the SSE stream
- Shows DFA state, decision latencies (ms), chunk/flush ticks, and a live events panel

API helpers in `console/src/services/api.ts`: `getDevModeStreamUrl`, `getDFAState`.

## Notes

- SSE payloads are JSON in `event.data`
- Production-shaped deployments should emit latencies and DFA state from runtime/sidecar instrumentation rather than simulated ticks
- Local stack ports: [local-workflows.md](../dev/local-workflows.md)
