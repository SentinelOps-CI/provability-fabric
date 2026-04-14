# Direct Agent Promotion Decision

Date: 2026-03-23

## Decision

No-go for default-engine promotion at this time.

## Evidence

- Gate run: `runs/direct-agent-ab-gate-10-hardening`
- Decision artifact: `ab_gate_decision.json` (`promotable: false`)
- Summary artifact: `ab_gate_summary.json`
- Checkpoint artifact: `ab_gate_checkpoint.json`

## Why promotion is blocked

The strict 10-instance gate did not pass under required conditions. The run produced a bounded failure result in baseline phase under enforced runtime guardrails, so promotion criteria were not met.

## Promotion-phase status

- Switch default engine to `direct_agent`: **deferred**
- 20-instance canary: **deferred**
- Full Verified run: **deferred**
- OpenHands remains secondary fallback with telemetry.

## Next unblock sequence

1. Stabilize baseline/candidate completion under strict gate budgets without bounded-phase abort.
2. Re-run strict 10 gate with same IDs and required flags.
3. Promote only if gate passes (`patch_apply.applies_false == 0` and non-regression checks satisfied).
