# Red-team HTTP test harnesses

The PII red-team program in `pii_leak.py` targets the Rust egress firewall's
`POST /egress` endpoint. It sends the server's `EgressRequest` fields
(`text`, `tenant`, `subject_id`, `plan_id`, `context`, and `streaming`),
checks the observed `EgressResponse` fields, and binds each certificate to its
requested tenant and plan identifier.

For a disposable development deployment with the documented `acme-corp` policy
and reachable test ledger, use:

```bash
python3 -m pip install -r tests/redteam/requirements.txt
python3 tests/redteam/pii_leak.py --firewall-url http://127.0.0.1:8081 --tenant acme-corp --vectors 100 --concurrency 4 --seed 42
```

The test fails on transport failures, malformed or misattributed responses,
incomplete vector coverage, missing observed blocked-PII or permitted-clean
controls, or unexpected policy decisions. It generates synthetic inputs and
writes a local JSON report. It does **not** verify certificate signatures,
independent policy semantics, a deployed agent's use of the `blocked` response
field, or operational privacy noninterference.

The PII test's original case quotas account for approximately 85% of the
requested sample; the remainder is now filled using identified, distinct
synthetic direct-PII and clean control cases. This preserves the legacy family
allocation while accurately honoring `--vectors`. The count is a harness input,
not a statistically representative estimate of a production threat distribution.

The ABAC fuzz harness is still awaiting reconciliation with the Rust retrieval
gateway's `POST /query` contract, authenticated capability tokens and seeded
multi-tenant fixture. See issue #294. An empty search index cannot validate
tenant isolation. Until that work is complete, the ABAC probe's strict
observation gate is expected to fail without positive document observations.

The offline red-team workflow is a harness smoke, not a live security test.
