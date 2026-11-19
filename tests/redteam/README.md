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

The ABAC fuzz program now uses the retrieval gateway's `POST /query`
request and response fields. It accepts an independently authored reference
manifest with at least two tenants and known public documents for each. It
verifies document identifiers, tenant ownership, labels, SHA-256 content
hashes, receipt attribution and explicit denial controls for empty tokens and
the `secret` label. Receipt signature presence is checked, not its actual
cryptographic verification. The current Rust gateway also accepts arbitrary
nonempty capability tokens; the real authorization defects are tracked
separately in issue #297.

The checked-in `fixtures/abac-reference.example.json` is a schema example,
not a seeded service or observed security result. The current gateway starts
with an empty index and exposes no document-seeding HTTP route. First populate
a disposable fixture-enabled gateway independently with exactly the declared
documents. Then run:

```bash
export PF_RETRIEVAL_CAPABILITY_TOKEN="<disposable-test-token>"
python3 tests/redteam/abac_fuzz.py --base-url http://127.0.0.1:8080 --fixture-manifest tests/redteam/fixtures/abac-reference.example.json --queries 60 --seed 42
```

The harness refuses missing credentials or reference manifests. It fails if
one tenant has no observed positive document, if declared negative controls are
unobserved, or if any response is malformed or unknown to the independent
reference. Until a separately seeded gateway and independent reference
authorization specification are available, these probes are not proof of
tenant-isolation or capability-enforcement correctness. See issues #294 and
#297.

The offline red-team workflow is a harness smoke, not a live security test.
