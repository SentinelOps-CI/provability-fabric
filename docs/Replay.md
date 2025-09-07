## Replays & Low-View Determinism

This repo integrates the canonical TRACE-REPLAY-KIT to run deterministic replays and assert low-view equality.

Link: https://github.com/verifiable-ai-ci/TRACE-REPLAY-KIT

Quickstart:

1) Ensure submodules are initialized
```
make submodules
```

2) Run replays
```
bash tests/replay/run_replays.sh
```

3) Validate emitted CERTs
```
make validate-certs
```

CLI usage:

- Run a trace via TRACE-REPLAY-KIT
```
so trace run --trace tests/replay/bundles/simple/trace.json --fixtures tests/replay/bundles/simple/fixtures --out tests/replay/out
```

- Compare low-view equality across runs (oracle)
```
so trace compare-lowview --in tests/replay/out --threshold 0.999999
```

- Generate a replay report (basic aggregator)
```
so trace report --in tests/replay/out
```

Compliance packet (Console and CLI):

- Console Evidence tab → “Download Packet” creates a zip containing:
  - cert.json, replay-report.json, audit-proof.json, conformance.md

- CLI
```
so packet make <decision-id> --out artifacts/compliance_packet.zip
```

Outputs are written under `tests/replay/out/`, with CERTs in `tests/replay/out/certs/`.

The low-view oracle enforces ≥99.9999% determinism.


