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

Outputs are written under `tests/replay/out/`, with CERTs in `tests/replay/out/certs/`.

The low-view oracle enforces ≥99.9999% determinism.


