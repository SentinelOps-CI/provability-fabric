# Forensic replay basic

Walkthrough for pass and tamper cases using `examples/forensic-replay-basic/`.

## Passing case

```bash
pf evidence replay --bundle examples/forensic-replay-basic/basic-evidence-bundle.json
```

Expect exit code 0 and `trace_found=true` when the bundle includes an execution trace.

## Tampered case

`tampered-bundle.json` contains an invalid `bundle_digest`.

```bash
pf evidence replay --bundle examples/forensic-replay-basic/tampered-bundle.json
echo exit:$?
```

Expect non-zero exit — strict validation fails closed.

## Testbed

```bash
bash testbed/evidence-v0.1/run_tamper_case.sh
pytest tests/forensic_replay/test_forensic_replay_basic.py -q
```

## Related

- [Replay guarantees](replay-guarantees.md)
- [Evidence v0.1 quickstart](evidence-v0.1-quickstart.md)
