# Forensic replay basic

Contains a passing bundle and a tampered bundle (`tampered-bundle.json`) with an invalid `bundle_digest`.

```bash
pf evidence replay --bundle examples/forensic-replay-basic/basic-evidence-bundle.json
pf evidence replay --bundle examples/forensic-replay-basic/tampered-bundle.json || true
```

See [Forensic replay basic](../../docs/guides/forensic-replay-basic.md).
