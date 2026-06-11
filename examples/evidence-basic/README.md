# Evidence basic example

Minimal Evidence v0.1 bundle used by the walkthrough and e2e tests.

```bash
pf evidence bundle pack --manifest examples/evidence-basic/manifest.json --out /tmp/bundle.json
pf evidence validate /tmp/bundle.json --strict --base-dir examples/evidence-basic
```

See [Evidence bundle walkthrough](../../docs/guides/evidence-bundle-walkthrough.md).
