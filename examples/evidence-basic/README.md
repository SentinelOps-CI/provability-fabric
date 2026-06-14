# Evidence basic example

Minimal Evidence v0.1 bundle used by the walkthrough and e2e tests.

```bash
# Build CLI once: cd core/cli/pf && go build -o pf .

# Pack (use a writable path: /tmp on Linux, %TEMP% on Windows, or a repo-local file)
pf evidence bundle pack --manifest examples/evidence-basic/manifest.json --out evidence-bundle-out.json
pf evidence validate evidence-bundle-out.json --strict --base-dir examples/evidence-basic
```

Golden outputs for quick checks live in [`expected/`](expected/):

- `expected/validation-report.pass.json` — stable fields from strict validation (compare `status`, `errors`, `warnings`)
- `expected/bundle.digest.txt` — single-line `bundle_digest` for the checked-in bundle

See [Evidence bundle walkthrough](../../docs/guides/evidence-bundle-walkthrough.md).
