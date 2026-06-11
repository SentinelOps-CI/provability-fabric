# Evidence bundle walkthrough

End-to-end path using `examples/evidence-basic/`.

## 1. Inspect manifest

`examples/evidence-basic/manifest.json` lists artifact roles and relative paths.

## 2. Pack

```bash
pf evidence bundle pack \
  --manifest examples/evidence-basic/manifest.json \
  --out /tmp/basic-bundle.json
```

## 3. Validate strict

```bash
pf evidence validate /tmp/basic-bundle.json --strict --report-out /tmp/report.json
```

Expect `status: pass` in the validation report.

## 4. Tamper test

Edit any artifact byte or `bundle_digest` and re-run validate — strict mode must fail closed.

## 5. Automated test

```bash
pytest tests/e2e/test_evidence_bundle_basic.py -q
```

## Related

- [Bundle format spec](../specs/evidence-bundle-v0.1.md)
- [Compatibility matrix](../specs/evidence-compatibility.md)
