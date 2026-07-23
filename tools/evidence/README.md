# Evidence session bundles

Scripts under this directory build auditor-facing session safety-case bundles
(Avro schemas + DSSE-signed manifests).

## Config

`session_bundle.py` loads `session_config.yaml` when `--config` points at an
existing file. If the path is omitted or missing, the same defaults are used
in code (see `SessionBundleGenerator.load_config`).

Committed defaults: [session_config.yaml](session_config.yaml)

```bash
python tools/evidence/session_bundle.py \
  --config tools/evidence/session_config.yaml \
  --start-time "$(date -u -d '24 hours ago' -Iseconds)" \
  --end-time "$(date -u -Iseconds)"
```

CI: `.github/workflows/evidence.yaml` passes the committed config path.
