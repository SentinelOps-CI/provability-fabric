# PCS benchmark reference artifacts

Committed `*.pcs_bench_ingest.reference.json` files are gold-standard `PcsBenchIngest.v0` snapshots for diff audits and CI (`pcs validate`, `TestExportPCSBenchIngestReferenceArtifact`).

Regenerate after changing admission benchmark emit logic or labtrust cases:

```bash
bash scripts/export-pcs-benchmark-ingest-reference.sh
# or: make export-pcs-benchmark-ingest-reference
```
