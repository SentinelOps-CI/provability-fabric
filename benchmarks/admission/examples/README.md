# PCS benchmark reference artifacts

Committed `*.pcs_bench_ingest.reference.json` files are gold-standard `PcsBenchIngest.v0` snapshots for diff audits and CI.

| File | Producer output |
|------|-----------------|
| `labtrust_qc_release.pcs_bench_ingest.reference.json` | `benchmark_runs/labtrust_admission/pcs_bench_ingest.v0.json` |

CI and `TestExportPCSBenchIngestReferenceArtifact` enforce the following properties.

- `producer_id` is `provability-fabric`, `suite_id` is `pf-labtrust-admission-v0`, and `workflow_id` is `hospital_lab.qc_release`
- `failure_localization_reports`, `explain_quality_reports`, and `artifact_refs` are non-empty
- `commands` and `artifact_refs[].path` use repo-relative forward slashes for portability

See [docs/pcs/admission-benchmarks.md](../../../docs/pcs/admission-benchmarks.md).

Regenerate after changing admission benchmark emit logic or labtrust cases.

```bash
make pcs-bench-producer
make export-pcs-benchmark-ingest-reference
bash scripts/pcs-bench-validate-ingest.sh \
  --input benchmarks/admission/examples/labtrust_qc_release.pcs_bench_ingest.reference.json \
  --bundle-dir benchmark_runs/labtrust_admission \
  --pcs-core ../pcs-core \
  --release-grade
```
