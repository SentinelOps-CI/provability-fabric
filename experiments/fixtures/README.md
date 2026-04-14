# Experiment fixtures

Minimal in-repo data used by verification and tests (no network, no Docker).

- **verify_publish_bundle/** – Publish dir (`publish/`) and `compare.json` satisfying verify_publish_bundle.py and compare_report.schema.json. Used by `.github/workflows/verify-publish-bundle.yaml` and `run_verification_tests.py`.
- **stress_baseline/**, **stress_pf/** – Empty run dirs for `summarize_stress_run.py` minimal path (no instance timing); produces stress_summary with schema_version and provenance only.
