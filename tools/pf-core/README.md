# PF-Core CLI wrapper (Phase 7 PR-3)

Install:

```bash
pip install -e tools/pf-core
```

Invoke (same surface as provability-fabric-core):

```bash
python -m pf_core_wrapper.cli core schema-check --schemas vendor/pf-core/schemas
python -m pf_core.cli core compile-observation --schemas vendor/pf-core/schemas --file obs.json
```

Or via repo helper:

```bash
bash scripts/pf-core.sh core check-trace --schemas vendor/pf-core/schemas --file trace.json
```

The Go `pf` CLI exposes `pf core` as a subprocess bridge to this wrapper.
