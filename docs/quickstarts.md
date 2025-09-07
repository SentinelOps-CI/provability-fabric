# Quickstarts (5 minutes)

Three lanes:

- Standards lane (CERT emission only)
- Replay lane (deterministic replay)
- Full lane (compile→prove→build→deploy→replay)

## Standards Lane

```
npx create-sentinel-app my-standards-app
cd my-standards-app
make dev-up
# simulate middleware emitting a CERT
```

## Replay Lane

```
so replay run <decision-id> --open --json
```

## Full Lane

```
so policy compile --in policy.md --out build/
so policy prove --build build/
so policy build --build build/
so deploy --build build/ --epoch rotate
so replay run <decision-id> --open
so packet make <decision-id> --out artifacts/
```
