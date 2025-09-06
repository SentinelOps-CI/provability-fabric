# Buf usage for API v1

This directory contains protobuf specs. Lint and breaking change checks are configured via `api/buf.yaml`.

Common commands:

```bash
buf lint
buf breaking --against .git#ref=main
```

Optionally, add a `buf.gen.yaml` to generate stubs for Go and TypeScript.


