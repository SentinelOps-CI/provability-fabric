# Certificate validation tool

This tool validates two certificate families without conflating their schemas:

- runtime certificates against `external/CERT-V1/schema/cert-v1.schema.json`;
- `cert_type: "trace_replay"` certificates against `specs/evidence/v0.2/schemas/trace-replay-cert.schema.json`.

The trace-replay schema is resolved from the repository containing this tool, so validation does not depend on the caller's working directory. `--schema` selects only the runtime-certificate schema and does not override the trace-replay schema.

## Installation

```bash
pip install -r requirements.txt
```

Trace-replay `timestamp` format checking requires `rfc3339-validator`. If that extra is missing, validation fails closed as an operational error rather than accepting structurally invalid date-time values.

## Usage

```bash
python validate.py evidence/**/*.cert.json tests/replay/out/**/*.cert.json
python validate.py --schema path/to/runtime-schema.json evidence/certs/session1/001.cert.json
```

Use `--allow-missing-schema` only when intentionally permitting runtime certificates to be skipped because the external runtime schema is unavailable. Such files are reported as skipped, not passed. Trace-replay validation always requires the checked-in Evidence v0.2 schema.

## Exit codes

- `0`: validation completed with no invalid files or operational errors; explicit runtime-schema skips may be present.
- `1`: one or more certificates are invalid.
- `2`: validation could not complete because of an operational error, such as a missing file, unreadable input, or required schema failure.

Schema validation establishes the documented structural contract. It does not by itself authenticate an arbitrary signature or prove replay-input binding; the Evidence replay execution path performs the additional trace/environment/result acceptance checks.
