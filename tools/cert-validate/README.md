# CERT-V1 Schema Validation Tool

This tool validates JSON files against the CERT-V1 schema from the external standards.

## Installation

```bash
pip install -r requirements.txt
```

## Usage

### Basic validation
```bash
python validate.py evidence/**/*.cert.json tests/replay/out/**/*.cert.json
```

### Validate specific files
```bash
python validate.py evidence/certs/session1/001.cert.json
```

### Use custom schema path
```bash
python validate.py --schema path/to/schema.json *.json
```

### Verbose output
```bash
python validate.py -v evidence/**/*.json
```

## Exit Codes

- `0`: All files validated successfully
- `1`: Validation failed (one or more files failed validation)

## Schema Source

The tool uses the CERT-V1 schema from `external/CERT-V1/schema/cert-v1.schema.json`.
This schema is maintained as an external standard and should not be modified in this repository.
