# CERT-V1 Validators – Adopt in 10 Minutes

This guide shows how to validate CERT-V1 evidence quickly in TypeScript, Python, and Go, with ready-made test vectors.

## Test Vectors

Location: `tests/cert-v1/`

- `valid.cert.json` – minimal valid certificate
- `invalid.cert.json` – intentionally malformed certificate

## TypeScript (Node.js)

Install dependencies:

```bash
npm install ajv
```

Validate against JSON Schema:

```ts
import Ajv from 'ajv';
import { readFileSync } from 'fs';

const schema = JSON.parse(readFileSync('external/CERT-V1/schema/cert-v1.schema.json', 'utf8'));
const ajv = new Ajv({ allErrors: true, strict: false });
const validate = ajv.compile(schema);

const data = JSON.parse(readFileSync('tests/cert-v1/valid.cert.json', 'utf8'));
if (validate(data)) {
  console.log('CERT valid');
} else {
  console.error('CERT invalid', validate.errors);
  process.exit(1);
}
```

## Python

```bash
pip install jsonschema
```

```python
import json
from jsonschema import validate, Draft7Validator

with open('external/CERT-V1/schema/cert-v1.schema.json', 'r') as f:
    schema = json.load(f)
with open('tests/cert-v1/valid.cert.json', 'r') as f:
    cert = json.load(f)

Draft7Validator.check_schema(schema)
validate(instance=cert, schema=schema)
print('CERT valid')
```

## Go

```go
package main

import (
	"encoding/json"
	"fmt"
	"os"

	"github.com/xeipuuv/gojsonschema"
)

func main() {
	schema := gojsonschema.NewReferenceLoader("file://external/CERT-V1/schema/cert-v1.schema.json")
	cert := gojsonschema.NewReferenceLoader("file://tests/cert-v1/valid.cert.json")
	res, err := gojsonschema.Validate(schema, cert)
	if err != nil { panic(err) }
	if res.Valid() { fmt.Println("CERT valid") } else { os.Exit(1) }
}
```

## Signature Verification (Optional)

Add a "sig" field (base64 or base64url) and verify using your preferred crypto library.

- Use a canonical JSON encoding (stable key ordering) before verify
- Support Ed25519 keys via local PEM or JWKS

See CLI `so cert verify --schema-validate --jwks <url> --key <pem>` for reference.
