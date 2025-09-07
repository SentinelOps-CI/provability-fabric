# Error Catalog

A unified error envelope is returned across CLI, Console, and Runtime services:

```
{
  "error": {
    "code": "<MACHINE_CODE>",
    "cause": "<human-readable cause>",
    "action": "<actionable next step>",
    "docs_url": "https://docs.sentinelops.dev/error-catalog#<MACHINE_CODE>"
  }
}
```

## Standard Codes

- INVALID_REQUEST: Request body or parameters invalid.
- SERVICE_NOT_FOUND: No backend matched the path.
- CERT_STORE_FAILED: Certificate persistence or validation failed.
- CERT_SEARCH_FAILED: Certificate lookup failed.
- CERT_NOT_FOUND: Certificate not found for the given selector.
- CFG_MISSING_KEY: Missing config key in `sentinelops.yml`.
- CFG_INVALID_VALUE: Invalid value in `sentinelops.yml`.
- SPEC_AMBIGUOUS_ACTOR: Ambiguous actor in English spec.

Each code links here for remediation steps.
