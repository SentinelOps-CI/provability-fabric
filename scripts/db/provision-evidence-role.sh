#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Local root Compose database only. Production roles are provisioned separately.
set -euo pipefail
if [[ "${PGHOST:-}" != postgres || "${PGUSER:-}" != sentinelops || "${PGDATABASE:-}" != sentinelops ]]; then
  echo "Refusing non-local Compose database configuration" >&2
  exit 2
fi
if [[ ! "${PF_EVIDENCE_RUNTIME_PASSWORD:-}" =~ ^[0-9a-f]{64}$ ]]; then
  echo "PF_EVIDENCE_RUNTIME_PASSWORD must be 64 lowercase hexadecimal characters" >&2
  exit 2
fi
psql -X -v ON_ERROR_STOP=1 <<'SQL'
\getenv runtime_password PF_EVIDENCE_RUNTIME_PASSWORD
BEGIN;
SELECT 'CREATE ROLE pf_evidence_runtime LOGIN NOSUPERUSER NOBYPASSRLS NOCREATEDB NOCREATEROLE NOREPLICATION NOINHERIT'
 WHERE NOT EXISTS (SELECT 1 FROM pg_roles WHERE rolname = 'pf_evidence_runtime')
\gexec
DO $$
BEGIN
    IF NOT EXISTS (
        SELECT 1 FROM pg_roles r
        WHERE r.rolname = 'pf_evidence_runtime' AND r.rolcanlogin
          AND NOT r.rolsuper AND NOT r.rolbypassrls AND NOT r.rolcreatedb
          AND NOT r.rolcreaterole AND NOT r.rolreplication AND NOT r.rolinherit
          AND NOT EXISTS (SELECT 1 FROM pg_auth_members m WHERE m.member = r.oid)
    ) THEN
        RAISE EXCEPTION 'existing evidence runtime role has unexpected attributes or memberships';
    END IF;
END $$;
ALTER ROLE pf_evidence_runtime PASSWORD :'runtime_password';
GRANT USAGE ON SCHEMA public TO pf_evidence_runtime;
GRANT SELECT, INSERT ON TABLE public.certificates TO pf_evidence_runtime;
COMMIT;
SQL
echo "Local evidence runtime role provisioned; service startup verifies effective privileges and RLS."
