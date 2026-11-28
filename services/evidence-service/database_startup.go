// SPDX-License-Identifier: Apache-2.0

package main

import (
	"context"
	"database/sql"
	"fmt"
	"os"
	"strings"
	"time"
)

// Migration is an explicit, offline administrative operation; it never
// starts the HTTP listener and never uses the runtime DATABASE_URL.
func migrateEvidenceDatabase() error {
	dsn := strings.TrimSpace(os.Getenv("EVIDENCE_MIGRATION_DATABASE_URL"))
	if dsn == "" {
		return fmt.Errorf("EVIDENCE_MIGRATION_DATABASE_URL is required")
	}
	db, err := sql.Open("postgres", dsn)
	if err != nil {
		return err
	}
	defer db.Close()
	return (&EvidenceService{db: db}).initializeSchema()
}

// Runtime startup checks the expected RLS policy and rejects excessive
// privileges. The database administrator and schema remain trusted.
func (s *EvidenceService) validateRuntimeDatabase() error {
	if s.db == nil {
		return nil
	}
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	var safe bool
	err := s.db.QueryRowContext(ctx, `
		SELECT NOT r.rolsuper AND NOT r.rolbypassrls
			AND NOT pg_has_role(current_user, c.relowner, 'MEMBER')
			AND row_security_active(c.oid)
			AND has_table_privilege(c.oid, 'SELECT')
			AND has_table_privilege(c.oid, 'INSERT')
			AND NOT has_table_privilege(c.oid, 'UPDATE')
			AND NOT has_table_privilege(c.oid, 'DELETE')
			AND NOT has_table_privilege(c.oid, 'TRUNCATE')
			AND NOT has_table_privilege(c.oid, 'TRIGGER')
			AND NOT has_schema_privilege(c.relnamespace, 'CREATE')
		FROM pg_class c, pg_roles r
		WHERE c.oid = to_regclass('certificates') AND r.rolname = current_user
	`).Scan(&safe)
	if err != nil {
		return fmt.Errorf("inspect runtime database privileges: %w", err)
	}
	if !safe {
		return fmt.Errorf("runtime identity must have active RLS and restricted read/insert privileges")
	}

	// Reject additional policies as they could broaden the authorized scope.
	// pg_get_expr is the server's deparsed expression for the migrated policy.
	var count, expected int
	err = s.db.QueryRowContext(ctx, `
		SELECT count(*), count(*) FILTER (
			WHERE polname = 'tenant_isolation' AND polcmd = '*'
			AND polpermissive AND polroles = ARRAY[0::oid]
			AND pg_get_expr(polqual, polrelid) =
				'((tenant_id)::text = current_setting(''app.current_tenant''::text, true))'
			AND pg_get_expr(polwithcheck, polrelid) =
				'((tenant_id)::text = current_setting(''app.current_tenant''::text, true))'
		)
		FROM pg_policy WHERE polrelid = to_regclass('certificates')
	`).Scan(&count, &expected)
	if err != nil {
		return fmt.Errorf("inspect runtime tenant policy: %w", err)
	}
	if count != 1 || expected != 1 {
		return fmt.Errorf("unexpected certificate tenant policy; apply reviewed migration")
	}
	return nil
}
