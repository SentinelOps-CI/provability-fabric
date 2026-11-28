// SPDX-License-Identifier: Apache-2.0

package main

import (
	"context"
	"database/sql"
	"fmt"
)

// beginTenantTx binds tenant identity to one transaction on one pooled connection.
func (s *EvidenceService) beginTenantTx(ctx context.Context, tenant string, readOnly bool) (*sql.Tx, error) {
	if err := validateEvidencePathSegment("tenant_id", tenant); err != nil {
		return nil, err
	}
	options := &sql.TxOptions{ReadOnly: readOnly}
	if readOnly {
		options.Isolation = sql.LevelRepeatableRead
	}
	tx, err := s.db.BeginTx(ctx, options)
	if err != nil {
		return nil, err
	}
	if _, err := tx.ExecContext(ctx, "SELECT set_config('app.current_tenant', $1, true)", tenant); err != nil {
		_ = tx.Rollback()
		return nil, fmt.Errorf("bind database tenant: %w", err)
	}
	return tx, nil
}
