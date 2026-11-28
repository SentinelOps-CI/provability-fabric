// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

package main

import (
	"context"
	"database/sql"
	"encoding/json"
	"fmt"
	"net/url"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/google/uuid"
)

// openDisposablePostgres connects only to the explicitly configured CI fixture.
// Local tests skip the database integration when no disposable database is supplied.
func openDisposablePostgres(t *testing.T) *sql.DB {
	t.Helper()
	dsn := os.Getenv("EVIDENCE_TEST_DATABASE_URL")
	if dsn == "" {
		t.Skip("EVIDENCE_TEST_DATABASE_URL is required for database integration")
	}
	db, err := sql.Open("postgres", dsn)
	if err != nil {
		t.Fatalf("open disposable PostgreSQL: %v", err)
	}
	t.Cleanup(func() { _ = db.Close() })
	ctx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()
	if err := db.PingContext(ctx); err != nil {
		t.Fatalf("disposable PostgreSQL fixture is unreachable: %v", err)
	}
	return db
}

func TestEvidencePostgresSchemaIsIdempotentAndTenantPolicyApplies(t *testing.T) {
	db := openDisposablePostgres(t)
	service := &EvidenceService{db: db}
	if err := service.initializeSchema(); err != nil {
		t.Fatalf("initialize PostgreSQL schema: %v", err)
	}

	// Simulate a previously deployed, dangerously permissive service-owned
	// policy. Reinitialization must restore the intended tenant predicate.
	if _, err := db.Exec(`
		DROP POLICY tenant_isolation ON certificates;
		CREATE POLICY tenant_isolation ON certificates FOR ALL TO PUBLIC
		USING (true) WITH CHECK (true);
	`); err != nil {
		t.Fatalf("install disposable permissive fixture policy: %v", err)
	}
	if err := service.initializeSchema(); err != nil {
		t.Fatalf("reinitialize PostgreSQL policy: %v", err)
	}
	if err := service.initializeSchema(); err != nil {
		t.Fatalf("repeat idempotent schema initialization: %v", err)
	}

	var policyCount int
	var enabled bool
	if err := db.QueryRow(`
		SELECT count(*) FROM pg_policies
		WHERE schemaname = current_schema()
		  AND tablename = 'certificates'
		  AND policyname = 'tenant_isolation'
	`).Scan(&policyCount); err != nil {
		t.Fatalf("inspect policy catalog: %v", err)
	}
	if policyCount != 1 {
		t.Fatalf("expected one managed RLS policy, found %d", policyCount)
	}
	if err := db.QueryRow(`
		SELECT relrowsecurity FROM pg_class
		WHERE oid = 'certificates'::regclass
	`).Scan(&enabled); err != nil {
		t.Fatalf("inspect table row security: %v", err)
	}
	if !enabled {
		t.Fatal("certificate row-level security is disabled")
	}

	// A NOLOGIN, non-owner role has SELECT permission but cannot bypass RLS.
	// The entire test transaction is rolled back, including role creation.
	tx, err := db.Begin()
	if err != nil {
		t.Fatal(err)
	}
	defer tx.Rollback()
	cert := validStorageTestCertificate()
	for _, tenant := range []string{"fixture-tenant-a", "fixture-tenant-b"} {
		cert.TenantID = tenant
		encoded, err := json.Marshal(cert)
		if err != nil {
			t.Fatal(err)
		}
		_, err = tx.Exec(`
			INSERT INTO certificates (
				bundle_id, policy_hash, proof_hash, automata_hash, labeler_hash,
				ni_claim, ni_monitor, sidecar_build, tenant_id, session_id,
				timestamp, cert_data
			) VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,$11,$12)
		`, cert.BundleID, cert.PolicyHash, cert.ProofHash,
			cert.AutomataHash, cert.LabelerHash, cert.NIClaim, cert.NIMonitor,
			cert.SidecarBuild, cert.TenantID, cert.SessionID,
			cert.Timestamp, string(encoded))
		if err != nil {
			t.Fatalf("seed disposable tenant fixture %s: %v", tenant, err)
		}
	}
	role := "evidence_ci_reader_" + strings.ReplaceAll(uuid.NewString(), "-", "")[:12]
	if _, err := tx.Exec("CREATE ROLE " + role + " NOLOGIN"); err != nil {
		t.Fatalf("create restricted test role: %v", err)
	}
	if _, err := tx.Exec("GRANT SELECT ON certificates TO " + role); err != nil {
		t.Fatalf("grant restricted fixture access: %v", err)
	}
	if _, err := tx.Exec("SET LOCAL ROLE " + role); err != nil {
		t.Fatalf("switch to non-owner restricted role: %v", err)
	}

	checkCount := func(tenant string, expected int) {
		t.Helper()
		if tenant != "" {
			if _, err := tx.Exec("SELECT set_config('app.current_tenant', $1, true)", tenant); err != nil {
				t.Fatalf("bind tenant %q: %v", tenant, err)
			}
		}
		var observed int
		if err := tx.QueryRow("SELECT COUNT(*) FROM certificates").Scan(&observed); err != nil {
			t.Fatalf("query restricted tenant %q: %v", tenant, err)
		}
		if observed != expected {
			t.Fatalf("tenant %q: got %d certificates, expected %d", tenant, observed, expected)
		}
	}
	checkCount("", 0)
	checkCount("fixture-tenant-a", 1)
	checkCount("fixture-tenant-b", 1)
	checkCount("fixture-tenant-absent", 0)
}

func TestEvidenceStartupRejectsReachableDatabaseWithUnusableSchema(t *testing.T) {
	db := openDisposablePostgres(t)
	base, err := url.Parse(os.Getenv("EVIDENCE_TEST_DATABASE_URL"))
	if err != nil {
		t.Fatal(err)
	}
	role := "evidence_ci_no_ddl_" + strings.ReplaceAll(uuid.NewString(), "-", "")[:12]
	const password = "ci_disposable_only"
	if _, err := db.Exec(fmt.Sprintf("CREATE ROLE %s LOGIN PASSWORD '%s'", role, password)); err != nil {
		t.Fatalf("create restricted startup role: %v", err)
	}
	t.Cleanup(func() {
		if _, err := db.Exec("DROP ROLE " + role); err != nil {
			t.Errorf("clean up restricted startup role: %v", err)
		}
	})
	base.User = url.UserPassword(role, password)
	t.Setenv("DATABASE_URL", base.String())
	t.Setenv("EVIDENCE_STORAGE_PATH", filepath.Join(t.TempDir(), "evidence"))
	t.Setenv("CERT_SIGNER_BACKEND", "")
	service, err := NewEvidenceService()
	if err == nil || service != nil {
		t.Fatal("service accepted a reachable database with an unmodifiable schema")
	}
	if !strings.Contains(err.Error(), "validate certificate runtime database") {
		t.Fatalf("unrecognized startup failure: %v", err)
	}
}

func TestEvidenceStartupRejectsUnreachableConfiguredDatabase(t *testing.T) {
	// A non-listening loopback port guarantees no production data access.
	t.Setenv("DATABASE_URL", "postgres://unavailable:fixture@127.0.0.1:1/evidence?sslmode=disable&connect_timeout=1")
	t.Setenv("EVIDENCE_STORAGE_PATH", filepath.Join(t.TempDir(), "evidence"))
	t.Setenv("CERT_SIGNER_BACKEND", "")
	service, err := NewEvidenceService()
	if err == nil || service != nil {
		t.Fatal("configured database outage was silently downgraded to local issuance")
	}
	if !strings.Contains(err.Error(), "configured certificate database unavailable") {
		t.Fatalf("unexpected unreachable-database error: %v", err)
	}
}

func TestEvidenceWithoutDatabaseURLUsesExplicitFilesystemOnlyMode(t *testing.T) {
	t.Setenv("DATABASE_URL", "")
	t.Setenv("CERT_SIGNER_BACKEND", "")
	storage := filepath.Join(t.TempDir(), "evidence")
	t.Setenv("EVIDENCE_STORAGE_PATH", storage)
	service, err := NewEvidenceService()
	if err != nil {
		t.Fatalf("initialize filesystem-only development service: %v", err)
	}
	if service.db != nil {
		t.Fatal("service connected to an implicit database despite an absent DATABASE_URL")
	}
	if service.storagePath != storage {
		t.Fatalf("unexpected filesystem storage path: %q", service.storagePath)
	}
}

func TestEvidenceStartupWithoutDatabaseRejectsBrokenSigner(t *testing.T) {
	// Filesystem-only deployments must return an error, not dereference a
	// nonexistent database when an explicitly configured signer is invalid.
	for _, backend := range []string{"file", "kms", "vault"} {
		t.Run(backend, func(t *testing.T) {
			t.Setenv("DATABASE_URL", "")
			t.Setenv("CERT_SIGNER_BACKEND", backend)
			t.Setenv("CERT_SIGNER_FILE", filepath.Join(t.TempDir(), "missing-private-key.pem"))
			t.Setenv("EVIDENCE_STORAGE_PATH", filepath.Join(t.TempDir(), "evidence"))
			service, err := NewEvidenceService()
			if service != nil || err == nil {
				t.Fatalf("invalid signer backend %q unexpectedly initialized service", backend)
			}
			if !strings.Contains(err.Error(), "configured certificate signer unavailable") {
				t.Fatalf("unexpected signer-startup error: %v", err)
			}
		})
	}
}

func TestEvidenceDatabaseOutageCannotDowngradeToFilesystem(t *testing.T) {
	// A closed SQL handle is a deterministic, offline simulation of a
	// previously configured database that becomes unavailable at runtime.
	db, err := sql.Open("postgres", "postgres://fixture:fixture@127.0.0.1:1/evidence?sslmode=disable")
	if err != nil {
		t.Fatalf("create database handle: %v", err)
	}
	if err := db.Close(); err != nil {
		t.Fatalf("close database handle: %v", err)
	}

	ctx := context.Background()
	storage := filepath.Join(t.TempDir(), "evidence")
	cert := validStorageTestCertificate()
	service := &EvidenceService{db: db, storagePath: storage}

	if err := service.StoreCertificate(ctx, cert); err == nil ||
		!strings.Contains(err.Error(), "database certificate storage failed") {
		t.Fatalf("database outage did not reject issuance: %v", err)
	}
	if _, err := os.Stat(storage); !os.IsNotExist(err) {
		t.Fatalf("failed database issuance created filesystem storage: %v", err)
	}

	// An existing, matching filesystem certificate must not be returned as
	// a successful database search when PostgreSQL has failed.
	filesystemService := &EvidenceService{storagePath: storage}
	if err := filesystemService.StoreCertificate(ctx, cert); err != nil {
		t.Fatalf("seed offline filesystem certificate: %v", err)
	}
	filesystemResults, err := filesystemService.SearchCertificates(ctx, CertSearchRequest{TenantID: cert.TenantID})
	if err != nil || filesystemResults.Total != 1 {
		t.Fatalf("filesystem positive control failed: results=%+v err=%v", filesystemResults, err)
	}
	result, err := service.SearchCertificates(ctx, CertSearchRequest{TenantID: cert.TenantID})
	if err == nil || !strings.Contains(err.Error(), "database certificate search failed") {
		t.Fatalf("database search outage was concealed: results=%+v err=%v", result, err)
	}
	if result != nil {
		t.Fatalf("failed database search returned unverified fallback results: %+v", result)
	}
}
