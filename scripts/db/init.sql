-- SPDX-License-Identifier: Apache-2.0
-- Copyright 2025 SentinelOps Platform Contributors

-- Initialize SentinelOps Platform database

-- Enable required extensions
CREATE EXTENSION IF NOT EXISTS "uuid-ossp";
CREATE EXTENSION IF NOT EXISTS "pgcrypto";

-- Create certificates table with RLS
CREATE TABLE IF NOT EXISTS certificates (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    bundle_id VARCHAR(255) NOT NULL,
    policy_hash VARCHAR(64) NOT NULL,
    proof_hash VARCHAR(64) NOT NULL,
    automata_hash VARCHAR(64) NOT NULL,
    labeler_hash VARCHAR(64) NOT NULL,
    ni_claim VARCHAR(255) NOT NULL,
    ni_monitor VARCHAR(20) NOT NULL CHECK (ni_monitor IN ('inapplicable', 'accept', 'reject', 'error')),
    sidecar_build VARCHAR(255) NOT NULL,
    tenant_id VARCHAR(255) NOT NULL,
    session_id VARCHAR(255) NOT NULL,
    timestamp TIMESTAMP WITH TIME ZONE NOT NULL,
    cert_data JSONB NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- Create indexes for performance
CREATE INDEX IF NOT EXISTS idx_certificates_tenant_id ON certificates(tenant_id);
CREATE INDEX IF NOT EXISTS idx_certificates_policy_hash ON certificates(policy_hash);
CREATE INDEX IF NOT EXISTS idx_certificates_session_id ON certificates(session_id);
CREATE INDEX IF NOT EXISTS idx_certificates_timestamp ON certificates(timestamp);
CREATE INDEX IF NOT EXISTS idx_certificates_ni_monitor ON certificates(ni_monitor);

-- Enable Row Level Security for multi-tenant isolation
ALTER TABLE certificates ENABLE ROW LEVEL SECURITY;

-- Create RLS policy for tenant isolation
CREATE POLICY tenant_isolation ON certificates
    FOR ALL
    USING (tenant_id = current_setting('app.current_tenant', true));

-- Create audit_logs table for hash chain
CREATE TABLE IF NOT EXISTS audit_logs (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    timestamp TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    action VARCHAR(100) NOT NULL,
    actor VARCHAR(255) NOT NULL,
    resource VARCHAR(255) NOT NULL,
    hash VARCHAR(64) NOT NULL,
    previous_hash VARCHAR(64),
    signature TEXT,
    metadata JSONB,
    tenant_id VARCHAR(255) NOT NULL
);

-- Create indexes for audit logs
CREATE INDEX IF NOT EXISTS idx_audit_logs_timestamp ON audit_logs(timestamp);
CREATE INDEX IF NOT EXISTS idx_audit_logs_tenant_id ON audit_logs(tenant_id);
CREATE INDEX IF NOT EXISTS idx_audit_logs_hash ON audit_logs(hash);

-- Enable RLS for audit logs
ALTER TABLE audit_logs ENABLE ROW LEVEL SECURITY;

CREATE POLICY audit_tenant_isolation ON audit_logs
    FOR ALL
    USING (tenant_id = current_setting('app.current_tenant', true));

-- Create policy_versions table
CREATE TABLE IF NOT EXISTS policy_versions (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    policy_id VARCHAR(255) NOT NULL,
    version VARCHAR(50) NOT NULL,
    policy_hash VARCHAR(64) NOT NULL UNIQUE,
    english_text TEXT NOT NULL,
    action_dsl JSONB NOT NULL,
    proof_hash VARCHAR(64),
    automata_hash VARCHAR(64),
    labeler_hash VARCHAR(64),
    status VARCHAR(50) NOT NULL DEFAULT 'draft',
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    created_by VARCHAR(255),
    tenant_id VARCHAR(255) NOT NULL,
    metadata JSONB
);

-- Create indexes for policy versions
CREATE INDEX IF NOT EXISTS idx_policy_versions_policy_id ON policy_versions(policy_id);
CREATE INDEX IF NOT EXISTS idx_policy_versions_hash ON policy_versions(policy_hash);
CREATE INDEX IF NOT EXISTS idx_policy_versions_tenant ON policy_versions(tenant_id);
CREATE INDEX IF NOT EXISTS idx_policy_versions_status ON policy_versions(status);

-- Enable RLS for policy versions
ALTER TABLE policy_versions ENABLE ROW LEVEL SECURITY;

CREATE POLICY policy_tenant_isolation ON policy_versions
    FOR ALL
    USING (tenant_id = current_setting('app.current_tenant', true));

-- Create epochs table
CREATE TABLE IF NOT EXISTS epochs (
    epoch INTEGER PRIMARY KEY,
    policy_hash VARCHAR(64) NOT NULL,
    automata_hash VARCHAR(64) NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    created_by VARCHAR(255),
    revoked_principals TEXT[],
    metadata JSONB,
    tenant_id VARCHAR(255) NOT NULL
);

-- Create indexes for epochs
CREATE INDEX IF NOT EXISTS idx_epochs_tenant ON epochs(tenant_id);
CREATE INDEX IF NOT EXISTS idx_epochs_created_at ON epochs(created_at);

-- Enable RLS for epochs
ALTER TABLE epochs ENABLE ROW LEVEL SECURITY;

CREATE POLICY epoch_tenant_isolation ON epochs
    FOR ALL
    USING (tenant_id = current_setting('app.current_tenant', true));

-- Create replay_jobs table
CREATE TABLE IF NOT EXISTS replay_jobs (
    job_id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    decision_id VARCHAR(255) NOT NULL,
    status VARCHAR(50) NOT NULL DEFAULT 'running',
    progress DECIMAL(5,4) DEFAULT 0.0,
    low_view_match_pct DECIMAL(7,6),
    outputs JSONB,
    artifacts TEXT[],
    started_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    completed_at TIMESTAMP WITH TIME ZONE,
    execution_time_ms INTEGER,
    drift_detected BOOLEAN DEFAULT FALSE,
    error_message TEXT,
    config JSONB,
    tenant_id VARCHAR(255) NOT NULL
);

-- Create indexes for replay jobs
CREATE INDEX IF NOT EXISTS idx_replay_jobs_tenant ON replay_jobs(tenant_id);
CREATE INDEX IF NOT EXISTS idx_replay_jobs_status ON replay_jobs(status);
CREATE INDEX IF NOT EXISTS idx_replay_jobs_started_at ON replay_jobs(started_at);

-- Enable RLS for replay jobs
ALTER TABLE replay_jobs ENABLE ROW LEVEL SECURITY;

CREATE POLICY replay_tenant_isolation ON replay_jobs
    FOR ALL
    USING (tenant_id = current_setting('app.current_tenant', true));

-- Insert sample data for demo
INSERT INTO policy_versions (policy_id, version, policy_hash, english_text, action_dsl, status, tenant_id, created_by) VALUES
('fraud-detection-v1', '1.0.0', 'a1b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef123456', 
 'Only FraudService may call /score endpoint. Rate limit alerts to 5 per 10 seconds per tenant. Block transactions with score >= 0.93.',
 '{"rules": [{"type": "allow", "role": "FraudService", "action": {"type": "call", "tool": "score"}}]}',
 'deployed', 'acme-corp', 'admin@acme-corp.com')
ON CONFLICT (policy_hash) DO NOTHING;

INSERT INTO epochs (epoch, policy_hash, automata_hash, tenant_id, created_by) VALUES
(42, 'a1b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef123456',
 'b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef123456',
 'acme-corp', 'admin@acme-corp.com')
ON CONFLICT (epoch) DO NOTHING;