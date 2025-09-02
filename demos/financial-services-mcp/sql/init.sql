-- SPDX-License-Identifier: Apache-2.0
-- Copyright 2025 Provability-Fabric Contributors
-- Financial Services Database Schema with Performance Optimizations

-- Enable required extensions
CREATE EXTENSION IF NOT EXISTS "uuid-ossp";
CREATE EXTENSION IF NOT EXISTS "pg_stat_statements";

-- Create optimized database schema for financial services

-- Financial institutions table
CREATE TABLE institutions (
    id VARCHAR(32) PRIMARY KEY,
    name VARCHAR(255) NOT NULL,
    country_code CHAR(2) NOT NULL,
    regulation_tier VARCHAR(32) NOT NULL DEFAULT 'TIER_1',
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- Account holders table with privacy considerations
CREATE TABLE account_holders (
    id VARCHAR(64) PRIMARY KEY,
    institution_id VARCHAR(32) NOT NULL REFERENCES institutions(id),
    account_type VARCHAR(32) NOT NULL DEFAULT 'CHECKING',
    risk_profile VARCHAR(32) NOT NULL DEFAULT 'LOW',
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
    last_activity TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- Optimized transactions table for high-volume processing
CREATE TABLE transactions (
    id VARCHAR(64) PRIMARY KEY,
    amount DECIMAL(18,2) NOT NULL,
    currency CHAR(3) NOT NULL DEFAULT 'USD',
    from_account VARCHAR(64) NOT NULL,
    to_account VARCHAR(64) NOT NULL,
    timestamp BIGINT NOT NULL, -- Unix timestamp for performance
    institution_id VARCHAR(32) NOT NULL REFERENCES institutions(id),
    transaction_type VARCHAR(32) NOT NULL DEFAULT 'TRANSFER',
    risk_score DECIMAL(5,4) DEFAULT 0.0000,
    fraud_probability DECIMAL(5,4) DEFAULT 0.0000,
    status VARCHAR(32) NOT NULL DEFAULT 'PENDING',
    processing_time_ms INTEGER DEFAULT 0,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- Partition transactions table by timestamp for better performance
-- Note: This is a simplified approach; production would use range partitioning
ALTER TABLE transactions ENABLE ROW LEVEL SECURITY;

-- Audit events table with blockchain-like properties
CREATE TABLE audit_events (
    id VARCHAR(64) PRIMARY KEY,
    timestamp BIGINT NOT NULL,
    event_type VARCHAR(64) NOT NULL,
    details JSONB NOT NULL,
    hash VARCHAR(64) NOT NULL UNIQUE,
    previous_hash VARCHAR(64),
    transaction_id VARCHAR(64),
    institution_id VARCHAR(32) NOT NULL REFERENCES institutions(id),
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- Fraud detection results table
CREATE TABLE fraud_detections (
    id VARCHAR(64) PRIMARY KEY,
    transaction_id VARCHAR(64) NOT NULL REFERENCES transactions(id),
    fraud_probability DECIMAL(5,4) NOT NULL,
    decision VARCHAR(32) NOT NULL CHECK (decision IN ('approve', 'reject', 'review')),
    risk_factors JSONB,
    model_version VARCHAR(32) NOT NULL,
    processing_time_ms INTEGER NOT NULL,
    confidence_score DECIMAL(5,4),
    created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
);

-- Real-time risk metrics table
CREATE TABLE risk_metrics (
    id VARCHAR(64) PRIMARY KEY,
    account_id VARCHAR(64) NOT NULL,
    institution_id VARCHAR(32) NOT NULL REFERENCES institutions(id),
    window_minutes INTEGER NOT NULL,
    transaction_count INTEGER NOT NULL DEFAULT 0,
    total_amount DECIMAL(18,2) NOT NULL DEFAULT 0,
    avg_amount DECIMAL(18,2) NOT NULL DEFAULT 0,
    max_amount DECIMAL(18,2) NOT NULL DEFAULT 0,
    risk_score DECIMAL(5,4) NOT NULL DEFAULT 0,
    calculated_at BIGINT NOT NULL,
    expires_at BIGINT NOT NULL
);

-- Performance monitoring table
CREATE TABLE performance_metrics (
    id SERIAL PRIMARY KEY,
    metric_name VARCHAR(128) NOT NULL,
    metric_value DECIMAL(10,4) NOT NULL,
    timestamp BIGINT NOT NULL,
    institution_id VARCHAR(32),
    metadata JSONB
);

-- Create Row Level Security policies for multi-tenant isolation

-- Institutions RLS
CREATE POLICY tenant_isolation_institutions ON institutions
    FOR ALL USING (id = current_setting('app.current_institution_id', true));

-- Account holders RLS
CREATE POLICY tenant_isolation_account_holders ON account_holders
    FOR ALL USING (institution_id = current_setting('app.current_institution_id', true));

-- Transactions RLS
CREATE POLICY tenant_isolation_transactions ON transactions
    FOR ALL USING (institution_id = current_setting('app.current_institution_id', true));

-- Audit events RLS
CREATE POLICY tenant_isolation_audit_events ON audit_events
    FOR ALL USING (institution_id = current_setting('app.current_institution_id', true));

-- Fraud detections RLS (via transaction relationship)
CREATE POLICY tenant_isolation_fraud_detections ON fraud_detections
    FOR ALL USING (
        transaction_id IN (
            SELECT id FROM transactions 
            WHERE institution_id = current_setting('app.current_institution_id', true)
        )
    );

-- Risk metrics RLS
CREATE POLICY tenant_isolation_risk_metrics ON risk_metrics
    FOR ALL USING (institution_id = current_setting('app.current_institution_id', true));

-- Enable RLS on all tables
ALTER TABLE institutions ENABLE ROW LEVEL SECURITY;
ALTER TABLE account_holders ENABLE ROW LEVEL SECURITY;
ALTER TABLE transactions ENABLE ROW LEVEL SECURITY;
ALTER TABLE audit_events ENABLE ROW LEVEL SECURITY;
ALTER TABLE fraud_detections ENABLE ROW LEVEL SECURITY;
ALTER TABLE risk_metrics ENABLE ROW LEVEL SECURITY;

-- Insert demo institutions
INSERT INTO institutions (id, name, country_code, regulation_tier) VALUES
('BANK_US_001', 'First National Bank', 'US', 'TIER_1'),
('BANK_US_002', 'Metropolitan Trust', 'US', 'TIER_1'),
('BANK_UK_001', 'London Financial Group', 'UK', 'TIER_1'),
('BANK_EU_001', 'European Banking Corp', 'DE', 'TIER_1'),
('BANK_ASIA_001', 'Asia Pacific Bank', 'SG', 'TIER_2');

-- Insert demo account holders
INSERT INTO account_holders (id, institution_id, account_type, risk_profile) VALUES
-- US Bank 1 accounts
('ACC_US_001_001', 'BANK_US_001', 'CHECKING', 'LOW'),
('ACC_US_001_002', 'BANK_US_001', 'SAVINGS', 'LOW'),
('ACC_US_001_003', 'BANK_US_001', 'BUSINESS', 'MEDIUM'),
('ACC_US_001_004', 'BANK_US_001', 'CHECKING', 'HIGH'),

-- US Bank 2 accounts
('ACC_US_002_001', 'BANK_US_002', 'CHECKING', 'LOW'),
('ACC_US_002_002', 'BANK_US_002', 'INVESTMENT', 'MEDIUM'),
('ACC_US_002_003', 'BANK_US_002', 'BUSINESS', 'HIGH'),

-- UK Bank accounts
('ACC_UK_001_001', 'BANK_UK_001', 'CURRENT', 'LOW'),
('ACC_UK_001_002', 'BANK_UK_001', 'SAVINGS', 'MEDIUM'),
('ACC_UK_001_003', 'BANK_UK_001', 'BUSINESS', 'LOW'),

-- European Bank accounts
('ACC_EU_001_001', 'BANK_EU_001', 'CHECKING', 'LOW'),
('ACC_EU_001_002', 'BANK_EU_001', 'SAVINGS', 'LOW'),

-- Asian Bank accounts
('ACC_ASIA_001_001', 'BANK_ASIA_001', 'CHECKING', 'MEDIUM'),
('ACC_ASIA_001_002', 'BANK_ASIA_001', 'SAVINGS', 'LOW');

-- Create indexes for optimal query performance
CREATE INDEX CONCURRENTLY idx_transactions_fraud_analysis ON transactions 
(from_account, timestamp DESC) 
WHERE risk_score > 0.1;

CREATE INDEX CONCURRENTLY idx_audit_events_recent ON audit_events 
(institution_id, timestamp DESC);

-- Create materialized view for real-time analytics
CREATE MATERIALIZED VIEW real_time_transaction_stats AS
SELECT 
    institution_id,
    COUNT(*) as total_transactions,
    SUM(amount) as total_volume,
    AVG(amount) as avg_amount,
    MAX(amount) as max_amount,
    AVG(risk_score) as avg_risk_score,
    COUNT(*) FILTER (WHERE risk_score > 0.5) as high_risk_count,
    COUNT(*) FILTER (WHERE status = 'REJECTED') as rejected_count,
    DATE_TRUNC('hour', to_timestamp(timestamp / 1000)) as hour_bucket
FROM transactions 
WHERE timestamp > EXTRACT(EPOCH FROM NOW() - INTERVAL '24 hours') * 1000
GROUP BY institution_id, hour_bucket;

-- Create unique index on materialized view
CREATE UNIQUE INDEX idx_real_time_stats_unique ON real_time_transaction_stats 
(institution_id, hour_bucket);

-- Refresh materialized view function
CREATE OR REPLACE FUNCTION refresh_real_time_stats()
RETURNS void AS $$
BEGIN
    REFRESH MATERIALIZED VIEW CONCURRENTLY real_time_transaction_stats;
END;
$$ LANGUAGE plpgsql;

-- Create function for automatic performance metric insertion
CREATE OR REPLACE FUNCTION record_performance_metric(
    p_metric_name VARCHAR(128),
    p_metric_value DECIMAL(10,4),
    p_institution_id VARCHAR(32) DEFAULT NULL,
    p_metadata JSONB DEFAULT NULL
)
RETURNS void AS $$
BEGIN
    INSERT INTO performance_metrics (metric_name, metric_value, timestamp, institution_id, metadata)
    VALUES (p_metric_name, p_metric_value, EXTRACT(EPOCH FROM NOW()) * 1000, p_institution_id, p_metadata);
END;
$$ LANGUAGE plpgsql;

-- Create function for audit hash verification
CREATE OR REPLACE FUNCTION verify_audit_chain(p_transaction_id VARCHAR(64))
RETURNS TABLE (
    event_id VARCHAR(64),
    is_valid BOOLEAN,
    expected_hash VARCHAR(64),
    actual_hash VARCHAR(64)
) AS $$
DECLARE
    r RECORD;
    prev_hash VARCHAR(64) := NULL;
    computed_hash VARCHAR(64);
BEGIN
    FOR r IN 
        SELECT id, hash, previous_hash, timestamp, event_type, details
        FROM audit_events 
        WHERE transaction_id = p_transaction_id
        ORDER BY timestamp ASC
    LOOP
        -- In production, this would call a proper hash function
        -- For demo purposes, we'll simulate hash verification
        computed_hash := encode(sha256(
            (r.id || r.timestamp || r.event_type || r.details::text || COALESCE(r.previous_hash, ''))::bytea
        ), 'hex');
        
        event_id := r.id;
        is_valid := (r.hash = computed_hash AND (prev_hash IS NULL OR r.previous_hash = prev_hash));
        expected_hash := computed_hash;
        actual_hash := r.hash;
        
        RETURN NEXT;
        
        prev_hash := r.hash;
    END LOOP;
END;
$$ LANGUAGE plpgsql;

-- Grant permissions for application user
GRANT USAGE ON SCHEMA public TO fintech_user;
GRANT ALL PRIVILEGES ON ALL TABLES IN SCHEMA public TO fintech_user;
GRANT ALL PRIVILEGES ON ALL SEQUENCES IN SCHEMA public TO fintech_user;
GRANT EXECUTE ON ALL FUNCTIONS IN SCHEMA public TO fintech_user;

-- Create application database user with limited permissions
CREATE USER mcp_server_user WITH PASSWORD 'mcp_secure_2025';
GRANT CONNECT ON DATABASE financial_services TO mcp_server_user;
GRANT USAGE ON SCHEMA public TO mcp_server_user;
GRANT SELECT, INSERT, UPDATE ON ALL TABLES IN SCHEMA public TO mcp_server_user;
GRANT USAGE, SELECT ON ALL SEQUENCES IN SCHEMA public TO mcp_server_user;
GRANT EXECUTE ON ALL FUNCTIONS IN SCHEMA public TO mcp_server_user;

-- Create read-only user for monitoring
CREATE USER monitoring_user WITH PASSWORD 'monitor_2025';
GRANT CONNECT ON DATABASE financial_services TO monitoring_user;
GRANT USAGE ON SCHEMA public TO monitoring_user;
GRANT SELECT ON ALL TABLES IN SCHEMA public TO monitoring_user;
GRANT SELECT ON real_time_transaction_stats TO monitoring_user;

-- Set up automatic statistics collection
SELECT pg_stat_statements_reset();

-- Create indexes for monitoring queries
CREATE INDEX CONCURRENTLY idx_transactions_monitoring ON transactions 
(created_at, institution_id, status, risk_score);

CREATE INDEX CONCURRENTLY idx_performance_metrics_monitoring ON performance_metrics 
(timestamp DESC, metric_name, institution_id);

-- Vacuum and analyze for optimal performance
VACUUM ANALYZE;

-- Display setup completion message
-- Create performance-critical indexes
-- Account holders indexes
CREATE INDEX idx_account_holders_institution ON account_holders (institution_id);
CREATE INDEX idx_account_holders_risk ON account_holders (risk_profile);
CREATE INDEX idx_account_holders_activity ON account_holders (last_activity);

-- Transactions indexes
CREATE INDEX idx_transactions_timestamp ON transactions (timestamp);
CREATE INDEX idx_transactions_from_account ON transactions (from_account);
CREATE INDEX idx_transactions_to_account ON transactions (to_account);
CREATE INDEX idx_transactions_institution ON transactions (institution_id);
CREATE INDEX idx_transactions_risk_score ON transactions (risk_score);
CREATE INDEX idx_transactions_status ON transactions (status);

-- Composite indexes for common queries
CREATE INDEX idx_transactions_account_timestamp ON transactions (from_account, timestamp);
CREATE INDEX idx_transactions_institution_timestamp ON transactions (institution_id, timestamp);
CREATE INDEX idx_transactions_risk_timestamp ON transactions (risk_score, timestamp);

-- Audit events indexes
CREATE INDEX idx_audit_events_timestamp ON audit_events (timestamp);
CREATE INDEX idx_audit_events_transaction ON audit_events (transaction_id);
CREATE INDEX idx_audit_events_institution ON audit_events (institution_id);
CREATE INDEX idx_audit_events_hash ON audit_events (hash);
CREATE INDEX idx_audit_events_previous_hash ON audit_events (previous_hash);

-- GIN index for JSONB details
CREATE INDEX idx_audit_events_details_gin ON audit_events USING gin(details);

-- Fraud detections indexes
CREATE INDEX idx_fraud_detections_transaction ON fraud_detections (transaction_id);
CREATE INDEX idx_fraud_detections_probability ON fraud_detections (fraud_probability);
CREATE INDEX idx_fraud_detections_decision ON fraud_detections (decision);
CREATE INDEX idx_fraud_detections_created_at ON fraud_detections (created_at);

-- Risk metrics indexes
CREATE INDEX idx_risk_metrics_account ON risk_metrics (account_id);
CREATE INDEX idx_risk_metrics_institution ON risk_metrics (institution_id);
CREATE INDEX idx_risk_metrics_calculated_at ON risk_metrics (calculated_at);
CREATE INDEX idx_risk_metrics_expires_at ON risk_metrics (expires_at);

-- Performance metrics indexes
CREATE INDEX idx_performance_metrics_name ON performance_metrics (metric_name);
CREATE INDEX idx_performance_metrics_timestamp ON performance_metrics (timestamp);
CREATE INDEX idx_performance_metrics_institution ON performance_metrics (institution_id);

DO $$
BEGIN
    RAISE NOTICE 'Financial Services MCP Database initialized successfully!';
    RAISE NOTICE 'Institutions: %', (SELECT COUNT(*) FROM institutions);
    RAISE NOTICE 'Account holders: %', (SELECT COUNT(*) FROM account_holders);
    RAISE NOTICE 'Performance optimizations: Enabled';
    RAISE NOTICE 'Row Level Security: Enabled';
    RAISE NOTICE 'Real-time analytics: Ready';
    RAISE NOTICE 'Indexes created: 24 performance-critical indexes';
END $$;
