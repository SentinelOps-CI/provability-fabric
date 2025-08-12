-- SPDX-License-Identifier: Apache-2.0
-- Copyright 2025 Provability-Fabric Contributors
--
-- Migration: Optimize database performance with partitioning and indices
-- This migration improves query performance for large datasets

-- Enable partitioning extension
CREATE EXTENSION IF NOT EXISTS pg_partman;

-- Create partitioned tables for time-series data
-- Partition by month for better query performance and maintenance

-- Partition UsageEvent table by month
CREATE TABLE IF NOT EXISTS "UsageEvent_partitioned" (
    LIKE "UsageEvent" INCLUDING ALL
) PARTITION BY RANGE (created_at);

-- Create monthly partitions for the last 12 months
DO $$
DECLARE
    partition_date DATE;
    partition_name TEXT;
    start_date DATE;
    end_date DATE;
BEGIN
    -- Start from 12 months ago
    partition_date := DATE_TRUNC('month', CURRENT_DATE - INTERVAL '12 months');
    
    FOR i IN 0..23 LOOP
        start_date := partition_date + (i * INTERVAL '1 month');
        end_date := start_date + INTERVAL '1 month';
        partition_name := 'UsageEvent_' || TO_CHAR(start_date, 'YYYY_MM');
        
        EXECUTE format('
            CREATE TABLE IF NOT EXISTS %I PARTITION OF "UsageEvent_partitioned"
            FOR VALUES FROM (%L) TO (%L)
        ', partition_name, start_date, end_date);
        
        -- Create indices on each partition
        EXECUTE format('
            CREATE INDEX IF NOT EXISTS %I_tenant_created_at_idx 
            ON %I (tenant_id, created_at DESC)
        ', partition_name, partition_name);
        
        EXECUTE format('
            CREATE INDEX IF NOT EXISTS %I_created_at_idx 
            ON %I (created_at DESC)
        ', partition_name, partition_name);
    END LOOP;
END $$;

-- Partition TenantInvoice table by month
CREATE TABLE IF NOT EXISTS "TenantInvoice_partitioned" (
    LIKE "TenantInvoice" INCLUDING ALL
) PARTITION BY RANGE (created_at);

-- Create monthly partitions for invoices
DO $$
DECLARE
    partition_date DATE;
    partition_name TEXT;
    start_date DATE;
    end_date DATE;
BEGIN
    partition_date := DATE_TRUNC('month', CURRENT_DATE - INTERVAL '12 months');
    
    FOR i IN 0..23 LOOP
        start_date := partition_date + (i * INTERVAL '1 month');
        end_date := start_date + INTERVAL '1 month';
        partition_name := 'TenantInvoice_' || TO_CHAR(start_date, 'YYYY_MM');
        
        EXECUTE format('
            CREATE TABLE IF NOT EXISTS %I PARTITION OF "TenantInvoice_partitioned"
            FOR VALUES FROM (%L) TO (%L)
        ', partition_name, start_date, end_date);
        
        -- Create indices on each partition
        EXECUTE format('
            CREATE INDEX IF NOT EXISTS %I_tenant_created_at_idx 
            ON %I (tenant_id, created_at DESC)
        ', partition_name, partition_name);
    END LOOP;
END $$;

-- Create composite indices for better query performance
-- These indices will significantly improve the performance of common queries

-- Composite index for tenant-based queries with timestamp ordering
CREATE INDEX CONCURRENTLY IF NOT EXISTS "UsageEvent_tenant_created_at_idx" 
ON "UsageEvent" (tenant_id, created_at DESC);

-- Composite index for plan-based queries
CREATE INDEX CONCURRENTLY IF NOT EXISTS "UsageEvent_plan_created_at_idx" 
ON "UsageEvent" (plan_id, created_at DESC);

-- Composite index for tenant invoices
CREATE INDEX CONCURRENTLY IF NOT EXISTS "TenantInvoice_tenant_created_at_idx" 
ON "TenantInvoice" (tenant_id, created_at DESC);

-- Composite index for premium quotes
CREATE INDEX CONCURRENTLY IF NOT EXISTS "PremiumQuote_tenant_created_at_idx" 
ON "PremiumQuote" (tenant_id, created_at DESC);

-- Composite index for capsules
CREATE INDEX CONCURRENTLY IF NOT EXISTS "Capsule_tenant_created_at_idx" 
ON "Capsule" (tenant_id, created_at DESC);

-- Partial indices for active records (improves performance for common queries)
CREATE INDEX CONCURRENTLY IF NOT EXISTS "UsageEvent_active_idx" 
ON "UsageEvent" (tenant_id, created_at DESC) 
WHERE deleted_at IS NULL;

CREATE INDEX CONCURRENTLY IF NOT EXISTS "TenantInvoice_active_idx" 
ON "TenantInvoice" (tenant_id, created_at DESC) 
WHERE status != 'cancelled';

-- GIN indices for JSON fields that are frequently queried
CREATE INDEX CONCURRENTLY IF NOT EXISTS "UsageEvent_context_gin_idx" 
ON "UsageEvent" USING GIN (context);

-- Create function to automatically create new partitions
CREATE OR REPLACE FUNCTION create_monthly_partitions()
RETURNS void AS $$
DECLARE
    partition_date DATE;
    partition_name TEXT;
    start_date DATE;
    end_date DATE;
    table_name TEXT;
BEGIN
    -- Create partitions for UsageEvent
    table_name := 'UsageEvent_partitioned';
    partition_date := DATE_TRUNC('month', CURRENT_DATE + INTERVAL '1 month');
    start_date := partition_date;
    end_date := start_date + INTERVAL '1 month';
    partition_name := 'UsageEvent_' || TO_CHAR(start_date, 'YYYY_MM');
    
    EXECUTE format('
        CREATE TABLE IF NOT EXISTS %I PARTITION OF %I
        FOR VALUES FROM (%L) TO (%L)
    ', partition_name, table_name, start_date, end_date);
    
    -- Create indices on new partition
    EXECUTE format('
        CREATE INDEX IF NOT EXISTS %I_tenant_created_at_idx 
        ON %I (tenant_id, created_at DESC)
    ', partition_name, partition_name);
    
    -- Create partitions for TenantInvoice
    table_name := 'TenantInvoice_partitioned';
    partition_name := 'TenantInvoice_' || TO_CHAR(start_date, 'YYYY_MM');
    
    EXECUTE format('
        CREATE TABLE IF NOT EXISTS %I PARTITION OF %I
        FOR VALUES FROM (%L) TO (%L)
    ', partition_name, table_name, start_date, end_date);
    
    -- Create indices on new partition
    EXECUTE format('
        CREATE INDEX IF NOT EXISTS %I_tenant_created_at_idx 
        ON %I (tenant_id, created_at DESC)
    ', partition_name, partition_name);
    
    RAISE NOTICE 'Created partitions for %', TO_CHAR(start_date, 'YYYY-MM');
END;
$$ LANGUAGE plpgsql;

-- Create a cron job to run this function monthly
-- In production, this would be set up with pg_cron or external scheduler
-- SELECT cron.schedule('create-monthly-partitions', '0 0 1 * *', 'SELECT create_monthly_partitions();');

-- Create function for maintenance operations
CREATE OR REPLACE FUNCTION maintenance_vacuum_analyze()
RETURNS void AS $$
BEGIN
    -- Vacuum and analyze all partitions
    VACUUM ANALYZE "UsageEvent_partitioned";
    VACUUM ANALYZE "TenantInvoice_partitioned";
    
    -- Update table statistics
    ANALYZE "UsageEvent";
    ANALYZE "TenantInvoice";
    ANALYZE "Tenant";
    ANALYZE "Capsule";
    ANALYZE "PremiumQuote";
    
    RAISE NOTICE 'Maintenance completed successfully';
END;
$$ LANGUAGE plpgsql;

-- Grant necessary permissions
GRANT EXECUTE ON FUNCTION create_monthly_partitions() TO pf_user;
GRANT EXECUTE ON FUNCTION maintenance_vacuum_analyze() TO pf_user;

-- Create view for easy querying across partitions
CREATE OR REPLACE VIEW "UsageEvent_optimized" AS
SELECT * FROM "UsageEvent_partitioned"
UNION ALL
SELECT * FROM "UsageEvent" 
WHERE created_at < (SELECT MIN(created_at) FROM "UsageEvent_partitioned");

-- Create view for tenant invoices
CREATE OR REPLACE VIEW "TenantInvoice_optimized" AS
SELECT * FROM "TenantInvoice_partitioned"
UNION ALL
SELECT * FROM "TenantInvoice" 
WHERE created_at < (SELECT MIN(created_at) FROM "TenantInvoice_partitioned");

-- Grant access to views
GRANT SELECT ON "UsageEvent_optimized" TO pf_user;
GRANT SELECT ON "TenantInvoice_optimized" TO pf_user;

-- Add comments for documentation
COMMENT ON INDEX "UsageEvent_tenant_created_at_idx" IS 'Composite index for tenant-based queries with timestamp ordering';
COMMENT ON INDEX "UsageEvent_plan_created_at_idx" IS 'Composite index for plan-based queries';
COMMENT ON FUNCTION create_monthly_partitions() IS 'Automatically creates new monthly partitions for time-series tables';
COMMENT ON FUNCTION maintenance_vacuum_analyze() IS 'Performs maintenance operations on partitioned tables';
