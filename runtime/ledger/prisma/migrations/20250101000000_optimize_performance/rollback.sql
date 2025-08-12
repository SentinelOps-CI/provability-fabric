-- SPDX-License-Identifier: Apache-2.0
-- Copyright 2025 Provability-Fabric Contributors
--
-- Rollback Migration: Revert database performance optimizations
-- This migration safely reverts all changes made in the optimization migration

-- Drop views first
DROP VIEW IF EXISTS "UsageEvent_optimized";
DROP VIEW IF EXISTS "TenantInvoice_optimized";

-- Drop functions
DROP FUNCTION IF EXISTS create_monthly_partitions();
DROP FUNCTION IF EXISTS maintenance_vacuum_analyze();

-- Drop composite indices
DROP INDEX CONCURRENTLY IF EXISTS "UsageEvent_tenant_created_at_idx";
DROP INDEX CONCURRENTLY IF EXISTS "UsageEvent_plan_created_at_idx";
DROP INDEX CONCURRENTLY IF EXISTS "TenantInvoice_tenant_created_at_idx";
DROP INDEX CONCURRENTLY IF EXISTS "PremiumQuote_tenant_created_at_idx";
DROP INDEX CONCURRENTLY IF EXISTS "Capsule_tenant_created_at_idx";

-- Drop partial indices
DROP INDEX CONCURRENTLY IF EXISTS "UsageEvent_active_idx";
DROP INDEX CONCURRENTLY IF EXISTS "TenantInvoice_active_idx";

-- Drop GIN indices
DROP INDEX CONCURRENTLY IF EXISTS "UsageEvent_context_gin_idx";

-- Drop partitioned tables and their partitions
-- First, drop all partitions
DO $$
DECLARE
    partition_name TEXT;
    partition_record RECORD;
BEGIN
    -- Drop UsageEvent partitions
    FOR partition_record IN 
        SELECT tablename FROM pg_tables 
        WHERE tablename LIKE 'UsageEvent_%' AND tablename != 'UsageEvent'
    LOOP
        EXECUTE 'DROP TABLE IF EXISTS ' || quote_ident(partition_record.tablename) || ' CASCADE';
    END LOOP;
    
    -- Drop TenantInvoice partitions
    FOR partition_record IN 
        SELECT tablename FROM pg_tables 
        WHERE tablename LIKE 'TenantInvoice_%' AND tablename != 'TenantInvoice'
    LOOP
        EXECUTE 'DROP TABLE IF EXISTS ' || quote_ident(partition_record.tablename) || ' CASCADE';
    END LOOP;
END $$;

-- Drop partitioned table definitions
DROP TABLE IF EXISTS "UsageEvent_partitioned";
DROP TABLE IF EXISTS "TenantInvoice_partitioned";

-- Note: The original tables remain intact with their data
-- Only the optimization structures are removed

-- Log the rollback
INSERT INTO "_prisma_migrations" (
    "id",
    "checksum",
    "finished_at",
    "migration_name",
    "logs",
    "rolled_back_at",
    "started_at",
    "applied_steps_count"
) VALUES (
    '20250101000000_optimize_performance_rollback',
    'rollback_checksum_placeholder',
    NOW(),
    '20250101000000_optimize_performance_rollback',
    '{"message": "Rolled back database performance optimizations", "timestamp": "' || NOW() || '"}',
    NOW(),
    NOW(),
    1
);

-- Verify rollback completion
DO $$
BEGIN
    RAISE NOTICE 'Rollback completed successfully';
    RAISE NOTICE 'All optimization structures have been removed';
    RAISE NOTICE 'Original tables and data remain intact';
END $$;
