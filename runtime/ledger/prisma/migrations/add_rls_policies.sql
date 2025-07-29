-- SPDX-License-Identifier: Apache-2.0
-- Copyright 2025 Provability-Fabric Contributors

-- Enable Row Level Security on tables
ALTER TABLE "Tenant" ENABLE ROW LEVEL SECURITY;
ALTER TABLE "Capsule" ENABLE ROW LEVEL SECURITY;
ALTER TABLE "PremiumQuote" ENABLE ROW LEVEL SECURITY;

-- Create RLS policies for tenant isolation

-- Tenant table policies
CREATE POLICY "tenant_isolation_tenant" ON "Tenant"
    FOR ALL USING (auth0_id = current_setting('app.current_tenant_id', true));

-- Capsule table policies
CREATE POLICY "tenant_isolation_capsule_select" ON "Capsule"
    FOR SELECT USING (tenant_id = current_setting('app.current_tenant_id', true));

CREATE POLICY "tenant_isolation_capsule_insert" ON "Capsule"
    FOR INSERT WITH CHECK (tenant_id = current_setting('app.current_tenant_id', true));

CREATE POLICY "tenant_isolation_capsule_update" ON "Capsule"
    FOR UPDATE USING (tenant_id = current_setting('app.current_tenant_id', true));

CREATE POLICY "tenant_isolation_capsule_delete" ON "Capsule"
    FOR DELETE USING (tenant_id = current_setting('app.current_tenant_id', true));

-- PremiumQuote table policies
CREATE POLICY "tenant_isolation_premiumquote_select" ON "PremiumQuote"
    FOR SELECT USING (tenant_id = current_setting('app.current_tenant_id', true));

CREATE POLICY "tenant_isolation_premiumquote_insert" ON "PremiumQuote"
    FOR INSERT WITH CHECK (tenant_id = current_setting('app.current_tenant_id', true));

CREATE POLICY "tenant_isolation_premiumquote_update" ON "PremiumQuote"
    FOR UPDATE USING (tenant_id = current_setting('app.current_tenant_id', true));

CREATE POLICY "tenant_isolation_premiumquote_delete" ON "PremiumQuote"
    FOR DELETE USING (tenant_id = current_setting('app.current_tenant_id', true));

-- Create function to set current tenant context
CREATE OR REPLACE FUNCTION set_tenant_context(tenant_id TEXT)
RETURNS VOID AS $$
BEGIN
    PERFORM set_config('app.current_tenant_id', tenant_id, false);
END;
$$ LANGUAGE plpgsql;

-- Create function to clear tenant context
CREATE OR REPLACE FUNCTION clear_tenant_context()
RETURNS VOID AS $$
BEGIN
    PERFORM set_config('app.current_tenant_id', NULL, false);
END;
$$ LANGUAGE plpgsql;

-- Grant necessary permissions
GRANT EXECUTE ON FUNCTION set_tenant_context(TEXT) TO postgres;
GRANT EXECUTE ON FUNCTION clear_tenant_context() TO postgres;