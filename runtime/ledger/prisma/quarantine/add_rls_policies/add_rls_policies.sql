-- SPDX-License-Identifier: Apache-2.0
-- Copyright 2025 Provability-Fabric Contributors
-- Quarantined: column names aligned to Prisma camelCase mapping.

ALTER TABLE "Tenant" ENABLE ROW LEVEL SECURITY;
ALTER TABLE "Capsule" ENABLE ROW LEVEL SECURITY;
ALTER TABLE "PremiumQuote" ENABLE ROW LEVEL SECURITY;

CREATE POLICY "tenant_isolation_tenant" ON "Tenant"
    FOR ALL USING ("auth0Id" = current_setting('app.current_tenant_id', true));

CREATE POLICY "tenant_isolation_capsule_select" ON "Capsule"
    FOR SELECT USING ("tenantId" = current_setting('app.current_tenant_id', true));

CREATE POLICY "tenant_isolation_capsule_insert" ON "Capsule"
    FOR INSERT WITH CHECK ("tenantId" = current_setting('app.current_tenant_id', true));

CREATE POLICY "tenant_isolation_capsule_update" ON "Capsule"
    FOR UPDATE USING ("tenantId" = current_setting('app.current_tenant_id', true));

CREATE POLICY "tenant_isolation_capsule_delete" ON "Capsule"
    FOR DELETE USING ("tenantId" = current_setting('app.current_tenant_id', true));

CREATE POLICY "tenant_isolation_premiumquote_select" ON "PremiumQuote"
    FOR SELECT USING ("tenantId" = current_setting('app.current_tenant_id', true));

CREATE POLICY "tenant_isolation_premiumquote_insert" ON "PremiumQuote"
    FOR INSERT WITH CHECK ("tenantId" = current_setting('app.current_tenant_id', true));

CREATE POLICY "tenant_isolation_premiumquote_update" ON "PremiumQuote"
    FOR UPDATE USING ("tenantId" = current_setting('app.current_tenant_id', true));

CREATE POLICY "tenant_isolation_premiumquote_delete" ON "PremiumQuote"
    FOR DELETE USING ("tenantId" = current_setting('app.current_tenant_id', true));

CREATE OR REPLACE FUNCTION set_tenant_context(tenant_id TEXT)
RETURNS VOID AS $$
BEGIN
    PERFORM set_config('app.current_tenant_id', tenant_id, false);
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION clear_tenant_context()
RETURNS VOID AS $$
BEGIN
    PERFORM set_config('app.current_tenant_id', NULL, false);
END;
$$ LANGUAGE plpgsql;

GRANT EXECUTE ON FUNCTION set_tenant_context(TEXT) TO postgres;
GRANT EXECUTE ON FUNCTION clear_tenant_context() TO postgres;
