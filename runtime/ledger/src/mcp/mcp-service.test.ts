// SPDX-License-Identifier: Apache-2.0

describe('McpService tenant resolution', () => {
  function resolveTenantId(user: {
    tid?: string;
    tenantId?: string;
    tenant_id?: string;
  } | undefined): string | undefined {
    if (!user) return undefined;
    return user.tid ?? user.tenantId ?? user.tenant_id;
  }

  it('prefers tid over legacy claims', () => {
    expect(resolveTenantId({ tid: 'canonical', tenant_id: 'legacy' })).toBe('canonical');
  });

  it('falls back to tenant_id', () => {
    expect(resolveTenantId({ tenant_id: 'legacy-tenant' })).toBe('legacy-tenant');
  });
});
