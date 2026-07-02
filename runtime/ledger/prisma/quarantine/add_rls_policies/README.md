# Quarantined: add_rls_policies

Row-level security policies for tenant isolation. Not applied via `prisma migrate` because
the original script used snake_case column names (`tenant_id`, `auth0_id`) while Prisma
maps to camelCase (`tenantId`, `auth0Id`).

Apply manually only after review on a database that matches `schema.prisma`.
See audit finding F09.
