# Prisma migrations (F09)

## Active migrations

Only timestamped directories under this folder are applied by `prisma migrate deploy`.
The canonical baseline is `20250804204349_provability_fabric/`.

## Quarantined SQL (never auto-apply)

The following files were removed from the active migration path because they reference
columns or naming that do not match `schema.prisma` (camelCase Prisma field mapping):

| Path | Reason |
|------|--------|
| `../quarantine/20250101000000_optimize_performance/` | Indexes on non-existent columns (`created_at` on `UsageEvent`, `deleted_at`, etc.) |
| `../quarantine/add_rls_policies/` | RLS policies used snake_case column names; corrected copy kept in quarantine |

Do **not** move quarantined SQL back into `migrations/` without reconciling against
`schema.prisma` and validating on a fresh database.

## Manual SQL in this directory

`add_billing_tables.sql` is a legacy hand-written script. Billing tables are already
included in `20250804204349_provability_fabric/migration.sql`. Keep for reference only;
`prisma migrate` does not execute loose `.sql` files.

## Fresh database bootstrap

```bash
cd runtime/ledger
export DATABASE_URL="postgresql://user:pass@localhost:5432/ledger"
npx prisma migrate deploy
npx prisma generate
```
