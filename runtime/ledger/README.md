# Ledger service (GraphQL)

## Setup

From this directory:

```bash
npm ci
npx prisma generate
npm run build
```

`@prisma/client` is generated into `node_modules/.prisma` and `node_modules/@prisma/client` after `prisma generate`. Do not commit `node_modules` or generated Prisma output.

## Common commands

- `npm run dev:minimal` — minimal local server
- `npm test` — Jest tests
- `npm run prisma:migrate` — apply migrations (development)
- `npm run prisma:studio` — Prisma Studio UI

See [package.json](package.json) for all scripts.
