#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors
#
# Ledger Prisma migrate deploy requires an empty database. Platform tables from
# init.sql live in POSTGRES_DB (sentinelops); ledger uses a separate database.

set -euo pipefail

psql -v ON_ERROR_STOP=1 --username "$POSTGRES_USER" <<-EOSQL
    CREATE DATABASE ledger;
    GRANT ALL PRIVILEGES ON DATABASE ledger TO ${POSTGRES_USER};
EOSQL
