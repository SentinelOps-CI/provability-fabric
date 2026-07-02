// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import type { PrismaClient } from '@prisma/client'

export interface UserContext {
  tid: string
  sub: string
  email: string
  permissions?: string[]
}

export interface GraphQLContext {
  user: UserContext
}

export interface ServerDeps {
  prisma: PrismaClient
}
