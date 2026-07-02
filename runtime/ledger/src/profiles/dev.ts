// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { PrismaClient } from '@prisma/client'
import express from 'express'
import { ApolloServer } from '@apollo/server'
import { expressMiddleware } from '@apollo/server/express4'
import bodyParser from 'body-parser'
import cors from 'cors'
import { authMiddleware, tenantMiddleware } from '../auth-simple.js'
import { BillingService, billingMiddleware } from '../billing.js'
import { typeDefs } from '../server/schema.js'
import { createResolvers } from '../server/resolvers.js'
import { ensureDefaultTenants, registerRestRoutes, userFromRequest } from '../server/rest-routes.js'

export async function startDevProfile(): Promise<void> {
  const prisma = new PrismaClient()
  await ensureDefaultTenants(prisma)

  const app = express()
  const port = process.env.PORT || 8080
  const billingService = new BillingService()
  const billing = billingMiddleware(billingService)

  app.use(cors())
  app.use(bodyParser.json())

  registerRestRoutes(app, { prisma, billing, authMiddleware, tenantMiddleware })

  await new Promise<void>((resolve) => {
    app.listen(port, () => {
      console.log(`Provability-Fabric Ledger (dev) on port ${port}`)
      console.log(`Health: http://localhost:${port}/health`)
      console.log(`GraphQL: http://localhost:${port}/graphql`)
      resolve()
    })
  })

  const server = new ApolloServer({
    typeDefs,
    resolvers: createResolvers({ prisma }),
  })

  await server.start()

  app.use(
    '/graphql',
    expressMiddleware(server, {
      context: async ({ req }) => ({
        user: userFromRequest(req),
      }),
    })
  )
}
