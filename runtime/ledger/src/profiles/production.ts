// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { PrismaClient } from '@prisma/client'
import express from 'express'
import { ApolloServer } from '@apollo/server'
import { expressMiddleware } from '@apollo/server/express4'
import bodyParser from 'body-parser'
import cors from 'cors'
import winston from 'winston'
import {
  authMiddleware,
  tenantMiddleware,
  AuthenticatedRequest,
} from '../auth.js'
import { BillingService, billingMiddleware } from '../billing.js'
import McpService from '../mcp/mcp-service.js'
import { typeDefs } from '../server/schema.js'
import { createResolvers } from '../server/resolvers.js'
import { registerRestRoutes } from '../server/rest-routes.js'

export async function startProductionProfile(): Promise<void> {
  const prisma = new PrismaClient()
  const app = express()
  const port = process.env.PORT || 4000

  const logger = winston.createLogger({
    level: 'info',
    format: winston.format.combine(winston.format.timestamp(), winston.format.json()),
    transports: [
      new winston.transports.Console(),
      new winston.transports.File({ filename: 'mcp-service.log' }),
    ],
  })

  const billingService = new BillingService()
  const billing = billingMiddleware(billingService)

  const mcpService = new McpService(
    {
      name: 'provability-fabric-mcp',
      version: '1.0.0',
      description: 'Model Context Protocol integration for Provability-Fabric',
      enableWebSocket: true,
      sidecarUrl: process.env.SIDECAR_URL || 'http://localhost:8006',
      enableMultiTenant: true,
    },
    prisma,
    logger
  )

  await mcpService.initialize()

  app.use(cors())
  app.use(bodyParser.json())

  registerRestRoutes(app, {
    prisma,
    billing,
    authMiddleware: authMiddleware as typeof import('../auth-simple.js').authMiddleware,
    tenantMiddleware: tenantMiddleware as typeof import('../auth-simple.js').tenantMiddleware,
  })

  app.use('/api', mcpService.getRouter())

  const apolloServer = new ApolloServer({
    typeDefs,
    resolvers: createResolvers({ prisma }),
  })

  await apolloServer.start()

  app.use(
    '/graphql',
    authMiddleware,
    tenantMiddleware,
    expressMiddleware(apolloServer, {
      context: async ({ req }) => ({
        user: (req as AuthenticatedRequest).user!,
      }),
    })
  )

  const httpServer = app.listen(port, () => {
    console.log(`Ledger service ready at http://localhost:${port}`)
    console.log(`GraphQL: http://localhost:${port}/graphql`)
    console.log(`MCP: http://localhost:${port}/api/mcp/*`)
    console.log(`MCP WebSocket: ws://localhost:${port}/mcp/ws`)
  })

  mcpService.setupWebSocket(httpServer)

  const shutdown = async () => {
    console.log('Shutting down gracefully...')
    await mcpService.shutdown()
    httpServer.close(() => process.exit(0))
  }

  process.on('SIGINT', shutdown)
  process.on('SIGTERM', shutdown)
}
