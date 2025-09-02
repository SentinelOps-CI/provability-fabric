// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { PrismaClient } from '@prisma/client'
import express from 'express'
import { ApolloServer } from '@apollo/server'
import { expressMiddleware } from '@apollo/server/express4'
import { json } from 'body-parser'
import cors from 'cors'
import { authMiddleware, tenantMiddleware, AuthenticatedRequest } from './auth'
import { BillingService, billingMiddleware } from './billing'
import McpService from './mcp/mcp-service.js'
import winston from 'winston'

const prisma = new PrismaClient()

// GraphQL schema
const typeDefs = `#graphql
  type Tenant {
    id: ID!
    name: String!
    auth0Id: String!
    createdAt: String!
    updatedAt: String!
  }

  type Capsule {
    id: ID!
    hash: String!
    specSig: String!
    riskScore: Float!
    reason: String
    tenantId: String!
    createdAt: String!
    updatedAt: String!
    tenant: Tenant!
    premiumQuotes: [PremiumQuote!]!
  }

  type PremiumQuote {
    id: ID!
    capsuleHash: String!
    riskScore: Float!
    annualUsd: Float!
    tenantId: String!
    createdAt: String!
    tenant: Tenant!
  }

  type Query {
    tenant: Tenant!
    capsules: [Capsule!]!
    capsule(hash: String!): Capsule
    premiumQuotes: [PremiumQuote!]!
    premiumQuote(capsuleHash: String!): PremiumQuote
  }

  type Mutation {
    createCapsule(hash: String!, specSig: String!, riskScore: Float!, reason: String): Capsule!
    updateCapsule(hash: String!, riskScore: Float!, reason: String): Capsule!
    createPremiumQuote(capsuleHash: String!, riskScore: Float!, annualUsd: Float!): PremiumQuote!
  }
`

// GraphQL resolvers with tenant scoping
const resolvers = {
  Query: {
    tenant: async (_: any, __: any, { user }: { user: any }) => {
      return await prisma.tenant.findUnique({
        where: { id: user.tid }
      })
    },
    capsules: async (_: any, __: any, { user }: { user: any }) => {
      return await prisma.capsule.findMany({
        where: { tenantId: user.tid },
        include: {
          tenant: true,
          premiumQuotes: true
        }
      })
    },
    capsule: async (_: any, { hash }: { hash: string }, { user }: { user: any }) => {
      return await prisma.capsule.findFirst({
        where: { 
          hash,
          tenantId: user.tid 
        },
        include: {
          tenant: true,
          premiumQuotes: true
        }
      })
    },
    premiumQuotes: async (_: any, __: any, { user }: { user: any }) => {
      return await prisma.premiumQuote.findMany({
        where: { tenantId: user.tid },
        include: { tenant: true }
      })
    },
    premiumQuote: async (_: any, { capsuleHash }: { capsuleHash: string }, { user }: { user: any }) => {
      return await prisma.premiumQuote.findFirst({
        where: { 
          capsuleHash,
          tenantId: user.tid 
        },
        include: { tenant: true }
      })
    }
  },
  Mutation: {
    createCapsule: async (_: any, { hash, specSig, riskScore, reason }: { hash: string, specSig: string, riskScore: number, reason?: string }, { user }: { user: any }) => {
      return await prisma.capsule.create({
        data: {
          hash,
          specSig,
          riskScore,
          reason,
          tenantId: user.tid
        },
        include: {
          tenant: true,
          premiumQuotes: true
        }
      })
    },
    updateCapsule: async (_: any, { hash, riskScore, reason }: { hash: string, riskScore: number, reason?: string }, { user }: { user: any }) => {
      return await prisma.capsule.update({
        where: { 
          hash,
          tenantId: user.tid 
        },
        data: {
          riskScore,
          reason
        },
        include: {
          tenant: true,
          premiumQuotes: true
        }
      })
    },
    createPremiumQuote: async (_: any, { capsuleHash, riskScore, annualUsd }: { capsuleHash: string, riskScore: number, annualUsd: number }, { user }: { user: any }) => {
      return await prisma.premiumQuote.create({
        data: {
          capsuleHash,
          riskScore,
          annualUsd,
          tenantId: user.tid
        },
        include: { tenant: true }
      })
    }
  }
}

async function startServer() {
  const app = express()
  const port = process.env.PORT || 4000

  // Initialize logger
  const logger = winston.createLogger({
    level: 'info',
    format: winston.format.combine(
      winston.format.timestamp(),
      winston.format.json()
    ),
    transports: [
      new winston.transports.Console(),
      new winston.transports.File({ filename: 'mcp-service.log' })
    ]
  })

  // Initialize billing service
  const billingService = new BillingService()
  const billing = billingMiddleware(billingService)

  // Initialize MCP service
  const mcpService = new McpService(
    {
      name: 'provability-fabric-mcp',
      version: '1.0.0',
      description: 'Model Context Protocol integration for Provability-Fabric',
      enableWebSocket: true,
      sidecarUrl: process.env.SIDECAR_URL || 'http://localhost:8081',
      enableMultiTenant: true
    },
    prisma,
    logger
  )

  await mcpService.initialize()

  // CORS middleware
  app.use(cors())
  app.use(json())

  // Health check endpoint
  app.get('/health', (req, res) => {
    res.json({ status: 'healthy', timestamp: new Date().toISOString() })
  })

  // MCP endpoints
  app.use('/api', mcpService.getRouter())

  // Billing endpoints
  app.post('/usage', authMiddleware, tenantMiddleware, billing.recordUsage)
  app.get('/tenant/:tenantId/invoice/pdf', authMiddleware, tenantMiddleware, billing.getInvoicePDF)
  app.get('/tenant/:tenantId/invoice/csv', authMiddleware, tenantMiddleware, billing.getInvoiceCSV)

  // Tenant-scoped REST endpoints
  app.get('/tenant/:tid/capsules', authMiddleware, tenantMiddleware, async (req: AuthenticatedRequest, res) => {
    try {
      const capsules = await prisma.capsule.findMany({
        where: { tenantId: req.user!.tid },
        include: {
          tenant: true,
          premiumQuotes: true
        }
      })

      res.json(capsules)
    } catch (error) {
      console.error('Error fetching capsules:', error)
      res.status(500).json({ error: 'Internal server error' })
    }
  })

  // REST endpoint for premium quotes (tenant-scoped)
  app.get('/tenant/:tid/quote/:hash', authMiddleware, tenantMiddleware, async (req: AuthenticatedRequest, res) => {
    try {
      const { hash } = req.params
      
      const capsule = await prisma.capsule.findFirst({
        where: { 
          hash,
          tenantId: req.user!.tid 
        },
        include: {
          premiumQuotes: {
            orderBy: { createdAt: 'desc' },
            take: 1
          }
        }
      })

      if (!capsule) {
        return res.status(404).json({ error: 'Capsule not found' })
      }

      const baseRate = parseFloat(process.env.BASE_RATE || '1000.0')
      const annualUsd = capsule.riskScore * baseRate

      // Create or update premium quote
      const premiumQuote = await prisma.premiumQuote.create({
        data: {
          capsuleHash: hash,
          riskScore: capsule.riskScore,
          annualUsd,
          tenantId: req.user!.tid
        }
      })

      res.json({
        risk: capsule.riskScore,
        premium: annualUsd,
        quote_id: premiumQuote.id,
        created_at: premiumQuote.createdAt
      })
    } catch (error) {
      console.error('Error generating premium quote:', error)
      res.status(500).json({ error: 'Internal server error' })
    }
  })

  // Apollo Server setup with context
  const apolloServer = new ApolloServer({
    typeDefs,
    resolvers,
  })

  await apolloServer.start()

  app.use('/graphql', 
    authMiddleware,
    tenantMiddleware,
    expressMiddleware(apolloServer, {
      context: async ({ req }) => {
        return { user: (req as AuthenticatedRequest).user }
      }
    })
  )

  const httpServer = app.listen(port, () => {
    console.log(`🚀 Ledger service ready at http://localhost:${port}`)
    console.log(`📊 GraphQL endpoint: http://localhost:${port}/graphql`)
    console.log(`🤖 MCP endpoints: http://localhost:${port}/api/mcp/*`)
    console.log(`🔌 MCP WebSocket: ws://localhost:${port}/mcp/ws`)
    console.log(`💰 Premium quotes: http://localhost:${port}/tenant/:tid/quote/:hash`)
    console.log(`🏢 Tenant capsules: http://localhost:${port}/tenant/:tid/capsules`)
    console.log(`💳 Billing endpoints: http://localhost:${port}/usage, /tenant/:tid/invoice/*`)
  })

  // Setup WebSocket support for MCP
  mcpService.setupWebSocket(httpServer)

  // Graceful shutdown handling
  process.on('SIGINT', async () => {
    console.log('🛑 Shutting down gracefully...')
    await mcpService.shutdown()
    httpServer.close(() => {
      console.log('✅ Server closed')
      process.exit(0)
    })
  })
}

startServer().catch(console.error) 