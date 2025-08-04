// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { PrismaClient } from '@prisma/client'
import express from 'express'
import { ApolloServer } from '@apollo/server'
import { expressMiddleware } from '@apollo/server/express4'
import bodyParser from 'body-parser'
import cors from 'cors'
import { authMiddleware, tenantMiddleware, AuthenticatedRequest } from './auth-simple'
import { BillingService, billingMiddleware } from './billing'

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
    createCapsule: async (_: any, { hash, specSig, riskScore, reason }: any, { user }: { user: any }) => {
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
    updateCapsule: async (_: any, { hash, riskScore, reason }: any, { user }: { user: any }) => {
      return await prisma.capsule.update({
        where: { hash },
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
    createPremiumQuote: async (_: any, { capsuleHash, riskScore, annualUsd }: any, { user }: { user: any }) => {
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
  const port = process.env.PORT || 8080

  // Initialize billing service
  const billingService = new BillingService()
  const billing = billingMiddleware(billingService)

  // CORS middleware
  app.use(cors())
  app.use(bodyParser.json())

  // Health check endpoint
  app.get('/health', (req, res) => {
    res.json({ status: 'healthy', timestamp: new Date().toISOString() })
  })

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
  const server = new ApolloServer({
    typeDefs,
    resolvers,
  })

  await server.start()

  app.use('/graphql', 
    expressMiddleware(server, {
      context: async ({ req }) => {
        // For development, create a mock user context
        return { 
          user: {
            tid: 'dev-tenant',
            sub: 'dev-user',
            email: 'dev@example.com'
          }
        }
      }
    })
  )

  app.listen(port, () => {
    console.log(`🚀 Provability-Fabric Ledger running on port ${port}`)
    console.log(`📊 Health check: http://localhost:${port}/health`)
    console.log(`🔍 GraphQL: http://localhost:${port}/graphql`)
    console.log(`📡 API Status: http://localhost:${port}/api/status`)
  })
}

startServer().catch(console.error) 