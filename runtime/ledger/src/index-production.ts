// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { PrismaClient } from '@prisma/client'
import express from 'express'
import { ApolloServer } from '@apollo/server'
import { expressMiddleware } from '@apollo/server/express4'
import bodyParser from 'body-parser'
import cors from 'cors'
import { 
  authMiddleware, 
  tenantMiddleware, 
  AuthenticatedRequest,
  logger,
  rateLimitMiddleware,
  requirePermission,
  AuthenticationError,
  AuthorizationError,
  TenantError
} from './auth-production'
import { BillingService, billingMiddleware } from './billing'

const prisma = new PrismaClient()

// Enhanced GraphQL schema with comprehensive types
const typeDefs = `#graphql
  type Tenant {
    id: ID!
    name: String!
    auth0Id: String!
    createdAt: String!
    updatedAt: String!
    capsules: [Capsule!]!
    premiumQuotes: [PremiumQuote!]!
    usageEvents: [UsageEvent!]!
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
    capsule: Capsule!
  }

  type UsageEvent {
    id: ID!
    tenantId: String!
    cpuMs: Int!
    netBytes: Int!
    ts: String!
    tenant: Tenant!
  }

  type InvoiceData {
    tenantId: String!
    periodStart: String!
    periodEnd: String!
    costUsd: Float!
    usageEvents: Int!
    totalCpuMs: Int!
    totalNetBytes: Int!
  }

  type Query {
    tenant: Tenant!
    capsules: [Capsule!]!
    capsule(hash: String!): Capsule
    premiumQuotes: [PremiumQuote!]!
    premiumQuote(capsuleHash: String!): PremiumQuote
    usageEvents: [UsageEvent!]!
    invoice(period: String!): InvoiceData!
  }

  type Mutation {
    createCapsule(hash: String!, specSig: String!, riskScore: Float!, reason: String): Capsule!
    updateCapsule(hash: String!, riskScore: Float!, reason: String): Capsule!
    createPremiumQuote(capsuleHash: String!, riskScore: Float!, annualUsd: Float!): PremiumQuote!
    recordUsage(cpuMs: Int!, netBytes: Int!): UsageEvent!
  }
`

// Enhanced GraphQL resolvers with comprehensive error handling
const resolvers = {
  Query: {
    tenant: async (_: any, __: any, { user }: { user: any }) => {
      try {
        const tenant = await prisma.tenant.findUnique({
          where: { id: user.tid },
          include: {
            capsules: true,
            premiumQuotes: true,
            usageEvents: true
          }
        })
        
        if (!tenant) {
          throw new Error('Tenant not found')
        }
        
        logger.info('Tenant query successful', { tenantId: user.tid })
        return tenant
      } catch (error) {
        logger.error('Tenant query error', { 
          error: error.message,
          userId: user?.sub,
          tenantId: user?.tid 
        })
        throw error
      }
    },
    
    capsules: async (_: any, __: any, { user }: { user: any }) => {
      try {
        const capsules = await prisma.capsule.findMany({
          where: { tenantId: user.tid },
          include: {
            tenant: true,
            premiumQuotes: true
          },
          orderBy: { createdAt: 'desc' }
        })
        
        logger.info('Capsules query successful', { 
          count: capsules.length,
          tenantId: user.tid 
        })
        return capsules
      } catch (error) {
        logger.error('Capsules query error', { 
          error: error.message,
          userId: user?.sub,
          tenantId: user?.tid 
        })
        throw error
      }
    },
    
    capsule: async (_: any, { hash }: { hash: string }, { user }: { user: any }) => {
      try {
        const capsule = await prisma.capsule.findFirst({
          where: { 
            hash,
            tenantId: user.tid 
          },
          include: {
            tenant: true,
            premiumQuotes: true
          }
        })
        
        if (!capsule) {
          logger.warn('Capsule not found', { hash, tenantId: user.tid })
          return null
        }
        
        logger.info('Capsule query successful', { hash, tenantId: user.tid })
        return capsule
      } catch (error) {
        logger.error('Capsule query error', { 
          error: error.message,
          hash,
          userId: user?.sub,
          tenantId: user?.tid 
        })
        throw error
      }
    },
    
    premiumQuotes: async (_: any, __: any, { user }: { user: any }) => {
      try {
        const quotes = await prisma.premiumQuote.findMany({
          where: { tenantId: user.tid },
          include: { 
            tenant: true,
            capsule: true
          },
          orderBy: { createdAt: 'desc' }
        })
        
        logger.info('Premium quotes query successful', { 
          count: quotes.length,
          tenantId: user.tid 
        })
        return quotes
      } catch (error) {
        logger.error('Premium quotes query error', { 
          error: error.message,
          userId: user?.sub,
          tenantId: user?.tid 
        })
        throw error
      }
    },
    
    premiumQuote: async (_: any, { capsuleHash }: { capsuleHash: string }, { user }: { user: any }) => {
      try {
        const quote = await prisma.premiumQuote.findFirst({
          where: { 
            capsuleHash,
            tenantId: user.tid 
          },
          include: { 
            tenant: true,
            capsule: true
          }
        })
        
        if (!quote) {
          logger.warn('Premium quote not found', { capsuleHash, tenantId: user.tid })
          return null
        }
        
        logger.info('Premium quote query successful', { capsuleHash, tenantId: user.tid })
        return quote
      } catch (error) {
        logger.error('Premium quote query error', { 
          error: error.message,
          capsuleHash,
          userId: user?.sub,
          tenantId: user?.tid 
        })
        throw error
      }
    },
    
    usageEvents: async (_: any, __: any, { user }: { user: any }) => {
      try {
        const events = await prisma.usageEvent.findMany({
          where: { tenantId: user.tid },
          include: { tenant: true },
          orderBy: { ts: 'desc' },
          take: 100
        })
        
        logger.info('Usage events query successful', { 
          count: events.length,
          tenantId: user.tid 
        })
        return events
      } catch (error) {
        logger.error('Usage events query error', { 
          error: error.message,
          userId: user?.sub,
          tenantId: user?.tid 
        })
        throw error
      }
    },
    
    invoice: async (_: any, { period }: { period: string }, { user }: { user: any }) => {
      try {
        // This would integrate with the billing service
        // For now, return mock data
        logger.info('Invoice query successful', { period, tenantId: user.tid })
        return {
          tenantId: user.tid,
          periodStart: new Date().toISOString(),
          periodEnd: new Date().toISOString(),
          costUsd: 100.0,
          usageEvents: 10,
          totalCpuMs: 1000,
          totalNetBytes: 1024
        }
      } catch (error) {
        logger.error('Invoice query error', { 
          error: error.message,
          period,
          userId: user?.sub,
          tenantId: user?.tid 
        })
        throw error
      }
    }
  },
  
  Mutation: {
    createCapsule: async (_: any, { hash, specSig, riskScore, reason }: any, { user }: { user: any }) => {
      try {
        const capsule = await prisma.capsule.create({
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
        
        logger.info('Capsule created successfully', { 
          hash,
          riskScore,
          tenantId: user.tid 
        })
        return capsule
      } catch (error) {
        logger.error('Capsule creation error', { 
          error: error.message,
          hash,
          userId: user?.sub,
          tenantId: user?.tid 
        })
        throw error
      }
    },
    
    updateCapsule: async (_: any, { hash, riskScore, reason }: any, { user }: { user: any }) => {
      try {
        const capsule = await prisma.capsule.update({
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
        
        logger.info('Capsule updated successfully', { 
          hash,
          riskScore,
          tenantId: user.tid 
        })
        return capsule
      } catch (error) {
        logger.error('Capsule update error', { 
          error: error.message,
          hash,
          userId: user?.sub,
          tenantId: user?.tid 
        })
        throw error
      }
    },
    
    createPremiumQuote: async (_: any, { capsuleHash, riskScore, annualUsd }: any, { user }: { user: any }) => {
      try {
        const quote = await prisma.premiumQuote.create({
          data: {
            capsuleHash,
            riskScore,
            annualUsd,
            tenantId: user.tid
          },
          include: { 
            tenant: true,
            capsule: true
          }
        })
        
        logger.info('Premium quote created successfully', { 
          capsuleHash,
          annualUsd,
          tenantId: user.tid 
        })
        return quote
      } catch (error) {
        logger.error('Premium quote creation error', { 
          error: error.message,
          capsuleHash,
          userId: user?.sub,
          tenantId: user?.tid 
        })
        throw error
      }
    },
    
    recordUsage: async (_: any, { cpuMs, netBytes }: any, { user }: { user: any }) => {
      try {
        const event = await prisma.usageEvent.create({
          data: {
            tenantId: user.tid,
            cpuMs,
            netBytes,
            ts: new Date()
          },
          include: { tenant: true }
        })
        
        logger.info('Usage event recorded successfully', { 
          cpuMs,
          netBytes,
          tenantId: user.tid 
        })
        return event
      } catch (error) {
        logger.error('Usage event recording error', { 
          error: error.message,
          cpuMs,
          netBytes,
          userId: user?.sub,
          tenantId: user?.tid 
        })
        throw error
      }
    }
  }
}

async function startServer() {
  try {
    const app = express()
    const port = process.env.PORT || 8080

    // Initialize billing service
    const billingService = new BillingService()
    const billing = billingMiddleware(billingService)

    // CORS middleware
    app.use(cors())
    app.use(bodyParser.json())

    // Global error handling middleware
    app.use((error: any, req: Request, res: Response, next: NextFunction) => {
      logger.error('Unhandled error', { 
        error: error.message,
        stack: error.stack,
        path: req.path,
        method: req.method,
        ip: req.ip
      })
      
      res.status(500).json({ 
        error: 'Internal server error',
        code: 'INTERNAL_ERROR' 
      })
    })

    // Root endpoint
    app.get('/', (req, res) => {
      res.json({ 
        message: 'Welcome to Provability-Fabric Ledger API',
        version: process.env.npm_package_version || '1.0.0',
        timestamp: new Date().toISOString(),
        environment: process.env.NODE_ENV || 'development',
        endpoints: {
          health: '/health',
          status: '/api/status',
          graphql: '/graphql',
          capsules: '/tenant/:tid/capsules',
          quotes: '/tenant/:tid/quote/:hash'
        }
      })
    })

    // Health check endpoint
    app.get('/health', (req, res) => {
      res.json({ 
        status: 'healthy', 
        timestamp: new Date().toISOString(),
        service: 'Provability-Fabric Ledger',
        version: process.env.npm_package_version || '1.0.0'
      })
    })

    // API status endpoint
    app.get('/api/status', (req, res) => {
      res.json({ 
        service: 'Provability-Fabric Ledger',
        status: 'running',
        timestamp: new Date().toISOString(),
        version: process.env.npm_package_version || '1.0.0',
        environment: process.env.NODE_ENV || 'development'
      })
    })

    // Billing endpoints with authentication and rate limiting
    app.post('/usage', 
      authMiddleware, 
      tenantMiddleware, 
      rateLimitMiddleware(15 * 60 * 1000, 1000),
      billing.recordUsage
    )
    
    app.get('/tenant/:tenantId/invoice/pdf', 
      authMiddleware, 
      tenantMiddleware, 
      requirePermission('read:invoices'),
      billing.getInvoicePDF
    )
    
    app.get('/tenant/:tenantId/invoice/csv', 
      authMiddleware, 
      tenantMiddleware, 
      requirePermission('read:invoices'),
      billing.getInvoiceCSV
    )

    // Tenant-scoped REST endpoints with enhanced error handling
    app.get('/tenant/:tid/capsules', 
      authMiddleware, 
      tenantMiddleware, 
      rateLimitMiddleware(15 * 60 * 1000, 100),
      async (req: AuthenticatedRequest, res) => {
        try {
          const capsules = await prisma.capsule.findMany({
            where: { tenantId: req.user!.tid },
            include: {
              tenant: true,
              premiumQuotes: true
            },
            orderBy: { createdAt: 'desc' }
          })

          logger.info('Capsules fetched successfully', { 
            count: capsules.length,
            tenantId: req.user!.tid 
          })

          res.json(capsules)
        } catch (error) {
          logger.error('Error fetching capsules', { 
            error: error.message,
            stack: error.stack,
            tenantId: req.user!.tid 
          })
          res.status(500).json({ 
            error: 'Internal server error',
            code: 'INTERNAL_ERROR' 
          })
        }
      }
    )

    // REST endpoint for premium quotes with enhanced error handling
    app.get('/tenant/:tid/quote/:hash', 
      authMiddleware, 
      tenantMiddleware, 
      rateLimitMiddleware(15 * 60 * 1000, 50),
      async (req: AuthenticatedRequest, res) => {
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
            logger.warn('Capsule not found for quote generation', { 
              hash,
              tenantId: req.user!.tid 
            })
            return res.status(404).json({ 
              error: 'Capsule not found',
              code: 'CAPSULE_NOT_FOUND' 
            })
          }

          const baseRate = parseFloat(process.env.BASE_RATE || '1000.0')
          const annualUsd = capsule.riskScore * baseRate

          // Create premium quote
          const premiumQuote = await prisma.premiumQuote.create({
            data: {
              capsuleHash: hash,
              riskScore: capsule.riskScore,
              annualUsd,
              tenantId: req.user!.tid
            }
          })

          logger.info('Premium quote generated successfully', { 
            hash,
            riskScore: capsule.riskScore,
            annualUsd,
            tenantId: req.user!.tid 
          })

          res.json({
            risk: capsule.riskScore,
            premium: annualUsd,
            quote_id: premiumQuote.id,
            created_at: premiumQuote.createdAt
          })
        } catch (error) {
          logger.error('Error generating premium quote', { 
            error: error.message,
            stack: error.stack,
            hash: req.params.hash,
            tenantId: req.user!.tid 
          })
          res.status(500).json({ 
            error: 'Internal server error',
            code: 'INTERNAL_ERROR' 
          })
        }
      }
    )

    // Apollo Server setup with enhanced error handling
    const server = new ApolloServer({
      typeDefs,
      resolvers,
      formatError: (error) => {
        logger.error('GraphQL error', { 
          message: error.message,
          path: error.path,
          extensions: error.extensions 
        })
        
        return {
          message: error.message,
          code: error.extensions?.code || 'GRAPHQL_ERROR'
        }
      }
    })

    await server.start()

    app.use('/graphql', 
      expressMiddleware(server, {
        context: async ({ req }) => {
          // For development, create a mock user context
          // In production, this would come from Auth0
          return { 
            user: {
              tid: 'dev-tenant',
              sub: 'dev-user',
              email: 'dev@example.com',
              permissions: ['read:capsules', 'write:capsules', 'read:quotes', 'write:quotes']
            }
          }
        }
      })
    )

    app.listen(port, () => {
      logger.info('Provability-Fabric Ledger started successfully', {
        port,
        environment: process.env.NODE_ENV || 'development',
        version: process.env.npm_package_version || '1.0.0'
      })
      
      console.log(`🚀 Provability-Fabric Ledger running on port ${port}`)
      console.log(`📊 Health check: http://localhost:${port}/health`)
      console.log(`🔍 GraphQL: http://localhost:${port}/graphql`)
      console.log(`📡 API Status: http://localhost:${port}/api/status`)
    })
  } catch (error) {
    logger.error('Failed to start server', { 
      error: error.message,
      stack: error.stack 
    })
    process.exit(1)
  }
}

// Graceful shutdown handling
process.on('SIGTERM', async () => {
  logger.info('SIGTERM received, shutting down gracefully')
  await prisma.$disconnect()
  process.exit(0)
})

process.on('SIGINT', async () => {
  logger.info('SIGINT received, shutting down gracefully')
  await prisma.$disconnect()
  process.exit(0)
})

// Unhandled error handling
process.on('uncaughtException', (error) => {
  logger.error('Uncaught exception', { 
    error: error.message,
    stack: error.stack 
  })
  process.exit(1)
})

process.on('unhandledRejection', (reason, promise) => {
  logger.error('Unhandled rejection', { 
    reason: reason,
    promise: promise 
  })
  process.exit(1)
})

startServer().catch((error) => {
  logger.error('Startup error', { 
    error: error.message,
    stack: error.stack 
  })
  process.exit(1)
}) 