// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { Request, Response, NextFunction } from 'express'
import jwt from 'express-jwt'
import jwksRsa from 'jwks-rsa'
import { PrismaClient } from '@prisma/client'

const prisma = new PrismaClient()

export interface AuthenticatedRequest extends Request {
  user?: {
    sub: string
    tid: string
    email: string
  }
}

// Auth0 JWT validation middleware
export const authMiddleware = jwt({
  secret: jwksRsa.expressJwtSecret({
    cache: true,
    rateLimit: true,
    jwksRequestsPerMinute: 5,
    jwksUri: `https://${process.env.AUTH0_DOMAIN}/.well-known/jwks.json`
  }),
  audience: process.env.AUTH0_AUDIENCE,
  issuer: `https://${process.env.AUTH0_DOMAIN}/`,
  algorithms: ['RS256']
})

// Tenant validation middleware
export const tenantMiddleware = async (req: AuthenticatedRequest, res: Response, next: NextFunction) => {
  try {
    if (!req.user?.tid) {
      return res.status(401).json({ error: 'Missing tenant ID in JWT claims' })
    }

    // Verify tenant exists in database
    const tenant = await prisma.tenant.findUnique({
      where: { auth0Id: req.user.tid }
    })

    if (!tenant) {
      return res.status(403).json({ error: 'Tenant not found or access denied' })
    }

    // Set PostgreSQL tenant context for RLS policies
    await prisma.$executeRaw`SELECT set_tenant_context(${tenant.id})`

    // Add tenant info to request
    req.user.tid = tenant.id
    next()
  } catch (error) {
    console.error('Tenant validation error:', error)
    return res.status(500).json({ error: 'Internal server error' })
  }
}

// Row-level security: ensure user can only access their tenant's data
export const tenantScopeMiddleware = (model: 'capsule' | 'premiumQuote') => {
  return async (req: AuthenticatedRequest, res: Response, next: NextFunction) => {
    try {
      const tenantId = req.user?.tid
      if (!tenantId) {
        return res.status(401).json({ error: 'Missing tenant ID' })
      }

      // Add tenant filter to request for database queries
      req.tenantFilter = { tenantId }
      next()
    } catch (error) {
      console.error('Tenant scope middleware error:', error)
      return res.status(500).json({ error: 'Internal server error' })
    }
  }
}

// Helper function to get tenant-scoped Prisma client
export const getTenantScopedPrisma = (tenantId: string) => {
  return prisma.$extends({
    query: {
      capsule: {
        async $allOperations({ args, query }) {
          args.where = { ...args.where, tenantId }
          return query(args)
        }
      },
      premiumQuote: {
        async $allOperations({ args, query }) {
          args.where = { ...args.where, tenantId }
          return query(args)
        }
      }
    }
  })
}

// Cleanup function to clear tenant context
export const clearTenantContext = async () => {
  try {
    await prisma.$executeRaw`SELECT clear_tenant_context()`
  } catch (error) {
    console.error('Error clearing tenant context:', error)
  }
}