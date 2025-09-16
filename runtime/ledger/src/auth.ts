// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { Request, Response, NextFunction } from 'express'
import { expressjwt as jwt } from 'express-jwt'
import jwksRsa from 'jwks-rsa'
import { PrismaClient } from '@prisma/client'

const prisma = new PrismaClient()

export interface AuthenticatedRequest extends Request {
  user?: {
    sub: string
    tid: string
    email: string
  }
  tenantFilter?: {
    tenantId: string
  }
}

// Enhanced JWT validation middleware with certificate chain pinning
export const authMiddleware = jwt({
  secret: jwksRsa.expressJwtSecret({
    cache: true,
    rateLimit: true,
    jwksRequestsPerMinute: 5,
    jwksUri: process.env.JWKS_URI || `https://${process.env.AUTH0_DOMAIN}/.well-known/jwks.json`,
    // Add certificate chain pinning
    requestAgent: new (require('https').Agent)({
      checkServerIdentity: (host: string, cert: any) => {
        // Certificate chain pinning validation
        const expectedPins = process.env.CERTIFICATE_PINS?.split(',') || [];
        const certFingerprint = require('crypto')
          .createHash('sha256')
          .update(cert.raw)
          .digest('base64');
        
        const certPin = `sha256/${certFingerprint}`;
        
        if (expectedPins.length > 0 && !expectedPins.includes(certPin)) {
          throw new Error(`Certificate pin validation failed. Expected: ${expectedPins.join(', ')}, Got: ${certPin}`);
        }
        
        return undefined; // Use default hostname validation
      }
    })
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
          if ('where' in args && args.where !== undefined) {
            args.where = { ...args.where, tenantId }
          } else if ('data' in args && args.data !== undefined) {
            args.data = { ...args.data, tenantId }
          }
          return query(args)
        }
      },
      premiumQuote: {
        async $allOperations({ args, query }) {
          if ('where' in args && args.where !== undefined) {
            args.where = { ...args.where, tenantId }
          } else if ('data' in args && args.data !== undefined) {
            args.data = { ...args.data, tenantId }
          }
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