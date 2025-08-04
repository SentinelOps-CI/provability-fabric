// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { Request, Response, NextFunction } from 'express'
import { expressjwt as jwt } from 'express-jwt'
import jwksRsa from 'jwks-rsa'
import { PrismaClient } from '@prisma/client'
import winston from 'winston'

const prisma = new PrismaClient()

// Configure Winston logger for production
const logger = winston.createLogger({
  level: process.env.LOG_LEVEL || 'info',
  format: winston.format.combine(
    winston.format.timestamp(),
    winston.format.errors({ stack: true }),
    winston.format.json()
  ),
  transports: [
    new winston.transports.File({ filename: 'logs/error.log', level: 'error' }),
    new winston.transports.File({ filename: 'logs/combined.log' }),
    new winston.transports.Console({
      format: winston.format.combine(
        winston.format.colorize(),
        winston.format.simple()
      )
    })
  ]
})

export interface AuthenticatedRequest extends Request {
  user?: {
    sub: string
    tid: string
    email: string
    permissions?: string[]
  }
  tenantFilter?: {
    tenantId: string
  }
}

// Custom error classes for better error handling
export class AuthenticationError extends Error {
  constructor(message: string, public statusCode: number = 401) {
    super(message)
    this.name = 'AuthenticationError'
  }
}

export class AuthorizationError extends Error {
  constructor(message: string, public statusCode: number = 403) {
    super(message)
    this.name = 'AuthorizationError'
  }
}

export class TenantError extends Error {
  constructor(message: string, public statusCode: number = 400) {
    super(message)
    this.name = 'TenantError'
  }
}

// Auth0 JWT validation middleware with error handling
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

// Enhanced tenant validation middleware
export const tenantMiddleware = async (req: AuthenticatedRequest, res: Response, next: NextFunction) => {
  try {
    if (!req.user?.tid) {
      logger.error('Missing tenant ID in JWT claims', { 
        userId: req.user?.sub,
        path: req.path,
        method: req.method 
      })
      throw new AuthenticationError('Missing tenant ID in JWT claims')
    }

    // Verify tenant exists in database
    const tenant = await prisma.tenant.findUnique({
      where: { auth0Id: req.user.tid }
    })

    if (!tenant) {
      logger.error('Tenant not found or access denied', { 
        tenantId: req.user.tid,
        userId: req.user.sub,
        path: req.path 
      })
      throw new AuthorizationError('Tenant not found or access denied')
    }

    // Set PostgreSQL tenant context for RLS policies
    await prisma.$executeRaw`SELECT set_tenant_context(${tenant.id})`

    // Add tenant info to request
    req.user.tid = tenant.id
    
    logger.info('Tenant validation successful', { 
      tenantId: tenant.id,
      userId: req.user.sub 
    })
    
    next()
  } catch (error) {
    logger.error('Tenant validation error', { 
      error: error.message,
      stack: error.stack,
      userId: req.user?.sub,
      path: req.path 
    })
    
    if (error instanceof AuthenticationError || error instanceof AuthorizationError) {
      return res.status(error.statusCode).json({ 
        error: error.message,
        code: error.name 
      })
    }
    
    return res.status(500).json({ 
      error: 'Internal server error',
      code: 'INTERNAL_ERROR' 
    })
  }
}

// Row-level security middleware with enhanced error handling
export const tenantScopeMiddleware = (model: 'capsule' | 'premiumQuote') => {
  return async (req: AuthenticatedRequest, res: Response, next: NextFunction) => {
    try {
      const tenantId = req.user?.tid
      if (!tenantId) {
        logger.error('Missing tenant ID in scope middleware', { 
          userId: req.user?.sub,
          model,
          path: req.path 
        })
        throw new AuthenticationError('Missing tenant ID')
      }

      // Add tenant filter to request for database queries
      req.tenantFilter = { tenantId }
      
      logger.debug('Tenant scope middleware applied', { 
        tenantId,
        model,
        userId: req.user.sub 
      })
      
      next()
    } catch (error) {
      logger.error('Tenant scope middleware error', { 
        error: error.message,
        stack: error.stack,
        userId: req.user?.sub,
        model,
        path: req.path 
      })
      
      if (error instanceof AuthenticationError) {
        return res.status(error.statusCode).json({ 
          error: error.message,
          code: error.name 
        })
      }
      
      return res.status(500).json({ 
        error: 'Internal server error',
        code: 'INTERNAL_ERROR' 
      })
    }
  }
}

// Enhanced tenant-scoped Prisma client with error handling
export const getTenantScopedPrisma = (tenantId: string) => {
  return prisma.$extends({
    query: {
      capsule: {
        async $allOperations({ args, query }) {
          try {
            args.where = { ...args.where, tenantId }
            return await query(args)
          } catch (error) {
            logger.error('Capsule query error', { 
              error: error.message,
              tenantId,
              operation: args 
            })
            throw error
          }
        }
      },
      premiumQuote: {
        async $allOperations({ args, query }) {
          try {
            args.where = { ...args.where, tenantId }
            return await query(args)
          } catch (error) {
            logger.error('PremiumQuote query error', { 
              error: error.message,
              tenantId,
              operation: args 
            })
            throw error
          }
        }
      }
    }
  })
}

// Cleanup function with error handling
export const clearTenantContext = async () => {
  try {
    await prisma.$executeRaw`SELECT clear_tenant_context()`
    logger.debug('Tenant context cleared successfully')
  } catch (error) {
    logger.error('Error clearing tenant context', { 
      error: error.message,
      stack: error.stack 
    })
  }
}

// Permission-based authorization middleware
export const requirePermission = (permission: string) => {
  return (req: AuthenticatedRequest, res: Response, next: NextFunction) => {
    try {
      if (!req.user?.permissions?.includes(permission)) {
        logger.warn('Permission denied', { 
          userId: req.user?.sub,
          requiredPermission: permission,
          userPermissions: req.user?.permissions,
          path: req.path 
        })
        throw new AuthorizationError(`Permission denied: ${permission}`)
      }
      
      logger.debug('Permission granted', { 
        userId: req.user.sub,
        permission,
        path: req.path 
      })
      
      next()
    } catch (error) {
      logger.error('Permission check error', { 
        error: error.message,
        userId: req.user?.sub,
        permission,
        path: req.path 
      })
      
      if (error instanceof AuthorizationError) {
        return res.status(error.statusCode).json({ 
          error: error.message,
          code: error.name 
        })
      }
      
      return res.status(500).json({ 
        error: 'Internal server error',
        code: 'INTERNAL_ERROR' 
      })
    }
  }
}

// Rate limiting middleware
export const rateLimitMiddleware = (windowMs: number = 15 * 60 * 1000, max: number = 100) => {
  const requests = new Map()
  
  return (req: AuthenticatedRequest, res: Response, next: NextFunction) => {
    const key = req.user?.sub || req.ip
    const now = Date.now()
    const windowStart = now - windowMs
    
    if (!requests.has(key)) {
      requests.set(key, [])
    }
    
    const userRequests = requests.get(key)
    const recentRequests = userRequests.filter(timestamp => timestamp > windowStart)
    
    if (recentRequests.length >= max) {
      logger.warn('Rate limit exceeded', { 
        userId: req.user?.sub,
        ip: req.ip,
        path: req.path 
      })
      return res.status(429).json({ 
        error: 'Too many requests',
        code: 'RATE_LIMIT_EXCEEDED' 
      })
    }
    
    recentRequests.push(now)
    requests.set(key, recentRequests)
    next()
  }
}

export { logger } 