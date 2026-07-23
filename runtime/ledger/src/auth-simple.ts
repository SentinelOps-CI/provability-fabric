// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { Request, Response, NextFunction } from 'express'
import { PrismaClient } from '@prisma/client'

const prisma = new PrismaClient()

/** Dev-only auth. Production must use `auth.js` / `auth-production.ts`. */
function assertDevProfile(): void {
  const explicit = (
    process.env.PF_PROFILE ||
    process.env.PROFILE ||
    ''
  ).toLowerCase()
  // Explicit PROFILE/PF_PROFILE=dev|simple wins over Docker NODE_ENV=production.
  if (explicit === 'dev' || explicit === 'simple') {
    return
  }
  const nodeEnv = (process.env.NODE_ENV || '').toLowerCase()
  if (
    explicit === 'production' ||
    explicit === 'prod' ||
    nodeEnv === 'production' ||
    nodeEnv === 'prod'
  ) {
    throw new Error(
      'auth-simple must not run under production/prod; use auth.js / auth-production'
    )
  }
}

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

// Simple authentication middleware (for development)
export const authMiddleware = async (req: AuthenticatedRequest, res: Response, next: NextFunction) => {
  try {
    assertDevProfile()
    // For development, create a mock user
    req.user = {
      sub: 'dev-user',
      tid: 'dev-tenant',
      email: 'dev@example.com'
    }
    next()
  } catch (error) {
    console.error('Auth middleware error:', error)
    const message = error instanceof Error ? error.message : 'Internal server error'
    if (message.includes('must not run under production')) {
      return res.status(500).json({ error: message })
    }
    return res.status(500).json({ error: 'Internal server error' })
  }
}

// Simple tenant validation middleware
export const tenantMiddleware = async (req: AuthenticatedRequest, res: Response, next: NextFunction) => {
  try {
    assertDevProfile()
    if (!req.user?.tid) {
      return res.status(401).json({ error: 'Missing tenant ID' })
    }

    // For development, always allow access
    next()
  } catch (error) {
    console.error('Tenant validation error:', error)
    const message = error instanceof Error ? error.message : 'Internal server error'
    if (message.includes('must not run under production')) {
      return res.status(500).json({ error: message })
    }
    return res.status(500).json({ error: 'Internal server error' })
  }
}

// Simple tenant scope middleware
export const tenantScopeMiddleware = (model: 'capsule' | 'premiumQuote') => {
  return async (req: AuthenticatedRequest, res: Response, next: NextFunction) => {
    try {
      assertDevProfile()
      const tenantId = req.user?.tid
      if (!tenantId) {
        return res.status(401).json({ error: 'Missing tenant ID' })
      }

      req.tenantFilter = { tenantId }
      next()
    } catch (error) {
      console.error('Tenant scope middleware error:', error)
      const message = error instanceof Error ? error.message : 'Internal server error'
      if (message.includes('must not run under production')) {
        return res.status(500).json({ error: message })
      }
      return res.status(500).json({ error: 'Internal server error' })
    }
  }
}

// Simple tenant-scoped Prisma client
export const getTenantScopedPrisma = (tenantId: string) => {
  return prisma
}

// Cleanup function
export const clearTenantContext = async () => {
  try {
    // No-op for development
  } catch (error) {
    console.error('Error clearing tenant context:', error)
  }
}
