// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import type { Express, Response } from 'express'
import type { BillingService } from '../billing.js'
import type { AuthenticatedRequest } from '../auth-simple.js'
import type { ServerDeps } from './types.js'

export interface RestRouteDeps extends ServerDeps {
  billing: ReturnType<typeof import('../billing.js').billingMiddleware>
  authMiddleware: typeof import('../auth-simple.js').authMiddleware
  tenantMiddleware: typeof import('../auth-simple.js').tenantMiddleware
}

export function registerRestRoutes(app: Express, deps: RestRouteDeps): void {
  const { prisma, billing, authMiddleware, tenantMiddleware } = deps

  app.get('/health', (_req, res) => {
    res.json({ status: 'healthy', timestamp: new Date().toISOString() })
  })

  app.post('/usage', authMiddleware, tenantMiddleware, billing.recordUsage)
  app.get('/tenant/:tenantId/invoice/pdf', authMiddleware, tenantMiddleware, billing.getInvoicePDF)
  app.get('/tenant/:tenantId/invoice/csv', authMiddleware, tenantMiddleware, billing.getInvoiceCSV)

  app.get(
    '/tenant/:tid/capsules',
    authMiddleware,
    tenantMiddleware,
    async (req: AuthenticatedRequest, res: Response) => {
      try {
        const capsules = await prisma.capsule.findMany({
          where: { tenantId: req.user!.tid },
          include: { tenant: true, premiumQuotes: true },
        })
        res.json(capsules)
      } catch (error) {
        console.error('Error fetching capsules:', error)
        res.status(500).json({ error: 'Internal server error' })
      }
    }
  )

  app.get(
    '/tenant/:tid/quote/:hash',
    authMiddleware,
    tenantMiddleware,
    async (req: AuthenticatedRequest, res: Response) => {
      try {
        const { hash } = req.params
        const capsule = await prisma.capsule.findFirst({
          where: { hash, tenantId: req.user!.tid },
          include: {
            premiumQuotes: { orderBy: { createdAt: 'desc' }, take: 1 },
          },
        })

        if (!capsule) {
          return res.status(404).json({ error: 'Capsule not found' })
        }

        const baseRate = parseFloat(process.env.BASE_RATE || '1000.0')
        const annualUsd = capsule.riskScore * baseRate

        const premiumQuote = await prisma.premiumQuote.create({
          data: {
            capsuleHash: hash,
            riskScore: capsule.riskScore,
            annualUsd,
            tenantId: req.user!.tid,
          },
        })

        res.json({
          risk: capsule.riskScore,
          premium: annualUsd,
          quote_id: premiumQuote.id,
          created_at: premiumQuote.createdAt,
        })
      } catch (error) {
        console.error('Error generating premium quote:', error)
        res.status(500).json({ error: 'Internal server error' })
      }
    }
  )
}

export async function ensureDefaultTenants(prisma: ServerDeps['prisma']): Promise<void> {
  const tenants = [
    { id: 'dev-tenant', name: 'Development Tenant', auth0Id: 'dev-tenant' },
    { id: 'tenant-a', name: 'Tenant A', auth0Id: 'tenant-a' },
    { id: 'tenant-b', name: 'Tenant B', auth0Id: 'tenant-b' },
  ]
  for (const tenant of tenants) {
    await prisma.tenant.upsert({
      where: { id: tenant.id },
      create: tenant,
      update: {},
    })
  }
}

export function userFromRequest(req: { headers: { authorization?: string } }) {
  const auth = req.headers.authorization
  if (auth?.startsWith('Bearer ')) {
    try {
      const payloadPart = auth.slice(7).split('.')[1]
      const payload = JSON.parse(
        Buffer.from(payloadPart.replace(/-/g, '+').replace(/_/g, '/'), 'base64').toString('utf8')
      )
      if (typeof payload.tid === 'string' && payload.tid.length > 0) {
        return {
          tid: payload.tid,
          sub: payload.sub ?? 'test-user',
          email: 'test@example.com',
        }
      }
    } catch {
      // fall through to dev defaults
    }
  }
  return {
    tid: 'dev-tenant',
    sub: 'dev-user',
    email: 'dev@example.com',
  }
}
