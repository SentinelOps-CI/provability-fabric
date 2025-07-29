// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { PrismaClient } from '@prisma/client'
import { Request, Response } from 'express'
import { PDFDocument, rgb, StandardFonts } from 'pdf-lib'
import { format } from 'date-fns'

const prisma = new PrismaClient()

export interface UsageEvent {
  tenantId: string
  cpuMs: number
  netBytes: number
  ts?: Date
}

export interface RateCard {
  cpuPerMs: number  // USD per millisecond of CPU
  networkPerMB: number  // USD per MB of network
  minimumMonthly: number  // Minimum monthly charge
}

export interface InvoiceData {
  tenantId: string
  periodStart: Date
  periodEnd: Date
  costUsd: number
  usageEvents: number
  totalCpuMs: number
  totalNetBytes: number
}

// Default rate card - should be loaded from ConfigMap in production
const DEFAULT_RATE_CARD: RateCard = {
  cpuPerMs: 0.000001,  // $1 per 1M CPU milliseconds
  networkPerMB: 0.01,   // $0.01 per MB
  minimumMonthly: 10.0  // $10 minimum
}

export class BillingService {
  private rateCard: RateCard

  constructor(rateCard?: RateCard) {
    this.rateCard = rateCard || DEFAULT_RATE_CARD
  }

  /**
   * Record a usage event for a tenant
   */
  async recordUsageEvent(event: UsageEvent): Promise<void> {
    // Validate timestamp is not in the future
    const eventTime = event.ts || new Date()
    if (eventTime > new Date()) {
      throw new Error('Usage event timestamp cannot be in the future')
    }

    await prisma.usageEvent.create({
      data: {
        tenantId: event.tenantId,
        cpuMs: event.cpuMs,
        netBytes: event.netBytes,
        ts: eventTime
      }
    })
  }

  /**
   * Calculate cost for usage metrics
   */
  calculateCost(cpuMs: number, netBytes: number): number {
    const cpuCost = cpuMs * this.rateCard.cpuPerMs
    const networkCost = (netBytes / (1024 * 1024)) * this.rateCard.networkPerMB
    const totalCost = cpuCost + networkCost
    
    return Math.max(totalCost, this.rateCard.minimumMonthly)
  }

  /**
   * Generate daily invoice for a tenant
   */
  async generateDailyInvoice(tenantId: string, date: Date): Promise<InvoiceData> {
    const startOfDay = new Date(date)
    startOfDay.setHours(0, 0, 0, 0)
    
    const endOfDay = new Date(date)
    endOfDay.setHours(23, 59, 59, 999)

    // Aggregate usage events for the day
    const usageEvents = await prisma.usageEvent.findMany({
      where: {
        tenantId,
        ts: {
          gte: startOfDay,
          lte: endOfDay
        }
      }
    })

    const totalCpuMs = usageEvents.reduce((sum, event) => sum + event.cpuMs, 0)
    const totalNetBytes = usageEvents.reduce((sum, event) => sum + event.netBytes, 0)
    const costUsd = this.calculateCost(totalCpuMs, totalNetBytes)

    // Create or update invoice
    const invoice = await prisma.tenantInvoice.upsert({
      where: {
        tenantId_periodStart: {
          tenantId,
          periodStart: startOfDay
        }
      },
      update: {
        costUsd,
        usageEvents: usageEvents.length,
        totalCpuMs,
        totalNetBytes,
        periodEnd: endOfDay
      },
      create: {
        tenantId,
        periodStart: startOfDay,
        periodEnd: endOfDay,
        costUsd,
        usageEvents: usageEvents.length,
        totalCpuMs,
        totalNetBytes
      }
    })

    return {
      tenantId: invoice.tenantId,
      periodStart: invoice.periodStart,
      periodEnd: invoice.periodEnd,
      costUsd: invoice.costUsd,
      usageEvents: invoice.usageEvents,
      totalCpuMs: invoice.totalCpuMs,
      totalNetBytes: invoice.totalNetBytes
    }
  }

  /**
   * Generate monthly invoice for a tenant
   */
  async generateMonthlyInvoice(tenantId: string, year: number, month: number): Promise<InvoiceData> {
    const startOfMonth = new Date(year, month - 1, 1)
    const endOfMonth = new Date(year, month, 0, 23, 59, 59, 999)

    // Aggregate usage events for the month
    const usageEvents = await prisma.usageEvent.findMany({
      where: {
        tenantId,
        ts: {
          gte: startOfMonth,
          lte: endOfMonth
        }
      }
    })

    const totalCpuMs = usageEvents.reduce((sum, event) => sum + event.cpuMs, 0)
    const totalNetBytes = usageEvents.reduce((sum, event) => sum + event.netBytes, 0)
    const costUsd = this.calculateCost(totalCpuMs, totalNetBytes)

    // Create or update invoice
    const invoice = await prisma.tenantInvoice.upsert({
      where: {
        tenantId_periodStart: {
          tenantId,
          periodStart: startOfMonth
        }
      },
      update: {
        costUsd,
        usageEvents: usageEvents.length,
        totalCpuMs,
        totalNetBytes,
        periodEnd: endOfMonth
      },
      create: {
        tenantId,
        periodStart: startOfMonth,
        periodEnd: endOfMonth,
        costUsd,
        usageEvents: usageEvents.length,
        totalCpuMs,
        totalNetBytes
      }
    })

    return {
      tenantId: invoice.tenantId,
      periodStart: invoice.periodStart,
      periodEnd: invoice.periodEnd,
      costUsd: invoice.costUsd,
      usageEvents: invoice.usageEvents,
      totalCpuMs: invoice.totalCpuMs,
      totalNetBytes: invoice.totalNetBytes
    }
  }

  /**
   * Generate PDF invoice
   */
  async generatePDFInvoice(tenantId: string, period: string): Promise<Buffer> {
    const [year, month] = period.split('-').map(Number)
    const invoice = await this.generateMonthlyInvoice(tenantId, year, month)
    
    const tenant = await prisma.tenant.findUnique({
      where: { id: tenantId }
    })

    if (!tenant) {
      throw new Error('Tenant not found')
    }

    // Create PDF document
    const pdfDoc = await PDFDocument.create()
    const page = pdfDoc.addPage([595, 842]) // A4 size
    const font = await pdfDoc.embedFont(StandardFonts.Helvetica)
    const boldFont = await pdfDoc.embedFont(StandardFonts.HelveticaBold)

    let y = 750

    // Header
    page.drawText('Provability-Fabric Invoice', {
      x: 50,
      y,
      size: 24,
      font: boldFont,
      color: rgb(0, 0, 0)
    })
    y -= 40

    // Tenant info
    page.drawText(`Tenant: ${tenant.name}`, {
      x: 50,
      y,
      size: 12,
      font,
      color: rgb(0, 0, 0)
    })
    y -= 20

    page.drawText(`Period: ${format(invoice.periodStart, 'MMMM yyyy')}`, {
      x: 50,
      y,
      size: 12,
      font,
      color: rgb(0, 0, 0)
    })
    y -= 40

    // Usage details
    page.drawText('Usage Summary:', {
      x: 50,
      y,
      size: 14,
      font: boldFont,
      color: rgb(0, 0, 0)
    })
    y -= 25

    page.drawText(`Total CPU Time: ${(invoice.totalCpuMs / 1000 / 60).toFixed(2)} minutes`, {
      x: 50,
      y,
      size: 12,
      font,
      color: rgb(0, 0, 0)
    })
    y -= 20

    page.drawText(`Total Network: ${(invoice.totalNetBytes / (1024 * 1024)).toFixed(2)} MB`, {
      x: 50,
      y,
      size: 12,
      font,
      color: rgb(0, 0, 0)
    })
    y -= 20

    page.drawText(`Usage Events: ${invoice.usageEvents}`, {
      x: 50,
      y,
      size: 12,
      font,
      color: rgb(0, 0, 0)
    })
    y -= 40

    // Total
    page.drawText(`Total Amount: $${invoice.costUsd.toFixed(2)}`, {
      x: 50,
      y,
      size: 16,
      font: boldFont,
      color: rgb(0, 0, 0)
    })

    return Buffer.from(await pdfDoc.save())
  }

  /**
   * Get invoice data for CSV export
   */
  async getInvoiceCSV(tenantId: string, period: string): Promise<string> {
    const [year, month] = period.split('-').map(Number)
    const invoice = await this.generateMonthlyInvoice(tenantId, year, month)
    
    const tenant = await prisma.tenant.findUnique({
      where: { id: tenantId }
    })

    if (!tenant) {
      throw new Error('Tenant not found')
    }

    const csv = [
      'Tenant,Period,CPU Minutes,Network MB,Usage Events,Cost USD',
      `${tenant.name},${period},${(invoice.totalCpuMs / 1000 / 60).toFixed(2)},${(invoice.totalNetBytes / (1024 * 1024)).toFixed(2)},${invoice.usageEvents},${invoice.costUsd.toFixed(2)}`
    ].join('\n')

    return csv
  }
}

// Express middleware for billing endpoints
export const billingMiddleware = (billingService: BillingService) => {
  return {
    // Record usage event
    recordUsage: async (req: Request, res: Response) => {
      try {
        const { tenantId, cpuMs, netBytes, ts } = req.body
        
        if (!tenantId || typeof cpuMs !== 'number' || typeof netBytes !== 'number') {
          return res.status(400).json({ error: 'Missing required fields' })
        }

        await billingService.recordUsageEvent({
          tenantId,
          cpuMs,
          netBytes,
          ts: ts ? new Date(ts) : undefined
        })

        res.status(201).json({ message: 'Usage event recorded' })
      } catch (error) {
        console.error('Error recording usage:', error)
        res.status(500).json({ error: 'Failed to record usage event' })
      }
    },

    // Get invoice PDF
    getInvoicePDF: async (req: Request, res: Response) => {
      try {
        const { tenantId } = req.params
        const { period } = req.query

        if (!period || typeof period !== 'string') {
          return res.status(400).json({ error: 'Period parameter required' })
        }

        const pdfBuffer = await billingService.generatePDFInvoice(tenantId, period)
        
        res.setHeader('Content-Type', 'application/pdf')
        res.setHeader('Content-Disposition', `attachment; filename="invoice-${period}.pdf"`)
        res.send(pdfBuffer)
      } catch (error) {
        console.error('Error generating PDF:', error)
        res.status(500).json({ error: 'Failed to generate invoice PDF' })
      }
    },

    // Get invoice CSV
    getInvoiceCSV: async (req: Request, res: Response) => {
      try {
        const { tenantId } = req.params
        const { period } = req.query

        if (!period || typeof period !== 'string') {
          return res.status(400).json({ error: 'Period parameter required' })
        }

        const csv = await billingService.getInvoiceCSV(tenantId, period)
        
        res.setHeader('Content-Type', 'text/csv')
        res.setHeader('Content-Disposition', `attachment; filename="invoice-${period}.csv"`)
        res.send(csv)
      } catch (error) {
        console.error('Error generating CSV:', error)
        res.status(500).json({ error: 'Failed to generate invoice CSV' })
      }
    }
  }
}