// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import type { PrismaClient } from '@prisma/client'
import type { GraphQLContext, ServerDeps, UserContext } from './types.js'

export function createResolvers({ prisma }: ServerDeps) {
  return {
    Query: {
      tenant: async (_: unknown, __: unknown, { user }: GraphQLContext) => {
        return prisma.tenant.findUnique({ where: { id: user.tid } })
      },
      capsules: async (_: unknown, __: unknown, { user }: GraphQLContext) => {
        return prisma.capsule.findMany({
          where: { tenantId: user.tid },
          include: { tenant: true, premiumQuotes: true },
        })
      },
      capsule: async (_: unknown, { hash }: { hash: string }, { user }: GraphQLContext) => {
        return prisma.capsule.findFirst({
          where: { hash, tenantId: user.tid },
          include: { tenant: true, premiumQuotes: true },
        })
      },
      premiumQuotes: async (_: unknown, __: unknown, { user }: GraphQLContext) => {
        return prisma.premiumQuote.findMany({
          where: { tenantId: user.tid },
          include: { tenant: true },
        })
      },
      premiumQuote: async (
        _: unknown,
        { capsuleHash }: { capsuleHash: string },
        { user }: GraphQLContext
      ) => {
        return prisma.premiumQuote.findFirst({
          where: { capsuleHash, tenantId: user.tid },
          include: { tenant: true },
        })
      },
    },
    Mutation: {
      createCapsule: async (
        _: unknown,
        args: { hash: string; specSig: string; riskScore: number; reason?: string },
        { user }: GraphQLContext
      ) => {
        return prisma.capsule.create({
          data: {
            hash: args.hash,
            specSig: args.specSig,
            riskScore: args.riskScore,
            reason: args.reason,
            tenantId: user.tid,
          },
          include: { tenant: true, premiumQuotes: true },
        })
      },
      publish: async (
        _: unknown,
        args: { hash: string; specSig: string; risk: number; reason?: string },
        { user }: GraphQLContext
      ) => {
        return prisma.capsule.create({
          data: {
            hash: args.hash,
            specSig: args.specSig,
            riskScore: args.risk,
            reason: args.reason,
            tenantId: user.tid,
          },
          include: { tenant: true, premiumQuotes: true },
        })
      },
      updateCapsule: async (
        _: unknown,
        args: { hash: string; riskScore: number; reason?: string },
        { user }: GraphQLContext
      ) => {
        const existing = await prisma.capsule.findFirst({
          where: { hash: args.hash, tenantId: user.tid },
        })
        if (!existing) {
          throw new Error(`Capsule not found for tenant ${user.tid}`)
        }
        return prisma.capsule.update({
          where: { hash: args.hash },
          data: { riskScore: args.riskScore, reason: args.reason },
          include: { tenant: true, premiumQuotes: true },
        })
      },
      createPremiumQuote: async (
        _: unknown,
        args: { capsuleHash: string; riskScore: number; annualUsd: number },
        { user }: GraphQLContext
      ) => {
        return prisma.premiumQuote.create({
          data: {
            capsuleHash: args.capsuleHash,
            riskScore: args.riskScore,
            annualUsd: args.annualUsd,
            tenantId: user.tid,
          },
          include: { tenant: true },
        })
      },
    },
  }
}

/** Exported for unit tests — builds the tenant-scoped update where clause. */
export function buildUpdateCapsuleWhere(hash: string, user: UserContext) {
  return { hash, tenantId: user.tid }
}

export type ResolversPrisma = PrismaClient
