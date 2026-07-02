// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

/** Canonical GraphQL schema for all ledger profiles. */
export const typeDefs = `#graphql
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
    publish(hash: String!, specSig: String!, risk: Float!, reason: String): Capsule!
    updateCapsule(hash: String!, riskScore: Float!, reason: String): Capsule!
    createPremiumQuote(capsuleHash: String!, riskScore: Float!, annualUsd: Float!): PremiumQuote!
  }
`
