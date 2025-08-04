// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import express from 'express'
import { ApolloServer } from '@apollo/server'
import { expressMiddleware } from '@apollo/server/express4'
import { json } from 'body-parser'
import cors from 'cors'

const app = express()
const port = process.env.PORT || 8080

// Simple GraphQL schema
const typeDefs = `#graphql
  type Query {
    hello: String!
    health: String!
  }

  type Mutation {
    echo(message: String!): String!
  }
`

// Simple resolvers
const resolvers = {
  Query: {
    hello: () => 'Hello from Provability-Fabric Ledger!',
    health: () => 'healthy'
  },
  Mutation: {
    echo: (_: any, { message }: { message: string }) => `Echo: ${message}`
  }
}

async function startServer() {
  // CORS middleware
  app.use(cors())
  app.use(json())

  // Health check endpoint
  app.get('/health', (req, res) => {
    res.json({ status: 'healthy', timestamp: new Date().toISOString() })
  })

  // Simple REST endpoint
  app.get('/api/status', (req, res) => {
    res.json({ 
      service: 'Provability-Fabric Ledger',
      status: 'running',
      timestamp: new Date().toISOString()
    })
  })

  // Apollo Server setup
  const server = new ApolloServer({
    typeDefs,
    resolvers,
  })

  await server.start()

  app.use('/graphql', 
    expressMiddleware(server, {
      context: async ({ req }) => ({ token: req.headers.token })
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