// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import express from 'express'
import cors from 'cors'

const app = express()
const port = process.env.PORT || 8080

// CORS middleware
app.use(cors())
app.use(express.json())

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

// GraphQL endpoint (simple)
app.post('/graphql', (req, res) => {
  res.json({
    data: {
      hello: 'Hello from Provability-Fabric Ledger!',
      health: 'healthy'
    }
  })
})

app.listen(port, () => {
  console.log(`🚀 Provability-Fabric Ledger running on port ${port}`)
  console.log(`📊 Health check: http://localhost:${port}/health`)
  console.log(`📡 API Status: http://localhost:${port}/api/status`)
  console.log(`🔍 GraphQL: http://localhost:${port}/graphql`)
}) 