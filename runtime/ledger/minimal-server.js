// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import express from 'express'
import cors from 'cors'

const app = express()
const port = process.env.PORT || 8080

// CORS middleware
app.use(cors())
app.use(express.json())

// Root endpoint
app.get('/', (req, res) => {
  res.json({ 
    message: 'Welcome to Provability-Fabric Ledger API',
    version: '1.0.0',
    timestamp: new Date().toISOString(),
    endpoints: {
      health: '/health',
      status: '/api/status',
      graphql: '/graphql',
      capsules: '/tenant/:tid/capsules',
      quotes: '/tenant/:tid/quote/:hash'
    }
  })
})

// Health check endpoint
app.get('/health', (req, res) => {
  res.json({ 
    status: 'healthy', 
    timestamp: new Date().toISOString(),
    service: 'Provability-Fabric Ledger'
  })
})

// API status endpoint
app.get('/api/status', (req, res) => {
  res.json({ 
    service: 'Provability-Fabric Ledger',
    status: 'running',
    timestamp: new Date().toISOString(),
    version: '1.0.0'
  })
})

// Simple GraphQL endpoint
app.post('/graphql', (req, res) => {
  res.json({
    data: {
      hello: 'Hello from Provability-Fabric Ledger!',
      health: 'healthy',
      message: 'GraphQL endpoint is working'
    }
  })
})

// Mock tenant endpoints
app.get('/tenant/:tid/capsules', (req, res) => {
  res.json({
    capsules: [
      {
        id: 'mock-capsule-1',
        hash: 'abc123',
        specSig: 'mock-signature',
        riskScore: 0.5,
        tenantId: req.params.tid,
        createdAt: new Date().toISOString()
      }
    ]
  })
})

app.get('/tenant/:tid/quote/:hash', (req, res) => {
  res.json({
    risk: 0.5,
    premium: 500.0,
    quote_id: 'mock-quote-1',
    created_at: new Date().toISOString()
  })
})

// Marketplace API endpoints for the React UI
app.get('/packages', (req, res) => {
  const { type, author } = req.query;
  
  // Mock marketplace packages
  const packages = [
    {
      id: 'marabou-adapter',
      name: 'Marabou Adapter',
      version: '1.2.0',
      description: 'Neural network verification adapter for Marabou',
      author: 'Stanford',
      type: 'adapter',
      downloads: 1250,
      rating: 4.8,
      updated: '2025-08-01T10:00:00Z',
      created: '2025-01-15T08:00:00Z',
      compatibility: { 'fabric-version': '1.0.0' }
    },
    {
      id: 'dryvr-adapter',
      name: 'DryVR Adapter',
      version: '2.1.0',
      description: 'Hybrid system verification adapter',
      author: 'MIT',
      type: 'adapter',
      downloads: 890,
      rating: 4.6,
      updated: '2025-07-28T14:30:00Z',
      created: '2025-02-10T09:00:00Z',
      compatibility: { 'fabric-version': '1.0.0' }
    },
    {
      id: 'art-spec',
      name: 'ART Specification',
      version: '1.0.0',
      description: 'Automated reasoning toolkit specification',
      author: 'Provability-Fabric',
      type: 'spec',
      downloads: 2100,
      rating: 4.9,
      updated: '2025-08-03T16:45:00Z',
      created: '2025-03-01T11:00:00Z',
      compatibility: { 'fabric-version': '1.0.0' }
    },
    {
      id: 'privacy-proofpack',
      name: 'Privacy Proof Pack',
      version: '1.1.0',
      description: 'Differential privacy verification proofs',
      author: 'Harvard',
      type: 'proofpack',
      downloads: 567,
      rating: 4.7,
      updated: '2025-07-25T12:15:00Z',
      created: '2025-04-05T13:00:00Z',
      compatibility: { 'fabric-version': '1.0.0' }
    }
  ];

  // Apply filters
  let filteredPackages = packages;
  if (type) {
    filteredPackages = filteredPackages.filter(pkg => pkg.type === type);
  }
  if (author) {
    filteredPackages = filteredPackages.filter(pkg => 
      pkg.author.toLowerCase().includes(author.toLowerCase())
    );
  }

  res.json({
    packages: filteredPackages,
    total: filteredPackages.length
  });
});

app.get('/packages/:id', (req, res) => {
  const { id } = req.params;
  
  // Mock package details
  const packageDetails = {
    id: id,
    name: id.split('-').map(word => word.charAt(0).toUpperCase() + word.slice(1)).join(' '),
    version: '1.2.0',
    description: `Detailed description for ${id}. This is a comprehensive package that provides advanced functionality for the Provability-Fabric ecosystem.`,
    author: 'Stanford',
    type: 'adapter',
    downloads: 1250,
    rating: 4.8,
    updated: '2025-08-01T10:00:00Z',
    created: '2025-01-15T08:00:00Z',
    compatibility: { 'fabric-version': '1.0.0' },
    readme: `# ${id}

This is a comprehensive package for the Provability-Fabric ecosystem.

## Features

- Advanced verification capabilities
- High performance optimization
- Comprehensive testing suite

## Installation

\`\`\`bash
pf install ${id}
\`\`\`

## Usage

\`\`\`typescript
import { ${id.split('-')[0]} } from '@provability-fabric/${id}';
\`\`\`

## Documentation

See the full documentation at [docs.provability-fabric.org/${id}](https://docs.provability-fabric.org/${id})
`,
    dependencies: ['@provability-fabric/core', '@provability-fabric/types'],
    repository: `https://github.com/provability-fabric/${id}`,
    license: 'Apache-2.0'
  };

  res.json(packageDetails);
});

app.get('/search', (req, res) => {
  const { q } = req.query;
  
  // Mock search results
  const searchResults = [
    {
      id: 'marabou-adapter',
      name: 'Marabou Adapter',
      version: '1.2.0',
      description: 'Neural network verification adapter for Marabou',
      author: 'Stanford',
      type: 'adapter',
      downloads: 1250,
      rating: 4.8,
      updated: '2025-08-01T10:00:00Z',
      created: '2025-01-15T08:00:00Z',
      compatibility: { 'fabric-version': '1.0.0' }
    }
  ];

  res.json({
    packages: searchResults,
    total: searchResults.length,
    query: q
  });
});

app.post('/install', (req, res) => {
  const { tenantId, packageId, version } = req.body;
  
  // Mock installation response
  res.json({
    installId: `install-${Date.now()}`,
    status: 'initiated',
    message: `Installation of ${packageId} v${version} initiated for tenant ${tenantId}`,
    timestamp: new Date().toISOString()
  });
});

app.get('/install/:installId', (req, res) => {
  const { installId } = req.params;
  
  // Mock installation status
  res.json({
    installId,
    status: 'completed',
    message: 'Installation completed successfully',
    timestamp: new Date().toISOString()
  });
});

app.listen(port, () => {
  console.log(`🚀 Provability-Fabric Ledger running on port ${port}`)
  console.log(`📊 Health check: http://localhost:${port}/health`)
  console.log(`🔍 GraphQL: http://localhost:${port}/graphql`)
  console.log(`📡 API Status: http://localhost:${port}/api/status`)
  console.log(`👤 Mock tenant: http://localhost:${port}/tenant/dev-tenant/capsules`)
}) 