// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors
//
// LOCAL DEMO ONLY — not a production server.
// Prefer `npm run dev` / compose ledger (PROFILE=dev). See docs/dev/local-workflows.md.

import express from 'express'
import cors from 'cors'
import compression from 'compression'
import jwt from 'jsonwebtoken'
import bcrypt from 'bcryptjs'
import { wsServer } from './websocket-server.js'

if (process.env.NODE_ENV === 'production') {
  console.error(
    'minimal-server.js is a local demo harness and refuses NODE_ENV=production. ' +
      'Use the full ledger (`npm run dev` / `npm run dev:production`) or compose.'
  )
  process.exit(1)
}

const app = express()
const port = process.env.PORT || 8080
// Demo JWT signing material — never a real secret. Override locally if needed.
const JWT_SECRET = process.env.JWT_SECRET || 'DEMO-ONLY-not-a-real-secret'

// In-memory demo users. Password for both accounts is the literal string "password"
// (well-known bcrypt fixture). Do not treat as production credentials.
const DEMO_PASSWORD_HASH =
  '$2a$10$92IXUNpkjO0rOQ5byMi.Ye4oKoEa3Ro9llC/.og/at2.uheWG/igi'
const users = new Map()
users.set('admin@provability-fabric.org', {
  id: 'admin-001',
  email: 'admin@provability-fabric.org',
  passwordHash: DEMO_PASSWORD_HASH,
  role: 'admin',
  name: 'System Administrator',
  createdAt: new Date('2025-01-01'),
})
users.set('developer@provability-fabric.org', {
  id: 'dev-001',
  email: 'developer@provability-fabric.org',
  passwordHash: DEMO_PASSWORD_HASH,
  role: 'developer',
  name: 'Developer User',
  createdAt: new Date('2025-01-15'),
})

// Security middleware
app.use((req, res, next) => {
  // Security headers
  res.setHeader('X-Content-Type-Options', 'nosniff')
  res.setHeader('X-Frame-Options', 'DENY')
  res.setHeader('X-XSS-Protection', '1; mode=block')
  res.setHeader('Referrer-Policy', 'strict-origin-when-cross-origin')
  res.setHeader('Content-Security-Policy', "default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline';")
  
  // Rate limiting headers
  res.setHeader('X-RateLimit-Limit', '1000')
  res.setHeader('X-RateLimit-Remaining', '999')
  res.setHeader('X-RateLimit-Reset', Date.now() + 3600000)
  
  next()
})

// Performance middleware
app.use(compression())

// CORS middleware with security restrictions
app.use(cors({
  origin: process.env.NODE_ENV === 'production' 
    ? ['https://localhost:3000', 'https://localhost:9000'] 
    : ['http://localhost:3000', 'http://localhost:9000', 'http://127.0.0.1:8002'],
  credentials: true,
  methods: ['GET', 'POST', 'PUT', 'DELETE'],
  allowedHeaders: ['Content-Type', 'Authorization']
}))

app.use(express.json({ limit: '10mb' }))
app.use(express.urlencoded({ extended: true, limit: '10mb' }))

// Simple in-memory cache
const cache = new Map()
const CACHE_TTL = 5 * 60 * 1000 // 5 minutes

// Cache middleware for GET requests
const cacheMiddleware = (req, res, next) => {
  if (req.method !== 'GET') return next()
  
  const key = `${req.method}:${req.url}`
  const cached = cache.get(key)
  
  if (cached && Date.now() - cached.timestamp < CACHE_TTL) {
    console.log(`[CACHE HIT] ${key}`)
    res.setHeader('X-Cache', 'HIT')
    return res.json(cached.data)
  }
  
  // Override res.json to cache the response
  const originalJson = res.json
  res.json = function(data) {
    cache.set(key, { data, timestamp: Date.now() })
    res.setHeader('X-Cache', 'MISS')
    return originalJson.call(this, data)
  }
  
  next()
}

app.use(cacheMiddleware)

// Request logging middleware
app.use((req, res, next) => {
  const timestamp = new Date().toISOString()
  console.log(`[${timestamp}] ${req.method} ${req.url} - ${req.ip}`)
  next()
})

// Authentication middleware
const authenticateToken = (req, res, next) => {
  const authHeader = req.headers['authorization']
  const token = authHeader && authHeader.split(' ')[1]

  if (!token) {
    return res.status(401).json({ error: 'Access token required' })
  }

  jwt.verify(token, JWT_SECRET, (err, user) => {
    if (err) {
      return res.status(403).json({ error: 'Invalid or expired token' })
    }
    req.user = user
    next()
  })
}

// Root endpoint
app.get('/', (req, res) => {
  res.json({
    message: 'Provability-Fabric Ledger (local demo harness)',
    demo: true,
    warning: 'Non-production. Demo accounts use the literal password "password".',
    version: '1.0.0-demo',
    timestamp: new Date().toISOString(),
    features: ['REST API', 'GraphQL', 'WebSocket Real-time', 'Authentication'],
    endpoints: {
      health: '/health',
      status: '/api/status',
      auth: {
        login: 'POST /auth/login',
        register: 'POST /auth/register',
        profile: 'GET /auth/profile',
      },
      graphql: '/graphql',
      websocket: 'ws://localhost:8081',
      capsules: '/tenant/:tid/capsules',
      quotes: '/tenant/:tid/quote/:hash',
    },
  })
})

// Authentication endpoints
app.post('/auth/login', async (req, res) => {
  try {
    const { email, password } = req.body
    
    if (!email || !password) {
      return res.status(400).json({ error: 'Email and password required' })
    }

    const user = users.get(email)
    if (!user) {
      return res.status(401).json({ error: 'Invalid credentials' })
    }

    const isValidPassword = await bcrypt.compare(password, user.passwordHash)
    if (!isValidPassword) {
      return res.status(401).json({ error: 'Invalid credentials' })
    }

    const token = jwt.sign(
      { 
        userId: user.id, 
        email: user.email, 
        role: user.role 
      },
      JWT_SECRET,
      { expiresIn: '24h' }
    )

    res.json({
      token,
      user: {
        id: user.id,
        email: user.email,
        name: user.name,
        role: user.role
      },
      websocketUrl: `ws://localhost:8081?token=${token}`
    })

    // Notify WebSocket server of login
    wsServer.notifySystemAlert('info', `User ${user.name} logged in`)
    
  } catch (error) {
    res.status(500).json({ error: 'Login failed' })
  }
})

app.post('/auth/register', async (req, res) => {
  try {
    const { email, password, name } = req.body
    
    if (!email || !password || !name) {
      return res.status(400).json({ error: 'Email, password, and name required' })
    }

    if (users.has(email)) {
      return res.status(409).json({ error: 'User already exists' })
    }

    const passwordHash = await bcrypt.hash(password, 10)
    const userId = `user-${Date.now()}`
    
    const newUser = {
      id: userId,
      email,
      passwordHash,
      name,
      role: 'user',
      createdAt: new Date()
    }
    
    users.set(email, newUser)

    const token = jwt.sign(
      { 
        userId: newUser.id, 
        email: newUser.email, 
        role: newUser.role 
      },
      JWT_SECRET,
      { expiresIn: '24h' }
    )

    res.status(201).json({
      token,
      user: {
        id: newUser.id,
        email: newUser.email,
        name: newUser.name,
        role: newUser.role
      },
      websocketUrl: `ws://localhost:8081?token=${token}`
    })

    // Notify WebSocket server of new registration
    wsServer.notifySystemAlert('info', `New user registered: ${newUser.name}`)
    
  } catch (error) {
    res.status(500).json({ error: 'Registration failed' })
  }
})

app.get('/auth/profile', authenticateToken, (req, res) => {
  const userEmail = req.user.email
  const user = users.get(userEmail)
  
  if (!user) {
    return res.status(404).json({ error: 'User not found' })
  }

  res.json({
    id: user.id,
    email: user.email,
    name: user.name,
    role: user.role,
    createdAt: user.createdAt
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

app.post('/install', authenticateToken, (req, res) => {
  const { tenantId, packageId, version } = req.body;
  
  // Mock installation response
  const installId = `install-${Date.now()}`;
  const response = {
    installId,
    status: 'initiated',
    message: `Installation of ${packageId} v${version} initiated for tenant ${tenantId}`,
    timestamp: new Date().toISOString()
  };

  res.json(response);

  // Send real-time notification
  wsServer.broadcastToRoom('marketplace', {
    type: 'package_installation',
    installId,
    packageId,
    version,
    tenantId,
    userId: req.user.userId,
    status: 'initiated',
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
  console.log(`[demo] minimal-server listening on port ${port}`)
  console.log(`[demo] Health: http://localhost:${port}/health`)
  console.log(`[demo] Auth login: http://localhost:${port}/auth/login`)
  console.log(
    '[demo] Seeded users use the literal password "password" — not production credentials.'
  )

  wsServer.initialize()
  console.log('[demo] WebSocket server initialized')
}) 