// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

/**
 * Provability-Fabric Edge API Worker
 * 
 * Provides read-only endpoints for /quote and /capsule with edge caching.
 * Caches responses for 5 seconds to reduce load on the ledger service.
 */

// Cache TTL in seconds
const CACHE_TTL = parseInt(env.CACHE_TTL || "300");

// Ledger service URL
const LEDGER_URL = env.LEDGER_URL || "https://ledger.provability-fabric.org";

/**
 * Main request handler
 */
addEventListener('fetch', event => {
  event.respondWith(handleRequest(event.request));
});

async function handleRequest(request) {
  const url = new URL(request.url);
  const path = url.pathname;
  
  // CORS headers
  const corsHeaders = {
    'Access-Control-Allow-Origin': '*',
    'Access-Control-Allow-Methods': 'GET, OPTIONS',
    'Access-Control-Allow-Headers': 'Content-Type, Authorization',
    'Access-Control-Max-Age': '86400',
  };
  
  // Handle preflight requests
  if (request.method === 'OPTIONS') {
    return new Response(null, {
      status: 200,
      headers: corsHeaders
    });
  }
  
  // Only allow GET requests
  if (request.method !== 'GET') {
    return new Response('Method not allowed', {
      status: 405,
      headers: corsHeaders
    });
  }
  
  try {
    let response;
    
    // Route requests based on path
    if (path.startsWith('/quote')) {
      response = await handleQuoteRequest(url);
    } else if (path.startsWith('/capsule')) {
      response = await handleCapsuleRequest(url);
    } else if (path === '/health') {
      response = new Response(JSON.stringify({
        status: 'healthy',
        region: request.cf?.colo || 'unknown',
        timestamp: new Date().toISOString()
      }), {
        status: 200,
        headers: {
          'Content-Type': 'application/json',
          ...corsHeaders
        }
      });
    } else {
      return new Response('Not found', {
        status: 404,
        headers: corsHeaders
      });
    }
    
    // Add CORS headers to response
    Object.entries(corsHeaders).forEach(([key, value]) => {
      response.headers.set(key, value);
    });
    
    return response;
    
  } catch (error) {
    console.error('Worker error:', error);
    return new Response('Internal server error', {
      status: 500,
      headers: corsHeaders
    });
  }
}

/**
 * Handle quote requests
 */
async function handleQuoteRequest(url) {
  const cacheKey = `quote:${url.search}`;
  
  // Try to get from cache first
  const cached = await CACHE.get(cacheKey);
  if (cached) {
    return new Response(cached, {
      status: 200,
      headers: {
        'Content-Type': 'application/json',
        'X-Cache': 'HIT',
        'X-Cache-Region': request.cf?.colo || 'unknown'
      }
    });
  }
  
  // Fetch from ledger service
  const ledgerUrl = `${LEDGER_URL}/api/quote${url.search}`;
  const response = await fetch(ledgerUrl, {
    headers: {
      'User-Agent': 'Provability-Fabric-Edge/1.0'
    }
  });
  
  if (!response.ok) {
    return new Response('Quote service unavailable', {
      status: response.status
    });
  }
  
  const data = await response.text();
  
  // Cache the response
  await CACHE.put(cacheKey, data, {
    expirationTtl: CACHE_TTL
  });
  
  return new Response(data, {
    status: 200,
    headers: {
      'Content-Type': 'application/json',
      'X-Cache': 'MISS',
      'X-Cache-Region': request.cf?.colo || 'unknown'
    }
  });
}

/**
 * Handle capsule requests
 */
async function handleCapsuleRequest(url) {
  const cacheKey = `capsule:${url.pathname}${url.search}`;
  
  // Try to get from cache first
  const cached = await CACHE.get(cacheKey);
  if (cached) {
    return new Response(cached, {
      status: 200,
      headers: {
        'Content-Type': 'application/json',
        'X-Cache': 'HIT',
        'X-Cache-Region': request.cf?.colo || 'unknown'
      }
    });
  }
  
  // Fetch from ledger service
  const ledgerUrl = `${LEDGER_URL}/api${url.pathname}${url.search}`;
  const response = await fetch(ledgerUrl, {
    headers: {
      'User-Agent': 'Provability-Fabric-Edge/1.0'
    }
  });
  
  if (!response.ok) {
    return new Response('Capsule service unavailable', {
      status: response.status
    });
  }
  
  const data = await response.text();
  
  // Cache the response
  await CACHE.put(cacheKey, data, {
    expirationTtl: CACHE_TTL
  });
  
  return new Response(data, {
    status: 200,
    headers: {
      'Content-Type': 'application/json',
      'X-Cache': 'MISS',
      'X-Cache-Region': request.cf?.colo || 'unknown'
    }
  });
}

/**
 * Webhook handler for cache invalidation
 */
addEventListener('fetch', event => {
  if (event.request.url.includes('/webhook/cache-invalidate')) {
    event.respondWith(handleCacheInvalidation(event.request));
  }
});

async function handleCacheInvalidation(request) {
  if (request.method !== 'POST') {
    return new Response('Method not allowed', { status: 405 });
  }
  
  try {
    const body = await request.json();
    const { keys } = body;
    
    if (!Array.isArray(keys)) {
      return new Response('Invalid request body', { status: 400 });
    }
    
    // Invalidate specified cache keys
    const results = await Promise.allSettled(
      keys.map(key => CACHE.delete(key))
    );
    
    const successCount = results.filter(r => r.status === 'fulfilled').length;
    
    return new Response(JSON.stringify({
      success: true,
      invalidated: successCount,
      total: keys.length
    }), {
      status: 200,
      headers: { 'Content-Type': 'application/json' }
    });
    
  } catch (error) {
    console.error('Cache invalidation error:', error);
    return new Response('Internal server error', { status: 500 });
  }
}