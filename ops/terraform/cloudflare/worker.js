// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

/**
 * Provability-Fabric Edge API Worker
 * 
 * Provides edge-first validation for PF-Sig and receipt schemas.
 * Deployed in shadow mode for 48 hours before enforcement.
 */

// Configuration
const CACHE_TTL = parseInt(env.CACHE_TTL || "300");
const LEDGER_URL = env.LEDGER_URL || "https://ledger.provability-fabric.org";
const SHADOW_MODE = env.SHADOW_MODE === "true"; // Shadow mode for 48 hours
const ENFORCEMENT_START = env.ENFORCEMENT_START || "2025-01-03T00:00:00Z"; // 48h after deployment

// Metrics tracking
let metrics = {
    requests_total: 0,
    requests_blocked: 0,
    requests_allowed: 0,
    validation_errors: 0,
    cache_hits: 0,
    cache_misses: 0,
    shadow_mode_blocks: 0,
    enforcement_mode_blocks: 0
};

// PF-Sig validation patterns
const PF_SIG_PATTERN = /^pf-sig-v1:[a-f0-9]{64}:[a-f0-9]{64}:[a-f0-9]{64}$/;
const RECEIPT_PATTERN = /^receipt-v1:[a-f0-9]{64}:[a-f0-9]{64}$/;

// Receipt schema validation
const RECEIPT_SCHEMA = {
    required: ['id', 'tenant_id', 'action', 'timestamp', 'signature'],
    properties: {
        id: { type: 'string', pattern: '^[a-f0-9]{64}$' },
        tenant_id: { type: 'string', pattern: '^[a-f0-9]{64}$' },
        action: { type: 'string', minLength: 1, maxLength: 100 },
        timestamp: { type: 'string', format: 'date-time' },
        signature: { type: 'string', pattern: '^[a-f0-9]{128}$' }
    }
};

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
        'Access-Control-Allow-Methods': 'GET, POST, OPTIONS',
        'Access-Control-Allow-Headers': 'Content-Type, Authorization, PF-Sig, PF-Receipt',
        'Access-Control-Max-Age': '86400',
    };
    
    // Handle preflight requests
    if (request.method === 'OPTIONS') {
        return new Response(null, {
            status: 200,
            headers: corsHeaders
        });
    }
    
    // Update metrics
    metrics.requests_total++;
    
    try {
        let response;
        
        // Route requests based on path
        if (path.startsWith('/quote')) {
            response = await handleQuoteRequest(url, request);
        } else if (path.startsWith('/capsule')) {
            response = await handleCapsuleRequest(url, request);
        } else if (path === '/health') {
            response = new Response(JSON.stringify({
                status: 'healthy',
                region: request.cf?.colo || 'unknown',
                timestamp: new Date().toISOString(),
                shadow_mode: SHADOW_MODE,
                enforcement_start: ENFORCEMENT_START,
                metrics: metrics
            }), {
                status: 200,
                headers: {
                    'Content-Type': 'application/json',
                    ...corsHeaders
                }
            });
        } else if (path === '/metrics') {
            response = new Response(JSON.stringify(metrics), {
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
        metrics.validation_errors++;
        
        return new Response('Internal server error', {
            status: 500,
            headers: corsHeaders
        });
    }
}

/**
 * Validate PF-Sig header
 */
function validatePFSig(pfSig) {
    if (!pfSig) {
        return { valid: false, reason: 'PF-Sig header missing' };
    }
    
    if (!PF_SIG_PATTERN.test(pfSig)) {
        return { valid: false, reason: 'PF-Sig format invalid' };
    }
    
    // Parse components: pf-sig-v1:policy_hash:attestation_hash:signature
    const parts = pfSig.split(':');
    if (parts.length !== 4) {
        return { valid: false, reason: 'PF-Sig has incorrect number of components' };
    }
    
    const [version, policyHash, attestationHash, signature] = parts;
    
    if (version !== 'pf-sig-v1') {
        return { valid: false, reason: 'PF-Sig version not supported' };
    }
    
    if (policyHash.length !== 64 || attestationHash.length !== 64 || signature.length !== 64) {
        return { valid: false, reason: 'PF-Sig component lengths invalid' };
    }
    
    return { valid: true, policyHash, attestationHash, signature };
}

/**
 * Validate receipt schema
 */
function validateReceipt(receipt) {
    if (!receipt) {
        return { valid: false, reason: 'Receipt missing' };
    }
    
    try {
        const receiptData = typeof receipt === 'string' ? JSON.parse(receipt) : receipt;
        
        // Check required fields
        for (const field of RECEIPT_SCHEMA.required) {
            if (!receiptData.hasOwnProperty(field)) {
                return { valid: false, reason: `Required field missing: ${field}` };
            }
        }
        
        // Validate field types and patterns
        for (const [field, schema] of Object.entries(RECEIPT_SCHEMA.properties)) {
            const value = receiptData[field];
            
            if (schema.type && typeof value !== schema.type) {
                return { valid: false, reason: `Field ${field} has wrong type` };
            }
            
            if (schema.pattern && !new RegExp(schema.pattern).test(value)) {
                return { valid: false, reason: `Field ${field} format invalid` };
            }
            
            if (schema.minLength && value.length < schema.minLength) {
                return { valid: false, reason: `Field ${field} too short` };
            }
            
            if (schema.maxLength && value.length > schema.maxLength) {
                return { valid: false, reason: `Field ${field} too long` };
            }
            
            if (schema.format === 'date-time') {
                const date = new Date(value);
                if (isNaN(date.getTime())) {
                    return { valid: false, reason: `Field ${field} not a valid date` };
                }
            }
        }
        
        return { valid: true, receipt: receiptData };
        
    } catch (error) {
        return { valid: false, reason: `Receipt parsing failed: ${error.message}` };
    }
}

/**
 * Handle quote requests with validation
 */
async function handleQuoteRequest(url, request) {
    const cacheKey = `quote:${url.search}`;
    
    // Check cache first
    const cached = await caches.default.match(request);
    if (cached) {
        metrics.cache_hits++;
        return cached;
    }
    
    // Validate request
    const validationResult = await validateRequest(request);
    
    if (!validationResult.valid) {
        // In shadow mode, log but don't block
        if (SHADOW_MODE) {
            metrics.shadow_mode_blocks++;
            console.log(`Shadow mode: Would block request: ${validationResult.reason}`);
        } else {
            metrics.enforcement_mode_blocks++;
            metrics.requests_blocked++;
            
            return new Response(JSON.stringify({
                error: 'Request validation failed',
                reason: validationResult.reason,
                blocked_at: new Date().toISOString()
            }), {
                status: 400,
                headers: {
                    'Content-Type': 'application/json',
                    'X-Edge-Blocked': 'true',
                    'X-Edge-Block-Reason': validationResult.reason
                }
            });
        }
    }
    
    // Forward to origin
    const originResponse = await fetch(`${LEDGER_URL}${url.pathname}${url.search}`, {
        method: request.method,
        headers: request.headers,
        body: request.method !== 'GET' ? request.body : undefined
    });
    
    // Cache successful responses
    if (originResponse.ok) {
        const response = new Response(originResponse.body, {
            status: originResponse.status,
            statusText: originResponse.statusText,
            headers: originResponse.headers
        });
        
        // Cache for TTL
        const cacheRequest = new Request(request.url);
        await caches.default.put(cacheRequest, response.clone());
        
        metrics.requests_allowed++;
        return response;
    }
    
    metrics.cache_misses++;
    return originResponse;
}

/**
 * Handle capsule requests with validation
 */
async function handleCapsuleRequest(url, request) {
    const cacheKey = `capsule:${url.search}`;
    
    // Check cache first
    const cached = await caches.default.match(request);
    if (cached) {
        metrics.cache_hits++;
        return cached;
    }
    
    // Validate request
    const validationResult = await validateRequest(request);
    
    if (!validationResult.valid) {
        // In shadow mode, log but don't block
        if (SHADOW_MODE) {
            metrics.shadow_mode_blocks++;
            console.log(`Shadow mode: Would block request: ${validationResult.reason}`);
        } else {
            metrics.enforcement_mode_blocks++;
            metrics.requests_blocked++;
            
            return new Response(JSON.stringify({
                error: 'Request validation failed',
                reason: validationResult.reason,
                blocked_at: new Date().toISOString()
            }), {
                status: 400,
                headers: {
                    'Content-Type': 'application/json',
                    'X-Edge-Blocked': 'true',
                    'X-Edge-Block-Reason': validationResult.reason
                }
            });
        }
    }
    
    // Forward to origin
    const originResponse = await fetch(`${LEDGER_URL}${url.pathname}${url.search}`, {
        method: request.method,
        headers: request.headers,
        body: request.method !== 'GET' ? request.body : undefined
    });
    
    // Cache successful responses
    if (originResponse.ok) {
        const response = new Response(originResponse.body, {
            status: originResponse.status,
            statusText: originResponse.statusText,
            headers: originResponse.headers
        });
        
        // Cache for TTL
        const cacheRequest = new Request(request.url);
        await caches.default.put(cacheRequest, response.clone());
        
        metrics.requests_allowed++;
        return response;
    }
    
    metrics.cache_misses++;
    return originResponse;
}

/**
 * Validate incoming request
 */
async function validateRequest(request) {
    // Check PF-Sig header
    const pfSig = request.headers.get('PF-Sig');
    const pfSigValidation = validatePFSig(pfSig);
    
    if (!pfSigValidation.valid) {
        return pfSigValidation;
    }
    
    // Check PF-Receipt header if present
    const pfReceipt = request.headers.get('PF-Receipt');
    if (pfReceipt) {
        const receiptValidation = validateReceipt(pfReceipt);
        if (!receiptValidation.valid) {
            return receiptValidation;
        }
    }
    
    // Additional validation rules can be added here
    // For example, rate limiting, IP allowlisting, etc.
    
    return { valid: true };
}

/**
 * Periodic metrics export (every 5 minutes)
 */
setInterval(() => {
    // Export metrics to external monitoring system
    // In production, this would send to Prometheus, DataDog, etc.
    console.log('Metrics export:', JSON.stringify(metrics));
    
    // Reset counters periodically
    metrics.requests_total = 0;
    metrics.requests_blocked = 0;
    metrics.requests_allowed = 0;
    metrics.validation_errors = 0;
    metrics.cache_hits = 0;
    metrics.cache_misses = 0;
    metrics.shadow_mode_blocks = 0;
    metrics.enforcement_mode_blocks = 0;
}, 5 * 60 * 1000);