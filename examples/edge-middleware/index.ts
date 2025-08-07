import { ProvabilityFabric } from '@provability-fabric/sdk';
import { NextRequest, NextResponse } from 'next/server';

// Initialize Provability Fabric client
const pf = new ProvabilityFabric({
  ledgerUrl: process.env.LEDGER_URL || 'https://ledger.provability-fabric.com',
  policyKernelUrl: process.env.POLICY_KERNEL_URL || 'https://kernel.provability-fabric.com',
});

interface RequestContext {
  tenant: string;
  userId: string;
  userCapabilities: string[];
  systemPrompt: string;
  policyHash: string;
}

export async function middleware(request: NextRequest) {
  try {
    // Extract context from request
    const context = extractContext(request);
    
    // Create plan for the request
    const plan = await createPlan(request, context);
    
    // Validate plan
    const validation = await pf.validatePlan(plan);
    if (!validation.valid) {
      console.error('Plan validation failed:', validation.errors);
      return NextResponse.json(
        { error: 'Request validation failed', details: validation.errors },
        { status: 400 }
      );
    }
    
    // Execute plan and get certificate
    const result = await pf.executePlan(plan);
    
    // Check certificate
    if (result.certificate.non_interference !== 'passed') {
      console.error('NI violation detected:', result.certificate);
      return NextResponse.json(
        { error: 'Security violation detected', certificate: result.certificate },
        { status: 403 }
      );
    }
    
    // Forward request with PF signature
    const response = await forwardRequest(request, result.certificate);
    
    // Add certificate to response headers
    response.headers.set('X-PF-Certificate', JSON.stringify(result.certificate));
    response.headers.set('X-PF-Plan-ID', plan.plan_id);
    response.headers.set('X-PF-NI-Status', result.certificate.non_interference);
    
    return response;
    
  } catch (error) {
    console.error('Middleware error:', error);
    return NextResponse.json(
      { error: 'Internal server error' },
      { status: 500 }
    );
  }
}

function extractContext(request: NextRequest): RequestContext {
  // Extract tenant from subdomain or header
  const hostname = request.nextUrl.hostname;
  const tenant = hostname.split('.')[0];
  
  // Extract user info from JWT or session
  const authHeader = request.headers.get('authorization');
  const userId = extractUserId(authHeader);
  const userCapabilities = getUserCapabilities(userId, tenant);
  
  // Get system prompt and policy
  const systemPrompt = getSystemPrompt(tenant);
  const policyHash = getPolicyHash(tenant);
  
  return {
    tenant,
    userId,
    userCapabilities,
    systemPrompt,
    policyHash,
  };
}

async function createPlan(request: NextRequest, context: RequestContext) {
  const body = await request.json();
  
  // Classify input channels
  const inputChannels = {
    system: {
      hash: hashContent(context.systemPrompt),
      policy_hash: context.policyHash,
    },
    user: {
      content_hash: hashContent(body.userInput),
      quoted: true, // Always quote user input
    },
    retrieved: await getRetrievedContent(body.retrievedIds, context.tenant),
    file: getFileContent(body.files),
  };
  
  // Create plan steps
  const steps = [
    {
      tool: 'openai_chat_completion',
      args: {
        model: body.model || 'gpt-4',
        messages: [
          { role: 'system', content: context.systemPrompt },
          { role: 'user', content: '{{user_input}}' }
        ],
        max_tokens: body.maxTokens || 1000,
        temperature: body.temperature || 0.7,
      },
      caps_required: ['openai_chat'],
      labels_in: ['tenant:' + context.tenant, 'pii:masked'],
      labels_out: ['tenant:' + context.tenant, 'pii:masked'],
    }
  ];
  
  return {
    plan_id: `plan_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
    tenant: context.tenant,
    subject: {
      id: context.userId,
      caps: context.userCapabilities,
    },
    input_channels: inputChannels,
    steps,
    constraints: {
      budget: 1.0,
      pii: false,
      dp_epsilon: 0.1,
      dp_delta: 1e-6,
      latency_max: 30.0,
    },
    system_prompt_hash: hashContent(context.systemPrompt),
    created_at: new Date().toISOString(),
    expires_at: new Date(Date.now() + 5 * 60 * 1000).toISOString(), // 5 minutes
  };
}

async function getRetrievedContent(retrievedIds: string[], tenant: string) {
  const retrieved = [];
  
  for (const id of retrievedIds || []) {
    // Get receipt for this content
    const receipt = await pf.getReceipt(id);
    
    if (receipt && receipt.tenant === tenant) {
      retrieved.push({
        receipt_id: receipt.receipt_id,
        content_hash: receipt.result_hash,
        quoted: true,
        labels: ['tenant:' + tenant, 'pii:masked'],
      });
    }
  }
  
  return retrieved;
}

function getFileContent(files: any[]) {
  return (files || []).map(file => ({
    sha256: file.sha256,
    media_type: file.mediaType,
    quoted: true,
  }));
}

async function forwardRequest(request: NextRequest, certificate: any) {
  // Create new request with PF signature
  const newRequest = new Request(request.url, {
    method: request.method,
    headers: {
      ...Object.fromEntries(request.headers.entries()),
      'X-PF-Signature': certificate.signature,
      'X-PF-Certificate-ID': certificate.certificate_id,
      'X-PF-NI-Status': certificate.non_interference,
    },
    body: request.body,
  });
  
  // Forward to OpenAI API
  const openaiUrl = 'https://api.openai.com/v1/chat/completions';
  const response = await fetch(openaiUrl, newRequest);
  
  return new NextResponse(response.body, {
    status: response.status,
    statusText: response.statusText,
    headers: response.headers,
  });
}

// Utility functions
function hashContent(content: string): string {
  // In production, use proper SHA-256 hashing
  return 'sha256:' + Buffer.from(content).toString('base64').substring(0, 64);
}

function extractUserId(authHeader: string | null): string {
  // In production, decode JWT and extract user ID
  return authHeader ? 'user_' + Math.random().toString(36).substr(2, 9) : 'anonymous';
}

function getUserCapabilities(userId: string, tenant: string): string[] {
  // In production, query user capabilities from database
  return ['openai_chat', 'data_retrieval'];
}

function getSystemPrompt(tenant: string): string {
  // In production, get tenant-specific system prompt
  return `You are a helpful assistant for ${tenant}. Always be respectful and accurate.`;
}

function getPolicyHash(tenant: string): string {
  // In production, get tenant-specific policy hash
  return 'sha256:policy_hash_for_' + tenant;
}

// Configuration
export const config = {
  matcher: [
    '/api/openai/:path*',
    '/api/chat/:path*',
  ],
}; 