// SPDX-License-Identifier: Apache-2.0
import http from 'http';
import { AddressInfo } from 'net';
import { ProvabilityFabricClient } from '../client.js';
import { ProvabilityFabricSDK } from '../index.js';
import { createIdempotentRetry, retryMiddleware } from '../retry.js';
import { ProvabilityFabricError } from '../errors.js';

type Handler = (
  req: http.IncomingMessage,
  res: http.ServerResponse,
  url: URL
) => void | Promise<void>;

async function withMockServer(
  handler: Handler,
  fn: (baseUrl: string, counts: { hits: Map<string, number> }) => Promise<void>
): Promise<void> {
  const hits = new Map<string, number>();
  const server = http.createServer(async (req, res) => {
    const url = new URL(req.url ?? '/', 'http://127.0.0.1');
    const key = `${req.method ?? 'GET'} ${url.pathname}`;
    hits.set(key, (hits.get(key) ?? 0) + 1);
    try {
      await handler(req, res, url);
    } catch {
      res.statusCode = 500;
      res.end(JSON.stringify({ error: 'handler failed' }));
    }
  });

  await new Promise<void>((resolve) => server.listen(0, '127.0.0.1', resolve));
  const { port } = server.address() as AddressInfo;
  const baseUrl = `http://127.0.0.1:${port}`;

  try {
    await fn(baseUrl, { hits });
  } finally {
    await new Promise<void>((resolve, reject) =>
      server.close((err) => (err ? reject(err) : resolve()))
    );
  }
}

describe('ProvabilityFabricClient HTTP lifecycle', () => {
  it('connect() probes /health and enables subsequent requests', async () => {
    await withMockServer(
      (req, res, url) => {
        if (url.pathname === '/health') {
          res.setHeader('Content-Type', 'application/json');
          res.end(JSON.stringify({ status: 'healthy', timestamp: '2026-01-01T00:00:00Z' }));
          return;
        }
        if (url.pathname === '/api/status') {
          res.setHeader('Content-Type', 'application/json');
          res.end(
            JSON.stringify({
              service: 'Provability-Fabric Ledger',
              status: 'running',
            })
          );
          return;
        }
        res.statusCode = 404;
        res.end('not found');
      },
      async (baseUrl, { hits }) => {
        const client = new ProvabilityFabricClient({
          endpoint: baseUrl,
          retries: 0,
          timeout: 2000,
        });
        expect(client.isConnected()).toBe(false);

        await client.connect();
        expect(client.isConnected()).toBe(true);
        expect(hits.get('GET /health')).toBe(1);

        const status = await client.getStatus();
        expect(status.status).toBe('running');
        expect(status.service).toContain('Ledger');

        await client.disconnect();
        expect(client.isConnected()).toBe(false);

        await expect(client.getStatus()).rejects.toMatchObject({
          code: 'NOT_CONNECTED',
        });
      }
    );
  });

  it('connect() fails closed when /health is unhealthy', async () => {
    await withMockServer(
      (_req, res) => {
        res.statusCode = 503;
        res.end(JSON.stringify({ status: 'down' }));
      },
      async (baseUrl) => {
        const client = new ProvabilityFabricClient({
          endpoint: baseUrl,
          retries: 0,
          timeout: 2000,
        });
        await expect(client.connect()).rejects.toBeInstanceOf(ProvabilityFabricError);
        expect(client.isConnected()).toBe(false);
      }
    );
  });

  it('retries idempotent GET on 503 then succeeds', async () => {
    let apiHits = 0;
    await withMockServer(
      (_req, res, url) => {
        res.setHeader('Content-Type', 'application/json');
        if (url.pathname === '/health') {
          res.end(JSON.stringify({ status: 'healthy' }));
          return;
        }
        apiHits += 1;
        if (apiHits < 3) {
          res.statusCode = 503;
          res.end(JSON.stringify({ error: 'unavailable' }));
          return;
        }
        res.end(JSON.stringify({ status: 'running', attempts: apiHits }));
      },
      async (baseUrl, { hits }) => {
        const client = new ProvabilityFabricClient({
          endpoint: baseUrl,
          retries: 3,
          baseDelay: 1,
          maxDelay: 5,
          timeout: 2000,
        });
        await client.connect();
        const status = await client.getStatus();
        expect(status.status).toBe('running');
        expect(hits.get('GET /api/status')).toBe(3);
      }
    );
  });

  it('does not retry non-idempotent POST', async () => {
    let posts = 0;
    await withMockServer(
      (_req, res, url) => {
        res.setHeader('Content-Type', 'application/json');
        if (url.pathname === '/health') {
          res.end(JSON.stringify({ status: 'healthy' }));
          return;
        }
        posts += 1;
        res.statusCode = 503;
        res.end(JSON.stringify({ error: 'unavailable' }));
      },
      async (baseUrl) => {
        const client = new ProvabilityFabricClient({
          endpoint: baseUrl,
          retries: 5,
          baseDelay: 1,
          maxDelay: 5,
          timeout: 2000,
        });
        await client.connect();
        await expect(client.request('POST', '/usage', { n: 1 })).rejects.toMatchObject({
          statusCode: 503,
        });
        expect(posts).toBe(1);
      }
    );
  });

  it('SDK initializeClient returns a working HTTP client (not null)', async () => {
    await withMockServer(
      (_req, res, url) => {
        res.setHeader('Content-Type', 'application/json');
        if (url.pathname === '/health') {
          res.end(JSON.stringify({ status: 'healthy' }));
          return;
        }
        res.end(JSON.stringify({ status: 'running' }));
      },
      async (baseUrl) => {
        const sdk = new ProvabilityFabricSDK({
          endpoint: baseUrl,
          retries: 0,
          timeout: 2000,
        });
        const client = sdk.getClient();
        expect(client).toBeInstanceOf(ProvabilityFabricClient);
        await sdk.connect();
        expect(client.isConnected()).toBe(true);
        await sdk.disconnect();
      }
    );
  });
});

describe('retryMiddleware (idempotent outbound)', () => {
  it('retries GET and does not retry POST', async () => {
    let gets = 0;
    let posts = 0;
    const retry = retryMiddleware({ maxRetries: 2, baseDelay: 1, maxDelay: 5 });

    const getResult = await retry('GET', async () => {
      gets += 1;
      if (gets < 3) {
        const err = new ProvabilityFabricError('fail', 'HTTP_ERROR', 503);
        throw err;
      }
      return 'ok';
    });
    expect(getResult).toBe('ok');
    expect(gets).toBe(3);

    await expect(
      retry('POST', async () => {
        posts += 1;
        throw new ProvabilityFabricError('fail', 'HTTP_ERROR', 503);
      })
    ).rejects.toMatchObject({ statusCode: 503 });
    expect(posts).toBe(1);
  });

  it('createIdempotentRetry matches retryMiddleware', async () => {
    const a = createIdempotentRetry({ maxRetries: 0, baseDelay: 1, maxDelay: 1 });
    const b = retryMiddleware({ maxRetries: 0, baseDelay: 1, maxDelay: 1 });
    await expect(a('GET', async () => 1)).resolves.toBe(1);
    await expect(b('HEAD', async () => 2)).resolves.toBe(2);
  });
});
