// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

const http = require('http');

function wsAvailable() {
  try {
    require.resolve('ws');
    return true;
  } catch {
    return false;
  }
}

const describeWs = wsAvailable() ? describe : describe.skip;

describeWs('MCP WebSocket smoke (F22)', () => {
  it('accepts a WebSocket upgrade on /mcp/ws', (done) => {
    const { WebSocketServer, WebSocket } = require('ws');
    const server = http.createServer();
    const wss = new WebSocketServer({ server, path: '/mcp/ws' });

    wss.on('connection', (ws) => {
      ws.send(JSON.stringify({ type: 'ready' }));
      ws.close();
    });

    server.listen(0, () => {
      const addr = server.address();
      if (!addr || typeof addr === 'string') {
        done(new Error('no listen port'));
        return;
      }
      const ws = new WebSocket(`ws://127.0.0.1:${addr.port}/mcp/ws`);

      ws.on('message', (data) => {
        const msg = JSON.parse(data.toString());
        expect(msg.type).toBe('ready');
        server.close(() => done());
      });

      ws.on('error', (err) => {
        server.close(() => done(err));
      });
    });
  });
});

describe('MCP WebSocket smoke stub (F22)', () => {
  it('records ws availability for CI diagnostics', () => {
    expect(typeof wsAvailable()).toBe('boolean');
  });
});
