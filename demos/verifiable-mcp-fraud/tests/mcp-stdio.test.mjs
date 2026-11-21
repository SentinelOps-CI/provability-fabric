// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import assert from "node:assert/strict";
import { test } from "node:test";
import { Client } from "@modelcontextprotocol/sdk/client/index.js";
import { StdioClientTransport } from "@modelcontextprotocol/sdk/client/stdio.js";

const textContent = (result) =>
  result.content.find((item) => item.type === "text")?.text ?? "";

test("MCP stdio handshake, validated transactions, and tenant boundary", { timeout: 45_000 }, async () => {
  const transport = new StdioClientTransport({
    command: process.execPath,
    args: ["dist/src/fraud-mcp-server.js", "--stdio"],
  });
  const client = new Client(
    { name: "fraud-demo-ci-client", version: "1.0.0" },
    { capabilities: {} },
  );

  try {
    await client.connect(transport);
    const discovered = await client.listTools();
    const names = discovered.tools.map((tool) => tool.name);
    for (const name of ["ingest_transaction", "score_fraud", "get_transaction"]) {
      assert.ok(names.includes(name), `Missing MCP tool: ${name}`);
    }

    const invalid = await client.callTool({
      name: "ingest_transaction",
      arguments: {
        transaction_id: "mcp-smoke-001",
        amount: "not-a-number",
        merchant: "Casino",
        user_id: "test-user",
        tenant_id: "tenant-one",
      },
    });
    assert.equal(invalid.isError, true, "Malformed tool arguments must be rejected");
    assert.match(textContent(invalid), /Invalid or missing amount/);

    const ingested = await client.callTool({
      name: "ingest_transaction",
      arguments: {
        transaction_id: "mcp-smoke-001",
        amount: 25_000,
        merchant: "Casino",
        user_id: "test-user",
        tenant_id: "tenant-one",
        location: "Offshore",
      },
    });
    assert.notEqual(ingested.isError, true, textContent(ingested));

    const forbidden = await client.callTool({
      name: "get_transaction",
      arguments: {
        transaction_id: "mcp-smoke-001",
        tenant_id: "tenant-two",
      },
    });
    assert.equal(forbidden.isError, true, "Cross-tenant transaction lookup must be rejected");
    assert.match(textContent(forbidden), /different tenant/);

    const retrieved = await client.callTool({
      name: "get_transaction",
      arguments: {
        transaction_id: "mcp-smoke-001",
        tenant_id: "tenant-one",
      },
    });
    assert.notEqual(retrieved.isError, true, textContent(retrieved));
    const row = JSON.parse(textContent(retrieved));
    assert.equal(row.id, "mcp-smoke-001");
    assert.equal(row.tenant_id, "tenant-one");

    // This path emits a high-risk diagnostic. A subsequent MCP response confirms
    // that operational logs did not corrupt the JSON-RPC stdout stream.
    const scored = await client.callTool({
      name: "score_fraud",
      arguments: {
        transaction_id: "mcp-smoke-001",
        tenant_id: "tenant-one",
      },
    });
    assert.notEqual(scored.isError, true, textContent(scored));
    const score = JSON.parse(textContent(scored));
    assert.ok(Number.isFinite(score.fraud_score));
    assert.ok(score.fraud_score >= 0.9 && score.fraud_score <= 1);
  } finally {
    await client.close();
  }
});
