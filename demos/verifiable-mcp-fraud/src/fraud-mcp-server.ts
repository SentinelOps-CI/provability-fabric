// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

import express from "express";
import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
  Tool,
} from "@modelcontextprotocol/sdk/types.js";
import { SentinelOpsClient } from "@provability-fabric/core-sdk-typescript";

interface Transaction {
  id: string;
  amount: number;
  merchant: string;
  timestamp: string;
  user_id: string;
  card_number: string;
  location: string;
  tenant_id: string;
}

interface FraudScore {
  transaction_id: string;
  score: number;
  risk_factors: string[];
  timestamp: string;
  model_version: string;
}

class FraudMCPServer {
  private mcpServer: Server;
  private sentinelOps: SentinelOpsClient;
  private transactions: Map<string, Transaction> = new Map();
  private scores: Map<string, FraudScore> = new Map();

  // HTTP pieces
  private app = express();
  private port = Number(process.env.PORT) || 3001;

  constructor() {
    // MCP server (stdio) — only started if explicitly enabled (see run()).
    this.mcpServer = new Server(
      { name: "fraud-detection-mcp", version: "1.0.0" },
      { capabilities: { tools: {} } }
    );

    // Initialize SentinelOps client (platform integration)
    this.sentinelOps = new SentinelOpsClient(
      process.env.SENTINELOPS_API_URL || "http://api-gateway:8000",
      process.env.SENTINELOPS_API_KEY
    );

    this.setupMcpHandlers();
    this.setupHttp();
  }

  // -----------------------
  // MCP (tools on stdio)
  // -----------------------

  private getTools(): Tool[] {
    return [
      {
        name: "ingest_transaction",
        description: "Ingest a financial transaction for fraud analysis",
        inputSchema: {
          type: "object",
          properties: {
            transaction_id: { type: "string" },
            amount: { type: "number" },
            merchant: { type: "string" },
            user_id: { type: "string" },
            card_number: { type: "string" },
            location: { type: "string" },
            tenant_id: { type: "string" },
          },
          required: ["transaction_id", "amount", "merchant", "user_id", "tenant_id"],
        },
      },
      {
        name: "score_fraud",
        description: "Score transaction for fraud risk (RESTRICTED: FraudService only)",
        inputSchema: {
          type: "object",
          properties: {
            transaction_id: { type: "string" },
            tenant_id: { type: "string" },
          },
          required: ["transaction_id", "tenant_id"],
        },
      },
      {
        name: "get_transaction",
        description: "Retrieve transaction details",
        inputSchema: {
          type: "object",
          properties: {
            transaction_id: { type: "string" },
            tenant_id: { type: "string" },
          },
          required: ["transaction_id", "tenant_id"],
        },
      },
    ];
  }

  private setupMcpHandlers(): void {
    // List available tools
    this.mcpServer.setRequestHandler(ListToolsRequestSchema, async () => {
      return { tools: this.getTools() };
    });

    // Handle tool calls
    this.mcpServer.setRequestHandler(CallToolRequestSchema, async (request) => {
      const { name, arguments: args } = request.params;

      try {
        switch (name) {
          case "ingest_transaction":
            return await this.handleIngestTransaction(args as any);
          case "score_fraud":
            return await this.handleScoreFraud(args as any);
          case "get_transaction":
            return await this.handleGetTransaction(args as any);
          default:
            throw new Error(`Unknown tool: ${name}`);
        }
      } catch (error: any) {
        return {
          content: [{ type: "text", text: `Error: ${error.message}` }],
          isError: true,
        };
      }
    });
  }

  // -----------------------
  // HTTP (keeps container alive)
  // -----------------------

  private setupHttp(): void {
    this.app.use(express.json());

    // Liveness / readiness
    this.app.get("/health", (_req, res) => res.status(200).send("ok"));
    this.app.get("/ready", (_req, res) => res.status(200).json({ ready: true }));

    // Simple info page
    this.app.get("/", (_req, res) =>
      res
        .status(200)
        .send("Fraud Detection MCP Server running (HTTP). MCP stdio is optional; set MCP_ENABLE_STDIO=true to enable.")
    );

    // Optional HTTP wrappers around the demo tools (handy for testing without MCP client)
    this.app.post("/api/ingest", async (req, res) => {
      try {
        const result = await this.handleIngestTransaction(req.body);
        res.json({ ok: true, result });
      } catch (e: any) {
        res.status(400).json({ ok: false, error: e.message });
      }
    });

    this.app.post("/api/score", async (req, res) => {
      try {
        const result = await this.handleScoreFraud(req.body);
        res.json({ ok: true, result });
      } catch (e: any) {
        res.status(400).json({ ok: false, error: e.message });
      }
    });

    this.app.get("/api/tx/:id", async (req, res) => {
      try {
        const result = await this.handleGetTransaction({
          transaction_id: req.params.id,
          tenant_id: String(req.query.tenant_id || ""),
        });
        res.json({ ok: true, result });
      } catch (e: any) {
        res.status(404).json({ ok: false, error: e.message });
      }
    });

    // Expose the tool list via HTTP as well (debugging aid)
    this.app.get("/api/tools", (_req, res) => res.json(this.getTools()));
  }

  // -----------------------
  // Tool implementations
  // -----------------------

  private async handleIngestTransaction(args: {
    transaction_id: string;
    amount: number;
    merchant: string;
    user_id: string;
    card_number?: string;
    location?: string;
    tenant_id: string;
  }) {
    const transaction: Transaction = {
      id: args.transaction_id,
      amount: args.amount,
      merchant: args.merchant,
      timestamp: new Date().toISOString(),
      user_id: args.user_id,
      card_number: args.card_number || "****-****-****-0000",
      location: args.location || "Unknown",
      tenant_id: args.tenant_id,
    };

    this.transactions.set(args.transaction_id, transaction);

    return {
      content: [
        {
          type: "text",
          text: `Transaction ${args.transaction_id} ingested successfully for tenant ${args.tenant_id}`,
        },
      ],
    };
  }

  private async handleScoreFraud(args: { transaction_id: string; tenant_id: string }) {
    // RESTRICTED — only FraudService should call this (enforced by platform policy)
    const transaction = this.transactions.get(args.transaction_id);
    if (!transaction) throw new Error(`Transaction not found: ${args.transaction_id}`);
    if (transaction.tenant_id !== args.tenant_id) throw new Error(`Transaction belongs to different tenant`);

    const score = this.calculateFraudScore(transaction);

    const fraudScore: FraudScore = {
      transaction_id: args.transaction_id,
      score,
      risk_factors: this.identifyRiskFactors(transaction, score),
      timestamp: new Date().toISOString(),
      model_version: "fraud-model-v1.0.0",
    };

    this.scores.set(args.transaction_id, fraudScore);

    const shouldBlock = score >= 0.93;
    if (score > 0.8) {
      // Rate limiting should be enforced by platform policy
      console.log(`[ALERT] High fraud score: ${score} for transaction ${args.transaction_id}`);
    }

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify(
            {
              transaction_id: args.transaction_id,
              fraud_score: score,
              risk_level: this.getRiskLevel(score),
              should_block: shouldBlock,
              risk_factors: fraudScore.risk_factors,
              model_version: fraudScore.model_version,
              timestamp: fraudScore.timestamp,
            },
            null,
            2
          ),
        },
      ],
    };
  }

  private async handleGetTransaction(args: { transaction_id: string; tenant_id: string }) {
    const transaction = this.transactions.get(args.transaction_id);
    if (!transaction) throw new Error(`Transaction not found: ${args.transaction_id}`);
    if (transaction.tenant_id !== args.tenant_id) throw new Error(`Transaction belongs to different tenant`);

    return {
      content: [{ type: "text", text: JSON.stringify(transaction, null, 2) }],
    };
  }

  private calculateFraudScore(transaction: Transaction): number {
    let score = 0.0;

    // Amount-based risk
    if (transaction.amount > 10000) score += 0.4;
    else if (transaction.amount > 5000) score += 0.2;
    else if (transaction.amount > 1000) score += 0.1;

    // Time-based risk (late night transactions)
    const hour = new Date(transaction.timestamp).getHours();
    if (hour < 6 || hour > 22) score += 0.15;

    // Merchant-based risk
    const highRiskMerchants = ["casino", "betting", "crypto", "unknown"];
    if (highRiskMerchants.some((m) => transaction.merchant.toLowerCase().includes(m))) score += 0.3;

    // Location-based risk (simplified)
    const highRiskLocations = ["unknown", "foreign", "offshore"];
    if (highRiskLocations.some((l) => transaction.location.toLowerCase().includes(l))) score += 0.25;

    // Demo randomness
    score += Math.random() * 0.1;

    return Math.min(score, 1.0);
  }

  private identifyRiskFactors(transaction: Transaction, score: number): string[] {
    const factors: string[] = [];
    if (transaction.amount > 10000) factors.push("high_amount");

    const hour = new Date(transaction.timestamp).getHours();
    if (hour < 6 || hour > 22) factors.push("unusual_time");

    const highRiskMerchants = ["casino", "betting", "crypto", "unknown"];
    if (highRiskMerchants.some((m) => transaction.merchant.toLowerCase().includes(m))) {
      factors.push("high_risk_merchant");
    }

    if (transaction.location.toLowerCase().includes("unknown")) factors.push("unknown_location");
    if (score > 0.7) factors.push("high_risk_profile");

    return factors;
  }

  private getRiskLevel(score: number): string {
    if (score >= 0.93) return "CRITICAL";
    if (score >= 0.8) return "HIGH";
    if (score >= 0.5) return "MEDIUM";
    if (score >= 0.3) return "LOW";
    return "MINIMAL";
  }

  // -----------------------
  // Lifecycle
  // -----------------------

  private async startHttp(): Promise<void> {
    await new Promise<void>((resolve) => {
      this.app.listen(this.port, () => {
        console.log(`Fraud Detection MCP Server (HTTP) listening on :${this.port}`);
        resolve();
      });
    });
  }

  private async startMcpIfEnabled(): Promise<void> {
    const enable = (process.env.MCP_ENABLE_STDIO ?? "false").toLowerCase() === "true";
    if (!enable) {
      console.log("MCP stdio transport disabled (set MCP_ENABLE_STDIO=true to enable).");
      return;
    }
    const transport = new StdioServerTransport();
    await this.mcpServer.connect(transport);
    console.error("Fraud Detection MCP Server (stdio) connected.");
  }

  async run(): Promise<void> {
    await this.startHttp();
    await this.startMcpIfEnabled();

    // Keep process alive; HTTP server does this already, but add signal handling for clean exit.
    const shutdown = () => process.exit(0);
    process.on("SIGTERM", shutdown);
    process.on("SIGINT", shutdown);
  }
}

// Initialize and run server
if (import.meta.url === `file://${process.argv[1]}`) {
  const server = new FraudMCPServer();
  server.run().catch((err) => {
    console.error(err);
    process.exit(1);
  });
}
