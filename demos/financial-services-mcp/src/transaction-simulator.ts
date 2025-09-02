/**
 * High-Performance Transaction Simulator
 * 
 * Generates realistic financial transaction patterns for testing and demonstration.
 * Supports configurable transaction rates, fraud injection, and multi-institution scenarios.
 */

import express from 'express';
import axios from 'axios';
import { Worker, isMainThread, parentPort, workerData } from 'worker_threads';
import { createHash, randomBytes } from 'crypto';

interface SimulationConfig {
  transactionsPerSecond: number;
  fraudRate: number;
  institutionsCount: number;
  mcpServerUrl: string;
  duration: number; // in seconds
  batchSize: number;
}

interface Transaction {
  id: string;
  institutionId: string;
  accountId: string;
  amount: number;
  currency: string;
  timestamp: number;
  type: 'transfer' | 'payment' | 'withdrawal' | 'deposit';
  merchantId?: string;
  location: {
    country: string;
    city: string;
    latitude: number;
    longitude: number;
  };
  metadata: {
    channel: 'online' | 'atm' | 'pos' | 'mobile';
    deviceId?: string;
    ipAddress?: string;
    userAgent?: string;
  };
  isFraudulent: boolean;
}

interface SimulationMetrics {
  totalTransactions: number;
  fraudulentTransactions: number;
  successfulTransactions: number;
  failedTransactions: number;
  averageLatency: number;
  throughput: number;
  startTime: number;
  endTime?: number;
}

class TransactionGenerator {
  private static readonly CURRENCIES = ['USD', 'EUR', 'GBP', 'JPY', 'CAD', 'AUD'];
  private static readonly COUNTRIES = [
    { name: 'USA', cities: ['New York', 'Los Angeles', 'Chicago'] },
    { name: 'UK', cities: ['London', 'Manchester', 'Birmingham'] },
    { name: 'Canada', cities: ['Toronto', 'Vancouver', 'Montreal'] },
    { name: 'Australia', cities: ['Sydney', 'Melbourne', 'Brisbane'] }
  ];
  private static readonly CHANNELS = ['online', 'atm', 'pos', 'mobile'] as const;
  private static readonly TRANSACTION_TYPES = ['transfer', 'payment', 'withdrawal', 'deposit'] as const;

  static generateTransaction(institutionId: string, isFraudulent: boolean = false): Transaction {
    const country = this.COUNTRIES[Math.floor(Math.random() * this.COUNTRIES.length)];
    const city = country.cities[Math.floor(Math.random() * country.cities.length)];
    const channel = this.CHANNELS[Math.floor(Math.random() * this.CHANNELS.length)];
    const type = this.TRANSACTION_TYPES[Math.floor(Math.random() * this.TRANSACTION_TYPES.length)];

    // Generate realistic amounts based on transaction type and fraud patterns
    let amount: number;
    if (isFraudulent) {
      // Fraudulent transactions often have suspicious patterns
      amount = Math.random() < 0.3 
        ? Math.floor(Math.random() * 50000) + 10000  // Large amounts
        : Math.floor(Math.random() * 100) + 1;       // Micro amounts (testing)
    } else {
      // Normal transaction amounts follow typical patterns
      switch (type) {
        case 'withdrawal':
          amount = Math.floor(Math.random() * 500) + 20;
          break;
        case 'transfer':
          amount = Math.floor(Math.random() * 5000) + 100;
          break;
        case 'payment':
          amount = Math.floor(Math.random() * 1000) + 10;
          break;
        case 'deposit':
          amount = Math.floor(Math.random() * 10000) + 50;
          break;
      }
    }

    const transaction: Transaction = {
      id: this.generateTransactionId(),
      institutionId,
      accountId: this.generateAccountId(),
      amount,
      currency: this.CURRENCIES[Math.floor(Math.random() * this.CURRENCIES.length)],
      timestamp: Date.now(),
      type,
      location: {
        country: country.name,
        city,
        latitude: Math.random() * 180 - 90,
        longitude: Math.random() * 360 - 180
      },
      metadata: {
        channel,
        deviceId: channel === 'mobile' ? this.generateDeviceId() : undefined,
        ipAddress: this.generateIpAddress(),
        userAgent: channel === 'online' || channel === 'mobile' ? this.generateUserAgent() : undefined
      },
      isFraudulent
    };

    // Add merchant for payment transactions
    if (type === 'payment') {
      transaction.merchantId = this.generateMerchantId();
    }

    return transaction;
  }

  private static generateTransactionId(): string {
    return 'TXN-' + createHash('sha256')
      .update(randomBytes(16))
      .digest('hex')
      .substring(0, 12)
      .toUpperCase();
  }

  private static generateAccountId(): string {
    return 'ACC-' + Math.floor(Math.random() * 1000000).toString().padStart(6, '0');
  }

  private static generateMerchantId(): string {
    return 'MER-' + Math.floor(Math.random() * 100000).toString().padStart(5, '0');
  }

  private static generateDeviceId(): string {
    return createHash('md5')
      .update(randomBytes(8))
      .digest('hex');
  }

  private static generateIpAddress(): string {
    return `${Math.floor(Math.random() * 256)}.${Math.floor(Math.random() * 256)}.${Math.floor(Math.random() * 256)}.${Math.floor(Math.random() * 256)}`;
  }

  private static generateUserAgent(): string {
    const agents = [
      'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
      'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36',
      'Mozilla/5.0 (iPhone; CPU iPhone OS 15_0 like Mac OS X) AppleWebKit/605.1.15',
      'Mozilla/5.0 (Android 12; Mobile; rv:91.0) Gecko/91.0 Firefox/91.0'
    ];
    return agents[Math.floor(Math.random() * agents.length)];
  }
}

class TransactionSimulator {
  private config: SimulationConfig;
  private metrics: SimulationMetrics;
  private isRunning: boolean = false;
  private workers: Worker[] = [];

  constructor(config: SimulationConfig) {
    this.config = config;
    this.metrics = {
      totalTransactions: 0,
      fraudulentTransactions: 0,
      successfulTransactions: 0,
      failedTransactions: 0,
      averageLatency: 0,
      throughput: 0,
      startTime: Date.now()
    };
  }

  async startSimulation(): Promise<void> {
    console.log('🚀 Starting transaction simulation...');
    console.log(`Configuration:`, this.config);

    this.isRunning = true;
    this.metrics.startTime = Date.now();

    // Create worker threads for parallel transaction generation
    const workerCount = Math.min(4, Math.ceil(this.config.transactionsPerSecond / 1000));
    const transactionsPerWorker = Math.ceil(this.config.transactionsPerSecond / workerCount);

    for (let i = 0; i < workerCount; i++) {
      const worker = new Worker(__filename, {
        workerData: {
          ...this.config,
          transactionsPerSecond: transactionsPerWorker,
          workerId: i
        }
      });

      worker.on('message', (message) => {
        this.handleWorkerMessage(message);
      });

      worker.on('error', (error) => {
        console.error(`Worker ${i} error:`, error);
      });

      this.workers.push(worker);
    }

    // Run simulation for specified duration
    setTimeout(() => {
      this.stopSimulation();
    }, this.config.duration * 1000);
  }

  private handleWorkerMessage(message: any) {
    switch (message.type) {
      case 'transaction_completed':
        this.metrics.totalTransactions++;
        if (message.success) {
          this.metrics.successfulTransactions++;
        } else {
          this.metrics.failedTransactions++;
        }
        if (message.isFraudulent) {
          this.metrics.fraudulentTransactions++;
        }
        break;
      
      case 'batch_completed':
        this.updateThroughputMetrics();
        break;
    }
  }

  private updateThroughputMetrics() {
    const elapsedSeconds = (Date.now() - this.metrics.startTime) / 1000;
    this.metrics.throughput = this.metrics.totalTransactions / elapsedSeconds;
  }

  async stopSimulation(): Promise<void> {
    console.log('🛑 Stopping transaction simulation...');
    this.isRunning = false;
    this.metrics.endTime = Date.now();

    // Terminate all workers
    await Promise.all(this.workers.map(worker => worker.terminate()));
    this.workers = [];

    this.printFinalMetrics();
  }

  private printFinalMetrics() {
    const duration = (this.metrics.endTime! - this.metrics.startTime) / 1000;
    
    console.log('\n📊 Simulation Complete - Final Metrics:');
    console.log(`Duration: ${duration.toFixed(2)}s`);
    console.log(`Total Transactions: ${this.metrics.totalTransactions}`);
    console.log(`Successful: ${this.metrics.successfulTransactions}`);
    console.log(`Failed: ${this.metrics.failedTransactions}`);
    console.log(`Fraudulent: ${this.metrics.fraudulentTransactions}`);
    console.log(`Average Throughput: ${(this.metrics.totalTransactions / duration).toFixed(2)} TPS`);
    console.log(`Success Rate: ${((this.metrics.successfulTransactions / this.metrics.totalTransactions) * 100).toFixed(2)}%`);
    console.log(`Fraud Rate: ${((this.metrics.fraudulentTransactions / this.metrics.totalTransactions) * 100).toFixed(2)}%`);
  }

  getMetrics(): SimulationMetrics {
    return { ...this.metrics };
  }
}

// Worker thread logic
async function runWorker(config: SimulationConfig & { workerId: number }) {
  const { workerId, transactionsPerSecond, fraudRate, institutionsCount, mcpServerUrl, batchSize } = config;
  
  console.log(`🔧 Worker ${workerId} started - ${transactionsPerSecond} TPS target`);

  const intervalMs = 1000 / transactionsPerSecond;
  const batchIntervalMs = intervalMs * batchSize;

  const processTransactionBatch = async () => {
    const transactions: Transaction[] = [];
    
    // Generate batch of transactions
    for (let i = 0; i < batchSize; i++) {
      const institutionId = `INST-${Math.floor(Math.random() * institutionsCount) + 1}`;
      const isFraudulent = Math.random() < fraudRate;
      
      const transaction = TransactionGenerator.generateTransaction(institutionId, isFraudulent);
      transactions.push(transaction);
    }

    // Send batch to MCP server
    try {
      const startTime = Date.now();
      
      const response = await axios.post(`${mcpServerUrl}/api/transactions/batch`, {
        transactions
      }, {
        timeout: 5000,
        headers: {
          'Content-Type': 'application/json'
        }
      });

      const latency = Date.now() - startTime;

      // Report results to main thread
      transactions.forEach(transaction => {
        parentPort?.postMessage({
          type: 'transaction_completed',
          success: response.status === 200,
          isFraudulent: transaction.isFraudulent,
          latency
        });
      });

      parentPort?.postMessage({
        type: 'batch_completed',
        batchSize,
        latency
      });

    } catch (error) {
      // Report failures
      transactions.forEach(transaction => {
        parentPort?.postMessage({
          type: 'transaction_completed',
          success: false,
          isFraudulent: transaction.isFraudulent,
          error: error instanceof Error ? error.message : 'Unknown error'
        });
      });
    }
  };

  // Start batch processing
  const interval = setInterval(processTransactionBatch, batchIntervalMs);

  // Cleanup on worker termination
  process.on('SIGTERM', () => {
    clearInterval(interval);
  });
}

// HTTP API for controlling simulation
class SimulatorAPI {
  private app: express.Application;
  private simulator: TransactionSimulator | null = null;

  constructor() {
    this.app = express();
    this.app.use(express.json());
    this.setupRoutes();
  }

  private setupRoutes() {
    this.app.get('/health', (req, res) => {
      res.json({
        status: 'healthy',
        uptime: process.uptime(),
        timestamp: new Date().toISOString()
      });
    });

    this.app.post('/simulation/start', async (req, res) => {
      try {
        if (this.simulator?.getMetrics()) {
          return res.status(400).json({ error: 'Simulation already running' });
        }

        const config: SimulationConfig = {
          transactionsPerSecond: req.body.transactionsPerSecond || 100,
          fraudRate: req.body.fraudRate || 0.02,
          institutionsCount: req.body.institutionsCount || 5,
          mcpServerUrl: req.body.mcpServerUrl || 'http://financial-mcp-server:8080',
          duration: req.body.duration || 300, // 5 minutes default
          batchSize: req.body.batchSize || 10
        };

        this.simulator = new TransactionSimulator(config);
        await this.simulator.startSimulation();

        res.json({ message: 'Simulation started', config });
      } catch (error) {
        res.status(500).json({ error: error instanceof Error ? error.message : 'Unknown error' });
      }
    });

    this.app.post('/simulation/stop', async (req, res) => {
      try {
        if (!this.simulator) {
          return res.status(400).json({ error: 'No simulation running' });
        }

        await this.simulator.stopSimulation();
        const metrics = this.simulator.getMetrics();
        this.simulator = null;

        res.json({ message: 'Simulation stopped', metrics });
      } catch (error) {
        res.status(500).json({ error: error instanceof Error ? error.message : 'Unknown error' });
      }
    });

    this.app.get('/simulation/metrics', (req, res) => {
      if (!this.simulator) {
        return res.status(404).json({ error: 'No simulation running' });
      }

      res.json(this.simulator.getMetrics());
    });
  }

  start(port: number = 8081) {
    this.app.listen(port, () => {
      console.log(`🎯 Transaction Simulator API listening on port ${port}`);
    });
  }
}

// Main execution
if (isMainThread) {
  // Start HTTP API
  const api = new SimulatorAPI();
  const port = parseInt(process.env.PORT || '8081');
  api.start(port);

  // Auto-start simulation if environment variables are set
  if (process.env.AUTO_START === 'true') {
    const config: SimulationConfig = {
      transactionsPerSecond: parseInt(process.env.TRANSACTIONS_PER_SECOND || '100'),
      fraudRate: parseFloat(process.env.FRAUD_RATE || '0.02'),
      institutionsCount: parseInt(process.env.INSTITUTIONS_COUNT || '5'),
      mcpServerUrl: process.env.MCP_SERVER_URL || 'http://financial-mcp-server:8080',
      duration: parseInt(process.env.DURATION || '300'),
      batchSize: parseInt(process.env.BATCH_SIZE || '10')
    };

    setTimeout(async () => {
      const simulator = new TransactionSimulator(config);
      await simulator.startSimulation();
    }, 5000); // Wait 5 seconds for other services to start
  }
} else {
  // Worker thread execution
  if (workerData) {
    runWorker(workerData);
  }
}
