import { Injectable } from '@nestjs/common';
import { Registry, Counter, Histogram, Gauge } from 'prom-client';

@Injectable()
export class MetricsService {
  private readonly registry: Registry;
  
  // Counters
  private readonly rollbacksTotal: Counter;
  private readonly guardTripsTotal: Counter;
  private readonly alertsTotal: Counter;
  private readonly decisionErrors: Counter;
  
  // Histograms
  private readonly decisionLatency: Histogram;
  
  // Gauges
  private readonly kafkaConsumerLag: Gauge;
  private readonly activeRollbacks: Gauge;

  constructor() {
    this.registry = new Registry();
    
    // Initialize counters
    this.rollbacksTotal = new Counter({
      name: 'incident_bot_rollbacks_total',
      help: 'Total number of rollbacks executed',
      labelNames: ['reason'],
      registers: [this.registry],
    });

    this.guardTripsTotal = new Counter({
      name: 'incident_bot_guard_trips_total',
      help: 'Total number of GuardTrip events processed',
      labelNames: ['tenant_id'],
      registers: [this.registry],
    });

    this.alertsTotal = new Counter({
      name: 'incident_bot_alerts_total',
      help: 'Total number of Alertmanager alerts processed',
      labelNames: ['alert_name'],
      registers: [this.registry],
    });

    this.decisionErrors = new Counter({
      name: 'incident_bot_decision_errors_total',
      help: 'Total number of decision engine errors',
      labelNames: ['error_type'],
      registers: [this.registry],
    });

    // Initialize histogram
    this.decisionLatency = new Histogram({
      name: 'incident_bot_decision_latency_seconds',
      help: 'Decision engine latency in seconds',
      labelNames: ['decision_type'],
      buckets: [0.1, 0.5, 1, 2, 5, 10, 30],
      registers: [this.registry],
    });

    // Initialize gauges
    this.kafkaConsumerLag = new Gauge({
      name: 'incident_bot_kafka_consumer_lag',
      help: 'Kafka consumer lag in messages',
      labelNames: ['topic', 'partition'],
      registers: [this.registry],
    });

    this.activeRollbacks = new Gauge({
      name: 'incident_bot_active_rollbacks',
      help: 'Number of active rollbacks in progress',
      registers: [this.registry],
    });
  }

  // Counter methods
  incrementRollbacks(reason: string) {
    this.rollbacksTotal.inc({ reason });
  }

  incrementGuardTrips(tenantId: string) {
    this.guardTripsTotal.inc({ tenant_id: tenantId });
  }

  incrementAlerts(alertName: string) {
    this.alertsTotal.inc({ alert_name: alertName });
  }

  incrementDecisionErrors(errorType: string) {
    this.decisionErrors.inc({ error_type: errorType });
  }

  // Histogram methods
  recordDecisionLatency(latencyMs: number, decisionType: string = 'guard_trip') {
    this.decisionLatency.observe({ decision_type: decisionType }, latencyMs / 1000);
  }

  // Gauge methods
  setKafkaConsumerLag(topic: string, partition: number, lag: number) {
    this.kafkaConsumerLag.set({ topic, partition }, lag);
  }

  setActiveRollbacks(count: number) {
    this.activeRollbacks.set(count);
  }

  // Registry access
  getRegistry(): Registry {
    return this.registry;
  }

  async getMetrics(): Promise<string> {
    return this.registry.metrics();
  }

  // Health check metrics
  getHealthMetrics() {
    return {
      rollbacksTotal: this.rollbacksTotal.get(),
      guardTripsTotal: this.guardTripsTotal.get(),
      alertsTotal: this.alertsTotal.get(),
      decisionErrors: this.decisionErrors.get(),
      activeRollbacks: this.activeRollbacks.get(),
    };
  }
}