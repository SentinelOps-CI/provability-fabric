import { Injectable, Logger, OnModuleInit, OnModuleDestroy } from '@nestjs/common';
import { ConfigService } from '@nestjs/config';
import { Kafka, Consumer, EachMessagePayload } from 'kafkajs';
import { GuardTrip } from '../types/guard-trip.interface';
import { DecisionEngineService } from '../decision-engine/decision-engine.service';

@Injectable()
export class KafkaService implements OnModuleInit, OnModuleDestroy {
  private readonly logger = new Logger(KafkaService.name);
  private kafka: Kafka;
  private consumer: Consumer;
  private isRunning = false;

  constructor(
    private readonly configService: ConfigService,
    private readonly decisionEngine: DecisionEngineService,
  ) {
    this.kafka = new Kafka({
      clientId: 'incident-bot',
      brokers: this.configService.get<string>('KAFKA_BROKERS', 'localhost:9092').split(','),
      ssl: this.configService.get<boolean>('KAFKA_SSL', false),
      sasl: this.configService.get<boolean>('KAFKA_SASL', false) ? {
        mechanism: 'plain',
        username: this.configService.get<string>('KAFKA_USERNAME'),
        password: this.configService.get<string>('KAFKA_PASSWORD'),
      } : undefined,
    });

    this.consumer = this.kafka.consumer({
      groupId: this.configService.get<string>('KAFKA_GROUP_ID', 'incident-bot-group'),
      sessionTimeout: 30000,
      heartbeatInterval: 3000,
    });
  }

  async onModuleInit() {
    await this.startConsumer();
  }

  async onModuleDestroy() {
    await this.stopConsumer();
  }

  private async startConsumer() {
    try {
      await this.consumer.connect();
      await this.consumer.subscribe({
        topic: 'provability.events.v1.GuardTrip',
        fromBeginning: false,
      });

      await this.consumer.run({
        eachMessage: async (payload: EachMessagePayload) => {
          await this.handleMessage(payload);
        },
      });

      this.isRunning = true;
      this.logger.log('Kafka consumer started successfully');
    } catch (error) {
      this.logger.error('Failed to start Kafka consumer:', error);
      throw error;
    }
  }

  private async stopConsumer() {
    if (this.isRunning) {
      try {
        await this.consumer.disconnect();
        this.isRunning = false;
        this.logger.log('Kafka consumer stopped');
      } catch (error) {
        this.logger.error('Error stopping Kafka consumer:', error);
      }
    }
  }

  private async handleMessage(payload: EachMessagePayload) {
    const { topic, partition, message } = payload;
    const messageValue = message.value?.toString();

    if (!messageValue) {
      this.logger.warn('Received empty message from Kafka');
      return;
    }

    try {
      const guardTrip: GuardTrip = JSON.parse(messageValue);
      
      // Validate GuardTrip event
      if (!this.validateGuardTrip(guardTrip)) {
        this.logger.warn('Invalid GuardTrip event received:', guardTrip);
        return;
      }

      this.logger.log(`Processing GuardTrip event: ${guardTrip.capsuleHash} (risk: ${guardTrip.riskScore})`);

      // Send to decision engine
      const decision = await this.decisionEngine.evaluateGuardTrip(guardTrip);
      
      if (decision.shouldRollback) {
        this.logger.warn(`Rollback decision made: ${decision.reason} for capsule ${guardTrip.capsuleHash}`);
        await this.decisionEngine.executeRollback(decision);
      } else {
        this.logger.log(`No rollback needed for capsule ${guardTrip.capsuleHash}`);
      }

    } catch (error) {
      this.logger.error('Error processing Kafka message:', error);
      // Don't throw to avoid stopping the consumer
    }
  }

  private validateGuardTrip(guardTrip: any): guardTrip is GuardTrip {
    return (
      guardTrip &&
      typeof guardTrip.capsuleHash === 'string' &&
      typeof guardTrip.tenantId === 'string' &&
      typeof guardTrip.riskScore === 'number' &&
      typeof guardTrip.heartbeatMisses === 'number' &&
      typeof guardTrip.ts === 'string' &&
      guardTrip.eventType === 'guard_trip'
    );
  }

  async getConsumerStatus() {
    return {
      isRunning: this.isRunning,
      groupId: this.configService.get<string>('KAFKA_GROUP_ID'),
      topic: 'provability.events.v1.GuardTrip',
    };
  }
}