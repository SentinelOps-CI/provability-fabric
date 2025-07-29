import { Controller, Post, Body, Headers, HttpException, HttpStatus, Logger } from '@nestjs/common';
import { ConfigService } from '@nestjs/config';
import { AlertmanagerAlert } from '../types/guard-trip.interface';
import { DecisionEngineService } from '../decision-engine/decision-engine.service';
import { MetricsService } from '../metrics/metrics.service';
import * as crypto from 'crypto';

@Controller('alertmanager')
export class AlertmanagerController {
  private readonly logger = new Logger(AlertmanagerController.name);

  constructor(
    private readonly configService: ConfigService,
    private readonly decisionEngine: DecisionEngineService,
    private readonly metricsService: MetricsService,
  ) {}

  @Post()
  async handleAlertmanagerWebhook(
    @Body() alert: AlertmanagerAlert,
    @Headers('x-signature') signature?: string,
  ) {
    try {
      // Validate HMAC signature if webhook secret is configured
      const webhookSecret = this.configService.get<string>('ALERTMANAGER_WEBHOOK_SECRET');
      if (webhookSecret && signature) {
        if (!this.validateSignature(alert, signature, webhookSecret)) {
          this.logger.warn('Invalid HMAC signature received');
          throw new HttpException('Invalid signature', HttpStatus.UNAUTHORIZED);
        }
      }

      this.logger.log(`Received Alertmanager webhook: ${alert.alerts.length} alerts`);

      // Process each alert
      for (const alertItem of alert.alerts) {
        await this.processAlert(alertItem);
      }

      return { status: 'processed', alerts: alert.alerts.length };

    } catch (error) {
      this.logger.error('Error processing Alertmanager webhook:', error);
      throw error;
    }
  }

  private validateSignature(alert: AlertmanagerAlert, signature: string, secret: string): boolean {
    try {
      const payload = JSON.stringify(alert);
      const expectedSignature = crypto
        .createHmac('sha256', secret)
        .update(payload)
        .digest('hex');

      return crypto.timingSafeEqual(
        Buffer.from(signature, 'hex'),
        Buffer.from(expectedSignature, 'hex'),
      );
    } catch (error) {
      this.logger.error('Error validating signature:', error);
      return false;
    }
  }

  private async processAlert(alert: any) {
    try {
      // Extract relevant information from alert labels
      const capsuleHash = alert.labels?.capsule_hash;
      const tenantId = alert.labels?.tenant_id;
      const riskScore = parseFloat(alert.labels?.risk_score || '0');
      const heartbeatMisses = parseInt(alert.labels?.heartbeat_misses || '0');

      if (!capsuleHash) {
        this.logger.warn('Alert missing capsule_hash label');
        return;
      }

      // Create GuardTrip-like event from alert
      const guardTripEvent = {
        capsuleHash,
        tenantId: tenantId || 'unknown',
        riskScore,
        heartbeatMisses,
        ts: new Date().toISOString(),
        eventType: 'guard_trip' as const,
        reason: alert.annotations?.summary || 'alertmanager_alert',
      };

      this.logger.log(`Processing alert for capsule ${capsuleHash}: risk=${riskScore}, misses=${heartbeatMisses}`);

      // Send to decision engine
      const decision = await this.decisionEngine.evaluateGuardTrip(guardTripEvent);
      
      if (decision.shouldRollback) {
        this.logger.warn(`Rollback decision from alert: ${decision.reason} for capsule ${capsuleHash}`);
        await this.decisionEngine.executeRollback(decision);
      } else {
        this.logger.log(`No rollback needed for alert capsule ${capsuleHash}`);
      }

    } catch (error) {
      this.logger.error('Error processing alert:', error);
      // Don't throw to avoid failing the entire webhook
    }
  }
}