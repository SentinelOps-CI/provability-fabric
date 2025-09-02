import { Injectable, Logger } from '@nestjs/common';
import { ConfigService } from '@nestjs/config';
import axios from 'axios';

export interface Alert {
  labels: Record<string, string>;
  annotations: Record<string, string>;
  startsAt: string;
  endsAt?: string;
  generatorURL?: string;
}

export interface AlertmanagerWebhook {
  version: string;
  groupKey: string;
  status: 'firing' | 'resolved';
  receiver: string;
  groupLabels: Record<string, string>;
  commonLabels: Record<string, string>;
  commonAnnotations: Record<string, string>;
  externalURL: string;
  alerts: Alert[];
}

@Injectable()
export class AlertmanagerService {
  private readonly logger = new Logger(AlertmanagerService.name);
  private readonly alertmanagerUrl: string;

  constructor(private configService: ConfigService) {
    this.alertmanagerUrl = this.configService.get<string>('ALERTMANAGER_URL', 'http://localhost:9093');
  }

  async processWebhook(webhook: AlertmanagerWebhook): Promise<void> {
    this.logger.log(`Processing webhook with ${webhook.alerts.length} alerts (${webhook.status})`);
    
    for (const alert of webhook.alerts) {
      await this.processAlert(alert, webhook.status);
    }
  }

  private async processAlert(alert: Alert, status: 'firing' | 'resolved'): Promise<void> {
    const severity = alert.labels.severity || 'unknown';
    const alertname = alert.labels.alertname || 'unknown';
    
    this.logger.log(`Processing ${status} alert: ${alertname} (severity: ${severity})`);

    if (status === 'firing') {
      await this.handleFiringAlert(alert);
    } else {
      await this.handleResolvedAlert(alert);
    }
  }

  private async handleFiringAlert(alert: Alert): Promise<void> {
    const severity = alert.labels.severity;
    const namespace = alert.labels.namespace;
    const deployment = alert.labels.deployment;

    switch (severity) {
      case 'critical':
        this.logger.warn(`Critical alert detected for ${deployment} in ${namespace}`);
        // Implement critical alert handling logic
        break;
      case 'warning':
        this.logger.warn(`Warning alert detected for ${deployment} in ${namespace}`);
        // Implement warning alert handling logic
        break;
      default:
        this.logger.log(`Alert detected: ${alert.labels.alertname}`);
    }
  }

  private async handleResolvedAlert(alert: Alert): Promise<void> {
    this.logger.log(`Alert resolved: ${alert.labels.alertname}`);
    // Implement resolved alert handling logic
  }

  async silenceAlert(alertId: string, duration: string): Promise<boolean> {
    try {
      const silenceData = {
        matchers: [
          {
            name: 'alertname',
            value: alertId,
            isRegex: false,
          },
        ],
        startsAt: new Date().toISOString(),
        endsAt: new Date(Date.now() + this.parseDuration(duration)).toISOString(),
        createdBy: 'incident-bot',
        comment: `Silenced by incident bot for ${duration}`,
      };

      const response = await axios.post(`${this.alertmanagerUrl}/api/v1/silences`, silenceData);
      this.logger.log(`Alert ${alertId} silenced for ${duration}`);
      return response.status === 200;
    } catch (error) {
      this.logger.error(`Failed to silence alert ${alertId}:`, error.message);
      return false;
    }
  }

  private parseDuration(duration: string): number {
    // Simple duration parser for formats like "1h", "30m", "2d"
    const match = duration.match(/^(\d+)([hmd])$/);
    if (!match) {
      return 3600000; // Default to 1 hour
    }

    const value = parseInt(match[1]);
    const unit = match[2];

    switch (unit) {
      case 'm':
        return value * 60 * 1000;
      case 'h':
        return value * 60 * 60 * 1000;
      case 'd':
        return value * 24 * 60 * 60 * 1000;
      default:
        return 3600000; // Default to 1 hour
    }
  }
}
