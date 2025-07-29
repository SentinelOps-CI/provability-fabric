import { Injectable, Logger } from '@nestjs/common';
import { ConfigService } from '@nestjs/config';
import { GuardTrip, RollbackDecision } from '../types/guard-trip.interface';
import { KubernetesService } from '../kubernetes/kubernetes.service';
import { MetricsService } from '../metrics/metrics.service';

@Injectable()
export class DecisionEngineService {
  private readonly logger = new Logger(DecisionEngineService.name);
  private readonly riskScoreThreshold: number;
  private readonly heartbeatMissesThreshold: number;

  constructor(
    private readonly configService: ConfigService,
    private readonly kubernetesService: KubernetesService,
    private readonly metricsService: MetricsService,
  ) {
    this.riskScoreThreshold = this.configService.get<number>('RISK_SCORE_THRESHOLD', 0.8);
    this.heartbeatMissesThreshold = this.configService.get<number>('HEARTBEAT_MISSES_THRESHOLD', 3);
  }

  async evaluateGuardTrip(guardTrip: GuardTrip): Promise<RollbackDecision> {
    const startTime = Date.now();
    
    try {
      this.logger.log(`Evaluating GuardTrip: risk=${guardTrip.riskScore}, misses=${guardTrip.heartbeatMisses}`);

      // Decision logic: rollback if high risk OR too many heartbeat misses
      const shouldRollback = 
        guardTrip.riskScore >= this.riskScoreThreshold || 
        guardTrip.heartbeatMisses >= this.heartbeatMissesThreshold;

      let reason = '';
      if (guardTrip.riskScore >= this.riskScoreThreshold) {
        reason = `high_risk_${guardTrip.capsuleHash}`;
      } else if (guardTrip.heartbeatMisses >= this.heartbeatMissesThreshold) {
        reason = `heartbeat_miss_${guardTrip.capsuleHash}`;
      }

      const decision: RollbackDecision = {
        shouldRollback,
        reason,
        targetRelease: shouldRollback ? await this.getLastStableRelease() : undefined,
        capsuleHash: guardTrip.capsuleHash,
        tenantId: guardTrip.tenantId,
        riskScore: guardTrip.riskScore,
        heartbeatMisses: guardTrip.heartbeatMisses,
      };

      // Record metrics
      this.metricsService.recordDecisionLatency(Date.now() - startTime);
      
      if (shouldRollback) {
        this.metricsService.incrementRollbacks(reason);
        this.logger.warn(`Rollback decision: ${reason} for capsule ${guardTrip.capsuleHash}`);
      } else {
        this.logger.log(`No rollback needed for capsule ${guardTrip.capsuleHash}`);
      }

      return decision;

    } catch (error) {
      this.logger.error('Error evaluating GuardTrip:', error);
      throw error;
    }
  }

  async executeRollback(decision: RollbackDecision): Promise<void> {
    if (!decision.shouldRollback || !decision.targetRelease) {
      this.logger.warn('Cannot execute rollback: invalid decision or missing target release');
      return;
    }

    try {
      this.logger.log(`Executing rollback to release ${decision.targetRelease} for reason: ${decision.reason}`);

      // Create Rollback CR
      const rollbackCr = {
        apiVersion: 'ops.prov-fabric.io/v1alpha1',
        kind: 'Rollback',
        metadata: {
          name: `rollback-${Date.now()}`,
          namespace: 'flux-system',
        },
        spec: {
          targetRelease: decision.targetRelease,
          reason: decision.reason,
          capsuleHash: decision.capsuleHash,
          tenantId: decision.tenantId,
        },
      };

      await this.kubernetesService.createRollback(rollbackCr);
      this.logger.log(`Rollback CR created successfully: ${rollbackCr.metadata.name}`);

    } catch (error) {
      this.logger.error('Failed to execute rollback:', error);
      throw error;
    }
  }

  private async getLastStableRelease(): Promise<string> {
    try {
      // Get the last stable release from Kubernetes
      const helmRelease = await this.kubernetesService.getHelmRelease('provability-fabric');
      
      if (!helmRelease) {
        throw new Error('HelmRelease not found');
      }

      // Get the previous revision from Helm history
      const history = await this.kubernetesService.getHelmReleaseHistory('provability-fabric');
      
      if (history && history.length > 1) {
        // Return the previous revision's image tag
        const previousRevision = history[1]; // Index 0 is current
        return previousRevision.chart?.metadata?.version || 'latest';
      }

      // Fallback to a default stable version
      return this.configService.get<string>('DEFAULT_STABLE_RELEASE', 'v0.1.0');

    } catch (error) {
      this.logger.error('Error getting last stable release:', error);
      return this.configService.get<string>('DEFAULT_STABLE_RELEASE', 'v0.1.0');
    }
  }

  getDecisionThresholds() {
    return {
      riskScoreThreshold: this.riskScoreThreshold,
      heartbeatMissesThreshold: this.heartbeatMissesThreshold,
    };
  }
}