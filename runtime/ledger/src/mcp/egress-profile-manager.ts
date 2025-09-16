/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * Egress Profile Manager for MCP Fraud Prevention
 * Implements deterministic egress profile for explanations with timeline visualization
 */

import winston from 'winston';

export interface EgressProfile {
  chunkSize: number;
  flushIntervalMs: number;
  locale: string;
  timezone: string;
  maxRetries: number;
  compressionEnabled: boolean;
  encryptionEnabled: boolean;
}

export interface DecisionEvent {
  eventId: string;
  timestamp: Date;
  eventType: 'input_received' | 'validation_started' | 'validation_completed' | 
            'policy_check' | 'tool_execution' | 'decision_made' | 'output_generated';
  details: {
    toolName?: string;
    tenantId?: string;
    userId?: string;
    toolSignature?: string;
    validationResult?: any;
    policyResult?: any;
    decision?: any;
    outputSize?: number;
    processingTimeMs?: number;
  };
  metadata: {
    requestId: string;
    sessionId: string;
    version: string;
  };
}

export interface TimelineEntry {
  timestamp: Date;
  event: DecisionEvent;
  duration?: number; // Duration from previous event
  cumulativeTime?: number; // Total time from start
}

export interface ExplanationProfile {
  profileId: string;
  tenantId: string;
  decisionId: string;
  timeline: TimelineEntry[];
  egressProfile: EgressProfile;
  totalProcessingTime: number;
  decisionSummary: {
    toolName: string;
    decision: string;
    confidence: number;
    riskFactors: string[];
    complianceChecks: string[];
  };
  auditTrail: {
    certificates: string[];
    signatures: string[];
    policyHashes: string[];
  };
}

export class EgressProfileManager {
  private logger: winston.Logger;
  private profiles: Map<string, EgressProfile> = new Map();
  private explanations: Map<string, ExplanationProfile> = new Map();
  private activeTimelines: Map<string, TimelineEntry[]> = new Map();

  // Standard egress profiles for different use cases
  private readonly STANDARD_PROFILES = {
    fraud_detection: {
      chunkSize: 1024,
      flushIntervalMs: 100,
      locale: 'en-US',
      timezone: 'UTC',
      maxRetries: 3,
      compressionEnabled: true,
      encryptionEnabled: true
    },
    compliance_audit: {
      chunkSize: 2048,
      flushIntervalMs: 200,
      locale: 'en-US',
      timezone: 'UTC',
      maxRetries: 5,
      compressionEnabled: false,
      encryptionEnabled: true
    },
    real_time_monitoring: {
      chunkSize: 512,
      flushIntervalMs: 50,
      locale: 'en-US',
      timezone: 'UTC',
      maxRetries: 2,
      compressionEnabled: true,
      encryptionEnabled: false
    }
  };

  constructor(logger: winston.Logger) {
    this.logger = logger;
    this.initializeStandardProfiles();
  }

  /**
   * Pin chunk size/flush ms/locale/tz for deterministic egress
   */
  public createEgressProfile(
    profileName: string,
    customProfile?: Partial<EgressProfile>
  ): EgressProfile {
    const baseProfile = this.STANDARD_PROFILES[profileName as keyof typeof this.STANDARD_PROFILES] || 
                       this.STANDARD_PROFILES.fraud_detection;
    
    const profile: EgressProfile = {
      ...baseProfile,
      ...customProfile
    };

    this.profiles.set(profileName, profile);
    
    this.logger.info('MCP: Egress profile created', {
      profileName,
      chunkSize: profile.chunkSize,
      flushIntervalMs: profile.flushIntervalMs,
      locale: profile.locale,
      timezone: profile.timezone
    });

    return profile;
  }

  /**
   * Start timeline tracking for a decision
   */
  public startDecisionTimeline(
    requestId: string,
    sessionId: string,
    tenantId: string,
    toolName: string
  ): string {
    const decisionId = `decision_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
    const timeline: TimelineEntry[] = [];

    // Initial event
    const startEvent: DecisionEvent = {
      eventId: `event_${Date.now()}_start`,
      timestamp: new Date(),
      eventType: 'input_received',
      details: {
        toolName,
        tenantId,
        requestId
      },
      metadata: {
        requestId,
        sessionId,
        version: '1.0.0'
      }
    };

    timeline.push({
      timestamp: startEvent.timestamp,
      event: startEvent,
      duration: 0,
      cumulativeTime: 0
    });

    this.activeTimelines.set(decisionId, timeline);

    this.logger.info('MCP: Decision timeline started', {
      decisionId,
      requestId,
      sessionId,
      tenantId,
      toolName
    });

    return decisionId;
  }

  /**
   * Add event to timeline
   */
  public addTimelineEvent(
    decisionId: string,
    eventType: DecisionEvent['eventType'],
    details: DecisionEvent['details']
  ): void {
    const timeline = this.activeTimelines.get(decisionId);
    if (!timeline) {
      this.logger.warn('MCP: Timeline not found for decision', { decisionId });
      return;
    }

    const now = new Date();
    const previousEvent = timeline[timeline.length - 1];
    const duration = previousEvent ? now.getTime() - previousEvent.timestamp.getTime() : 0;
    const cumulativeTime = timeline.length > 0 ? 
      (timeline[timeline.length - 1].cumulativeTime || 0) + duration : 0;

    const event: DecisionEvent = {
      eventId: `event_${Date.now()}_${eventType}`,
      timestamp: now,
      eventType,
      details,
      metadata: {
        requestId: details.requestId || '',
        sessionId: details.sessionId || '',
        version: '1.0.0'
      }
    };

    const timelineEntry: TimelineEntry = {
      timestamp: now,
      event,
      duration,
      cumulativeTime
    };

    timeline.push(timelineEntry);

    this.logger.debug('MCP: Timeline event added', {
      decisionId,
      eventType,
      duration,
      cumulativeTime
    });
  }

  /**
   * Complete timeline and create explanation profile
   */
  public completeDecisionTimeline(
    decisionId: string,
    tenantId: string,
    decisionSummary: ExplanationProfile['decisionSummary'],
    auditTrail: ExplanationProfile['auditTrail'],
    profileName: string = 'fraud_detection'
  ): ExplanationProfile {
    const timeline = this.activeTimelines.get(decisionId);
    if (!timeline) {
      throw new Error(`Timeline not found for decision: ${decisionId}`);
    }

    const egressProfile = this.profiles.get(profileName) || this.STANDARD_PROFILES.fraud_detection;
    const totalProcessingTime = timeline.length > 0 ? 
      (timeline[timeline.length - 1].cumulativeTime || 0) : 0;

    const explanation: ExplanationProfile = {
      profileId: `profile_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
      tenantId,
      decisionId,
      timeline: [...timeline], // Copy timeline
      egressProfile,
      totalProcessingTime,
      decisionSummary,
      auditTrail
    };

    this.explanations.set(decisionId, explanation);
    this.activeTimelines.delete(decisionId);

    this.logger.info('MCP: Decision timeline completed', {
      decisionId,
      profileId: explanation.profileId,
      totalProcessingTime,
      eventCount: timeline.length
    });

    return explanation;
  }

  /**
   * Generate timeline visualization for fraud analysts
   */
  public generateTimelineVisualization(decisionId: string): {
    timeline: TimelineEntry[];
    summary: {
      totalEvents: number;
      totalTime: number;
      criticalPath: string[];
      bottlenecks: string[];
    };
    visualization: {
      chart: any; // Chart.js compatible data
      timeline: any; // Timeline.js compatible data
    };
  } {
    const explanation = this.explanations.get(decisionId);
    if (!explanation) {
      throw new Error(`Explanation not found for decision: ${decisionId}`);
    }

    const timeline = explanation.timeline;
    const totalEvents = timeline.length;
    const totalTime = explanation.totalProcessingTime;

    // Identify critical path
    const criticalPath = timeline
      .filter(entry => 
        entry.event.eventType === 'validation_started' ||
        entry.event.eventType === 'policy_check' ||
        entry.event.eventType === 'tool_execution' ||
        entry.event.eventType === 'decision_made'
      )
      .map(entry => entry.event.eventType);

    // Identify bottlenecks (events with long duration)
    const bottlenecks = timeline
      .filter(entry => entry.duration && entry.duration > 1000) // > 1 second
      .map(entry => ({
        eventType: entry.event.eventType,
        duration: entry.duration,
        timestamp: entry.timestamp
      }));

    // Generate chart data
    const chartData = {
      labels: timeline.map(entry => entry.event.eventType),
      datasets: [{
        label: 'Processing Time (ms)',
        data: timeline.map(entry => entry.duration || 0),
        backgroundColor: timeline.map(entry => this.getEventColor(entry.event.eventType)),
        borderColor: timeline.map(entry => this.getEventColor(entry.event.eventType)),
        borderWidth: 1
      }]
    };

    // Generate timeline data
    const timelineData = timeline.map(entry => ({
      id: entry.event.eventId,
      content: this.formatEventContent(entry.event),
      start: entry.timestamp.toISOString(),
      group: entry.event.eventType,
      className: `timeline-event ${entry.event.eventType}`,
      duration: entry.duration
    }));

    return {
      timeline,
      summary: {
        totalEvents,
        totalTime,
        criticalPath,
        bottlenecks: bottlenecks.map(b => `${b.eventType} (${b.duration}ms)`)
      },
      visualization: {
        chart: chartData,
        timeline: timelineData
      }
    };
  }

  /**
   * Get deterministic egress parameters
   */
  public getEgressParameters(profileName: string): EgressProfile {
    const profile = this.profiles.get(profileName);
    if (!profile) {
      throw new Error(`Egress profile not found: ${profileName}`);
    }

    return { ...profile }; // Return copy
  }

  /**
   * Show timeline in Console for fraud analysts
   */
  public generateConsoleOutput(decisionId: string): string {
    const explanation = this.explanations.get(decisionId);
    if (!explanation) {
      return `No explanation found for decision: ${decisionId}`;
    }

    const timeline = explanation.timeline;
    const summary = explanation.decisionSummary;

    let output = `
=== FRAUD ANALYSIS TIMELINE ===
Decision ID: ${decisionId}
Profile ID: ${explanation.profileId}
Tenant ID: ${explanation.tenantId}
Total Processing Time: ${explanation.totalProcessingTime}ms

=== DECISION SUMMARY ===
Tool: ${summary.toolName}
Decision: ${summary.decision}
Confidence: ${(summary.confidence * 100).toFixed(1)}%
Risk Factors: ${summary.riskFactors.join(', ')}
Compliance Checks: ${summary.complianceChecks.join(', ')}

=== TIMELINE EVENTS ===
`;

    timeline.forEach((entry, index) => {
      const duration = entry.duration ? ` (+${entry.duration}ms)` : '';
      const cumulative = entry.cumulativeTime ? ` [${entry.cumulativeTime}ms]` : '';
      
      output += `${index + 1}. ${entry.timestamp.toISOString()}${duration}${cumulative}\n`;
      output += `   Event: ${entry.event.eventType}\n`;
      
      if (entry.event.details.toolName) {
        output += `   Tool: ${entry.event.details.toolName}\n`;
      }
      if (entry.event.details.processingTimeMs) {
        output += `   Processing Time: ${entry.event.details.processingTimeMs}ms\n`;
      }
      if (entry.event.details.decision) {
        output += `   Decision: ${JSON.stringify(entry.event.details.decision)}\n`;
      }
      
      output += '\n';
    });

    output += `=== AUDIT TRAIL ===
Certificates: ${explanation.auditTrail.certificates.length}
Signatures: ${explanation.auditTrail.signatures.length}
Policy Hashes: ${explanation.auditTrail.policyHashes.length}
`;

    return output;
  }

  /**
   * Get event color for visualization
   */
  private getEventColor(eventType: DecisionEvent['eventType']): string {
    const colors = {
      'input_received': '#4CAF50',
      'validation_started': '#2196F3',
      'validation_completed': '#2196F3',
      'policy_check': '#FF9800',
      'tool_execution': '#9C27B0',
      'decision_made': '#F44336',
      'output_generated': '#4CAF50'
    };
    return colors[eventType] || '#757575';
  }

  /**
   * Format event content for timeline
   */
  private formatEventContent(event: DecisionEvent): string {
    let content = `<strong>${event.eventType.replace('_', ' ').toUpperCase()}</strong>`;
    
    if (event.details.toolName) {
      content += `<br/>Tool: ${event.details.toolName}`;
    }
    if (event.details.processingTimeMs) {
      content += `<br/>Time: ${event.details.processingTimeMs}ms`;
    }
    if (event.details.decision) {
      content += `<br/>Decision: ${JSON.stringify(event.details.decision)}`;
    }

    return content;
  }

  /**
   * Initialize standard profiles
   */
  private initializeStandardProfiles(): void {
    for (const [name, profile] of Object.entries(this.STANDARD_PROFILES)) {
      this.profiles.set(name, profile);
    }

    this.logger.info('MCP: Standard egress profiles initialized', {
      profileCount: Object.keys(this.STANDARD_PROFILES).length
    });
  }

  /**
   * Get statistics for monitoring
   */
  public getStats(): {
    activeProfiles: number;
    completedExplanations: number;
    activeTimelines: number;
    profileTypes: string[];
  } {
    return {
      activeProfiles: this.profiles.size,
      completedExplanations: this.explanations.size,
      activeTimelines: this.activeTimelines.size,
      profileTypes: Array.from(this.profiles.keys())
    };
  }

  /**
   * Clean up old explanations
   */
  public cleanupOldExplanations(maxAgeHours: number = 24): void {
    const cutoff = new Date(Date.now() - maxAgeHours * 60 * 60 * 1000);
    let cleaned = 0;

    for (const [decisionId, explanation] of this.explanations.entries()) {
      const oldestEvent = explanation.timeline[0];
      if (oldestEvent && oldestEvent.timestamp < cutoff) {
        this.explanations.delete(decisionId);
        cleaned++;
      }
    }

    if (cleaned > 0) {
      this.logger.info('MCP: Cleaned up old explanations', { cleaned });
    }
  }
}

export default EgressProfileManager;
