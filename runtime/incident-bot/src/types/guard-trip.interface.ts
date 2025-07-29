export interface GuardTrip {
  capsuleHash: string;
  tenantId: string;
  riskScore: number;
  heartbeatMisses: number;
  ts: string;
  eventType: 'guard_trip';
  reason?: string;
  metadata?: Record<string, any>;
}

export interface AlertmanagerAlert {
  version: string;
  groupKey: string;
  truncatedAlerts: number;
  status: string;
  receiver: string;
  groupLabels: Record<string, string>;
  commonLabels: Record<string, string>;
  commonAnnotations: Record<string, string>;
  externalURL: string;
  alerts: Alert[];
}

export interface Alert {
  status: string;
  labels: Record<string, string>;
  annotations: Record<string, string>;
  startsAt: string;
  endsAt: string;
  generatorURL: string;
  fingerprint: string;
}

export interface RollbackDecision {
  shouldRollback: boolean;
  reason: string;
  targetRelease?: string;
  capsuleHash?: string;
  tenantId?: string;
  riskScore?: number;
  heartbeatMisses?: number;
}