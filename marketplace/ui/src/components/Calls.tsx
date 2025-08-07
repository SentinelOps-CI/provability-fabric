import React, { useState, useEffect } from 'react';
import { Card, CardContent, CardHeader, CardTitle } from './ui/card';
import { Button } from './ui/button';
import { Badge } from './ui/badge';
import { ExternalLink, Shield, Clock, User, Hash } from 'lucide-react';

interface Plan {
  plan_id: string;
  tenant: string;
  subject: {
    id: string;
    caps: string[];
  };
  steps: Array<{
    tool: string;
    args: Record<string, any>;
    caps_required: string[];
    labels_in: string[];
    labels_out: string[];
  }>;
  constraints: {
    budget: number;
    pii: boolean;
    dp_epsilon: number;
    dp_delta?: number;
    latency_max?: number;
  };
  system_prompt_hash: string;
  created_at: string;
  expires_at: string;
}

interface Receipt {
  receipt_id: string;
  tenant: string;
  subject: string;
  query_hash: string;
  index_shard: string;
  timestamp: string;
  result_hash: string;
  signed: boolean;
}

interface EgressCert {
  cert_id: string;
  plan_id: string;
  tenant: string;
  detectors: {
    pii: number;
    secret: number;
    near_dupe: number;
  };
  policy_hash: string;
  text_hash: string;
  timestamp: string;
  signer: string;
}

interface CapabilityToken {
  token_id: string;
  tenant: string;
  subject: string;
  scopes: string[];
  expires_at: string;
  signed: boolean;
}

interface CallsProps {
  callId?: string;
}

export const Calls: React.FC<CallsProps> = ({ callId }) => {
  const [activeTab, setActiveTab] = useState<'plan' | 'evidence' | 'sources' | 'cert'>('plan');
  const [plan, setPlan] = useState<Plan | null>(null);
  const [receipts, setReceipts] = useState<Receipt[]>([]);
  const [certificates, setCertificates] = useState<EgressCert[]>([]);
  const [capabilities, setCapabilities] = useState<CapabilityToken[]>([]);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    // Mock data for now - in production would fetch from ledger API
    const mockPlan: Plan = {
      plan_id: callId || 'plan_abc123',
      tenant: 'tenant_001',
      subject: {
        id: 'user_123',
        caps: ['read_data', 'send_email', 'log_events']
      },
      steps: [
        {
          tool: 'SendEmail',
          args: { to: 'user@example.com', subject: 'Notification' },
          caps_required: ['send_email'],
          labels_in: ['public'],
          labels_out: ['notification_sent']
        }
      ],
      constraints: {
        budget: 50.0,
        pii: false,
        dp_epsilon: 0.1,
        dp_delta: 1e-6,
        latency_max: 2.0
      },
      system_prompt_hash: 'sha256:abc123def456...',
      created_at: new Date().toISOString(),
      expires_at: new Date(Date.now() + 3600000).toISOString()
    };

    setPlan(mockPlan);
    setReceipts([
      {
        receipt_id: 'receipt_001',
        tenant: 'tenant_001',
        subject: 'user_123',
        query_hash: 'query_hash_001',
        index_shard: 'shard_1',
        timestamp: new Date().toISOString(),
        result_hash: 'result_hash_001',
        signed: true
      }
    ]);
    setCertificates([
      {
        cert_id: 'cert_001',
        plan_id: mockPlan.plan_id,
        tenant: 'tenant_001',
        detectors: { pii: 0, secret: 0, near_dupe: 0.1 },
        policy_hash: 'policy_hash_001',
        text_hash: 'text_hash_001',
        timestamp: new Date().toISOString(),
        signer: 'egress_firewall'
      }
    ]);
    setCapabilities([
      {
        token_id: 'token_001',
        tenant: 'tenant_001',
        subject: 'user_123',
        scopes: ['read_data', 'send_email'],
        expires_at: new Date(Date.now() + 86400000).toISOString(),
        signed: true
      }
    ]);
    setLoading(false);
  }, [callId]);

  const formatTimestamp = (timestamp: string) => {
    return new Date(timestamp).toLocaleString();
  };

  const tabs = [
    { id: 'plan', label: 'Plan', icon: Hash },
    { id: 'evidence', label: 'Evidence', icon: Shield },
    { id: 'sources', label: 'Sources', icon: ExternalLink },
    { id: 'cert', label: 'Cert', icon: User }
  ];

  if (loading) {
    return <div className="flex justify-center items-center h-64">Loading...</div>;
  }

  return (
    <div className="space-y-6">
      <Card>
        <CardHeader>
          <CardTitle className="flex items-center space-x-2">
            <Hash className="h-5 w-5" />
            <span>Call Details: {callId || 'Current Call'}</span>
          </CardTitle>
        </CardHeader>
        <CardContent>
          <div className="flex space-x-1 mb-6 bg-gray-100 p-1 rounded-lg">
            {tabs.map((tab) => {
              const Icon = tab.icon;
              return (
                <button
                  key={tab.id}
                  onClick={() => setActiveTab(tab.id as any)}
                  className={`flex items-center space-x-2 px-4 py-2 rounded-md transition-colors ${
                    activeTab === tab.id
                      ? 'bg-white text-blue-600 shadow-sm'
                      : 'text-gray-600 hover:text-gray-900'
                  }`}
                >
                  <Icon className="h-4 w-4" />
                  <span>{tab.label}</span>
                </button>
              );
            })}
          </div>

          {activeTab === 'plan' && plan && (
            <div className="space-y-4">
              <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
                <div>
                  <h4 className="font-semibold text-gray-700 mb-2">Plan Metadata</h4>
                  <div className="space-y-2 text-sm">
                    <div><strong>ID:</strong> {plan.plan_id}</div>
                    <div><strong>Tenant:</strong> {plan.tenant}</div>
                    <div><strong>Subject:</strong> {plan.subject.id}</div>
                    <div><strong>Created:</strong> {formatTimestamp(plan.created_at)}</div>
                    <div><strong>Expires:</strong> {formatTimestamp(plan.expires_at)}</div>
                  </div>
                </div>
                <div>
                  <h4 className="font-semibold text-gray-700 mb-2">Constraints</h4>
                  <div className="space-y-2 text-sm">
                    <div><strong>Budget:</strong> ${plan.constraints.budget}</div>
                    <div><strong>PII Allowed:</strong> {plan.constraints.pii ? 'Yes' : 'No'}</div>
                    <div><strong>DP Epsilon:</strong> {plan.constraints.dp_epsilon}</div>
                    {plan.constraints.latency_max && (
                      <div><strong>Max Latency:</strong> {plan.constraints.latency_max}s</div>
                    )}
                  </div>
                </div>
              </div>

              <div>
                <h4 className="font-semibold text-gray-700 mb-2">Subject Capabilities</h4>
                <div className="flex flex-wrap gap-2">
                  {plan.subject.caps.map((cap, index) => (
                    <Badge key={index} variant="secondary">{cap}</Badge>
                  ))}
                </div>
              </div>

              <div>
                <h4 className="font-semibold text-gray-700 mb-2">Execution Steps</h4>
                {plan.steps.map((step, index) => (
                  <Card key={index} className="mb-3">
                    <CardContent className="pt-4">
                      <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
                        <div>
                          <div className="text-sm"><strong>Tool:</strong> {step.tool}</div>
                          <div className="text-sm mt-2"><strong>Required Caps:</strong></div>
                          <div className="flex flex-wrap gap-1 mt-1">
                            {step.caps_required.map((cap, i) => (
                              <Badge key={i} variant="outline" className="text-xs">{cap}</Badge>
                            ))}
                          </div>
                        </div>
                        <div>
                          <div className="text-sm"><strong>Labels In:</strong></div>
                          <div className="flex flex-wrap gap-1 mt-1">
                            {step.labels_in.map((label, i) => (
                              <Badge key={i} variant="secondary" className="text-xs">{label}</Badge>
                            ))}
                          </div>
                          <div className="text-sm mt-2"><strong>Labels Out:</strong></div>
                          <div className="flex flex-wrap gap-1 mt-1">
                            {step.labels_out.map((label, i) => (
                              <Badge key={i} variant="secondary" className="text-xs">{label}</Badge>
                            ))}
                          </div>
                        </div>
                      </div>
                    </CardContent>
                  </Card>
                ))}
              </div>

              <div className="flex space-x-3">
                <Button variant="outline" size="sm">
                  <ExternalLink className="h-4 w-4 mr-2" />
                  View Lean Proof
                </Button>
                <Badge variant={plan.constraints.pii ? "destructive" : "default"} className="self-center">
                  <Shield className="h-3 w-3 mr-1" />
                  {plan.constraints.pii ? "PII Allowed" : "PII Protected"}
                </Badge>
              </div>
            </div>
          )}

          {activeTab === 'evidence' && (
            <div className="space-y-4">
              <h4 className="font-semibold text-gray-700">Evidence Chain</h4>
              
              {/* Trusted/Untrusted Channel Badges */}
              <div className="flex space-x-4 mb-4">
                <Badge variant="default" className="bg-green-100 text-green-800">
                  <Shield className="h-3 w-3 mr-1" />
                  Trusted Channel
                </Badge>
                <Badge variant="secondary" className="bg-yellow-100 text-yellow-800">
                  <User className="h-3 w-3 mr-1" />
                  Untrusted Channel
                </Badge>
              </div>

              {/* Evidence Items */}
              <div className="space-y-3">
                <Card>
                  <CardContent className="pt-4">
                    <div className="flex justify-between items-start">
                      <div>
                        <h5 className="font-medium">Kernel Decision</h5>
                        <p className="text-sm text-gray-600">Plan validation completed</p>
                      </div>
                      <Badge variant="default" className="bg-green-100 text-green-800">
                        PASS
                      </Badge>
                    </div>
                    <div className="mt-2 text-sm">
                      <div><strong>Reason:</strong> ALL_CHECKS_PASSED</div>
                      <div><strong>Timestamp:</strong> {formatTimestamp(new Date().toISOString())}</div>
                    </div>
                  </CardContent>
                </Card>

                <Card>
                  <CardContent className="pt-4">
                    <div className="flex justify-between items-start">
                      <div>
                        <h5 className="font-medium">Receipt Validation</h5>
                        <p className="text-sm text-gray-600">Access receipt verified</p>
                      </div>
                      <Badge variant="default" className="bg-green-100 text-green-800">
                        PASS
                      </Badge>
                    </div>
                    <div className="mt-2 text-sm">
                      <div><strong>Receipt ID:</strong> receipt_20241201_001</div>
                      <div><strong>Hash:</strong> sha256:abc123...</div>
                    </div>
                  </CardContent>
                </Card>

                <Card>
                  <CardContent className="pt-4">
                    <div className="flex justify-between items-start">
                      <div>
                        <h5 className="font-medium">Non-Interference Check</h5>
                        <p className="text-sm text-gray-600">NI verdict computed</p>
                      </div>
                      <Badge variant="default" className="bg-green-100 text-green-800">
                        PASS
                      </Badge>
                    </div>
                    <div className="mt-2 text-sm">
                      <div><strong>Verdict:</strong> passed</div>
                      <div><strong>Confidence:</strong> 0.95</div>
                    </div>
                  </CardContent>
                </Card>
              </div>
            </div>
          )}

          {activeTab === 'sources' && (
            <div className="space-y-4">
              <h4 className="font-semibold text-gray-700">Receipt IDs & Hashes</h4>
              
              <div className="space-y-3">
                {receipts.map((receipt, index) => (
                  <Card key={receipt.receipt_id}>
                    <CardContent className="pt-4">
                      <div className="flex justify-between items-start">
                        <div className="flex-1">
                          <h5 className="font-medium">Receipt {index + 1}</h5>
                          <div className="mt-2 space-y-1 text-sm">
                            <div><strong>ID:</strong> {receipt.receipt_id}</div>
                            <div><strong>Hash:</strong> {receipt.query_hash}</div>
                            <div><strong>Timestamp:</strong> {formatTimestamp(receipt.timestamp)}</div>
                          </div>
                        </div>
                        <Button 
                          variant="outline" 
                          size="sm"
                          onClick={() => navigator.clipboard.writeText(receipt.receipt_id)}
                        >
                          Copy ID
                        </Button>
                      </div>
                    </CardContent>
                  </Card>
                ))}
              </div>

              <div className="mt-6">
                <h5 className="font-medium mb-3">System Hashes</h5>
                <div className="space-y-2">
                  <div className="flex justify-between items-center p-2 bg-gray-50 rounded">
                    <span className="text-sm">System Prompt Hash</span>
                    <div className="flex items-center space-x-2">
                      <code className="text-xs">{plan?.system_prompt_hash.substring(0, 16)}...</code>
                      <Button 
                        variant="outline" 
                        size="sm"
                        onClick={() => navigator.clipboard.writeText(plan?.system_prompt_hash || '')}
                      >
                        Copy
                      </Button>
                    </div>
                  </div>
                  <div className="flex justify-between items-center p-2 bg-gray-50 rounded">
                    <span className="text-sm">Policy Hash</span>
                    <div className="flex items-center space-x-2">
                      <code className="text-xs">sha256:def456...</code>
                      <Button 
                        variant="outline" 
                        size="sm"
                        onClick={() => navigator.clipboard.writeText('sha256:def456...')}
                      >
                        Copy
                      </Button>
                    </div>
                  </div>
                </div>
              </div>
            </div>
          )}

          {activeTab === 'cert' && (
            <div className="space-y-4">
              <h4 className="font-semibold text-gray-700">Egress Certificate</h4>
              
              {/* NI Passed/Failed Badge */}
              <div className="mb-4">
                <Badge variant="default" className="bg-green-100 text-green-800">
                  <Shield className="h-3 w-3 mr-1" />
                  NI Passed
                </Badge>
              </div>

              {certificates.map((cert) => (
                <Card key={cert.cert_id}>
                  <CardContent className="pt-4">
                    <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
                      <div className="space-y-2 text-sm">
                        <div><strong>Certificate ID:</strong> {cert.cert_id}</div>
                        <div><strong>Plan ID:</strong> {cert.plan_id}</div>
                        <div><strong>Policy Hash:</strong> {cert.policy_hash.substring(0, 16)}...</div>
                        <div><strong>Signer:</strong> {cert.signer}</div>
                      </div>
                      <div className="space-y-2 text-sm">
                        <div><strong>Timestamp:</strong> {formatTimestamp(cert.timestamp)}</div>
                        <div><strong>Text Hash:</strong> {cert.text_hash.substring(0, 16)}...</div>
                        <div className="space-y-1">
                          <strong>Detectors:</strong>
                          <div className="flex space-x-3">
                            <Badge variant={cert.detectors.pii > 0 ? "destructive" : "default"}>
                              PII: {cert.detectors.pii}
                            </Badge>
                            <Badge variant={cert.detectors.secret > 0 ? "destructive" : "default"}>
                              Secret: {cert.detectors.secret}
                            </Badge>
                            <Badge variant={cert.detectors.near_dupe > 0.5 ? "secondary" : "default"}>
                              Similarity: {(cert.detectors.near_dupe * 100).toFixed(1)}%
                            </Badge>
                          </div>
                        </div>
                      </div>
                    </div>
                  </CardContent>
                </Card>
              ))}
            </div>
          )}
        </CardContent>
      </Card>
    </div>
  );
};