import React, { useState, useEffect } from 'react';
import { useNavigate } from 'react-router-dom';
import { useQuery } from 'react-query';
import {
  MagnifyingGlassIcon,
  DocumentArrowDownIcon,
  PlayIcon,
  FunnelIcon,
  DocumentMagnifyingGlassIcon,
  ClockIcon,
  CheckCircleIcon,
  XCircleIcon,
  ExclamationTriangleIcon,
  ArrowPathIcon,
  StarIcon,
  EyeIcon,
  EyeSlashIcon,
} from '@heroicons/react/24/outline';
import { 
  searchCertificates, 
  downloadCompliancePacket, 
  startReplay, 
  verifyCertificate, 
  buildCompliancePacket, 
  sendTelemetryEvent, 
  downloadReplayArtifact,
  getCertificateDetails,
  promoteToGolden,
  getPolicyDiffAnalysis
} from '../services/api';
import toast from 'react-hot-toast';

// Enhanced certificate interfaces
interface CertV1Core {
  bundle_id: string;
  seq: number;
  policy_hash: string;
  proof_hash: string;
  automata_hash: string;
  labeler_hash: string;
  ni_monitor: string;
  epoch: number;
  reason_code: string;
  timestamp: number;
  tenant_id: string;
  session_id: string;
}

interface CertV1Extended {
  core: CertV1Core;
  reasoning: DecisionReasoning;
  blocked_spans: BlockedSpan[];
  detector_stats: DetectorStats;
  metadata: ExtendedMetadata;
}

interface DecisionReasoning {
  primary_reason: string;
  explanation: string;
  applied_rules: AppliedRule[];
  policy_references: PolicyReference[];
  confidence: number;
  factors: DecisionFactor[];
}

interface AppliedRule {
  rule_id: string;
  description: string;
  rule_type: string;
  matched: boolean;
  priority: number;
  conditions: string[];
}

interface PolicyReference {
  policy_id: string;
  version: string;
  section: string;
  reference_text: string;
}

interface DecisionFactor {
  name: string;
  value: string;
  weight: number;
  impact: string;
}

interface BlockedSpan {
  span_id: string;
  start: number;
  end: number;
  reason: string;
  block_type: string;
  confidence: number;
  original_content?: string;
  replacement_content?: string;
}

interface DetectorStats {
  pii_stats: PIIStats;
  secret_stats: SecretStats;
  malicious_stats: MaliciousStats;
  policy_violation_stats: PolicyViolationStats;
  summary: DetectionSummary;
}

interface PIIStats {
  detections: number;
  types_detected: string[];
  confidence_scores: number[];
  false_positive_rate: number;
}

interface SecretStats {
  detections: number;
  types_detected: string[];
  confidence_scores: number[];
  false_positive_rate: number;
}

interface MaliciousStats {
  detections: number;
  threat_types: string[];
  severity_scores: number[];
  false_positive_rate: number;
}

interface PolicyViolationStats {
  violations: number;
  violation_types: string[];
  severity_scores: number[];
  compliance_rate: number;
}

interface DetectionSummary {
  total_detections: number;
  high_confidence: number;
  medium_confidence: number;
  low_confidence: number;
  risk_score: number;
  recommended_action: string;
}

interface ExtendedMetadata {
  generated_at: number;
  processing_time_ms: number;
  sidecar_build: string;
  environment: Record<string, string>;
  context: Record<string, string>;
  version: string;
}

interface ReplayMetrics {
  low_view_match_pct: number;
  first_mismatch_index: number;
  total_steps: number;
  matching_steps: number;
  drift_detected: boolean;
  drift_magnitude: number;
  counterexample?: MinimalCounterexample;
  performance_metrics: PerformanceMetrics;
}

interface MinimalCounterexample {
  original_steps: ReplayStep[];
  minimal_prefix: ReplayStep[];
  shrinking_steps: number;
  reduction_ratio: number;
  mismatch_point: number;
  failure_reason: string;
  minimization_time: number;
}

interface ReplayStep {
  index: number;
  action: string;
  input: Record<string, any>;
  output: Record<string, any>;
  timestamp: number;
  metadata?: Record<string, any>;
}

interface PerformanceMetrics {
  execution_time_ms: number;
  memory_usage_mb: number;
  cpu_usage_percent: number;
  throughput_steps_per_second: number;
  latency_p50_ms: number;
  latency_p95_ms: number;
  latency_p99_ms: number;
}

interface SearchFilters {
  tenant_id: string;
  policy_hash: string;
  session_id: string;
  ni_monitor: string;
  start_time: string;
  end_time: string;
  limit: number;
}

interface VerifyResult {
  schema_valid?: boolean;
  signature_checked?: boolean;
  signature_valid?: boolean;
  code?: string;
  cause?: string;
  action?: string;
  docs_url?: string;
  errors?: string[];
}

export default function EnhancedEvidencePage() {
  const navigate = useNavigate();
  const [searchTerm, setSearchTerm] = useState('');
  const [showFilters, setShowFilters] = useState(false);
  const [selectedCertificate, setSelectedCertificate] = useState<CertV1Core | CertV1Extended | null>(null);
  const [showExtended, setShowExtended] = useState(false);
  const [replayMetrics, setReplayMetrics] = useState<ReplayMetrics | null>(null);
  const [isPromotingToGolden, setIsPromotingToGolden] = useState(false);

  const [filters, setFilters] = useState<SearchFilters>({
    tenant_id: '',
    policy_hash: '',
    session_id: '',
    ni_monitor: '',
    start_time: '',
    end_time: '',
    limit: 100,
  });

  // Search certificates query
  const { data: certificates, isLoading, refetch } = useQuery(
    ['certificates', filters],
    () => searchCertificates(filters),
    {
      enabled: true,
      refetchOnWindowFocus: false,
    }
  );

  // Get certificate details when selected
  const { data: certificateDetails, isLoading: isLoadingDetails } = useQuery(
    ['certificate-details', selectedCertificate?.bundle_id, selectedCertificate?.session_id],
    () => {
      if (!selectedCertificate) return null;
      return getCertificateDetails(selectedCertificate.bundle_id, selectedCertificate.session_id);
    },
    {
      enabled: !!selectedCertificate,
    }
  );

  const handleSearch = () => {
    refetch();
  };

  const handleFilterChange = (key: keyof SearchFilters, value: string | number) => {
    setFilters(prev => ({ ...prev, [key]: value }));
  };

  const handleCertificateSelect = async (cert: any) => {
    setSelectedCertificate(cert);
    setShowExtended(false);
    
    // Try to get extended certificate details
    try {
      const details = await getCertificateDetails(cert.bundle_id, cert.session_id);
      if (details && 'reasoning' in details) {
        setSelectedCertificate(details as CertV1Extended);
        setShowExtended(true);
      }
    } catch (error) {
      console.log('Extended certificate not available, showing core only');
    }
  };

  const handleRunReplay = async (cert: CertV1Core | CertV1Extended) => {
    const coreCert = 'core' in cert ? cert.core : cert;
    
    try {
      const replayJob = await startReplay({
        decision_id: coreCert.session_id,
        config: {
          seed: 42,
          locale: 'C',
          timezone: 'UTC',
          chunk_size: 4096,
          flush_cadence_ms: 100,
          padding_policy: 'fixed',
          drift_threshold: 0.001,
        },
        use_morph: false,
      });

      // Poll for completion
      const poll = async () => {
        try {
          const status = await fetch(`/api/v1/replay/${replayJob.job_id}`);
          const data = await status.json();
          
          if (data.status === 'completed') {
            setReplayMetrics(data.metrics);
            toast.success('Replay completed successfully');
          } else if (data.status === 'failed') {
            toast.error('Replay failed');
          } else {
            setTimeout(poll, 1000);
          }
        } catch (error) {
          toast.error('Failed to check replay status');
        }
      };
      
      setTimeout(poll, 1000);
      toast.success('Replay started');
    } catch (error) {
      toast.error('Failed to start replay');
    }
  };

  const handlePromoteToGolden = async (cert: CertV1Core | CertV1Extended) => {
    const coreCert = 'core' in cert ? cert.core : cert;
    
    setIsPromotingToGolden(true);
    try {
      await promoteToGolden(coreCert.session_id, 'test-vector.json');
      toast.success('Test vector promoted to golden');
    } catch (error) {
      toast.error('Failed to promote to golden');
    } finally {
      setIsPromotingToGolden(false);
    }
  };

  const getMonitorStatusColor = (status: string) => {
    switch (status) {
      case 'accept': return 'bg-green-100 text-green-800';
      case 'reject': return 'bg-red-100 text-red-800';
      case 'error': return 'bg-yellow-100 text-yellow-800';
      case 'inapplicable': return 'bg-gray-100 text-gray-800';
      default: return 'bg-gray-100 text-gray-800';
    }
  };

  const getMonitorStatusIcon = (status: string) => {
    switch (status) {
      case 'accept': return <CheckCircleIcon className="h-4 w-4" />;
      case 'reject': return <XCircleIcon className="h-4 w-4" />;
      case 'error': return <ExclamationTriangleIcon className="h-4 w-4" />;
      case 'inapplicable': return <ClockIcon className="h-4 w-4" />;
      default: return <ClockIcon className="h-4 w-4" />;
    }
  };

  return (
    <div className="space-y-6">
      <div className="md:flex md:items-center md:justify-between">
        <div className="flex-1 min-w-0">
          <h2 className="text-2xl font-bold leading-7 text-gray-900 sm:text-3xl sm:truncate">
            Enhanced Evidence
          </h2>
          <p className="mt-1 text-sm text-gray-500">
            Browse certificates with core/extended resolution, run replays, and manage test vectors
          </p>
        </div>
        <div className="mt-4 flex md:mt-0 md:ml-4 space-x-3">
          <button
            onClick={() => setShowFilters(!showFilters)}
            className="inline-flex items-center px-4 py-2 border border-gray-300 rounded-md shadow-sm text-sm font-medium text-gray-700 bg-white hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
          >
            <FunnelIcon className="h-4 w-4 mr-2" />
            Filters
          </button>
          <button
            onClick={handleSearch}
            className="inline-flex items-center px-4 py-2 border border-transparent rounded-md shadow-sm text-sm font-medium text-white bg-blue-600 hover:bg-blue-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
          >
            <MagnifyingGlassIcon className="h-4 w-4 mr-2" />
            Search
          </button>
        </div>
      </div>

      {/* Filters */}
      {showFilters && (
        <div className="bg-white p-4 rounded-lg border border-gray-200">
          <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
            <div>
              <label className="block text-sm font-medium text-gray-700">Tenant ID</label>
              <input
                type="text"
                value={filters.tenant_id}
                onChange={(e) => handleFilterChange('tenant_id', e.target.value)}
                className="mt-1 block w-full border-gray-300 rounded-md shadow-sm focus:ring-blue-500 focus:border-blue-500 sm:text-sm"
              />
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700">Policy Hash</label>
              <input
                type="text"
                value={filters.policy_hash}
                onChange={(e) => handleFilterChange('policy_hash', e.target.value)}
                className="mt-1 block w-full border-gray-300 rounded-md shadow-sm focus:ring-blue-500 focus:border-blue-500 sm:text-sm"
              />
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700">Session ID</label>
              <input
                type="text"
                value={filters.session_id}
                onChange={(e) => handleFilterChange('session_id', e.target.value)}
                className="mt-1 block w-full border-gray-300 rounded-md shadow-sm focus:ring-blue-500 focus:border-blue-500 sm:text-sm"
              />
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700">NI Monitor</label>
              <select
                value={filters.ni_monitor}
                onChange={(e) => handleFilterChange('ni_monitor', e.target.value)}
                className="mt-1 block w-full border-gray-300 rounded-md shadow-sm focus:ring-blue-500 focus:border-blue-500 sm:text-sm"
              >
                <option value="">All</option>
                <option value="accept">Accept</option>
                <option value="reject">Reject</option>
                <option value="error">Error</option>
                <option value="inapplicable">Inapplicable</option>
              </select>
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700">Start Time</label>
              <input
                type="datetime-local"
                value={filters.start_time}
                onChange={(e) => handleFilterChange('start_time', e.target.value)}
                className="mt-1 block w-full border-gray-300 rounded-md shadow-sm focus:ring-blue-500 focus:border-blue-500 sm:text-sm"
              />
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700">End Time</label>
              <input
                type="datetime-local"
                value={filters.end_time}
                onChange={(e) => handleFilterChange('end_time', e.target.value)}
                className="mt-1 block w-full border-gray-300 rounded-md shadow-sm focus:ring-blue-500 focus:border-blue-500 sm:text-sm"
              />
            </div>
          </div>
        </div>
      )}

      {/* Certificate List */}
      <div className="bg-white shadow overflow-hidden sm:rounded-md">
        <ul className="divide-y divide-gray-200">
          {isLoading ? (
            <li className="px-6 py-4">
              <div className="flex items-center justify-center">
                <ArrowPathIcon className="h-6 w-6 animate-spin text-gray-400" />
                <span className="ml-2 text-gray-500">Loading certificates...</span>
              </div>
            </li>
          ) : certificates?.certificates?.length > 0 ? (
            certificates.certificates.map((cert: any) => {
              const coreCert = cert.core || cert;
              const isExtended = 'reasoning' in cert;
              
              return (
                <li key={`${coreCert.bundle_id}-${coreCert.session_id}`}>
                  <div className="px-6 py-4 hover:bg-gray-50 cursor-pointer"
                       onClick={() => handleCertificateSelect(cert)}>
                    <div className="flex items-center justify-between">
                      <div className="flex items-center">
                        <div className="flex-shrink-0">
                          {isExtended ? (
                            <EyeIcon className="h-5 w-5 text-blue-500" />
                          ) : (
                            <EyeSlashIcon className="h-5 w-5 text-gray-400" />
                          )}
                        </div>
                        <div className="ml-4">
                          <div className="flex items-center">
                            <p className="text-sm font-medium text-gray-900">
                              {coreCert.bundle_id}
                            </p>
                            {isExtended && (
                              <span className="ml-2 inline-flex items-center px-2.5 py-0.5 rounded-full text-xs font-medium bg-blue-100 text-blue-800">
                                Extended
                              </span>
                            )}
                          </div>
                          <div className="flex items-center mt-1">
                            <span className={`inline-flex items-center px-2.5 py-0.5 rounded-full text-xs font-medium ${getMonitorStatusColor(coreCert.ni_monitor)}`}>
                              {getMonitorStatusIcon(coreCert.ni_monitor)}
                              <span className="ml-1">{coreCert.ni_monitor}</span>
                            </span>
                            <span className="ml-2 text-sm text-gray-500">
                              {coreCert.reason_code}
                            </span>
                          </div>
                        </div>
                      </div>
                      <div className="flex items-center space-x-2">
                        <button
                          onClick={(e) => {
                            e.stopPropagation();
                            handleRunReplay(cert);
                          }}
                          className="inline-flex items-center px-3 py-1 border border-gray-300 rounded-md text-sm font-medium text-gray-700 bg-white hover:bg-gray-50"
                        >
                          <PlayIcon className="h-4 w-4 mr-1" />
                          Replay
                        </button>
                        <button
                          onClick={(e) => {
                            e.stopPropagation();
                            handlePromoteToGolden(cert);
                          }}
                          disabled={isPromotingToGolden}
                          className="inline-flex items-center px-3 py-1 border border-gray-300 rounded-md text-sm font-medium text-gray-700 bg-white hover:bg-gray-50 disabled:opacity-50"
                        >
                          <StarIcon className="h-4 w-4 mr-1" />
                          {isPromotingToGolden ? 'Promoting...' : 'Promote to Golden'}
                        </button>
                      </div>
                    </div>
                  </div>
                </li>
              );
            })
          ) : (
            <li className="px-6 py-4">
              <div className="text-center text-gray-500">No certificates found</div>
            </li>
          )}
        </ul>
      </div>

      {/* Certificate Details Modal */}
      {selectedCertificate && (
        <div className="fixed inset-0 bg-gray-600 bg-opacity-50 overflow-y-auto h-full w-full z-50">
          <div className="relative top-20 mx-auto p-5 border w-11/12 md:w-3/4 lg:w-1/2 shadow-lg rounded-md bg-white">
            <div className="flex justify-between items-center mb-4">
              <h3 className="text-lg font-medium text-gray-900">
                Certificate Details
                {showExtended && ' (Extended)'}
              </h3>
              <button
                onClick={() => setSelectedCertificate(null)}
                className="text-gray-400 hover:text-gray-600"
              >
                <XCircleIcon className="h-6 w-6" />
              </button>
            </div>

            <div className="space-y-4">
              {/* Core Certificate Info */}
              <div>
                <h4 className="text-md font-medium text-gray-900 mb-2">Core Information</h4>
                <div className="bg-gray-50 p-4 rounded-md">
                  <dl className="grid grid-cols-2 gap-4">
                    <div>
                      <dt className="text-sm font-medium text-gray-500">Bundle ID</dt>
                      <dd className="text-sm text-gray-900">
                        {'core' in selectedCertificate ? selectedCertificate.core.bundle_id : selectedCertificate.bundle_id}
                      </dd>
                    </div>
                    <div>
                      <dt className="text-sm font-medium text-gray-500">Session ID</dt>
                      <dd className="text-sm text-gray-900">
                        {'core' in selectedCertificate ? selectedCertificate.core.session_id : selectedCertificate.session_id}
                      </dd>
                    </div>
                    <div>
                      <dt className="text-sm font-medium text-gray-500">NI Monitor</dt>
                      <dd className="text-sm text-gray-900">
                        {'core' in selectedCertificate ? selectedCertificate.core.ni_monitor : selectedCertificate.ni_monitor}
                      </dd>
                    </div>
                    <div>
                      <dt className="text-sm font-medium text-gray-500">Reason Code</dt>
                      <dd className="text-sm text-gray-900">
                        {'core' in selectedCertificate ? selectedCertificate.core.reason_code : selectedCertificate.reason_code}
                      </dd>
                    </div>
                  </dl>
                </div>
              </div>

              {/* Extended Certificate Info */}
              {showExtended && 'reasoning' in selectedCertificate && (
                <div>
                  <h4 className="text-md font-medium text-gray-900 mb-2">Extended Information</h4>
                  <div className="bg-blue-50 p-4 rounded-md">
                    <div className="mb-4">
                      <h5 className="text-sm font-medium text-gray-700">Decision Reasoning</h5>
                      <p className="text-sm text-gray-600 mt-1">{selectedCertificate.reasoning.explanation}</p>
                      <p className="text-sm text-gray-500 mt-1">Confidence: {(selectedCertificate.reasoning.confidence * 100).toFixed(1)}%</p>
                    </div>
                    
                    {selectedCertificate.blocked_spans.length > 0 && (
                      <div className="mb-4">
                        <h5 className="text-sm font-medium text-gray-700">Blocked Spans</h5>
                        <div className="mt-2 space-y-2">
                          {selectedCertificate.blocked_spans.map((span, index) => (
                            <div key={index} className="text-sm text-gray-600">
                              <span className="font-medium">{span.block_type}</span>: {span.reason} (confidence: {(span.confidence * 100).toFixed(1)}%)
                            </div>
                          ))}
                        </div>
                      </div>
                    )}

                    <div>
                      <h5 className="text-sm font-medium text-gray-700">Detector Statistics</h5>
                      <div className="mt-2 grid grid-cols-2 gap-4 text-sm">
                        <div>
                          <span className="text-gray-500">PII Detections:</span> {selectedCertificate.detector_stats.pii_stats.detections}
                        </div>
                        <div>
                          <span className="text-gray-500">Secret Detections:</span> {selectedCertificate.detector_stats.secret_stats.detections}
                        </div>
                        <div>
                          <span className="text-gray-500">Risk Score:</span> {(selectedCertificate.detector_stats.summary.risk_score * 100).toFixed(1)}%
                        </div>
                        <div>
                          <span className="text-gray-500">Recommended Action:</span> {selectedCertificate.detector_stats.summary.recommended_action}
                        </div>
                      </div>
                    </div>
                  </div>
                </div>
              )}

              {/* Replay Metrics */}
              {replayMetrics && (
                <div>
                  <h4 className="text-md font-medium text-gray-900 mb-2">Replay Analysis</h4>
                  <div className="bg-green-50 p-4 rounded-md">
                    <div className="grid grid-cols-2 gap-4 text-sm">
                      <div>
                        <span className="text-gray-500">Low-view Match:</span> {replayMetrics.low_view_match_pct.toFixed(1)}%
                      </div>
                      <div>
                        <span className="text-gray-500">First Mismatch:</span> {replayMetrics.first_mismatch_index}
                      </div>
                      <div>
                        <span className="text-gray-500">Drift Detected:</span> {replayMetrics.drift_detected ? 'Yes' : 'No'}
                      </div>
                      <div>
                        <span className="text-gray-500">Execution Time:</span> {replayMetrics.performance_metrics.execution_time_ms}ms
                      </div>
                    </div>
                    
                    {replayMetrics.counterexample && (
                      <div className="mt-4">
                        <h5 className="text-sm font-medium text-gray-700">Minimal Counterexample</h5>
                        <div className="mt-2 text-sm text-gray-600">
                          <p>Reduction Ratio: {(replayMetrics.counterexample.reduction_ratio * 100).toFixed(1)}%</p>
                          <p>Shrinking Steps: {replayMetrics.counterexample.shrinking_steps}</p>
                          <p>Failure Reason: {replayMetrics.counterexample.failure_reason}</p>
                        </div>
                      </div>
                    )}
                  </div>
                </div>
              )}
            </div>
          </div>
        </div>
      )}
    </div>
  );
}
