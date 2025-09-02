import React, { useState } from 'react';
import { useQuery } from 'react-query';
import {
  PlayIcon,
  ClockIcon,
  CheckCircleIcon,
  XCircleIcon,
  DocumentArrowDownIcon,
} from '@heroicons/react/24/outline';

interface ReplayJob {
  job_id: string;
  status: 'running' | 'completed' | 'failed';
  progress: number;
  low_view_match_pct: number;
  outputs: string[];
  artifacts: string[];
  started_at: string;
  completed_at?: string;
  execution_time_ms: number;
  drift_detected: boolean;
  error_message?: string;
}

export default function ReplayPage() {
  const [selectedJob, setSelectedJob] = useState<ReplayJob | null>(null);

  // Mock replay jobs for demo
  const [replayJobs] = useState<ReplayJob[]>([
    {
      job_id: 'replay_1706355000_1234',
      status: 'completed',
      progress: 1.0,
      low_view_match_pct: 0.9995,
      outputs: ['permission_check:call:decision_abc123', 'tool_call:fraud_scorer:result_def456'],
      artifacts: ['lowview_report.json', 'execution.log'],
      started_at: '2025-01-27T10:30:00Z',
      completed_at: '2025-01-27T10:30:05Z',
      execution_time_ms: 5234,
      drift_detected: false,
    },
    {
      job_id: 'replay_1706355100_5678',
      status: 'running',
      progress: 0.65,
      low_view_match_pct: 0.0,
      outputs: [],
      artifacts: [],
      started_at: '2025-01-27T10:31:40Z',
      execution_time_ms: 0,
      drift_detected: false,
    },
    {
      job_id: 'replay_1706355200_9012',
      status: 'failed',
      progress: 0.3,
      low_view_match_pct: 0.0,
      outputs: [],
      artifacts: [],
      started_at: '2025-01-27T10:33:20Z',
      completed_at: '2025-01-27T10:33:25Z',
      execution_time_ms: 5000,
      drift_detected: true,
      error_message: 'Trace file validation failed',
    },
  ]);

  const getStatusIcon = (status: string) => {
    switch (status) {
      case 'completed':
        return <CheckCircleIcon className="h-5 w-5 text-green-500" />;
      case 'failed':
        return <XCircleIcon className="h-5 w-5 text-red-500" />;
      case 'running':
        return <ClockIcon className="h-5 w-5 text-yellow-500" />;
      default:
        return <ClockIcon className="h-5 w-5 text-gray-500" />;
    }
  };

  const getStatusColor = (status: string) => {
    switch (status) {
      case 'completed': return 'bg-green-100 text-green-800';
      case 'failed': return 'bg-red-100 text-red-800';
      case 'running': return 'bg-yellow-100 text-yellow-800';
      default: return 'bg-gray-100 text-gray-800';
    }
  };

  const getMatchColor = (matchPct: number) => {
    if (matchPct >= 0.999) return 'text-green-600';
    if (matchPct >= 0.99) return 'text-yellow-600';
    return 'text-red-600';
  };

  const handleDownloadArtifact = (jobId: string, artifact: string) => {
    // In production, this would download from the replay service
    console.log(`Downloading artifact ${artifact} from job ${jobId}`);
  };

  return (
    <div className="space-y-6">
      <div className="md:flex md:items-center md:justify-between">
        <div className="flex-1 min-w-0">
          <h2 className="text-2xl font-bold leading-7 text-gray-900 sm:text-3xl sm:truncate">
            Replay
          </h2>
          <p className="mt-1 text-sm text-gray-500">
            Monitor replay jobs, track low-view equality, and download artifacts
          </p>
        </div>
      </div>

      {/* Replay Jobs */}
      <div className="bg-white shadow overflow-hidden sm:rounded-md">
        <ul className="divide-y divide-gray-200">
          {replayJobs.map((job) => (
            <li key={job.job_id}>
              <div className="px-4 py-4 sm:px-6">
                <div className="flex items-center justify-between">
                  <div className="flex-1">
                    <div className="flex items-center justify-between">
                      <div className="flex items-center">
                        {getStatusIcon(job.status)}
                        <p className="ml-2 text-sm font-medium text-gray-900">
                          {job.job_id}
                        </p>
                      </div>
                      <div className="ml-2 flex-shrink-0 flex">
                        <span className={`px-2 py-1 text-xs font-medium rounded-full ${getStatusColor(job.status)}`}>
                          {job.status}
                        </span>
                      </div>
                    </div>
                    
                    <div className="mt-2 grid grid-cols-2 md:grid-cols-4 gap-4 text-sm text-gray-500">
                      <div>
                        <span className="font-medium">Progress:</span> {(job.progress * 100).toFixed(1)}%
                      </div>
                      <div>
                        <span className="font-medium">Started:</span> {new Date(job.started_at).toLocaleString()}
                      </div>
                      {job.status === 'completed' && (
                        <>
                          <div>
                            <span className="font-medium">Match:</span> 
                            <span className={`ml-1 font-bold ${getMatchColor(job.low_view_match_pct)}`}>
                              {(job.low_view_match_pct * 100).toFixed(3)}%
                            </span>
                          </div>
                          <div>
                            <span className="font-medium">Duration:</span> {job.execution_time_ms}ms
                          </div>
                        </>
                      )}
                    </div>

                    {/* Progress Bar */}
                    {job.status === 'running' && (
                      <div className="mt-3">
                        <div className="bg-gray-200 rounded-full h-2">
                          <div
                            className="bg-blue-600 h-2 rounded-full transition-all duration-300"
                            style={{ width: `${job.progress * 100}%` }}
                          />
                        </div>
                      </div>
                    )}

                    {/* Error Message */}
                    {job.status === 'failed' && job.error_message && (
                      <div className="mt-2 p-2 bg-red-50 rounded text-sm text-red-700">
                        {job.error_message}
                      </div>
                    )}

                    {/* Drift Detection */}
                    {job.drift_detected && (
                      <div className="mt-2 p-2 bg-yellow-50 rounded text-sm text-yellow-700">
                        ⚠️ Execution drift detected - low-view match below threshold
                      </div>
                    )}
                  </div>
                </div>
                
                {/* Artifacts */}
                {job.artifacts.length > 0 && (
                  <div className="mt-4">
                    <h4 className="text-sm font-medium text-gray-900 mb-2">Artifacts</h4>
                    <div className="flex flex-wrap gap-2">
                      {job.artifacts.map((artifact, index) => (
                        <button
                          key={index}
                          onClick={() => handleDownloadArtifact(job.job_id, artifact)}
                          className="inline-flex items-center px-2 py-1 border border-gray-300 text-xs font-medium rounded text-gray-700 bg-white hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
                        >
                          <DocumentArrowDownIcon className="h-3 w-3 mr-1" />
                          {artifact}
                        </button>
                      ))}
                    </div>
                  </div>
                )}

                {/* Outputs */}
                {job.outputs.length > 0 && selectedJob?.job_id === job.job_id && (
                  <div className="mt-4 p-4 bg-gray-50 rounded-md">
                    <h4 className="text-sm font-medium text-gray-900 mb-2">Replay Outputs</h4>
                    <div className="space-y-1">
                      {job.outputs.map((output, index) => (
                        <div key={index} className="text-xs font-mono text-gray-600">
                          {index + 1}. {output}
                        </div>
                      ))}
                    </div>
                  </div>
                )}

                {job.outputs.length > 0 && (
                  <button
                    onClick={() => setSelectedJob(selectedJob?.job_id === job.job_id ? null : job)}
                    className="mt-2 text-xs text-blue-600 hover:text-blue-500"
                  >
                    {selectedJob?.job_id === job.job_id ? 'Hide' : 'Show'} Outputs
                  </button>
                )}
              </div>
            </li>
          ))}
        </ul>
      </div>

      {/* Replay Guidelines */}
      <div className="bg-blue-50 border border-blue-200 rounded-md p-4">
        <h3 className="text-sm font-medium text-blue-800 mb-2">Replay Quality Guidelines</h3>
        <div className="text-xs text-blue-700 space-y-1">
          <p>• Target low-view match: ≥99.9%</p>
          <p>• Alert threshold: &lt;99.9% indicates potential drift</p>
          <p>• Deterministic execution ensures reproducible results</p>
          <p>• All replays use fixed seeds, locale, and timezone</p>
        </div>
      </div>
    </div>
  );
}