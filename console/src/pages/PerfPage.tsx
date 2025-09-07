import React from 'react';
import { useQuery } from 'react-query';
import { getRuntimeSLO } from '../services/api';
import { BoltIcon, ChartBarIcon } from '@heroicons/react/24/outline';

interface SLOResponse {
  latency: { p50: number; p95: number; p99: number };
  tps: number;
  error_rate: number;
  cert_validation_failures: number;
  sidecar_decision_latency: number;
  egress_write_latency: number;
  timestamp: string;
}

export default function PerfPage() {
  const { data, isLoading, refetch } = useQuery<SLOResponse>('runtime-slo', getRuntimeSLO);

  const p50 = data?.latency?.p50 ?? 0;
  const p95 = data?.latency?.p95 ?? 0;
  const p99 = data?.latency?.p99 ?? 0;
  const tps = data?.tps ?? 0;

  return (
    <div className="space-y-6">
      <div className="md:flex md:items-center md:justify-between">
        <div className="flex-1 min-w-0">
          <h2 className="text-2xl font-bold leading-7 text-gray-900 sm:text-3xl sm:truncate">
            Performance HUD
          </h2>
          <p className="mt-1 text-sm text-gray-500">P50/P95/P99 latency and TPS. Matches CLI: `so perf smoke`.</p>
        </div>
        <div className="mt-4 flex md:mt-0 md:ml-4">
          <button
            onClick={() => refetch()}
            className="inline-flex items-center px-4 py-2 border border-gray-300 rounded-md shadow-sm text-sm font-medium text-gray-700 bg-white hover:bg-gray-50"
          >
            <BoltIcon className="h-4 w-4 mr-2" /> Refresh
          </button>
        </div>
      </div>

      <div className="grid grid-cols-1 md:grid-cols-4 gap-6">
        <MetricCard title="P50" value={`${p50.toFixed(1)}ms`} icon={<ChartBarIcon className="h-6 w-6 text-gray-400" />} />
        <MetricCard title="P95" value={`${p95.toFixed(1)}ms`} icon={<ChartBarIcon className="h-6 w-6 text-gray-400" />} />
        <MetricCard title="P99" value={`${p99.toFixed(1)}ms`} icon={<ChartBarIcon className="h-6 w-6 text-gray-400" />} />
        <MetricCard title="TPS" value={`${Math.round(tps)}`} icon={<BoltIcon className="h-6 w-6 text-gray-400" />} />
      </div>

      {isLoading && (
        <div className="text-sm text-gray-500">Loading SLO metrics...</div>
      )}

      <div className="text-xs text-gray-400">Last updated: {data?.timestamp ? new Date(data.timestamp).toLocaleString() : '—'}</div>
    </div>
  );
}

function MetricCard({ title, value, icon }: { title: string; value: string; icon: React.ReactNode }) {
  return (
    <div className="bg-white overflow-hidden shadow rounded-lg">
      <div className="p-5">
        <div className="flex items-center">
          <div className="flex-shrink-0">{icon}</div>
          <div className="ml-5 w-0 flex-1">
            <dl>
              <dt className="text-sm font-medium text-gray-500 truncate">{title}</dt>
              <dd className="text-2xl font-semibold text-gray-900">{value}</dd>
            </dl>
          </div>
        </div>
      </div>
    </div>
  );
}
