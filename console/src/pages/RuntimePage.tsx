import React, { useState, useEffect } from 'react';
import { useQuery } from 'react-query';
import {
  CpuChipIcon,
  ClockIcon,
  ExclamationTriangleIcon,
  ArrowPathIcon,
  DocumentCheckIcon,
} from '@heroicons/react/24/outline';
import { getRuntimeSLO, rotateEpoch } from '../services/api';

interface SLOMetrics {
  latency_p50: number;
  latency_p95: number;
  latency_p99: number;
  tps: number;
  error_rate: number;
  cert_validation_failures: number;
  sidecar_decision_latency: number;
  egress_write_latency: number;
}

interface EpochInfo {
  current_epoch: number;
  policy_hash: string;
  automata_hash: string;
  created_at: string;
  last_rotated_by: string;
}

export default function RuntimePage() {
  const [epochInfo, setEpochInfo] = useState<EpochInfo>({
    current_epoch: 42,
    policy_hash: 'a1b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef12345678',
    automata_hash: 'b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef1234567890ab',
    created_at: '2025-01-27T10:30:00Z',
    last_rotated_by: 'admin@example.com',
  });

  const [sloMetrics, setSloMetrics] = useState<SLOMetrics>({
    latency_p50: 1.2,
    latency_p95: 2.8,
    latency_p99: 4.1,
    tps: 1250,
    error_rate: 0.02,
    cert_validation_failures: 0,
    sidecar_decision_latency: 1.8,
    egress_write_latency: 0.8,
  });

  // Simulate real-time updates
  useEffect(() => {
    const interval = setInterval(() => {
      setSloMetrics(prev => ({
        ...prev,
        latency_p50: prev.latency_p50 + (Math.random() - 0.5) * 0.2,
        latency_p95: prev.latency_p95 + (Math.random() - 0.5) * 0.4,
        latency_p99: prev.latency_p99 + (Math.random() - 0.5) * 0.6,
        tps: prev.tps + Math.floor((Math.random() - 0.5) * 100),
        error_rate: Math.max(0, prev.error_rate + (Math.random() - 0.5) * 0.01),
        sidecar_decision_latency: prev.sidecar_decision_latency + (Math.random() - 0.5) * 0.2,
        egress_write_latency: prev.egress_write_latency + (Math.random() - 0.5) * 0.1,
      }));
    }, 2000);

    return () => clearInterval(interval);
  }, []);

  const handleRotateEpoch = () => {
    const newEpoch = epochInfo.current_epoch + 1;
    setEpochInfo(prev => ({
      ...prev,
      current_epoch: newEpoch,
      created_at: new Date().toISOString(),
      last_rotated_by: 'current_user@example.com',
    }));
  };

  const getSLOStatus = (metric: number, threshold: number) => {
    return metric <= threshold ? 'good' : 'warning';
  };

  const getStatusColor = (status: string) => {
    switch (status) {
      case 'good': return 'text-green-600';
      case 'warning': return 'text-yellow-600';
      case 'critical': return 'text-red-600';
      default: return 'text-gray-600';
    }
  };

  return (
    <div className="space-y-6">
      <div className="md:flex md:items-center md:justify-between">
        <div className="flex-1 min-w-0">
          <h2 className="text-2xl font-bold leading-7 text-gray-900 sm:text-3xl sm:truncate">
            Runtime
          </h2>
          <p className="mt-1 text-sm text-gray-500">
            Monitor SLOs, manage epochs, and track system performance
          </p>
        </div>
      </div>

      {/* SLO Cards */}
      <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-6">
        <div className="bg-white overflow-hidden shadow rounded-lg">
          <div className="p-5">
            <div className="flex items-center">
              <div className="flex-shrink-0">
                <ClockIcon className="h-6 w-6 text-gray-400" />
              </div>
              <div className="ml-5 w-0 flex-1">
                <dl>
                  <dt className="text-sm font-medium text-gray-500 truncate">
                    Latency P95
                  </dt>
                  <dd className={`text-lg font-medium ${getStatusColor(getSLOStatus(sloMetrics.latency_p95, 2.0))}`}>
                    {sloMetrics.latency_p95.toFixed(1)}ms
                  </dd>
                  <dd className="text-xs text-gray-500">
                    Target: &lt; 2ms
                  </dd>
                </dl>
              </div>
            </div>
          </div>
        </div>

        <div className="bg-white overflow-hidden shadow rounded-lg">
          <div className="p-5">
            <div className="flex items-center">
              <div className="flex-shrink-0">
                <CpuChipIcon className="h-6 w-6 text-gray-400" />
              </div>
              <div className="ml-5 w-0 flex-1">
                <dl>
                  <dt className="text-sm font-medium text-gray-500 truncate">
                    Transactions/sec
                  </dt>
                  <dd className="text-lg font-medium text-gray-900">
                    {sloMetrics.tps.toLocaleString()}
                  </dd>
                </dl>
              </div>
            </div>
          </div>
        </div>

        <div className="bg-white overflow-hidden shadow rounded-lg">
          <div className="p-5">
            <div className="flex items-center">
              <div className="flex-shrink-0">
                <ExclamationTriangleIcon className="h-6 w-6 text-gray-400" />
              </div>
              <div className="ml-5 w-0 flex-1">
                <dl>
                  <dt className="text-sm font-medium text-gray-500 truncate">
                    Error Rate
                  </dt>
                  <dd className={`text-lg font-medium ${getStatusColor(getSLOStatus(sloMetrics.error_rate, 0.05))}`}>
                    {(sloMetrics.error_rate * 100).toFixed(2)}%
                  </dd>
                </dl>
              </div>
            </div>
          </div>
        </div>

        <div className="bg-white overflow-hidden shadow rounded-lg">
          <div className="p-5">
            <div className="flex items-center">
              <div className="flex-shrink-0">
                <DocumentCheckIcon className="h-6 w-6 text-gray-400" />
              </div>
              <div className="ml-5 w-0 flex-1">
                <dl>
                  <dt className="text-sm font-medium text-gray-500 truncate">
                    Cert Failures
                  </dt>
                  <dd className={`text-lg font-medium ${sloMetrics.cert_validation_failures > 0 ? 'text-red-600' : 'text-green-600'}`}>
                    {sloMetrics.cert_validation_failures}
                  </dd>
                </dl>
              </div>
            </div>
          </div>
        </div>
      </div>

      {/* Detailed Metrics */}
      <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
        <div className="bg-white shadow rounded-lg p-6">
          <h3 className="text-lg font-medium text-gray-900 mb-4">Sidecar Performance</h3>
          <div className="space-y-4">
            <div className="flex justify-between">
              <span className="text-sm text-gray-600">Decision Latency (P95)</span>
              <span className={`text-sm font-medium ${getStatusColor(getSLOStatus(sloMetrics.sidecar_decision_latency, 2.0))}`}>
                {sloMetrics.sidecar_decision_latency.toFixed(1)}ms
              </span>
            </div>
            <div className="flex justify-between">
              <span className="text-sm text-gray-600">Egress Write Latency</span>
              <span className={`text-sm font-medium ${getStatusColor(getSLOStatus(sloMetrics.egress_write_latency, 1.0))}`}>
                {sloMetrics.egress_write_latency.toFixed(1)}ms
              </span>
            </div>
            <div className="flex justify-between">
              <span className="text-sm text-gray-600">Latency P50</span>
              <span className="text-sm font-medium text-gray-900">
                {sloMetrics.latency_p50.toFixed(1)}ms
              </span>
            </div>
            <div className="flex justify-between">
              <span className="text-sm text-gray-600">Latency P99</span>
              <span className="text-sm font-medium text-gray-900">
                {sloMetrics.latency_p99.toFixed(1)}ms
              </span>
            </div>
          </div>
        </div>

        <div className="bg-white shadow rounded-lg p-6">
          <h3 className="text-lg font-medium text-gray-900 mb-4">Epoch Management</h3>
          <div className="space-y-4">
            <div className="flex justify-between">
              <span className="text-sm text-gray-600">Current Epoch</span>
              <span className="text-sm font-medium text-gray-900">{epochInfo.current_epoch}</span>
            </div>
            <div className="flex justify-between">
              <span className="text-sm text-gray-600">Policy Hash</span>
              <span className="text-xs font-mono text-gray-600">
                {epochInfo.policy_hash.substring(0, 16)}...
              </span>
            </div>
            <div className="flex justify-between">
              <span className="text-sm text-gray-600">Last Rotated</span>
              <span className="text-sm text-gray-600">
                {new Date(epochInfo.created_at).toLocaleString()}
              </span>
            </div>
            <div className="flex justify-between">
              <span className="text-sm text-gray-600">Rotated By</span>
              <span className="text-sm text-gray-600">{epochInfo.last_rotated_by}</span>
            </div>
            <button
              onClick={handleRotateEpoch}
              className="w-full inline-flex items-center justify-center px-4 py-2 border border-transparent text-sm font-medium rounded-md text-white bg-blue-600 hover:bg-blue-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
            >
              <ArrowPathIcon className="h-4 w-4 mr-2" />
              Rotate Epoch
            </button>
          </div>
        </div>
      </div>

      {/* Alerts */}
      {(sloMetrics.cert_validation_failures > 0 || sloMetrics.latency_p95 > 2.0 || sloMetrics.error_rate > 0.05) && (
        <div className="bg-red-50 border border-red-200 rounded-md p-4">
          <div className="flex">
            <div className="flex-shrink-0">
              <ExclamationTriangleIcon className="h-5 w-5 text-red-400" />
            </div>
            <div className="ml-3">
              <h3 className="text-sm font-medium text-red-800">SLO Violations Detected</h3>
              <div className="mt-2 text-sm text-red-700">
                <ul className="list-disc pl-5 space-y-1">
                  {sloMetrics.cert_validation_failures > 0 && (
                    <li>Certificate validation failures detected ({sloMetrics.cert_validation_failures})</li>
                  )}
                  {sloMetrics.latency_p95 > 2.0 && (
                    <li>Latency P95 exceeds 2ms threshold ({sloMetrics.latency_p95.toFixed(1)}ms)</li>
                  )}
                  {sloMetrics.error_rate > 0.05 && (
                    <li>Error rate exceeds 5% threshold ({(sloMetrics.error_rate * 100).toFixed(2)}%)</li>
                  )}
                </ul>
              </div>
            </div>
          </div>
        </div>
      )}
    </div>
  );
}