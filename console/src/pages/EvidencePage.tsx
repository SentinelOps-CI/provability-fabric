import React, { useState } from 'react';
import { useQuery } from 'react-query';
import {
  MagnifyingGlassIcon,
  DocumentArrowDownIcon,
  PlayIcon,
  FunnelIcon,
} from '@heroicons/react/24/outline';
import { searchCertificates, downloadCompliancePacket, startReplay } from '../services/api';

interface Certificate {
  bundle_id: string;
  policy_hash: string;
  proof_hash: string;
  automata_hash: string;
  labeler_hash: string;
  ni_claim: string;
  ni_monitor: string;
  sidecar_build: string;
  tenant_id: string;
  session_id: string;
  timestamp: string;
  extensions?: {
    egress_profile?: string;
    permission_epoch?: number;
    permit_decision?: string;
    path_witness_ok?: boolean;
    label_derivation_ok?: boolean;
  };
}

interface SearchFilters {
  tenant_id: string;
  policy_hash: string;
  session_id: string;
  ni_monitor: string;
  start_time: string;
  end_time: string;
}

export default function EvidencePage() {
  const [searchFilters, setSearchFilters] = useState<SearchFilters>({
    tenant_id: '',
    policy_hash: '',
    session_id: '',
    ni_monitor: '',
    start_time: '',
    end_time: '',
  });
  
  const [selectedCert, setSelectedCert] = useState<Certificate | null>(null);
  const [showFilters, setShowFilters] = useState(false);

  // Mock certificates for demo
  const [certificates] = useState<Certificate[]>([
    {
      bundle_id: 'fraud-detection-v1',
      policy_hash: 'a1b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef12345678',
      proof_hash: 'b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef1234567890ab',
      automata_hash: 'c3d4e5f6789012345678901234567890abcdef1234567890abcdef1234567890abcd',
      labeler_hash: 'd4e5f6789012345678901234567890abcdef1234567890abcdef1234567890abcde',
      ni_claim: 'global_non_interference',
      ni_monitor: 'accept',
      sidecar_build: 'sidecar-v1.0.0',
      tenant_id: 'acme-corp',
      session_id: 'session_abc123',
      timestamp: '2025-01-27T10:30:00Z',
      extensions: {
        egress_profile: 'EGRESS-DET-P1@1.0',
        permission_epoch: 42,
        permit_decision: 'accept',
        path_witness_ok: true,
        label_derivation_ok: true,
      },
    },
    {
      bundle_id: 'fraud-detection-v1',
      policy_hash: 'a1b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef12345678',
      proof_hash: 'b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef1234567890ab',
      automata_hash: 'c3d4e5f6789012345678901234567890abcdef1234567890abcdef1234567890abcd',
      labeler_hash: 'd4e5f6789012345678901234567890abcdef1234567890abcdef1234567890abcde',
      ni_claim: 'global_non_interference',
      ni_monitor: 'reject',
      sidecar_build: 'sidecar-v1.0.0',
      tenant_id: 'acme-corp',
      session_id: 'session_def456',
      timestamp: '2025-01-27T10:31:00Z',
      extensions: {
        egress_profile: 'EGRESS-DET-P1@1.0',
        permission_epoch: 42,
        permit_decision: 'reject',
        path_witness_ok: false,
        label_derivation_ok: true,
      },
    },
  ]);

  const filteredCertificates = certificates.filter(cert => {
    if (searchFilters.tenant_id && !cert.tenant_id.includes(searchFilters.tenant_id)) return false;
    if (searchFilters.policy_hash && !cert.policy_hash.includes(searchFilters.policy_hash)) return false;
    if (searchFilters.session_id && !cert.session_id.includes(searchFilters.session_id)) return false;
    if (searchFilters.ni_monitor && cert.ni_monitor !== searchFilters.ni_monitor) return false;
    return true;
  });

  const handleSearch = () => {
    // In production, this would trigger API call
    console.log('Searching with filters:', searchFilters);
  };

  const handleDownloadPacket = (cert: Certificate) => {
    // In production, this would call the compliance packet API
    console.log('Downloading compliance packet for:', cert.session_id);
  };

  const handleRunReplay = (cert: Certificate) => {
    // In production, this would start a replay job
    console.log('Starting replay for:', cert.session_id);
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

  return (
    <div className="space-y-6">
      <div className="md:flex md:items-center md:justify-between">
        <div className="flex-1 min-w-0">
          <h2 className="text-2xl font-bold leading-7 text-gray-900 sm:text-3xl sm:truncate">
            Evidence
          </h2>
          <p className="mt-1 text-sm text-gray-500">
            Browse certificates, run replays, and download compliance packets
          </p>
        </div>
        <div className="mt-4 flex md:mt-0 md:ml-4">
          <button
            onClick={() => setShowFilters(!showFilters)}
            className="inline-flex items-center px-4 py-2 border border-gray-300 rounded-md shadow-sm text-sm font-medium text-gray-700 bg-white hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
          >
            <FunnelIcon className="h-4 w-4 mr-2" />
            Filters
          </button>
        </div>
      </div>

      {/* Search Filters */}
      {showFilters && (
        <div className="bg-white shadow rounded-lg p-6">
          <h3 className="text-lg font-medium text-gray-900 mb-4">Search Filters</h3>
          <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Tenant ID
              </label>
              <input
                type="text"
                className="block w-full border-gray-300 rounded-md shadow-sm focus:ring-blue-500 focus:border-blue-500"
                value={searchFilters.tenant_id}
                onChange={(e) => setSearchFilters(prev => ({ ...prev, tenant_id: e.target.value }))}
                placeholder="e.g., acme-corp"
              />
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Policy Hash
              </label>
              <input
                type="text"
                className="block w-full border-gray-300 rounded-md shadow-sm focus:ring-blue-500 focus:border-blue-500"
                value={searchFilters.policy_hash}
                onChange={(e) => setSearchFilters(prev => ({ ...prev, policy_hash: e.target.value }))}
                placeholder="Hash prefix..."
              />
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                NI Monitor
              </label>
              <select
                className="block w-full border-gray-300 rounded-md shadow-sm focus:ring-blue-500 focus:border-blue-500"
                value={searchFilters.ni_monitor}
                onChange={(e) => setSearchFilters(prev => ({ ...prev, ni_monitor: e.target.value }))}
              >
                <option value="">All</option>
                <option value="accept">Accept</option>
                <option value="reject">Reject</option>
                <option value="error">Error</option>
                <option value="inapplicable">Inapplicable</option>
              </select>
            </div>
          </div>
          <div className="mt-4 flex space-x-2">
            <button
              onClick={handleSearch}
              className="inline-flex items-center px-4 py-2 border border-transparent text-sm font-medium rounded-md text-white bg-blue-600 hover:bg-blue-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
            >
              <MagnifyingGlassIcon className="h-4 w-4 mr-2" />
              Search
            </button>
            <button
              onClick={() => setSearchFilters({
                tenant_id: '', policy_hash: '', session_id: '', ni_monitor: '', start_time: '', end_time: ''
              })}
              className="inline-flex items-center px-4 py-2 border border-gray-300 text-sm font-medium rounded-md text-gray-700 bg-white hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
            >
              Clear
            </button>
          </div>
        </div>
      )}

      {/* Certificates List */}
      <div className="bg-white shadow overflow-hidden sm:rounded-md">
        <ul className="divide-y divide-gray-200">
          {filteredCertificates.map((cert) => (
            <li key={cert.session_id}>
              <div className="px-4 py-4 sm:px-6">
                <div className="flex items-center justify-between">
                  <div className="flex-1">
                    <div className="flex items-center justify-between">
                      <p className="text-sm font-medium text-blue-600 truncate">
                        {cert.session_id}
                      </p>
                      <div className="ml-2 flex-shrink-0 flex">
                        <span className={`px-2 py-1 text-xs font-medium rounded-full ${getMonitorStatusColor(cert.ni_monitor)}`}>
                          {cert.ni_monitor}
                        </span>
                      </div>
                    </div>
                    <div className="mt-2 grid grid-cols-2 gap-4 text-sm text-gray-500">
                      <div>
                        <span className="font-medium">Tenant:</span> {cert.tenant_id}
                      </div>
                      <div>
                        <span className="font-medium">Timestamp:</span> {new Date(cert.timestamp).toLocaleString()}
                      </div>
                      <div>
                        <span className="font-medium">Policy:</span> {cert.policy_hash.substring(0, 16)}...
                      </div>
                      <div>
                        <span className="font-medium">Bundle:</span> {cert.bundle_id}
                      </div>
                    </div>
                    
                    {/* Extensions */}
                    {cert.extensions && (
                      <div className="mt-2 grid grid-cols-2 gap-4 text-xs text-gray-400">
                        {cert.extensions.permit_decision && (
                          <div>
                            <span className="font-medium">Permit:</span> {cert.extensions.permit_decision}
                          </div>
                        )}
                        {cert.extensions.permission_epoch && (
                          <div>
                            <span className="font-medium">Epoch:</span> {cert.extensions.permission_epoch}
                          </div>
                        )}
                        {cert.extensions.path_witness_ok !== undefined && (
                          <div>
                            <span className="font-medium">Path Witness:</span> {cert.extensions.path_witness_ok ? '✓' : '✗'}
                          </div>
                        )}
                        {cert.extensions.label_derivation_ok !== undefined && (
                          <div>
                            <span className="font-medium">Label Derivation:</span> {cert.extensions.label_derivation_ok ? '✓' : '✗'}
                          </div>
                        )}
                      </div>
                    )}
                  </div>
                </div>
                
                {/* Action Buttons */}
                <div className="mt-4 flex space-x-2">
                  <button
                    onClick={() => setSelectedCert(selectedCert?.session_id === cert.session_id ? null : cert)}
                    className="inline-flex items-center px-3 py-1.5 border border-gray-300 text-xs font-medium rounded text-gray-700 bg-white hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
                  >
                    {selectedCert?.session_id === cert.session_id ? 'Hide' : 'View'} CERT
                  </button>
                  
                  <button
                    onClick={() => handleRunReplay(cert)}
                    className="inline-flex items-center px-3 py-1.5 border border-gray-300 text-xs font-medium rounded text-gray-700 bg-white hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
                  >
                    <PlayIcon className="h-3 w-3 mr-1" />
                    Replay
                  </button>
                  
                  <button
                    onClick={() => handleDownloadPacket(cert)}
                    className="inline-flex items-center px-3 py-1.5 border border-transparent text-xs font-medium rounded text-white bg-blue-600 hover:bg-blue-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
                  >
                    <DocumentArrowDownIcon className="h-3 w-3 mr-1" />
                    Download Packet
                  </button>
                </div>
                
                {/* Certificate Details */}
                {selectedCert?.session_id === cert.session_id && (
                  <div className="mt-4 p-4 bg-gray-50 rounded-md">
                    <h4 className="text-sm font-medium text-gray-900 mb-2">CERT-V1 Details</h4>
                    <pre className="text-xs text-gray-600 overflow-x-auto">
                      {JSON.stringify(cert, null, 2)}
                    </pre>
                  </div>
                )}
              </div>
            </li>
          ))}
        </ul>
      </div>

      {/* Summary Stats */}
      <div className="grid grid-cols-1 md:grid-cols-4 gap-6">
        <div className="bg-white overflow-hidden shadow rounded-lg">
          <div className="p-5">
            <div className="flex items-center">
              <div className="flex-shrink-0">
                <DocumentMagnifyingGlassIcon className="h-6 w-6 text-gray-400" />
              </div>
              <div className="ml-5 w-0 flex-1">
                <dl>
                  <dt className="text-sm font-medium text-gray-500 truncate">
                    Total Certificates
                  </dt>
                  <dd className="text-lg font-medium text-gray-900">
                    {filteredCertificates.length}
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
                <div className="h-6 w-6 bg-green-100 rounded-full flex items-center justify-center">
                  <span className="text-green-600 text-xs font-bold">✓</span>
                </div>
              </div>
              <div className="ml-5 w-0 flex-1">
                <dl>
                  <dt className="text-sm font-medium text-gray-500 truncate">
                    Accepted
                  </dt>
                  <dd className="text-lg font-medium text-green-600">
                    {filteredCertificates.filter(c => c.ni_monitor === 'accept').length}
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
                <div className="h-6 w-6 bg-red-100 rounded-full flex items-center justify-center">
                  <span className="text-red-600 text-xs font-bold">✗</span>
                </div>
              </div>
              <div className="ml-5 w-0 flex-1">
                <dl>
                  <dt className="text-sm font-medium text-gray-500 truncate">
                    Rejected
                  </dt>
                  <dd className="text-lg font-medium text-red-600">
                    {filteredCertificates.filter(c => c.ni_monitor === 'reject').length}
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
                <div className="h-6 w-6 bg-yellow-100 rounded-full flex items-center justify-center">
                  <span className="text-yellow-600 text-xs font-bold">!</span>
                </div>
              </div>
              <div className="ml-5 w-0 flex-1">
                <dl>
                  <dt className="text-sm font-medium text-gray-500 truncate">
                    Errors
                  </dt>
                  <dd className="text-lg font-medium text-yellow-600">
                    {filteredCertificates.filter(c => c.ni_monitor === 'error').length}
                  </dd>
                </dl>
              </div>
            </div>
          </div>
        </div>
      </div>
    </div>
  );
}