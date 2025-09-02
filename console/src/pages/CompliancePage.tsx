import React, { useState } from 'react';
import {
  ShieldCheckIcon,
  DocumentArrowDownIcon,
  ChartBarIcon,
  LockClosedIcon,
} from '@heroicons/react/24/outline';

interface ComplianceMetrics {
  rls_isolation_blocks: number;
  audit_chain_integrity: number;
  cross_tenant_violations: number;
  compliance_rate: number;
  total_decisions: number;
  policy_violations: number;
}

interface EvidencePack {
  pack_id: string;
  name: string;
  tenant_id: string;
  policy_hash: string;
  date_range: string;
  certificate_count: number;
  compliance_rate: number;
  created_at: string;
  size_mb: number;
}

export default function CompliancePage() {
  const [selectedPack, setSelectedPack] = useState<EvidencePack | null>(null);

  // Mock compliance metrics
  const [metrics] = useState<ComplianceMetrics>({
    rls_isolation_blocks: 1247,
    audit_chain_integrity: 100,
    cross_tenant_violations: 0,
    compliance_rate: 99.85,
    total_decisions: 125000,
    policy_violations: 187,
  });

  // Mock evidence packs
  const [evidencePacks] = useState<EvidencePack[]>([
    {
      pack_id: 'pack_2025_01_q1',
      name: 'Q1 2025 Compliance Pack',
      tenant_id: 'acme-corp',
      policy_hash: 'a1b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef12345678',
      date_range: '2025-01-01 to 2025-03-31',
      certificate_count: 45230,
      compliance_rate: 99.92,
      created_at: '2025-01-27T10:30:00Z',
      size_mb: 156.7,
    },
    {
      pack_id: 'pack_2024_12_monthly',
      name: 'December 2024 Monthly Pack',
      tenant_id: 'acme-corp',
      policy_hash: 'b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef1234567890ab',
      date_range: '2024-12-01 to 2024-12-31',
      certificate_count: 38950,
      compliance_rate: 99.88,
      created_at: '2025-01-01T00:00:00Z',
      size_mb: 134.2,
    },
  ]);

  const handleDownloadPack = (pack: EvidencePack) => {
    // In production, this would download the compliance pack
    console.log('Downloading compliance pack:', pack.pack_id);
  };

  const handleExportCompliance = (format: 'pdf' | 'json' | 'csv') => {
    // In production, this would export compliance data in specified format
    console.log('Exporting compliance data as:', format);
  };

  const getComplianceColor = (rate: number) => {
    if (rate >= 99.9) return 'text-green-600';
    if (rate >= 99.0) return 'text-yellow-600';
    return 'text-red-600';
  };

  return (
    <div className="space-y-6">
      <div className="md:flex md:items-center md:justify-between">
        <div className="flex-1 min-w-0">
          <h2 className="text-2xl font-bold leading-7 text-gray-900 sm:text-3xl sm:truncate">
            Compliance
          </h2>
          <p className="mt-1 text-sm text-gray-500">
            Monitor compliance metrics, manage evidence packs, and export reports
          </p>
        </div>
        <div className="mt-4 flex space-x-2 md:mt-0 md:ml-4">
          <button
            onClick={() => handleExportCompliance('pdf')}
            className="inline-flex items-center px-4 py-2 border border-gray-300 rounded-md shadow-sm text-sm font-medium text-gray-700 bg-white hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
          >
            <DocumentArrowDownIcon className="h-4 w-4 mr-2" />
            Export PDF
          </button>
        </div>
      </div>

      {/* Compliance Metrics */}
      <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-6">
        <div className="bg-white overflow-hidden shadow rounded-lg">
          <div className="p-5">
            <div className="flex items-center">
              <div className="flex-shrink-0">
                <ShieldCheckIcon className="h-6 w-6 text-gray-400" />
              </div>
              <div className="ml-5 w-0 flex-1">
                <dl>
                  <dt className="text-sm font-medium text-gray-500 truncate">
                    Compliance Rate
                  </dt>
                  <dd className={`text-lg font-medium ${getComplianceColor(metrics.compliance_rate)}`}>
                    {metrics.compliance_rate.toFixed(2)}%
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
                <LockClosedIcon className="h-6 w-6 text-gray-400" />
              </div>
              <div className="ml-5 w-0 flex-1">
                <dl>
                  <dt className="text-sm font-medium text-gray-500 truncate">
                    RLS Isolation
                  </dt>
                  <dd className="text-lg font-medium text-green-600">
                    {metrics.rls_isolation_blocks.toLocaleString()}
                  </dd>
                  <dd className="text-xs text-gray-500">
                    Blocks prevented
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
                <ChartBarIcon className="h-6 w-6 text-gray-400" />
              </div>
              <div className="ml-5 w-0 flex-1">
                <dl>
                  <dt className="text-sm font-medium text-gray-500 truncate">
                    Audit Integrity
                  </dt>
                  <dd className="text-lg font-medium text-green-600">
                    {metrics.audit_chain_integrity}%
                  </dd>
                  <dd className="text-xs text-gray-500">
                    Chain verified
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
                    Cross-Tenant Violations
                  </dt>
                  <dd className={`text-lg font-medium ${metrics.cross_tenant_violations === 0 ? 'text-green-600' : 'text-red-600'}`}>
                    {metrics.cross_tenant_violations}
                  </dd>
                </dl>
              </div>
            </div>
          </div>
        </div>
      </div>

      {/* Evidence Packs */}
      <div className="bg-white shadow rounded-lg">
        <div className="px-4 py-5 sm:p-6">
          <h3 className="text-lg font-medium text-gray-900 mb-4">Evidence Packs</h3>
          <div className="space-y-4">
            {evidencePacks.map((pack) => (
              <div key={pack.pack_id} className="border border-gray-200 rounded-lg p-4">
                <div className="flex items-center justify-between">
                  <div className="flex-1">
                    <h4 className="text-sm font-medium text-gray-900">{pack.name}</h4>
                    <div className="mt-1 grid grid-cols-2 md:grid-cols-4 gap-4 text-xs text-gray-500">
                      <div>
                        <span className="font-medium">Tenant:</span> {pack.tenant_id}
                      </div>
                      <div>
                        <span className="font-medium">Period:</span> {pack.date_range}
                      </div>
                      <div>
                        <span className="font-medium">Certificates:</span> {pack.certificate_count.toLocaleString()}
                      </div>
                      <div>
                        <span className="font-medium">Size:</span> {pack.size_mb.toFixed(1)} MB
                      </div>
                    </div>
                    <div className="mt-2 flex items-center space-x-4 text-xs text-gray-500">
                      <div>
                        <span className="font-medium">Compliance Rate:</span> 
                        <span className={`ml-1 ${getComplianceColor(pack.compliance_rate)}`}>
                          {pack.compliance_rate.toFixed(2)}%
                        </span>
                      </div>
                      <div>
                        <span className="font-medium">Created:</span> {new Date(pack.created_at).toLocaleDateString()}
                      </div>
                    </div>
                  </div>
                  <div className="ml-4">
                    <button
                      onClick={() => handleDownloadPack(pack)}
                      className="inline-flex items-center px-3 py-2 border border-transparent text-sm font-medium rounded-md text-white bg-blue-600 hover:bg-blue-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
                    >
                      <DocumentArrowDownIcon className="h-4 w-4 mr-2" />
                      Download
                    </button>
                  </div>
                </div>
              </div>
            ))}
          </div>
        </div>
      </div>

      {/* Compliance Summary */}
      <div className="bg-white shadow rounded-lg">
        <div className="px-4 py-5 sm:p-6">
          <h3 className="text-lg font-medium text-gray-900 mb-4">Compliance Summary</h3>
          <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
            <div>
              <h4 className="text-sm font-medium text-gray-700 mb-2">Key Metrics</h4>
              <div className="space-y-2 text-sm">
                <div className="flex justify-between">
                  <span>Total Decisions Processed:</span>
                  <span className="font-medium">{metrics.total_decisions.toLocaleString()}</span>
                </div>
                <div className="flex justify-between">
                  <span>Policy Violations:</span>
                  <span className="font-medium text-red-600">{metrics.policy_violations}</span>
                </div>
                <div className="flex justify-between">
                  <span>RLS Isolation Effective:</span>
                  <span className="font-medium text-green-600">Yes</span>
                </div>
                <div className="flex justify-between">
                  <span>Audit Chain Status:</span>
                  <span className="font-medium text-green-600">Verified</span>
                </div>
              </div>
            </div>
            
            <div>
              <h4 className="text-sm font-medium text-gray-700 mb-2">Export Options</h4>
              <div className="space-y-2">
                <button
                  onClick={() => handleExportCompliance('pdf')}
                  className="w-full inline-flex items-center justify-center px-3 py-2 border border-gray-300 text-sm font-medium rounded-md text-gray-700 bg-white hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
                >
                  PCI/SOX Compliance PDF
                </button>
                <button
                  onClick={() => handleExportCompliance('json')}
                  className="w-full inline-flex items-center justify-center px-3 py-2 border border-gray-300 text-sm font-medium rounded-md text-gray-700 bg-white hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
                >
                  Basel III JSON Export
                </button>
                <button
                  onClick={() => handleExportCompliance('csv')}
                  className="w-full inline-flex items-center justify-center px-3 py-2 border border-gray-300 text-sm font-medium rounded-md text-gray-700 bg-white hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
                >
                  Audit Trail CSV
                </button>
              </div>
            </div>
          </div>
        </div>
      </div>
    </div>
  );
}