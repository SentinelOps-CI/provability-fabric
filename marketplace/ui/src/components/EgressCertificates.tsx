import React, { useState, useEffect } from 'react';
import { Card, CardContent, CardHeader, CardTitle } from './ui/card';
import { Badge } from './ui/badge';
import { Button } from './ui/button';
import { Search, Filter, Download, AlertTriangle, Shield, Eye, Clock } from 'lucide-react';

interface EgressCertificate {
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
  text_preview?: string;
  rule_fired?: string;
  severity: 'low' | 'medium' | 'high' | 'critical';
}

export const EgressCertificates: React.FC = () => {
  const [certificates, setCertificates] = useState<EgressCertificate[]>([]);
  const [loading, setLoading] = useState(true);
  const [searchTerm, setSearchTerm] = useState('');
  const [filterSeverity, setFilterSeverity] = useState<'all' | 'low' | 'medium' | 'high' | 'critical'>('all');
  const [selectedCert, setSelectedCert] = useState<EgressCertificate | null>(null);

  useEffect(() => {
    // Mock data - in production would fetch from ledger API
    const mockCertificates: EgressCertificate[] = [
      {
        cert_id: 'cert_001',
        plan_id: 'plan_abc123',
        tenant: 'tenant_001',
        detectors: { pii: 0, secret: 0, near_dupe: 0.1 },
        policy_hash: 'sha256:policy123...',
        text_hash: 'sha256:text123...',
        timestamp: new Date(Date.now() - 3600000).toISOString(),
        signer: 'egress_firewall',
        text_preview: 'The customer inquiry was about general product information...',
        rule_fired: 'none',
        severity: 'low'
      },
      {
        cert_id: 'cert_002',
        plan_id: 'plan_def456',
        tenant: 'tenant_001',
        detectors: { pii: 1, secret: 0, near_dupe: 0.3 },
        policy_hash: 'sha256:policy456...',
        text_hash: 'sha256:text456...',
        timestamp: new Date(Date.now() - 7200000).toISOString(),
        signer: 'egress_firewall',
        text_preview: 'Email detected: [REDACTED]@company.com for billing inquiry...',
        rule_fired: 'email_detection',
        severity: 'medium'
      },
      {
        cert_id: 'cert_003',
        plan_id: 'plan_ghi789',
        tenant: 'tenant_002',
        detectors: { pii: 0, secret: 1, near_dupe: 0.8 },
        policy_hash: 'sha256:policy789...',
        text_hash: 'sha256:text789...',
        timestamp: new Date(Date.now() - 1800000).toISOString(),
        signer: 'egress_firewall',
        text_preview: 'API key pattern detected: sk-[REDACTED]...',
        rule_fired: 'api_key_detection',
        severity: 'critical'
      }
    ];
    setCertificates(mockCertificates);
    setLoading(false);
  }, []);

  const filteredCertificates = certificates.filter(cert => {
    const matchesSearch = cert.cert_id.toLowerCase().includes(searchTerm.toLowerCase()) ||
                         cert.plan_id.toLowerCase().includes(searchTerm.toLowerCase()) ||
                         cert.tenant.toLowerCase().includes(searchTerm.toLowerCase()) ||
                         (cert.text_preview && cert.text_preview.toLowerCase().includes(searchTerm.toLowerCase()));
    
    const matchesFilter = filterSeverity === 'all' || cert.severity === filterSeverity;
    
    return matchesSearch && matchesFilter;
  });

  const formatTimestamp = (timestamp: string) => {
    return new Date(timestamp).toLocaleString();
  };

  const getSeverityBadge = (severity: string) => {
    switch (severity) {
      case 'low':
        return <Badge variant="secondary">Low</Badge>;
      case 'medium':
        return <Badge variant="outline">Medium</Badge>;
      case 'high':
        return <Badge variant="destructive">High</Badge>;
      case 'critical':
        return <Badge variant="destructive" className="bg-red-600">Critical</Badge>;
      default:
        return <Badge variant="secondary">Unknown</Badge>;
    }
  };

  const getDetectorBadge = (type: string, value: number) => {
    if (value === 0) {
      return <Badge variant="default">{type}: Clean</Badge>;
    }
    
    switch (type) {
      case 'PII':
        return <Badge variant="destructive">{type}: {value} detected</Badge>;
      case 'Secret':
        return <Badge variant="destructive">{type}: {value} detected</Badge>;
      case 'Similarity':
        return <Badge variant={value > 0.5 ? "secondary" : "default"}>
          {type}: {(value * 100).toFixed(1)}%
        </Badge>;
      default:
        return <Badge variant="outline">{type}: {value}</Badge>;
    }
  };

  if (loading) {
    return <div className="flex justify-center items-center h-64">Loading certificates...</div>;
  }

  return (
    <div className="space-y-6">
      <div className="flex justify-between items-center">
        <h1 className="text-3xl font-bold">Egress Certificates</h1>
        <Button variant="outline">
          <Download className="h-4 w-4 mr-2" />
          Export Certificates
        </Button>
      </div>

      {/* Search and Filter Controls */}
      <Card>
        <CardContent className="pt-6">
          <div className="flex flex-col sm:flex-row space-y-4 sm:space-y-0 sm:space-x-4">
            <div className="flex-1 relative">
              <Search className="absolute left-3 top-1/2 transform -translate-y-1/2 text-gray-400 h-4 w-4" />
              <input
                type="text"
                placeholder="Search certificates..."
                value={searchTerm}
                onChange={(e) => setSearchTerm(e.target.value)}
                className="w-full pl-10 pr-4 py-2 border border-gray-300 rounded-md focus:ring-2 focus:ring-blue-500 focus:border-transparent"
              />
            </div>
            <div className="flex items-center space-x-2">
              <Filter className="h-4 w-4 text-gray-400" />
              <select
                value={filterSeverity}
                onChange={(e) => setFilterSeverity(e.target.value as any)}
                className="px-3 py-2 border border-gray-300 rounded-md focus:ring-2 focus:ring-blue-500 focus:border-transparent"
              >
                <option value="all">All Severities</option>
                <option value="low">Low</option>
                <option value="medium">Medium</option>
                <option value="high">High</option>
                <option value="critical">Critical</option>
              </select>
            </div>
          </div>
        </CardContent>
      </Card>

      {/* Statistics */}
      <div className="grid grid-cols-1 md:grid-cols-5 gap-4">
        <Card>
          <CardContent className="pt-6">
            <div className="text-2xl font-bold">{certificates.length}</div>
            <p className="text-sm text-gray-600">Total Certificates</p>
          </CardContent>
        </Card>
        <Card>
          <CardContent className="pt-6">
            <div className="text-2xl font-bold text-red-600">
              {certificates.filter(c => c.detectors.pii > 0).length}
            </div>
            <p className="text-sm text-gray-600">PII Detected</p>
          </CardContent>
        </Card>
        <Card>
          <CardContent className="pt-6">
            <div className="text-2xl font-bold text-red-600">
              {certificates.filter(c => c.detectors.secret > 0).length}
            </div>
            <p className="text-sm text-gray-600">Secrets Detected</p>
          </CardContent>
        </Card>
        <Card>
          <CardContent className="pt-6">
            <div className="text-2xl font-bold text-orange-600">
              {certificates.filter(c => c.detectors.near_dupe > 0.5).length}
            </div>
            <p className="text-sm text-gray-600">High Similarity</p>
          </CardContent>
        </Card>
        <Card>
          <CardContent className="pt-6">
            <div className="text-2xl font-bold text-red-600">
              {certificates.filter(c => c.severity === 'critical').length}
            </div>
            <p className="text-sm text-gray-600">Critical Issues</p>
          </CardContent>
        </Card>
      </div>

      {/* Certificates List */}
      <div className="space-y-4">
        {filteredCertificates.map((cert) => (
          <Card key={cert.cert_id} className="hover:shadow-md transition-shadow">
            <CardContent className="pt-6">
              <div className="flex justify-between items-start mb-4">
                <div className="flex items-center space-x-3">
                  <h3 className="text-lg font-semibold">{cert.cert_id}</h3>
                  {getSeverityBadge(cert.severity)}
                  {(cert.detectors.pii > 0 || cert.detectors.secret > 0) && (
                    <AlertTriangle className="h-5 w-5 text-red-500" />
                  )}
                </div>
                <div className="flex items-center text-sm text-gray-500">
                  <Clock className="h-4 w-4 mr-1" />
                  {formatTimestamp(cert.timestamp)}
                </div>
              </div>

              <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4 mb-4">
                <div>
                  <div className="text-sm font-medium text-gray-700 mb-1">Plan ID</div>
                  <div className="text-sm text-gray-600">{cert.plan_id}</div>
                </div>
                <div>
                  <div className="text-sm font-medium text-gray-700 mb-1">Tenant</div>
                  <div className="text-sm text-gray-600">{cert.tenant}</div>
                </div>
                <div>
                  <div className="text-sm font-medium text-gray-700 mb-1">Signer</div>
                  <div className="text-sm text-gray-600 flex items-center">
                    <Shield className="h-4 w-4 mr-1" />
                    {cert.signer}
                  </div>
                </div>
              </div>

              {/* Detector Results */}
              <div className="mb-4">
                <div className="text-sm font-medium text-gray-700 mb-2">Detector Results</div>
                <div className="flex flex-wrap gap-2">
                  {getDetectorBadge('PII', cert.detectors.pii)}
                  {getDetectorBadge('Secret', cert.detectors.secret)}
                  {getDetectorBadge('Similarity', cert.detectors.near_dupe)}
                </div>
              </div>

              {/* Text Preview */}
              {cert.text_preview && (
                <div className="mb-4">
                  <div className="text-sm font-medium text-gray-700 mb-1">Text Preview</div>
                  <div className="text-sm text-gray-600 bg-gray-50 p-3 rounded border-l-4 border-blue-500">
                    {cert.text_preview}
                  </div>
                </div>
              )}

              {/* Rule Fired */}
              {cert.rule_fired && cert.rule_fired !== 'none' && (
                <div className="mb-4">
                  <div className="text-sm font-medium text-gray-700 mb-1">Rule Fired</div>
                  <Badge variant="outline" className="font-mono text-xs">
                    {cert.rule_fired}
                  </Badge>
                </div>
              )}

              <div className="space-y-2">
                <div className="text-sm">
                  <span className="font-medium text-gray-700">Policy Hash: </span>
                  <span className="text-gray-600 font-mono text-xs">{cert.policy_hash}</span>
                </div>
                <div className="text-sm">
                  <span className="font-medium text-gray-700">Text Hash: </span>
                  <span className="text-gray-600 font-mono text-xs">{cert.text_hash}</span>
                </div>
              </div>

              <div className="flex justify-end space-x-2 mt-4">
                <Button variant="outline" size="sm" onClick={() => setSelectedCert(cert)}>
                  <Eye className="h-4 w-4 mr-2" />
                  View Details
                </Button>
                <Button variant="outline" size="sm">
                  View Policy
                </Button>
              </div>
            </CardContent>
          </Card>
        ))}
      </div>

      {filteredCertificates.length === 0 && (
        <Card>
          <CardContent className="pt-6 text-center text-gray-500">
            No certificates found matching your criteria.
          </CardContent>
        </Card>
      )}

      {/* Certificate Detail Modal */}
      {selectedCert && (
        <div className="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center p-4 z-50">
          <Card className="max-w-4xl w-full max-h-[80vh] overflow-y-auto">
            <CardHeader>
              <CardTitle className="flex items-center space-x-2">
                <span>Certificate Details: {selectedCert.cert_id}</span>
                {getSeverityBadge(selectedCert.severity)}
              </CardTitle>
            </CardHeader>
            <CardContent>
              <div className="space-y-6">
                <div className="grid grid-cols-2 gap-4">
                  <div>
                    <strong>Plan ID:</strong> {selectedCert.plan_id}
                  </div>
                  <div>
                    <strong>Tenant:</strong> {selectedCert.tenant}
                  </div>
                  <div>
                    <strong>Signer:</strong> {selectedCert.signer}
                  </div>
                  <div>
                    <strong>Timestamp:</strong> {formatTimestamp(selectedCert.timestamp)}
                  </div>
                </div>

                <div>
                  <strong>Detector Results:</strong>
                  <div className="grid grid-cols-1 md:grid-cols-3 gap-4 mt-2">
                    <div className="bg-gray-50 p-3 rounded">
                      <div className="text-sm font-medium">PII Detection</div>
                      <div className="text-2xl font-bold text-red-600">{selectedCert.detectors.pii}</div>
                      <div className="text-xs text-gray-600">instances found</div>
                    </div>
                    <div className="bg-gray-50 p-3 rounded">
                      <div className="text-sm font-medium">Secret Detection</div>
                      <div className="text-2xl font-bold text-red-600">{selectedCert.detectors.secret}</div>
                      <div className="text-xs text-gray-600">secrets found</div>
                    </div>
                    <div className="bg-gray-50 p-3 rounded">
                      <div className="text-sm font-medium">Similarity Score</div>
                      <div className="text-2xl font-bold text-orange-600">
                        {(selectedCert.detectors.near_dupe * 100).toFixed(1)}%
                      </div>
                      <div className="text-xs text-gray-600">similarity</div>
                    </div>
                  </div>
                </div>

                {selectedCert.rule_fired && selectedCert.rule_fired !== 'none' && (
                  <div>
                    <strong>Firewall Rule Fired:</strong>
                    <div className="bg-red-50 border border-red-200 p-3 rounded mt-2">
                      <code className="text-sm text-red-800">{selectedCert.rule_fired}</code>
                    </div>
                  </div>
                )}

                {selectedCert.text_preview && (
                  <div>
                    <strong>Text Preview:</strong>
                    <div className="bg-gray-100 p-3 rounded mt-2 font-mono text-sm">
                      {selectedCert.text_preview}
                    </div>
                  </div>
                )}
                
                <div>
                  <strong>Policy Hash:</strong>
                  <div className="font-mono text-xs bg-gray-100 p-2 rounded mt-1 break-all">
                    {selectedCert.policy_hash}
                  </div>
                </div>
                
                <div>
                  <strong>Text Hash:</strong>
                  <div className="font-mono text-xs bg-gray-100 p-2 rounded mt-1 break-all">
                    {selectedCert.text_hash}
                  </div>
                </div>
              </div>
              
              <div className="flex justify-end space-x-2 mt-6">
                <Button variant="outline" onClick={() => setSelectedCert(null)}>
                  Close
                </Button>
                <Button variant="outline">
                  <Download className="h-4 w-4 mr-2" />
                  Export
                </Button>
              </div>
            </CardContent>
          </Card>
        </div>
      )}
    </div>
  );
};