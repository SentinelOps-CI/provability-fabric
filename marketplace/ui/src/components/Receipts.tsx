import React, { useState, useEffect } from 'react';
import { Card, CardContent, CardHeader, CardTitle } from './ui/card';
import { Badge } from './ui/badge';
import { Button } from './ui/button';
import { Search, Filter, Download, ExternalLink, Shield, Clock } from 'lucide-react';

interface Receipt {
  receipt_id: string;
  tenant: string;
  subject: string;
  query_hash: string;
  index_shard: string;
  timestamp: string;
  result_hash: string;
  signed: boolean;
  query_text?: string;
  result_diff?: 'match' | 'mismatch' | 'unknown';
}

export const Receipts: React.FC = () => {
  const [receipts, setReceipts] = useState<Receipt[]>([]);
  const [loading, setLoading] = useState(true);
  const [searchTerm, setSearchTerm] = useState('');
  const [filterStatus, setFilterStatus] = useState<'all' | 'signed' | 'unsigned'>('all');
  const [selectedReceipt, setSelectedReceipt] = useState<Receipt | null>(null);

  useEffect(() => {
    // Mock data - in production would fetch from ledger API
    const mockReceipts: Receipt[] = [
      {
        receipt_id: 'receipt_001',
        tenant: 'tenant_001',
        subject: 'user_123',
        query_hash: 'sha256:abc123def456789...',
        index_shard: 'shard_1',
        timestamp: new Date(Date.now() - 3600000).toISOString(),
        result_hash: 'sha256:def456abc789123...',
        signed: true,
        query_text: 'Find documents about privacy policy',
        result_diff: 'match'
      },
      {
        receipt_id: 'receipt_002',
        tenant: 'tenant_001',
        subject: 'user_456',
        query_hash: 'sha256:789abc123def456...',
        index_shard: 'shard_2',
        timestamp: new Date(Date.now() - 7200000).toISOString(),
        result_hash: 'sha256:123def456abc789...',
        signed: true,
        query_text: 'Search for billing information',
        result_diff: 'match'
      },
      {
        receipt_id: 'receipt_003',
        tenant: 'tenant_002',
        subject: 'user_789',
        query_hash: 'sha256:456def789abc123...',
        index_shard: 'shard_1',
        timestamp: new Date(Date.now() - 1800000).toISOString(),
        result_hash: 'sha256:789abc456def123...',
        signed: false,
        query_text: 'Query about system performance',
        result_diff: 'mismatch'
      }
    ];
    setReceipts(mockReceipts);
    setLoading(false);
  }, []);

  const filteredReceipts = receipts.filter(receipt => {
    const matchesSearch = receipt.receipt_id.toLowerCase().includes(searchTerm.toLowerCase()) ||
                         receipt.subject.toLowerCase().includes(searchTerm.toLowerCase()) ||
                         (receipt.query_text && receipt.query_text.toLowerCase().includes(searchTerm.toLowerCase()));
    
    const matchesFilter = filterStatus === 'all' || 
                         (filterStatus === 'signed' && receipt.signed) ||
                         (filterStatus === 'unsigned' && !receipt.signed);
    
    return matchesSearch && matchesFilter;
  });

  const formatTimestamp = (timestamp: string) => {
    return new Date(timestamp).toLocaleString();
  };

  const getDiffBadge = (diff: string) => {
    switch (diff) {
      case 'match':
        return <Badge variant="default">Hash Match</Badge>;
      case 'mismatch':
        return <Badge variant="destructive">Hash Mismatch</Badge>;
      default:
        return <Badge variant="secondary">Unknown</Badge>;
    }
  };

  if (loading) {
    return <div className="flex justify-center items-center h-64">Loading receipts...</div>;
  }

  return (
    <div className="space-y-6">
      <div className="flex justify-between items-center">
        <h1 className="text-3xl font-bold">Access Receipts</h1>
        <Button variant="outline">
          <Download className="h-4 w-4 mr-2" />
          Export Receipts
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
                placeholder="Search receipts..."
                value={searchTerm}
                onChange={(e) => setSearchTerm(e.target.value)}
                className="w-full pl-10 pr-4 py-2 border border-gray-300 rounded-md focus:ring-2 focus:ring-blue-500 focus:border-transparent"
              />
            </div>
            <div className="flex items-center space-x-2">
              <Filter className="h-4 w-4 text-gray-400" />
              <select
                value={filterStatus}
                onChange={(e) => setFilterStatus(e.target.value as any)}
                className="px-3 py-2 border border-gray-300 rounded-md focus:ring-2 focus:ring-blue-500 focus:border-transparent"
              >
                <option value="all">All Status</option>
                <option value="signed">Signed Only</option>
                <option value="unsigned">Unsigned Only</option>
              </select>
            </div>
          </div>
        </CardContent>
      </Card>

      {/* Statistics */}
      <div className="grid grid-cols-1 md:grid-cols-4 gap-4">
        <Card>
          <CardContent className="pt-6">
            <div className="text-2xl font-bold">{receipts.length}</div>
            <p className="text-sm text-gray-600">Total Receipts</p>
          </CardContent>
        </Card>
        <Card>
          <CardContent className="pt-6">
            <div className="text-2xl font-bold text-green-600">
              {receipts.filter(r => r.signed).length}
            </div>
            <p className="text-sm text-gray-600">Signed Receipts</p>
          </CardContent>
        </Card>
        <Card>
          <CardContent className="pt-6">
            <div className="text-2xl font-bold text-green-600">
              {receipts.filter(r => r.result_diff === 'match').length}
            </div>
            <p className="text-sm text-gray-600">Hash Matches</p>
          </CardContent>
        </Card>
        <Card>
          <CardContent className="pt-6">
            <div className="text-2xl font-bold text-red-600">
              {receipts.filter(r => r.result_diff === 'mismatch').length}
            </div>
            <p className="text-sm text-gray-600">Hash Mismatches</p>
          </CardContent>
        </Card>
      </div>

      {/* Receipts List */}
      <div className="space-y-4">
        {filteredReceipts.map((receipt) => (
          <Card key={receipt.receipt_id} className="hover:shadow-md transition-shadow">
            <CardContent className="pt-6">
              <div className="flex justify-between items-start mb-4">
                <div className="flex items-center space-x-3">
                  <h3 className="text-lg font-semibold">{receipt.receipt_id}</h3>
                  <Badge variant={receipt.signed ? "default" : "destructive"}>
                    <Shield className="h-3 w-3 mr-1" />
                    {receipt.signed ? "Signed" : "Unsigned"}
                  </Badge>
                  {receipt.result_diff && getDiffBadge(receipt.result_diff)}
                </div>
                <div className="flex items-center text-sm text-gray-500">
                  <Clock className="h-4 w-4 mr-1" />
                  {formatTimestamp(receipt.timestamp)}
                </div>
              </div>

              <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
                <div>
                  <div className="text-sm font-medium text-gray-700 mb-1">Subject</div>
                  <div className="text-sm text-gray-600">{receipt.subject}</div>
                </div>
                <div>
                  <div className="text-sm font-medium text-gray-700 mb-1">Index Shard</div>
                  <div className="text-sm text-gray-600">{receipt.index_shard}</div>
                </div>
                <div>
                  <div className="text-sm font-medium text-gray-700 mb-1">Tenant</div>
                  <div className="text-sm text-gray-600">{receipt.tenant}</div>
                </div>
              </div>

              {receipt.query_text && (
                <div className="mt-4">
                  <div className="text-sm font-medium text-gray-700 mb-1">Query</div>
                  <div className="text-sm text-gray-600 bg-gray-50 p-2 rounded">
                    {receipt.query_text}
                  </div>
                </div>
              )}

              <div className="mt-4 space-y-2">
                <div className="text-sm">
                  <span className="font-medium text-gray-700">Query Hash: </span>
                  <span className="text-gray-600 font-mono text-xs">{receipt.query_hash}</span>
                </div>
                <div className="text-sm">
                  <span className="font-medium text-gray-700">Result Hash: </span>
                  <span className="text-gray-600 font-mono text-xs">{receipt.result_hash}</span>
                </div>
              </div>

              <div className="flex justify-end space-x-2 mt-4">
                <Button variant="outline" size="sm" onClick={() => setSelectedReceipt(receipt)}>
                  View Details
                </Button>
                <Button variant="outline" size="sm">
                  <ExternalLink className="h-4 w-4 mr-2" />
                  Verify
                </Button>
              </div>
            </CardContent>
          </Card>
        ))}
      </div>

      {filteredReceipts.length === 0 && (
        <Card>
          <CardContent className="pt-6 text-center text-gray-500">
            No receipts found matching your criteria.
          </CardContent>
        </Card>
      )}

      {/* Receipt Detail Modal */}
      {selectedReceipt && (
        <div className="fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center p-4 z-50">
          <Card className="max-w-2xl w-full max-h-[80vh] overflow-y-auto">
            <CardHeader>
              <CardTitle>Receipt Details: {selectedReceipt.receipt_id}</CardTitle>
            </CardHeader>
            <CardContent>
              <div className="space-y-4">
                <div className="grid grid-cols-2 gap-4">
                  <div>
                    <strong>Tenant:</strong> {selectedReceipt.tenant}
                  </div>
                  <div>
                    <strong>Subject:</strong> {selectedReceipt.subject}
                  </div>
                  <div>
                    <strong>Index Shard:</strong> {selectedReceipt.index_shard}
                  </div>
                  <div>
                    <strong>Timestamp:</strong> {formatTimestamp(selectedReceipt.timestamp)}
                  </div>
                </div>
                
                <div>
                  <strong>Query Hash:</strong>
                  <div className="font-mono text-xs bg-gray-100 p-2 rounded mt-1">
                    {selectedReceipt.query_hash}
                  </div>
                </div>
                
                <div>
                  <strong>Result Hash:</strong>
                  <div className="font-mono text-xs bg-gray-100 p-2 rounded mt-1">
                    {selectedReceipt.result_hash}
                  </div>
                </div>

                {selectedReceipt.query_text && (
                  <div>
                    <strong>Query Text:</strong>
                    <div className="bg-gray-100 p-2 rounded mt-1">
                      {selectedReceipt.query_text}
                    </div>
                  </div>
                )}

                <div className="flex items-center space-x-4">
                  <div className="flex items-center space-x-2">
                    <strong>Signature Status:</strong>
                    <Badge variant={selectedReceipt.signed ? "default" : "destructive"}>
                      {selectedReceipt.signed ? "Valid" : "Invalid"}
                    </Badge>
                  </div>
                  {selectedReceipt.result_diff && (
                    <div className="flex items-center space-x-2">
                      <strong>Hash Verification:</strong>
                      {getDiffBadge(selectedReceipt.result_diff)}
                    </div>
                  )}
                </div>
              </div>
              
              <div className="flex justify-end space-x-2 mt-6">
                <Button variant="outline" onClick={() => setSelectedReceipt(null)}>
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