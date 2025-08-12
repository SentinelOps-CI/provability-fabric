import React, { useState, useEffect } from 'react';
import {
  Card,
  CardContent,
  CardHeader,
  CardTitle,
} from './ui/card';
import { Badge } from './ui/badge';
import { Button } from './ui/button';
import { Tabs, TabsContent, TabsList, TabsTrigger } from './ui/tabs';
import { Alert, AlertDescription } from './ui/alert';
import { Separator } from './ui/separator';
import { ScrollArea } from './ui/scroll-area';
import { 
  Shield, 
  AlertTriangle, 
  CheckCircle, 
  XCircle, 
  Info,
  Download,
  Eye,
  EyeOff,
  Clock,
  Hash,
  FileText,
  Code,
  Database,
  Lock,
  Unlock
} from 'lucide-react';

interface EgressCertificate {
  cert_id: string;
  plan_id?: string;
  tenant: string;
  detector_flags: DetectorFlags;
  near_dupe_score: number;
  policy_hash: string;
  text_hash: string;
  timestamp: number;
  signer?: string;
  non_interference: NonInterferenceVerdict;
  influencing_labels: string[];
  attestation_ref?: string;
  pii_detected: string[];
  secrets_detected: string[];
  entropy_score: number;
  format_analysis: FormatAnalysis;
  simhash: string;
  minhash_signature?: string;
  llm_analysis_required: boolean;
  llm_verdict?: string;
}

interface DetectorFlags {
  pii_detected: boolean;
  secrets_detected: boolean;
  near_dupe_detected: boolean;
  policy_violations: boolean;
  high_entropy: boolean;
  suspicious_format: boolean;
}

interface NonInterferenceVerdict {
  status: 'passed' | 'failed' | 'ambiguous';
  reason?: string;
  severity?: string;
  confidence?: number;
  requires_llm?: boolean;
}

interface FormatAnalysis {
  text_length: number;
  word_count: number;
  avg_word_length: number;
  entropy_per_char: number;
  contains_code: boolean;
  contains_structured_data: boolean;
  language_detected?: string;
}

interface EgressCertificateViewProps {
  certificate: EgressCertificate;
  showRedactedContent?: boolean;
  onExport?: (format: 'json' | 'csv' | 'pdf') => void;
}

export const EgressCertificateView: React.FC<EgressCertificateViewProps> = ({
  certificate,
  showRedactedContent = false,
  onExport,
}) => {
  const [activeTab, setActiveTab] = useState('overview');
  const [showSensitiveData, setShowSensitiveData] = useState(false);

  const getStatusColor = (status: string) => {
    switch (status) {
      case 'passed':
        return 'bg-green-100 text-green-800 border-green-200';
      case 'failed':
        return 'bg-red-100 text-red-800 border-red-200';
      case 'ambiguous':
        return 'bg-yellow-100 text-yellow-800 border-yellow-200';
      default:
        return 'bg-gray-100 text-gray-800 border-gray-200';
    }
  };

  const getSeverityColor = (severity?: string) => {
    switch (severity) {
      case 'critical':
        return 'bg-red-100 text-red-800 border-red-200';
      case 'high':
        return 'bg-orange-100 text-orange-800 border-orange-200';
      case 'medium':
        return 'bg-yellow-100 text-yellow-800 border-yellow-200';
      case 'low':
        return 'bg-blue-100 text-blue-800 border-blue-200';
      default:
        return 'bg-gray-100 text-gray-800 border-gray-200';
    }
  };

  const formatTimestamp = (timestamp: number) => {
    return new Date(timestamp * 1000).toLocaleString();
  };

  const truncateHash = (hash: string, length: number = 8) => {
    if (hash.length <= length * 2) return hash;
    return `${hash.substring(0, length)}...${hash.substring(hash.length - length)}`;
  };

  const getSecurityScore = () => {
    let score = 100;
    
    if (certificate.detector_flags.pii_detected) score -= 30;
    if (certificate.detector_flags.secrets_detected) score -= 40;
    if (certificate.detector_flags.near_dupe_detected) score -= 10;
    if (certificate.detector_flags.policy_violations) score -= 20;
    if (certificate.detector_flags.high_entropy) score -= 15;
    if (certificate.detector_flags.suspicious_format) score -= 10;
    if (certificate.non_interference.status === 'failed') score -= 50;
    if (certificate.non_interference.status === 'ambiguous') score -= 25;
    
    return Math.max(0, score);
  };

  const securityScore = getSecurityScore();

  return (
    <div className="space-y-6">
      {/* Header with Security Score */}
      <Card>
        <CardHeader className="pb-4">
          <div className="flex items-center justify-between">
            <div className="flex items-center space-x-3">
              <Shield className="h-8 w-8 text-blue-600" />
              <div>
                <CardTitle className="text-2xl">Egress Certificate</CardTitle>
                <p className="text-sm text-muted-foreground">
                  {certificate.cert_id}
                </p>
              </div>
            </div>
            <div className="text-right">
              <div className="text-3xl font-bold text-blue-600">{securityScore}</div>
              <div className="text-sm text-muted-foreground">Security Score</div>
            </div>
          </div>
        </CardHeader>
        <CardContent>
          <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
            <div>
              <div className="text-sm font-medium text-muted-foreground">Tenant</div>
              <div className="text-lg font-semibold">{certificate.tenant}</div>
            </div>
            <div>
              <div className="text-sm font-medium text-muted-foreground">Plan ID</div>
              <div className="text-lg font-semibold">
                {certificate.plan_id || 'N/A'}
              </div>
            </div>
            <div>
              <div className="text-sm font-medium text-muted-foreground">Timestamp</div>
              <div className="text-sm">{formatTimestamp(certificate.timestamp)}</div>
            </div>
            <div>
              <div className="text-sm font-medium text-muted-foreground">Status</div>
              <Badge className={getStatusColor(certificate.non_interference.status)}>
                {certificate.non_interference.status.toUpperCase()}
              </Badge>
            </div>
          </div>
        </CardContent>
      </Card>

      {/* Security Alerts Banner */}
      {(certificate.detector_flags.pii_detected || 
        certificate.detector_flags.secrets_detected || 
        certificate.non_interference.status === 'failed') && (
        <Alert className="border-red-200 bg-red-50">
          <AlertTriangle className="h-4 w-4 text-red-600" />
          <AlertDescription className="text-red-800">
            <strong>Security Alert:</strong> This content contains sensitive information or failed security checks.
            {certificate.detector_flags.pii_detected && ' PII detected.'}
            {certificate.detector_flags.secrets_detected && ' Secrets detected.'}
            {certificate.non_interference.status === 'failed' && ' Non-interference check failed.'}
          </AlertDescription>
        </Alert>
      )}

      {/* Main Content Tabs */}
      <Tabs value={activeTab} onValueChange={setActiveTab} className="w-full">
        <TabsList className="grid w-full grid-cols-5">
          <TabsTrigger value="overview">Overview</TabsTrigger>
          <TabsTrigger value="security">Security</TabsTrigger>
          <TabsTrigger value="analysis">Analysis</TabsTrigger>
          <TabsTrigger value="technical">Technical</TabsTrigger>
          <TabsTrigger value="export">Export</TabsTrigger>
        </TabsList>

        {/* Overview Tab */}
        <TabsContent value="overview" className="space-y-4">
          <Card>
            <CardHeader>
              <CardTitle className="flex items-center space-x-2">
                <CheckCircle className="h-5 w-5 text-green-600" />
                <span>Security Status</span>
              </CardTitle>
            </CardHeader>
            <CardContent>
              <div className="grid grid-cols-2 md:grid-cols-3 gap-4">
                <div className="flex items-center space-x-2">
                  {certificate.detector_flags.pii_detected ? (
                    <XCircle className="h-5 w-5 text-red-600" />
                  ) : (
                    <CheckCircle className="h-5 w-5 text-green-600" />
                  )}
                  <span>PII Detection</span>
                </div>
                <div className="flex items-center space-x-2">
                  {certificate.detector_flags.secrets_detected ? (
                    <XCircle className="h-5 w-5 text-red-600" />
                  ) : (
                    <CheckCircle className="h-5 w-5 text-green-600" />
                  )}
                  <span>Secret Detection</span>
                </div>
                <div className="flex items-center space-x-2">
                  {certificate.detector_flags.near_dupe_detected ? (
                    <AlertTriangle className="h-5 w-5 text-yellow-600" />
                  ) : (
                    <CheckCircle className="h-5 w-5 text-green-600" />
                  )}
                  <span>Near-Duplicate</span>
                </div>
                <div className="flex items-center space-x-2">
                  {certificate.detector_flags.policy_violations ? (
                    <XCircle className="h-5 w-5 text-red-600" />
                  ) : (
                    <CheckCircle className="h-5 w-5 text-green-600" />
                  )}
                  <span>Policy Compliance</span>
                </div>
                <div className="flex items-center space-x-2">
                  {certificate.detector_flags.high_entropy ? (
                    <AlertTriangle className="h-5 w-5 text-yellow-600" />
                  ) : (
                    <CheckCircle className="h-5 w-5 text-green-600" />
                  )}
                  <span>Entropy Analysis</span>
                </div>
                <div className="flex items-center space-x-2">
                  {certificate.detector_flags.suspicious_format ? (
                    <AlertTriangle className="h-5 w-5 text-yellow-600" />
                  ) : (
                    <CheckCircle className="h-5 w-5 text-green-600" />
                  )}
                  <span>Format Analysis</span>
                </div>
              </div>
            </CardContent>
          </Card>

          <Card>
            <CardHeader>
              <CardTitle className="flex items-center space-x-2">
                <Lock className="h-5 w-5 text-blue-600" />
                <span>Non-Interference Verdict</span>
              </CardTitle>
            </CardHeader>
            <CardContent>
              <div className="space-y-3">
                <div className="flex items-center justify-between">
                  <span className="font-medium">Status:</span>
                  <Badge className={getStatusColor(certificate.non_interference.status)}>
                    {certificate.non_interference.status.toUpperCase()}
                  </Badge>
                </div>
                {certificate.non_interference.reason && (
                  <div className="flex items-center justify-between">
                    <span className="font-medium">Reason:</span>
                    <span className="text-sm text-muted-foreground">
                      {certificate.non_interference.reason}
                    </span>
                  </div>
                )}
                {certificate.non_interference.severity && (
                  <div className="flex items-center justify-between">
                    <span className="font-medium">Severity:</span>
                    <Badge className={getSeverityColor(certificate.non_interference.severity)}>
                      {certificate.non_interference.severity.toUpperCase()}
                    </Badge>
                  </div>
                )}
                {certificate.non_interference.confidence && (
                  <div className="flex items-center justify-between">
                    <span className="font-medium">Confidence:</span>
                    <span className="text-sm text-muted-foreground">
                      {(certificate.non_interference.confidence * 100).toFixed(1)}%
                    </span>
                  </div>
                )}
                {certificate.non_interference.requires_llm && (
                  <div className="flex items-center justify-between">
                    <span className="font-medium">LLM Analysis:</span>
                    <Badge className="bg-purple-100 text-purple-800 border-purple-200">
                      REQUIRED
                    </Badge>
                  </div>
                )}
              </div>
            </CardContent>
          </Card>
        </TabsContent>

        {/* Security Tab */}
        <TabsContent value="security" className="space-y-4">
          <Card>
            <CardHeader>
              <CardTitle className="flex items-center space-x-2">
                <Shield className="h-5 w-5 text-red-600" />
                <span>Detected Issues</span>
              </CardTitle>
            </CardHeader>
            <CardContent>
              <div className="space-y-4">
                {certificate.pii_detected.length > 0 && (
                  <div>
                    <div className="flex items-center space-x-2 mb-2">
                      <XCircle className="h-5 w-5 text-red-600" />
                      <span className="font-medium text-red-800">PII Detected</span>
                    </div>
                    <div className="pl-7">
                      {certificate.pii_detected.map((pii, index) => (
                        <Badge key={index} variant="destructive" className="mr-2 mb-2">
                          {pii}
                        </Badge>
                      ))}
                    </div>
                  </div>
                )}

                {certificate.secrets_detected.length > 0 && (
                  <div>
                    <div className="flex items-center space-x-2 mb-2">
                      <Lock className="h-5 w-5 text-red-600" />
                      <span className="font-medium text-red-800">Secrets Detected</span>
                    </div>
                    <div className="pl-7">
                      {certificate.secrets_detected.map((secret, index) => (
                        <Badge key={index} variant="destructive" className="mr-2 mb-2">
                          {secret}
                        </Badge>
                      ))}
                    </div>
                  </div>
                )}

                {certificate.detector_flags.near_dupe_detected && (
                  <div>
                    <div className="flex items-center space-x-2 mb-2">
                      <AlertTriangle className="h-5 w-5 text-yellow-600" />
                      <span className="font-medium text-yellow-800">Near-Duplicate Content</span>
                    </div>
                    <div className="pl-7">
                      <p className="text-sm text-muted-foreground">
                        Similarity score: {(certificate.near_dupe_score * 100).toFixed(1)}%
                      </p>
                    </div>
                  </div>
                )}

                {certificate.detector_flags.high_entropy && (
                  <div>
                    <div className="flex items-center space-x-2 mb-2">
                      <AlertTriangle className="h-5 w-5 text-yellow-600" />
                      <span className="font-medium text-yellow-800">High Entropy</span>
                    </div>
                    <div className="pl-7">
                      <p className="text-sm text-muted-foreground">
                        Entropy score: {certificate.entropy_score.toFixed(2)}
                      </p>
                    </div>
                  </div>
                )}

                {!certificate.pii_detected.length && 
                 !certificate.secrets_detected.length && 
                 !certificate.detector_flags.near_dupe_detected &&
                 !certificate.detector_flags.high_entropy && (
                  <div className="flex items-center space-x-2 text-green-800">
                    <CheckCircle className="h-5 w-5" />
                    <span className="font-medium">No security issues detected</span>
                  </div>
                )}
              </div>
            </CardContent>
          </Card>

          <Card>
            <CardHeader>
              <CardTitle className="flex items-center space-x-2">
                <Hash className="h-5 w-5 text-blue-600" />
                <span>Content Hashes</span>
              </CardTitle>
            </CardHeader>
            <CardContent>
              <div className="space-y-3">
                <div className="flex items-center justify-between">
                  <span className="font-medium">Text Hash:</span>
                  <code className="text-sm bg-gray-100 px-2 py-1 rounded">
                    {truncateHash(certificate.text_hash)}
                  </code>
                </div>
                <div className="flex items-center justify-between">
                  <span className="font-medium">Policy Hash:</span>
                  <code className="text-sm bg-gray-100 px-2 py-1 rounded">
                    {truncateHash(certificate.policy_hash)}
                  </code>
                </div>
                <div className="flex items-center justify-between">
                  <span className="font-medium">SimHash:</span>
                  <code className="text-sm bg-gray-100 px-2 py-1 rounded">
                    {truncateHash(certificate.simhash)}
                  </code>
                </div>
                {certificate.minhash_signature && (
                  <div className="flex items-center justify-between">
                    <span className="font-medium">MinHash:</span>
                    <code className="text-sm bg-gray-100 px-2 py-1 rounded">
                      {truncateHash(certificate.minhash_signature)}
                    </code>
                  </div>
                )}
              </div>
            </CardContent>
          </Card>
        </TabsContent>

        {/* Analysis Tab */}
        <TabsContent value="analysis" className="space-y-4">
          <Card>
            <CardHeader>
              <CardTitle className="flex items-center space-x-2">
                <FileText className="h-5 w-5 text-green-600" />
                <span>Content Analysis</span>
              </CardTitle>
            </CardHeader>
            <CardContent>
              <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
                <div>
                  <div className="text-sm font-medium text-muted-foreground">Text Length</div>
                  <div className="text-lg font-semibold">{certificate.format_analysis.text_length}</div>
                </div>
                <div>
                  <div className="text-sm font-medium text-muted-foreground">Word Count</div>
                  <div className="text-lg font-semibold">{certificate.format_analysis.word_count}</div>
                </div>
                <div>
                  <div className="text-sm font-medium text-muted-foreground">Avg Word Length</div>
                  <div className="text-lg font-semibold">
                    {certificate.format_analysis.avg_word_length.toFixed(1)}
                  </div>
                </div>
                <div>
                  <div className="text-sm font-medium text-muted-foreground">Entropy Score</div>
                  <div className="text-lg font-semibold">
                    {certificate.entropy_score.toFixed(2)}
                  </div>
                </div>
              </div>
            </CardContent>
          </Card>

          <Card>
            <CardHeader>
              <CardTitle className="flex items-center space-x-2">
                <Code className="h-5 w-5 text-purple-600" />
                <span>Format Analysis</span>
              </CardTitle>
            </CardHeader>
            <CardContent>
              <div className="space-y-3">
                <div className="flex items-center justify-between">
                  <span className="font-medium">Contains Code:</span>
                  <Badge variant={certificate.format_analysis.contains_code ? "destructive" : "secondary"}>
                    {certificate.format_analysis.contains_code ? "Yes" : "No"}
                  </Badge>
                </div>
                <div className="flex items-center justify-between">
                  <span className="font-medium">Structured Data:</span>
                  <Badge variant={certificate.format_analysis.contains_structured_data ? "destructive" : "secondary"}>
                    {certificate.format_analysis.contains_structured_data ? "Yes" : "No"}
                  </Badge>
                </div>
                {certificate.format_analysis.language_detected && (
                  <div className="flex items-center justify-between">
                    <span className="font-medium">Language:</span>
                    <Badge variant="outline">
                      {certificate.format_analysis.language_detected}
                    </Badge>
                  </div>
                )}
              </div>
            </CardContent>
          </Card>

          {certificate.llm_analysis_required && (
            <Card>
              <CardHeader>
                <CardTitle className="flex items-center space-x-2">
                  <Database className="h-5 w-5 text-purple-600" />
                  <span>LLM Analysis</span>
                </CardTitle>
              </CardHeader>
              <CardContent>
                <div className="space-y-3">
                  <div className="flex items-center justify-between">
                    <span className="font-medium">Analysis Required:</span>
                    <Badge className="bg-purple-100 text-purple-800 border-purple-200">
                      YES
                    </Badge>
                  </div>
                  {certificate.llm_verdict && (
                    <div>
                      <div className="font-medium mb-2">LLM Verdict:</div>
                      <div className="bg-gray-50 p-3 rounded text-sm">
                        {certificate.llm_verdict}
                      </div>
                    </div>
                  )}
                </div>
              </CardContent>
            </Card>
          )}
        </TabsContent>

        {/* Technical Tab */}
        <TabsContent value="technical" className="space-y-4">
          <Card>
            <CardHeader>
              <CardTitle className="flex items-center space-x-2">
                <Info className="h-5 w-5 text-blue-600" />
                <span>Technical Details</span>
              </CardTitle>
            </CardHeader>
            <CardContent>
              <div className="space-y-4">
                <div>
                  <div className="font-medium mb-2">Influencing Labels:</div>
                  <div className="flex flex-wrap gap-2">
                    {certificate.influencing_labels.length > 0 ? (
                      certificate.influencing_labels.map((label, index) => (
                        <Badge key={index} variant="outline">
                          {label}
                        </Badge>
                      ))
                    ) : (
                      <span className="text-sm text-muted-foreground">None</span>
                    )}
                  </div>
                </div>

                {certificate.attestation_ref && (
                  <div>
                    <div className="font-medium mb-2">Attestation Reference:</div>
                    <code className="text-sm bg-gray-100 px-2 py-1 rounded block">
                      {certificate.attestation_ref}
                    </code>
                  </div>
                )}

                {certificate.signer && (
                  <div>
                    <div className="font-medium mb-2">Digital Signature:</div>
                    <code className="text-sm bg-gray-100 px-2 py-1 rounded block">
                      {truncateHash(certificate.signer, 16)}
                    </code>
                  </div>
                )}
              </div>
            </CardContent>
          </Card>
        </TabsContent>

        {/* Export Tab */}
        <TabsContent value="export" className="space-y-4">
          <Card>
            <CardHeader>
              <CardTitle className="flex items-center space-x-2">
                <Download className="h-5 w-5 text-green-600" />
                <span>Export Certificate</span>
              </CardTitle>
            </CardHeader>
            <CardContent>
              <div className="space-y-4">
                <p className="text-sm text-muted-foreground">
                  Export this certificate in various formats for compliance, auditing, or analysis purposes.
                </p>
                
                <div className="grid grid-cols-3 gap-3">
                  <Button
                    variant="outline"
                    onClick={() => onExport?.('json')}
                    className="flex flex-col items-center space-y-2 p-4"
                  >
                    <FileText className="h-8 w-8" />
                    <span>JSON</span>
                  </Button>
                  
                  <Button
                    variant="outline"
                    onClick={() => onExport?.('csv')}
                    className="flex flex-col items-center space-y-2 p-4"
                  >
                    <Database className="h-8 w-8" />
                    <span>CSV</span>
                  </Button>
                  
                  <Button
                    variant="outline"
                    onClick={() => onExport?.('pdf')}
                    className="flex flex-col items-center space-y-2 p-4"
                  >
                    <FileText className="h-8 w-8" />
                    <span>PDF</span>
                  </Button>
                </div>

                <Separator />

                <div className="flex items-center justify-between">
                  <span className="text-sm font-medium">Show Sensitive Data:</span>
                  <Button
                    variant="outline"
                    size="sm"
                    onClick={() => setShowSensitiveData(!showSensitiveData)}
                  >
                    {showSensitiveData ? (
                      <>
                        <EyeOff className="h-4 w-4 mr-2" />
                        Hide
                      </>
                    ) : (
                      <>
                        <Eye className="h-4 w-4 mr-2" />
                        Show
                      </>
                    )}
                  </Button>
                </div>

                {showSensitiveData && (
                  <div className="bg-yellow-50 border border-yellow-200 rounded-lg p-4">
                    <div className="flex items-center space-x-2 mb-2">
                      <AlertTriangle className="h-4 w-4 text-yellow-600" />
                      <span className="font-medium text-yellow-800">Sensitive Data</span>
                    </div>
                    <div className="space-y-2 text-sm">
                      {certificate.pii_detected.length > 0 && (
                        <div>
                          <strong>PII Types:</strong> {certificate.pii_detected.join(', ')}
                        </div>
                      )}
                      {certificate.secrets_detected.length > 0 && (
                        <div>
                          <strong>Secret Types:</strong> {certificate.secrets_detected.join(', ')}
                        </div>
                      )}
                      <div>
                        <strong>Entropy Score:</strong> {certificate.entropy_score.toFixed(3)}
                      </div>
                    </div>
                  </div>
                )}
              </div>
            </CardContent>
          </Card>
        </TabsContent>
      </Tabs>
    </div>
  );
};

export default EgressCertificateView;
