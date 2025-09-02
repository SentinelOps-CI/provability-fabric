/**
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * 
 * Real-Time Financial Services MCP Monitoring Dashboard
 * React-based dashboard for monitoring performance and compliance metrics
 */

import React, { useState, useEffect, useCallback, useMemo } from 'react';
import {
  LineChart,
  Line,
  XAxis,
  YAxis,
  CartesianGrid,
  Tooltip,
  Legend,
  ResponsiveContainer,
  AreaChart,
  Area,
  BarChart,
  Bar,
  PieChart,
  Pie,
  Cell,
  RadialBarChart,
  RadialBar
} from 'recharts';
import {
  AlertTriangle,
  CheckCircle,
  XCircle,
  Clock,
  TrendingUp,
  TrendingDown,
  Activity,
  Shield,
  Database,
  Zap,
  Users,
  AlertCircle,
  Eye,
  Download,
  RefreshCw
} from 'lucide-react';

// Types and interfaces
interface DashboardMetrics {
  timestamp: number;
  transactions: {
    total: number;
    successful: number;
    failed: number;
    fraudulent: number;
    throughput: number;
  };
  latency: {
    p50: number;
    p95: number;
    p99: number;
    mean: number;
  };
  fraud: {
    detectionsPerMinute: number;
    falsePositiveRate: number;
    accuracy: number;
    avgConfidence: number;
  };
  compliance: {
    auditTrailCompleteness: number;
    dataIntegrityScore: number;
    regulatoryCompliance: number;
    violations: ComplianceViolation[];
  };
  resources: {
    cpuUsage: number;
    memoryUsage: number;
    networkThroughput: number;
    diskIOPS: number;
  };
  institutions: InstitutionMetrics[];
}

interface InstitutionMetrics {
  id: string;
  name: string;
  transactionVolume: number;
  fraudRate: number;
  latency: number;
  availability: number;
  complianceScore: number;
}

interface ComplianceViolation {
  id: string;
  type: string;
  severity: 'LOW' | 'MEDIUM' | 'HIGH' | 'CRITICAL';
  description: string;
  timestamp: number;
  institutionId: string;
  resolved: boolean;
}

interface AlertConfig {
  latencyThreshold: number;
  fraudRateThreshold: number;
  availabilityThreshold: number;
  complianceThreshold: number;
}

// Custom hooks
const useWebSocket = (url: string) => {
  const [data, setData] = useState<DashboardMetrics | null>(null);
  const [connected, setConnected] = useState(false);

  useEffect(() => {
    const ws = new WebSocket(url);
    
    ws.onopen = () => setConnected(true);
    ws.onclose = () => setConnected(false);
    ws.onerror = () => setConnected(false);
    
    ws.onmessage = (event) => {
      try {
        const metrics = JSON.parse(event.data);
        setData(metrics);
      } catch (error) {
        console.error('Failed to parse WebSocket data:', error);
      }
    };

    return () => ws.close();
  }, [url]);

  return { data, connected };
};

const usePolling = (url: string, interval: number = 5000) => {
  const [data, setData] = useState<DashboardMetrics | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const fetchData = useCallback(async () => {
    try {
      setLoading(true);
      setError(null);
      
      const response = await fetch(url);
      if (!response.ok) {
        throw new Error(`HTTP ${response.status}: ${response.statusText}`);
      }
      
      const metrics = await response.json();
      setData(metrics);
    } catch (err) {
      setError(err instanceof Error ? err.message : 'Unknown error');
    } finally {
      setLoading(false);
    }
  }, [url]);

  useEffect(() => {
    fetchData(); // Initial fetch
    const intervalId = setInterval(fetchData, interval);
    return () => clearInterval(intervalId);
  }, [fetchData, interval]);

  return { data, loading, error, refetch: fetchData };
};

// Utility components
const MetricCard: React.FC<{
  title: string;
  value: string | number;
  change?: number;
  icon: React.ReactNode;
  color: string;
  trend?: 'up' | 'down' | 'neutral';
}> = ({ title, value, change, icon, color, trend }) => {
  return (
    <div className="bg-white rounded-lg shadow-md p-6 border-l-4" style={{ borderColor: color }}>
      <div className="flex items-center justify-between">
        <div>
          <p className="text-sm font-medium text-gray-600">{title}</p>
          <p className="text-2xl font-bold text-gray-900">{value}</p>
          {change !== undefined && (
            <div className="flex items-center mt-1">
              {trend === 'up' && <TrendingUp className="w-4 h-4 text-green-500 mr-1" />}
              {trend === 'down' && <TrendingDown className="w-4 h-4 text-red-500 mr-1" />}
              <span className={`text-sm ${
                trend === 'up' ? 'text-green-600' : 
                trend === 'down' ? 'text-red-600' : 'text-gray-600'
              }`}>
                {change > 0 ? '+' : ''}{change.toFixed(1)}%
              </span>
            </div>
          )}
        </div>
        <div className="text-3xl" style={{ color }}>
          {icon}
        </div>
      </div>
    </div>
  );
};

const StatusIndicator: React.FC<{
  status: 'healthy' | 'warning' | 'critical';
  label: string;
}> = ({ status, label }) => {
  const colors = {
    healthy: 'text-green-600',
    warning: 'text-yellow-600',
    critical: 'text-red-600'
  };

  const icons = {
    healthy: <CheckCircle className="w-4 h-4" />,
    warning: <AlertTriangle className="w-4 h-4" />,
    critical: <XCircle className="w-4 h-4" />
  };

  return (
    <div className={`flex items-center space-x-2 ${colors[status]}`}>
      {icons[status]}
      <span className="text-sm font-medium">{label}</span>
    </div>
  );
};

const ComplianceViolationItem: React.FC<{
  violation: ComplianceViolation;
  onResolve: (id: string) => void;
}> = ({ violation, onResolve }) => {
  const severityColors = {
    LOW: 'bg-blue-100 text-blue-800',
    MEDIUM: 'bg-yellow-100 text-yellow-800',
    HIGH: 'bg-orange-100 text-orange-800',
    CRITICAL: 'bg-red-100 text-red-800'
  };

  return (
    <div className="border-l-4 border-red-400 bg-red-50 p-4 mb-3">
      <div className="flex justify-between items-start">
        <div className="flex-1">
          <div className="flex items-center mb-2">
            <span className={`px-2 py-1 rounded-full text-xs font-medium ${severityColors[violation.severity]}`}>
              {violation.severity}
            </span>
            <span className="ml-2 text-sm text-gray-600">
              {new Date(violation.timestamp).toLocaleString()}
            </span>
          </div>
          <h4 className="text-sm font-medium text-gray-900 mb-1">{violation.type}</h4>
          <p className="text-sm text-gray-700">{violation.description}</p>
          <p className="text-xs text-gray-500 mt-1">Institution: {violation.institutionId}</p>
        </div>
        {!violation.resolved && (
          <button
            onClick={() => onResolve(violation.id)}
            className="ml-4 px-3 py-1 bg-green-600 text-white text-xs rounded hover:bg-green-700"
          >
            Resolve
          </button>
        )}
      </div>
    </div>
  );
};

// Main dashboard component
const FinancialServicesDashboard: React.FC = () => {
  const [activeTab, setActiveTab] = useState<'overview' | 'performance' | 'compliance' | 'institutions'>('overview');
  const [timeRange, setTimeRange] = useState<'5m' | '1h' | '24h' | '7d'>('1h');
  const [alertConfig, setAlertConfig] = useState<AlertConfig>({
    latencyThreshold: 5.0,
    fraudRateThreshold: 0.1,
    availabilityThreshold: 99.9,
    complianceThreshold: 95.0
  });

  // Data sources - in production, these would come from actual APIs
  const { data: metricsData, loading, error, refetch } = usePolling(
    'http://localhost:3001/api/metrics',
    2000 // 2 second polling
  );

  const { data: realtimeData, connected } = useWebSocket('ws://localhost:3001/ws/metrics');

  // Use real-time data if available, otherwise fall back to polling
  const currentData = realtimeData || metricsData;

  // Generate mock data for demonstration
  const mockData = useMemo(() => {
    if (currentData) return currentData;

    return {
      timestamp: Date.now(),
      transactions: {
        total: 45672,
        successful: 45234,
        failed: 438,
        fraudulent: 89,
        throughput: 1234.5
      },
      latency: {
        p50: 0.8,
        p95: 2.1,
        p99: 4.5,
        mean: 1.2
      },
      fraud: {
        detectionsPerMinute: 12,
        falsePositiveRate: 0.03,
        accuracy: 0.987,
        avgConfidence: 0.92
      },
      compliance: {
        auditTrailCompleteness: 100.0,
        dataIntegrityScore: 99.97,
        regulatoryCompliance: 98.5,
        violations: [
          {
            id: 'v1',
            type: 'BASEL_III_VIOLATION',
            severity: 'HIGH' as const,
            description: 'Capital adequacy ratio below threshold for BANK_EU_001',
            timestamp: Date.now() - 300000,
            institutionId: 'BANK_EU_001',
            resolved: false
          }
        ]
      },
      resources: {
        cpuUsage: 34.5,
        memoryUsage: 67.8,
        networkThroughput: 125.6,
        diskIOPS: 1205
      },
      institutions: [
        {
          id: 'BANK_US_001',
          name: 'First National Bank',
          transactionVolume: 15234,
          fraudRate: 0.019,
          latency: 0.9,
          availability: 99.98,
          complianceScore: 99.1
        },
        {
          id: 'BANK_UK_001',
          name: 'London Financial Group',
          transactionVolume: 12456,
          fraudRate: 0.021,
          latency: 1.1,
          availability: 99.95,
          complianceScore: 98.7
        },
        {
          id: 'BANK_EU_001',
          name: 'European Banking Corp',
          transactionVolume: 9876,
          fraudRate: 0.025,
          latency: 1.3,
          availability: 99.89,
          complianceScore: 97.2
        }
      ]
    } as DashboardMetrics;
  }, [currentData]);

  // Historical data for charts (mock)
  const historicalData = useMemo(() => {
    const data = [];
    const now = Date.now();
    const interval = timeRange === '5m' ? 5000 : timeRange === '1h' ? 60000 : timeRange === '24h' ? 3600000 : 86400000;
    const points = 50;

    for (let i = points; i >= 0; i--) {
      data.push({
        timestamp: now - (i * interval),
        time: new Date(now - (i * interval)).toLocaleTimeString(),
        latency: 0.5 + Math.random() * 2,
        throughput: 800 + Math.random() * 400,
        fraudRate: 0.01 + Math.random() * 0.02,
        cpuUsage: 30 + Math.random() * 40,
        memoryUsage: 60 + Math.random() * 20
      });
    }

    return data;
  }, [timeRange]);

  const handleResolveViolation = (violationId: string) => {
    // In production, this would make an API call to resolve the violation
    console.log('Resolving violation:', violationId);
  };

  const exportReport = () => {
    const report = {
      timestamp: new Date().toISOString(),
      metrics: mockData,
      historicalData: historicalData.slice(-10) // Last 10 data points
    };

    const blob = new Blob([JSON.stringify(report, null, 2)], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `financial-mcp-report-${Date.now()}.json`;
    a.click();
    URL.revokeObjectURL(url);
  };

  const getSystemStatus = () => {
    if (!mockData) return 'critical';
    
    const { latency, transactions, compliance } = mockData;
    const availability = (transactions.successful / transactions.total) * 100;
    
    if (latency.p99 > alertConfig.latencyThreshold || 
        availability < alertConfig.availabilityThreshold ||
        compliance.regulatoryCompliance < alertConfig.complianceThreshold) {
      return 'critical';
    }
    
    if (latency.p95 > alertConfig.latencyThreshold * 0.8 ||
        availability < alertConfig.availabilityThreshold + 0.1) {
      return 'warning';
    }
    
    return 'healthy';
  };

  if (error) {
    return (
      <div className="min-h-screen bg-gray-100 flex items-center justify-center">
        <div className="bg-white rounded-lg shadow-lg p-8 max-w-md text-center">
          <XCircle className="w-16 h-16 text-red-500 mx-auto mb-4" />
          <h2 className="text-xl font-bold text-gray-900 mb-2">Dashboard Error</h2>
          <p className="text-gray-600 mb-4">{error}</p>
          <button
            onClick={refetch}
            className="px-4 py-2 bg-blue-600 text-white rounded hover:bg-blue-700"
          >
            Retry Connection
          </button>
        </div>
      </div>
    );
  }

  if (!mockData) {
    return (
      <div className="min-h-screen bg-gray-100 flex items-center justify-center">
        <div className="text-center">
          <div className="animate-spin rounded-full h-16 w-16 border-b-2 border-blue-600 mx-auto mb-4"></div>
          <p className="text-gray-600">Loading dashboard...</p>
        </div>
      </div>
    );
  }

  return (
    <div className="min-h-screen bg-gray-100">
      {/* Header */}
      <header className="bg-white shadow-sm border-b">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
          <div className="flex justify-between items-center py-4">
            <div className="flex items-center space-x-4">
              <h1 className="text-2xl font-bold text-gray-900">Financial Services MCP</h1>
              <div className="flex items-center space-x-2">
                <StatusIndicator 
                  status={getSystemStatus()} 
                  label={`System ${getSystemStatus()}`}
                />
                {connected && (
                  <div className="flex items-center text-green-600">
                    <div className="w-2 h-2 bg-green-600 rounded-full mr-2 animate-pulse"></div>
                    <span className="text-sm">Real-time</span>
                  </div>
                )}
              </div>
            </div>
            
            <div className="flex items-center space-x-4">
              <select
                value={timeRange}
                onChange={(e) => setTimeRange(e.target.value as any)}
                className="border border-gray-300 rounded px-3 py-1 text-sm"
              >
                <option value="5m">Last 5 minutes</option>
                <option value="1h">Last hour</option>
                <option value="24h">Last 24 hours</option>
                <option value="7d">Last 7 days</option>
              </select>
              
              <button
                onClick={refetch}
                className="p-2 text-gray-600 hover:text-gray-900"
                title="Refresh data"
              >
                <RefreshCw className={`w-4 h-4 ${loading ? 'animate-spin' : ''}`} />
              </button>
              
              <button
                onClick={exportReport}
                className="flex items-center space-x-2 px-4 py-2 bg-blue-600 text-white rounded hover:bg-blue-700"
              >
                <Download className="w-4 h-4" />
                <span>Export</span>
              </button>
            </div>
          </div>
        </div>
      </header>

      {/* Navigation */}
      <nav className="bg-white shadow-sm">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
          <div className="flex space-x-8">
            {[
              { id: 'overview', label: 'Overview', icon: <Activity className="w-4 h-4" /> },
              { id: 'performance', label: 'Performance', icon: <Zap className="w-4 h-4" /> },
              { id: 'compliance', label: 'Compliance', icon: <Shield className="w-4 h-4" /> },
              { id: 'institutions', label: 'Institutions', icon: <Users className="w-4 h-4" /> }
            ].map(tab => (
              <button
                key={tab.id}
                onClick={() => setActiveTab(tab.id as any)}
                className={`flex items-center space-x-2 py-4 px-1 border-b-2 text-sm font-medium ${
                  activeTab === tab.id
                    ? 'border-blue-500 text-blue-600'
                    : 'border-transparent text-gray-500 hover:text-gray-700 hover:border-gray-300'
                }`}
              >
                {tab.icon}
                <span>{tab.label}</span>
              </button>
            ))}
          </div>
        </div>
      </nav>

      {/* Main Content */}
      <main className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 py-8">
        {activeTab === 'overview' && (
          <div className="space-y-8">
            {/* Key Metrics */}
            <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-6">
              <MetricCard
                title="Total Transactions"
                value={mockData.transactions.total.toLocaleString()}
                change={5.2}
                trend="up"
                icon={<Database />}
                color="#3B82F6"
              />
              <MetricCard
                title="Fraud Detections"
                value={mockData.transactions.fraudulent}
                change={-12.3}
                trend="down"
                icon={<Shield />}
                color="#EF4444"
              />
              <MetricCard
                title="P99 Latency"
                value={`${mockData.latency.p99.toFixed(2)}ms`}
                change={-8.1}
                trend="down"
                icon={<Clock />}
                color="#10B981"
              />
              <MetricCard
                title="Throughput"
                value={`${mockData.transactions.throughput.toFixed(0)} TPS`}
                change={15.7}
                trend="up"
                icon={<TrendingUp />}
                color="#8B5CF6"
              />
            </div>

            {/* Charts Row */}
            <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
              {/* Latency Chart */}
              <div className="bg-white rounded-lg shadow-md p-6">
                <h3 className="text-lg font-semibold text-gray-900 mb-4">Latency Trends</h3>
                <ResponsiveContainer width="100%" height={300}>
                  <LineChart data={historicalData}>
                    <CartesianGrid strokeDasharray="3 3" />
                    <XAxis dataKey="time" />
                    <YAxis />
                    <Tooltip />
                    <Legend />
                    <Line 
                      type="monotone" 
                      dataKey="latency" 
                      stroke="#3B82F6" 
                      strokeWidth={2}
                      name="Latency (ms)"
                    />
                  </LineChart>
                </ResponsiveContainer>
              </div>

              {/* Throughput Chart */}
              <div className="bg-white rounded-lg shadow-md p-6">
                <h3 className="text-lg font-semibold text-gray-900 mb-4">Throughput</h3>
                <ResponsiveContainer width="100%" height={300}>
                  <AreaChart data={historicalData}>
                    <CartesianGrid strokeDasharray="3 3" />
                    <XAxis dataKey="time" />
                    <YAxis />
                    <Tooltip />
                    <Legend />
                    <Area 
                      type="monotone" 
                      dataKey="throughput" 
                      stroke="#10B981" 
                      fill="#10B981"
                      fillOpacity={0.6}
                      name="TPS"
                    />
                  </AreaChart>
                </ResponsiveContainer>
              </div>
            </div>

            {/* System Status */}
            <div className="bg-white rounded-lg shadow-md p-6">
              <h3 className="text-lg font-semibold text-gray-900 mb-4">System Health</h3>
              <div className="grid grid-cols-1 md:grid-cols-4 gap-4">
                <div className="text-center">
                  <div className="text-2xl font-bold text-green-600">
                    {((mockData.transactions.successful / mockData.transactions.total) * 100).toFixed(2)}%
                  </div>
                  <div className="text-sm text-gray-600">Success Rate</div>
                </div>
                <div className="text-center">
                  <div className="text-2xl font-bold text-blue-600">
                    {mockData.fraud.accuracy * 100}%
                  </div>
                  <div className="text-sm text-gray-600">Fraud Detection Accuracy</div>
                </div>
                <div className="text-center">
                  <div className="text-2xl font-bold text-purple-600">
                    {mockData.compliance.auditTrailCompleteness}%
                  </div>
                  <div className="text-sm text-gray-600">Audit Completeness</div>
                </div>
                <div className="text-center">
                  <div className="text-2xl font-bold text-indigo-600">
                    {mockData.compliance.regulatoryCompliance}%
                  </div>
                  <div className="text-sm text-gray-600">Regulatory Compliance</div>
                </div>
              </div>
            </div>
          </div>
        )}

        {activeTab === 'performance' && (
          <div className="space-y-8">
            {/* Performance Metrics */}
            <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
              <div className="bg-white rounded-lg shadow-md p-6">
                <h3 className="text-lg font-semibold text-gray-900 mb-4">Latency Distribution</h3>
                <ResponsiveContainer width="100%" height={300}>
                  <BarChart data={[
                    { name: 'P50', value: mockData.latency.p50 },
                    { name: 'P95', value: mockData.latency.p95 },
                    { name: 'P99', value: mockData.latency.p99 },
                    { name: 'Mean', value: mockData.latency.mean }
                  ]}>
                    <CartesianGrid strokeDasharray="3 3" />
                    <XAxis dataKey="name" />
                    <YAxis />
                    <Tooltip />
                    <Bar dataKey="value" fill="#3B82F6" />
                  </BarChart>
                </ResponsiveContainer>
              </div>

              <div className="bg-white rounded-lg shadow-md p-6">
                <h3 className="text-lg font-semibold text-gray-900 mb-4">Resource Usage</h3>
                <ResponsiveContainer width="100%" height={300}>
                  <LineChart data={historicalData}>
                    <CartesianGrid strokeDasharray="3 3" />
                    <XAxis dataKey="time" />
                    <YAxis />
                    <Tooltip />
                    <Legend />
                    <Line 
                      type="monotone" 
                      dataKey="cpuUsage" 
                      stroke="#EF4444" 
                      name="CPU %"
                    />
                    <Line 
                      type="monotone" 
                      dataKey="memoryUsage" 
                      stroke="#10B981" 
                      name="Memory %"
                    />
                  </LineChart>
                </ResponsiveContainer>
              </div>
            </div>

            {/* Resource Gauges */}
            <div className="grid grid-cols-1 md:grid-cols-4 gap-6">
              {[
                { name: 'CPU Usage', value: mockData.resources.cpuUsage, unit: '%', max: 100 },
                { name: 'Memory Usage', value: mockData.resources.memoryUsage, unit: '%', max: 100 },
                { name: 'Network', value: mockData.resources.networkThroughput, unit: 'MB/s', max: 200 },
                { name: 'Disk IOPS', value: mockData.resources.diskIOPS, unit: '', max: 2000 }
              ].map(metric => (
                <div key={metric.name} className="bg-white rounded-lg shadow-md p-6 text-center">
                  <h4 className="text-sm font-medium text-gray-600 mb-2">{metric.name}</h4>
                  <div className="text-2xl font-bold text-gray-900 mb-2">
                    {metric.value.toFixed(1)}{metric.unit}
                  </div>
                  <div className="w-full bg-gray-200 rounded-full h-2">
                    <div 
                      className="bg-blue-600 h-2 rounded-full" 
                      style={{ width: `${(metric.value / metric.max) * 100}%` }}
                    ></div>
                  </div>
                </div>
              ))}
            </div>
          </div>
        )}

        {activeTab === 'compliance' && (
          <div className="space-y-8">
            {/* Compliance Score */}
            <div className="bg-white rounded-lg shadow-md p-6">
              <h3 className="text-lg font-semibold text-gray-900 mb-4">Compliance Overview</h3>
              <div className="grid grid-cols-1 md:grid-cols-3 gap-6">
                <div className="text-center">
                  <div className="text-3xl font-bold text-green-600 mb-2">
                    {mockData.compliance.auditTrailCompleteness}%
                  </div>
                  <div className="text-sm text-gray-600">Audit Trail Completeness</div>
                </div>
                <div className="text-center">
                  <div className="text-3xl font-bold text-blue-600 mb-2">
                    {mockData.compliance.dataIntegrityScore}%
                  </div>
                  <div className="text-sm text-gray-600">Data Integrity Score</div>
                </div>
                <div className="text-center">
                  <div className="text-3xl font-bold text-purple-600 mb-2">
                    {mockData.compliance.regulatoryCompliance}%
                  </div>
                  <div className="text-sm text-gray-600">Regulatory Compliance</div>
                </div>
              </div>
            </div>

            {/* Violations */}
            <div className="bg-white rounded-lg shadow-md p-6">
              <div className="flex justify-between items-center mb-4">
                <h3 className="text-lg font-semibold text-gray-900">Compliance Violations</h3>
                <span className="bg-red-100 text-red-800 px-2 py-1 rounded-full text-sm">
                  {mockData.compliance.violations.filter(v => !v.resolved).length} Active
                </span>
              </div>
              
              {mockData.compliance.violations.length === 0 ? (
                <div className="text-center py-8 text-gray-500">
                  <CheckCircle className="w-16 h-16 mx-auto mb-4 text-green-500" />
                  <p>No compliance violations detected</p>
                </div>
              ) : (
                <div className="space-y-3">
                  {mockData.compliance.violations.map(violation => (
                    <ComplianceViolationItem
                      key={violation.id}
                      violation={violation}
                      onResolve={handleResolveViolation}
                    />
                  ))}
                </div>
              )}
            </div>
          </div>
        )}

        {activeTab === 'institutions' && (
          <div className="space-y-8">
            {/* Institution Cards */}
            <div className="grid grid-cols-1 lg:grid-cols-3 gap-6">
              {mockData.institutions.map(institution => (
                <div key={institution.id} className="bg-white rounded-lg shadow-md p-6">
                  <div className="flex justify-between items-start mb-4">
                    <div>
                      <h3 className="font-semibold text-gray-900">{institution.name}</h3>
                      <p className="text-sm text-gray-600">{institution.id}</p>
                    </div>
                    <StatusIndicator
                      status={institution.availability > 99.9 ? 'healthy' : institution.availability > 99.5 ? 'warning' : 'critical'}
                      label={`${institution.availability}%`}
                    />
                  </div>
                  
                  <div className="space-y-3">
                    <div className="flex justify-between">
                      <span className="text-sm text-gray-600">Transaction Volume</span>
                      <span className="text-sm font-medium">{institution.transactionVolume.toLocaleString()}</span>
                    </div>
                    <div className="flex justify-between">
                      <span className="text-sm text-gray-600">Fraud Rate</span>
                      <span className="text-sm font-medium">{(institution.fraudRate * 100).toFixed(2)}%</span>
                    </div>
                    <div className="flex justify-between">
                      <span className="text-sm text-gray-600">Avg Latency</span>
                      <span className="text-sm font-medium">{institution.latency.toFixed(1)}ms</span>
                    </div>
                    <div className="flex justify-between">
                      <span className="text-sm text-gray-600">Compliance Score</span>
                      <span className="text-sm font-medium">{institution.complianceScore}%</span>
                    </div>
                  </div>
                </div>
              ))}
            </div>

            {/* Institution Comparison Chart */}
            <div className="bg-white rounded-lg shadow-md p-6">
              <h3 className="text-lg font-semibold text-gray-900 mb-4">Institution Performance Comparison</h3>
              <ResponsiveContainer width="100%" height={400}>
                <BarChart data={mockData.institutions}>
                  <CartesianGrid strokeDasharray="3 3" />
                  <XAxis dataKey="name" />
                  <YAxis />
                  <Tooltip />
                  <Legend />
                  <Bar dataKey="transactionVolume" fill="#3B82F6" name="Transaction Volume" />
                  <Bar dataKey="complianceScore" fill="#10B981" name="Compliance Score" />
                </BarChart>
              </ResponsiveContainer>
            </div>
          </div>
        )}
      </main>
    </div>
  );
};

export default FinancialServicesDashboard;
