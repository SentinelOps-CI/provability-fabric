import React, { useState, useEffect } from 'react';
import { Card, CardContent, CardHeader, CardTitle } from './ui/card';
import { Badge } from './ui/badge';
import { Progress } from './ui/progress';
import { Clock, TrendingUp, TrendingDown, AlertTriangle } from 'lucide-react';

interface SLOData {
  p95: number;
  p99: number;
  error_rate: number;
  components: {
    plan_generation: number;
    retrieval_gateway: number;
    policy_kernel: number;
    egress_firewall: number;
    proof_replay: number;
  };
  thresholds: {
    p95_max: number;
    p99_max: number;
    error_rate_max: number;
    component_budgets: {
      plan_generation: number;
      retrieval_gateway: number;
      policy_kernel: number;
      egress_firewall: number;
      proof_replay: number;
    };
  };
}

interface SLOProps {
  className?: string;
}

export const SLO: React.FC<SLOProps> = ({ className = '' }) => {
  const [sloData, setSloData] = useState<SLOData | null>(null);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    // Mock data - in production would fetch from metrics API
    const mockData: SLOData = {
      p95: 1.8,
      p99: 3.2,
      error_rate: 0.05,
      components: {
        plan_generation: 145,
        retrieval_gateway: 580,
        policy_kernel: 115,
        egress_firewall: 385,
        proof_replay: 180
      },
      thresholds: {
        p95_max: 2.0,
        p99_max: 4.0,
        error_rate_max: 0.1,
        component_budgets: {
          plan_generation: 150,
          retrieval_gateway: 600,
          policy_kernel: 120,
          egress_firewall: 400,
          proof_replay: 200
        }
      }
    };

    setSloData(mockData);
    setLoading(false);
  }, []);

  if (loading) {
    return (
      <Card className={className}>
        <CardContent className="pt-6">
          <div className="flex justify-center items-center h-32">
            <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-blue-600"></div>
          </div>
        </CardContent>
      </Card>
    );
  }

  if (!sloData) {
    return (
      <Card className={className}>
        <CardContent className="pt-6">
          <div className="text-center text-gray-500">
            <AlertTriangle className="h-8 w-8 mx-auto mb-2" />
            <p>Unable to load SLO data</p>
          </div>
        </CardContent>
      </Card>
    );
  }

  const getStatusColor = (value: number, threshold: number) => {
    if (value <= threshold * 0.8) return 'bg-green-100 text-green-800';
    if (value <= threshold) return 'bg-yellow-100 text-yellow-800';
    return 'bg-red-100 text-red-800';
  };

  const getStatusIcon = (value: number, threshold: number) => {
    if (value <= threshold * 0.8) return <TrendingDown className="h-3 w-3 mr-1" />;
    if (value <= threshold) return <Clock className="h-3 w-3 mr-1" />;
    return <TrendingUp className="h-3 w-3 mr-1" />;
  };

  return (
    <div className={`space-y-4 ${className}`}>
      {/* Overall SLO Status */}
      <Card>
        <CardHeader>
          <CardTitle className="flex items-center space-x-2">
            <Clock className="h-5 w-5" />
            <span>Service Level Objectives</span>
          </CardTitle>
        </CardHeader>
        <CardContent>
          <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
            {/* P95 Latency */}
            <div className="space-y-2">
              <div className="flex justify-between items-center">
                <span className="text-sm font-medium">P95 Latency</span>
                <Badge 
                  variant="default" 
                  className={getStatusColor(sloData.p95, sloData.thresholds.p95_max)}
                >
                  {getStatusIcon(sloData.p95, sloData.thresholds.p95_max)}
                  {sloData.p95}s
                </Badge>
              </div>
              <Progress 
                value={(sloData.p95 / sloData.thresholds.p95_max) * 100} 
                className="h-2"
              />
              <p className="text-xs text-gray-500">Threshold: {sloData.thresholds.p95_max}s</p>
            </div>

            {/* P99 Latency */}
            <div className="space-y-2">
              <div className="flex justify-between items-center">
                <span className="text-sm font-medium">P99 Latency</span>
                <Badge 
                  variant="default" 
                  className={getStatusColor(sloData.p99, sloData.thresholds.p99_max)}
                >
                  {getStatusIcon(sloData.p99, sloData.thresholds.p99_max)}
                  {sloData.p99}s
                </Badge>
              </div>
              <Progress 
                value={(sloData.p99 / sloData.thresholds.p99_max) * 100} 
                className="h-2"
              />
              <p className="text-xs text-gray-500">Threshold: {sloData.thresholds.p99_max}s</p>
            </div>

            {/* Error Rate */}
            <div className="space-y-2">
              <div className="flex justify-between items-center">
                <span className="text-sm font-medium">Error Rate</span>
                <Badge 
                  variant="default" 
                  className={getStatusColor(sloData.error_rate * 100, sloData.thresholds.error_rate_max * 100)}
                >
                  {getStatusIcon(sloData.error_rate * 100, sloData.thresholds.error_rate_max * 100)}
                  {(sloData.error_rate * 100).toFixed(2)}%
                </Badge>
              </div>
              <Progress 
                value={(sloData.error_rate / sloData.thresholds.error_rate_max) * 100} 
                className="h-2"
              />
              <p className="text-xs text-gray-500">Threshold: {(sloData.thresholds.error_rate_max * 100).toFixed(2)}%</p>
            </div>
          </div>
        </CardContent>
      </Card>

      {/* Component Budgets */}
      <Card>
        <CardHeader>
          <CardTitle className="flex items-center space-x-2">
            <TrendingUp className="h-5 w-5" />
            <span>Component Budgets</span>
          </CardTitle>
        </CardHeader>
        <CardContent>
          <div className="space-y-4">
            {Object.entries(sloData.components).map(([component, value]) => {
              const budget = sloData.thresholds.component_budgets[component as keyof typeof sloData.thresholds.component_budgets];
              const percentage = (value / budget) * 100;
              
              return (
                <div key={component} className="space-y-2">
                  <div className="flex justify-between items-center">
                    <span className="text-sm font-medium capitalize">
                      {component.replace('_', ' ')}
                    </span>
                    <div className="flex items-center space-x-2">
                      <span className="text-sm text-gray-600">{value}ms</span>
                      <Badge 
                        variant="default" 
                        className={getStatusColor(value, budget)}
                      >
                        {getStatusIcon(value, budget)}
                        {percentage.toFixed(0)}%
                      </Badge>
                    </div>
                  </div>
                  <Progress value={percentage} className="h-2" />
                  <p className="text-xs text-gray-500">Budget: {budget}ms</p>
                </div>
              );
            })}
          </div>
        </CardContent>
      </Card>

      {/* SLO Gates Link */}
      <div className="text-center">
        <a 
          href="/.github/workflows/slo-gates.yaml" 
          target="_blank" 
          rel="noopener noreferrer"
          className="text-blue-600 hover:text-blue-800 text-sm underline"
        >
          View SLO Gates Configuration →
        </a>
      </div>
    </div>
  );
}; 