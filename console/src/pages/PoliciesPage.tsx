import React, { useState } from 'react';
import { useQuery, useMutation, useQueryClient } from 'react-query';
import { toast } from 'react-hot-toast';
import {
  PlayIcon,
  DocumentCheckIcon,
  RocketLaunchIcon,
  ClockIcon,
  Cog6ToothIcon,
} from '@heroicons/react/24/outline';
import { compilePolicy, buildPolicy, runProofs, deployPolicy } from '../services/api';

interface Policy {
  policy_id: string;
  version: string;
  english: string;
  actionDsl?: any;
  policy_hash?: string;
  proof_hash?: string;
  dfa_hash?: string;
  automata_hash?: string;
  labeler_hash?: string;
  status: 'draft' | 'compiled' | 'proven' | 'built' | 'deployed';
  epoch?: number;
}

export default function PoliciesPage() {
  const [selectedPolicy, setSelectedPolicy] = useState<Policy | null>(null);
  const [englishPolicy, setEnglishPolicy] = useState('');
  const [showActionDSL, setShowActionDSL] = useState(false);
  const queryClient = useQueryClient();

  // Mock policies for demo
  const [policies, setPolicies] = useState<Policy[]>([
    {
      policy_id: 'fraud-detection-v1',
      version: '1.0.0',
      english: 'Only FraudService may call /score endpoint. Rate limit alerts to 5 per 10 seconds per tenant. Block transactions with score >= 0.93.',
      status: 'draft',
    },
  ]);

  const compileMutation = useMutation(compilePolicy, {
    onSuccess: (data, variables) => {
      const updatedPolicies = policies.map(p => 
        p.policy_id === variables.policy_id 
          ? { ...p, actionDsl: data.actionDsl, policy_hash: data.policy_hash, status: 'compiled' as const }
          : p
      );
      setPolicies(updatedPolicies);
      setShowActionDSL(true);
      toast.success('Policy compiled successfully');
    },
    onError: (error: any) => {
      toast.error(`Compilation failed: ${error.message}`);
    },
  });

  const buildMutation = useMutation(buildPolicy, {
    onSuccess: (data, variables) => {
      const updatedPolicies = policies.map(p => 
        p.policy_id === variables.policy_hash 
          ? { 
              ...p, 
              dfa_hash: data.dfa_hash,
              automata_hash: data.automata_hash,
              labeler_hash: data.labeler_hash,
              status: 'built' as const 
            }
          : p
      );
      setPolicies(updatedPolicies);
      toast.success('Policy built successfully');
    },
    onError: (error: any) => {
      toast.error(`Build failed: ${error.message}`);
    },
  });

  const proofMutation = useMutation(runProofs, {
    onSuccess: (data, variables) => {
      const updatedPolicies = policies.map(p => 
        p.policy_hash === variables.policy_hash 
          ? { ...p, proof_hash: data.proof_hash, status: 'proven' as const }
          : p
      );
      setPolicies(updatedPolicies);
      toast.success('Proofs completed successfully');
    },
    onError: (error: any) => {
      toast.error(`Proof failed: ${error.message}`);
    },
  });

  const deployMutation = useMutation(deployPolicy, {
    onSuccess: (data, variables) => {
      const updatedPolicies = policies.map(p => 
        p.policy_hash === variables.policy_hash 
          ? { ...p, epoch: data.epoch, status: 'deployed' as const }
          : p
      );
      setPolicies(updatedPolicies);
      toast.success('Policy deployed successfully');
    },
    onError: (error: any) => {
      toast.error(`Deployment failed: ${error.message}`);
    },
  });

  const handleCompile = (policy: Policy) => {
    compileMutation.mutate({
      english: policy.english,
      policy_id: policy.policy_id,
      version: policy.version,
    });
  };

  const handleBuild = (policy: Policy) => {
    if (!policy.policy_hash) {
      toast.error('Policy must be compiled first');
      return;
    }
    
    buildMutation.mutate({
      policy_hash: policy.policy_hash,
      action_dsl: policy.actionDsl,
      proof_hash: policy.proof_hash || '',
    });
  };

  const handleRunProofs = (policy: Policy) => {
    if (!policy.policy_hash) {
      toast.error('Policy must be compiled first');
      return;
    }
    
    proofMutation.mutate({
      policy_hash: policy.policy_hash,
      action_dsl: policy.actionDsl,
    });
  };

  const handleDeploy = (policy: Policy) => {
    if (!policy.automata_hash) {
      toast.error('Policy must be built first');
      return;
    }
    
    deployMutation.mutate({
      policy_hash: policy.policy_hash!,
      automata_hash: policy.automata_hash,
      epoch: (policy.epoch || 0) + 1,
    });
  };

  const handleCreatePolicy = () => {
    if (!englishPolicy.trim()) {
      toast.error('Please enter a policy description');
      return;
    }

    const newPolicy: Policy = {
      policy_id: `policy-${Date.now()}`,
      version: '1.0.0',
      english: englishPolicy,
      status: 'draft',
    };

    setPolicies([...policies, newPolicy]);
    setEnglishPolicy('');
    toast.success('Policy created');
  };

  const getStatusColor = (status: string) => {
    switch (status) {
      case 'draft': return 'bg-gray-100 text-gray-800';
      case 'compiled': return 'bg-blue-100 text-blue-800';
      case 'proven': return 'bg-green-100 text-green-800';
      case 'built': return 'bg-purple-100 text-purple-800';
      case 'deployed': return 'bg-emerald-100 text-emerald-800';
      default: return 'bg-gray-100 text-gray-800';
    }
  };

  return (
    <div className="space-y-6">
      <div className="md:flex md:items-center md:justify-between">
        <div className="flex-1 min-w-0">
          <h2 className="text-2xl font-bold leading-7 text-gray-900 sm:text-3xl sm:truncate">
            Policies
          </h2>
          <p className="mt-1 text-sm text-gray-500">
            Write policies in English, compile to ActionDSL, run proofs, and deploy
          </p>
        </div>
      </div>

      {/* Policy Creation */}
      <div className="bg-white shadow rounded-lg p-6">
        <h3 className="text-lg font-medium text-gray-900 mb-4">Create New Policy</h3>
        <div className="space-y-4">
          <div>
            <label className="block text-sm font-medium text-gray-700 mb-2">
              Policy Description (English)
            </label>
            <textarea
              rows={4}
              className="block w-full border-gray-300 rounded-md shadow-sm focus:ring-blue-500 focus:border-blue-500"
              placeholder="Describe your policy in plain English..."
              value={englishPolicy}
              onChange={(e) => setEnglishPolicy(e.target.value)}
            />
          </div>
          <button
            onClick={handleCreatePolicy}
            className="inline-flex items-center px-4 py-2 border border-transparent text-sm font-medium rounded-md shadow-sm text-white bg-blue-600 hover:bg-blue-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
          >
            Create Policy
          </button>
        </div>
      </div>

      {/* Policy List */}
      <div className="bg-white shadow overflow-hidden sm:rounded-md">
        <ul className="divide-y divide-gray-200">
          {policies.map((policy) => (
            <li key={policy.policy_id}>
              <div className="px-4 py-4 sm:px-6">
                <div className="flex items-center justify-between">
                  <div className="flex-1">
                    <div className="flex items-center justify-between">
                      <p className="text-sm font-medium text-blue-600 truncate">
                        {policy.policy_id}
                      </p>
                      <div className="ml-2 flex-shrink-0 flex">
                        <span className={`px-2 py-1 text-xs font-medium rounded-full ${getStatusColor(policy.status)}`}>
                          {policy.status}
                        </span>
                      </div>
                    </div>
                    <div className="mt-2">
                      <p className="text-sm text-gray-900">{policy.english}</p>
                    </div>
                    
                    {/* Hashes */}
                    {policy.policy_hash && (
                      <div className="mt-2 space-y-1">
                        <p className="text-xs text-gray-500">Policy Hash: {policy.policy_hash.substring(0, 16)}...</p>
                        {policy.proof_hash && (
                          <p className="text-xs text-gray-500">Proof Hash: {policy.proof_hash.substring(0, 16)}...</p>
                        )}
                        {policy.dfa_hash && (
                          <p className="text-xs text-gray-500">DFA Hash: {policy.dfa_hash.substring(0, 16)}...</p>
                        )}
                        {policy.epoch && (
                          <p className="text-xs text-gray-500">Epoch: {policy.epoch}</p>
                        )}
                      </div>
                    )}
                  </div>
                </div>
                
                {/* Action Buttons */}
                <div className="mt-4 flex space-x-2">
                  <button
                    onClick={() => handleCompile(policy)}
                    disabled={compileMutation.isLoading || policy.status !== 'draft'}
                    className="inline-flex items-center px-3 py-1.5 border border-gray-300 text-xs font-medium rounded text-gray-700 bg-white hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500 disabled:opacity-50"
                  >
                    <DocumentCheckIcon className="h-4 w-4 mr-1" />
                    Compile
                  </button>
                  
                  <button
                    onClick={() => handleRunProofs(policy)}
                    disabled={proofMutation.isLoading || !policy.policy_hash}
                    className="inline-flex items-center px-3 py-1.5 border border-gray-300 text-xs font-medium rounded text-gray-700 bg-white hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500 disabled:opacity-50"
                  >
                    <PlayIcon className="h-4 w-4 mr-1" />
                    Run Proofs
                  </button>
                  
                  <button
                    onClick={() => handleBuild(policy)}
                    disabled={buildMutation.isLoading || !policy.proof_hash}
                    className="inline-flex items-center px-3 py-1.5 border border-gray-300 text-xs font-medium rounded text-gray-700 bg-white hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500 disabled:opacity-50"
                  >
                    <Cog6ToothIcon className="h-4 w-4 mr-1" />
                    Build
                  </button>
                  
                  <button
                    onClick={() => handleDeploy(policy)}
                    disabled={deployMutation.isLoading || !policy.automata_hash}
                    className="inline-flex items-center px-3 py-1.5 border border-transparent text-xs font-medium rounded text-white bg-blue-600 hover:bg-blue-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500 disabled:opacity-50"
                  >
                    <RocketLaunchIcon className="h-4 w-4 mr-1" />
                    Deploy
                  </button>
                </div>
                
                {/* ActionDSL Preview */}
                {policy.actionDsl && showActionDSL && selectedPolicy?.policy_id === policy.policy_id && (
                  <div className="mt-4 p-4 bg-gray-50 rounded-md">
                    <h4 className="text-sm font-medium text-gray-900 mb-2">ActionDSL Preview</h4>
                    <pre className="text-xs text-gray-600 overflow-x-auto">
                      {JSON.stringify(policy.actionDsl, null, 2)}
                    </pre>
                  </div>
                )}
                
                {selectedPolicy?.policy_id === policy.policy_id && (
                  <button
                    onClick={() => setShowActionDSL(!showActionDSL)}
                    className="mt-2 text-xs text-blue-600 hover:text-blue-500"
                  >
                    {showActionDSL ? 'Hide' : 'Show'} ActionDSL
                  </button>
                )}
                
                <button
                  onClick={() => setSelectedPolicy(selectedPolicy?.policy_id === policy.policy_id ? null : policy)}
                  className="mt-2 ml-4 text-xs text-blue-600 hover:text-blue-500"
                >
                  {selectedPolicy?.policy_id === policy.policy_id ? 'Collapse' : 'Expand'}
                </button>
              </div>
            </li>
          ))}
        </ul>
      </div>

      {/* Workflow Guide */}
      <div className="bg-blue-50 border border-blue-200 rounded-md p-4">
        <h3 className="text-sm font-medium text-blue-800 mb-2">Policy Workflow</h3>
        <div className="flex items-center space-x-4 text-xs text-blue-700">
          <div className="flex items-center">
            <DocumentCheckIcon className="h-4 w-4 mr-1" />
            1. Compile
          </div>
          <div className="flex items-center">
            <PlayIcon className="h-4 w-4 mr-1" />
            2. Run Proofs
          </div>
          <div className="flex items-center">
            <Cog6ToothIcon className="h-4 w-4 mr-1" />
            3. Build
          </div>
          <div className="flex items-center">
            <RocketLaunchIcon className="h-4 w-4 mr-1" />
            4. Deploy
          </div>
        </div>
      </div>
    </div>
  );
}