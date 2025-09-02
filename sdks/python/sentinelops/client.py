# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

import json
import time
from typing import List, Optional, Dict, Any, Union
import requests
from .types import *

class SentinelOpsClient:
    """Main client for SentinelOps Platform API"""
    
    def __init__(self, base_url: str = "http://localhost:8000", api_key: Optional[str] = None, timeout: int = 30):
        """
        Initialize SentinelOps client
        
        Args:
            base_url: Platform API base URL
            api_key: Optional API key for authentication
            timeout: Request timeout in seconds
        """
        self.base_url = base_url.rstrip('/')
        self.timeout = timeout
        self.session = requests.Session()
        
        if api_key:
            self.session.headers.update({'Authorization': f'Bearer {api_key}'})
        
        self.session.headers.update({'Content-Type': 'application/json'})

    def _request(self, method: str, endpoint: str, data: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        """Make HTTP request to platform API"""
        url = f"{self.base_url}{endpoint}"
        
        try:
            if method.upper() == 'GET':
                response = self.session.get(url, timeout=self.timeout)
            elif method.upper() == 'POST':
                response = self.session.post(url, json=data, timeout=self.timeout)
            elif method.upper() == 'PUT':
                response = self.session.put(url, json=data, timeout=self.timeout)
            elif method.upper() == 'DELETE':
                response = self.session.delete(url, timeout=self.timeout)
            else:
                raise ValueError(f"Unsupported HTTP method: {method}")
            
            response.raise_for_status()
            return response.json()
            
        except requests.exceptions.Timeout:
            raise Exception(f"Request timeout after {self.timeout} seconds")
        except requests.exceptions.HTTPError as e:
            if e.response.status_code == 401:
                raise Exception("Authentication required")
            elif e.response.status_code >= 500:
                raise Exception(f"Server error: {e.response.text}")
            else:
                raise Exception(f"API error: {e.response.text}")
        except requests.exceptions.RequestException as e:
            raise Exception(f"Request failed: {str(e)}")

    # Policy API
    def compile_policy(self, request: PolicyCompileRequest) -> PolicyCompileResponse:
        """Compile English policy to ActionDSL"""
        response = self._request('POST', '/api/v1/policy/compile', request.dict())
        return PolicyCompileResponse(**response)

    def build_policy(self, request: PolicyBuildRequest) -> PolicyBuildResponse:
        """Build policy (ActionDSL to DFA)"""
        response = self._request('POST', '/api/v1/policy/build', request.dict())
        return PolicyBuildResponse(**response)

    def run_proofs(self, request: ProofRunRequest) -> ProofRunResponse:
        """Run Lean proofs for policy"""
        response = self._request('POST', '/api/v1/proofs/run', request.dict())
        return ProofRunResponse(**response)

    def deploy_policy(self, request: DeployRequest) -> Dict[str, Any]:
        """Deploy policy to runtime"""
        return self._request('POST', '/api/v1/runtime/deploy', request.dict())

    def list_policies(self) -> List[Dict[str, Any]]:
        """List all policies"""
        response = self._request('GET', '/api/v1/policies')
        return response['policies']

    # Certificate API
    def verify_cert(self, cert: CertV1) -> bool:
        """Verify CERT-V1 certificate"""
        try:
            self._request('POST', '/api/v1/evidence/cert', cert.dict())
            return True
        except Exception:
            return False

    def search_certificates(self, request: CertSearchRequest) -> CertSearchResponse:
        """Search certificates with filters"""
        response = self._request('POST', '/api/v1/evidence/search', request.dict())
        return CertSearchResponse(**response)

    def get_certificate(self, cert_id: str) -> CertV1:
        """Get specific certificate"""
        response = self._request('GET', f'/api/v1/evidence/cert/{cert_id}')
        return CertV1(**response)

    # Replay API
    def start_replay(self, request: ReplayRequest) -> ReplayResponse:
        """Start deterministic replay"""
        response = self._request('POST', '/api/v1/replay', request.dict())
        return ReplayResponse(**response)

    def get_replay_status(self, job_id: str) -> ReplayStatus:
        """Get replay job status"""
        response = self._request('GET', f'/api/v1/replay/{job_id}')
        return ReplayStatus(**response)

    def download_packet(self, decision_id: str) -> bytes:
        """Download compliance packet"""
        # Create packet
        packet_response = self._request('POST', '/api/v1/compliance/packet', {
            'session_id': decision_id
        })
        
        packet_id = packet_response['packet_id']
        
        # Download packet
        url = f"{self.base_url}/api/v1/compliance/packet/{packet_id}"
        response = self.session.get(url, timeout=self.timeout)
        response.raise_for_status()
        
        return response.content

    # Epoch operations
    def rotate_epoch(self, old_epoch: int, new_epoch: int, reason: Optional[str] = None) -> Dict[str, Any]:
        """Rotate permission epoch"""
        data = {
            'old_epoch': old_epoch,
            'new_epoch': new_epoch,
        }
        if reason:
            data['reason'] = reason
            
        return self._request('POST', '/api/v1/runtime/epoch/rotate', data)

    # Health and monitoring
    def get_health(self) -> Dict[str, Any]:
        """Get platform health status"""
        return self._request('GET', '/health')

    def get_slo(self) -> Dict[str, Any]:
        """Get runtime SLO metrics"""
        return self._request('GET', '/api/v1/runtime/slo')

    # CI helpers
    def assert_certs_valid(self, certs: List[CertV1]) -> bool:
        """Assert all certificates are valid (CI helper)"""
        for cert in certs:
            if not self.verify_cert(cert):
                return False
        return True

    def assert_low_view(self, replay_id: str, threshold: float = 0.999) -> bool:
        """Assert replay low-view match meets threshold (CI helper)"""
        status = self.get_replay_status(replay_id)
        return status.low_view_match_pct >= threshold

    def wait_for_replay(self, job_id: str, timeout_seconds: int = 300) -> ReplayStatus:
        """Wait for replay completion with timeout"""
        start_time = time.time()
        
        while time.time() - start_time < timeout_seconds:
            status = self.get_replay_status(job_id)
            
            if status.status in ['completed', 'failed']:
                return status
            
            time.sleep(2)
        
        raise Exception(f"Replay timeout after {timeout_seconds} seconds")

    # Convenience methods for common workflows
    def full_policy_workflow(self, english_policy: str, policy_id: str) -> Dict[str, str]:
        """Execute complete policy workflow: compile -> prove -> build -> deploy"""
        
        # 1. Compile
        compile_req = PolicyCompileRequest(
            english=english_policy,
            policy_id=policy_id,
            version="1.0.0"
        )
        compile_resp = self.compile_policy(compile_req)
        
        # 2. Run proofs
        proof_req = ProofRunRequest(
            policy_hash=compile_resp.policy_hash,
            action_dsl=compile_resp.actionDsl
        )
        proof_resp = self.run_proofs(proof_req)
        
        # 3. Build policy
        build_req = PolicyBuildRequest(
            policy_hash=compile_resp.policy_hash,
            action_dsl=compile_resp.actionDsl,
            proof_hash=proof_resp.proof_hash
        )
        build_resp = self.build_policy(build_req)
        
        # 4. Deploy
        deploy_req = DeployRequest(
            policy_hash=compile_resp.policy_hash,
            automata_hash=build_resp.automata_hash,
            epoch=1
        )
        deploy_resp = self.deploy_policy(deploy_req)
        
        return {
            'policy_hash': compile_resp.policy_hash,
            'proof_hash': proof_resp.proof_hash,
            'automata_hash': build_resp.automata_hash,
            'epoch': str(deploy_resp.get('epoch', 1)),
            'status': 'deployed'
        }