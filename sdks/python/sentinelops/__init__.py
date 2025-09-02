# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

"""
SentinelOps Platform Python SDK

Provides client libraries for:
- Policy compilation and deployment
- Certificate verification and search
- Replay execution and monitoring
- Epoch operations and CI gates
"""

from .client import SentinelOpsClient
from .types import *

__version__ = "1.0.0"
__author__ = "SentinelOps Platform Contributors"
__license__ = "Apache-2.0"

__all__ = [
    "SentinelOpsClient",
    "PolicyCompileRequest",
    "PolicyCompileResponse", 
    "PolicyBuildRequest",
    "PolicyBuildResponse",
    "ProofRunRequest",
    "ProofRunResponse",
    "CertV1",
    "CertSearchRequest",
    "CertSearchResponse",
    "ReplayRequest",
    "ReplayResponse",
    "ReplayStatus",
    "DeployRequest",
    "Diagnostic",
    "ProofShard",
]