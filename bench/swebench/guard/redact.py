# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Redaction of secrets from tool outputs before writing to the ledger.

from __future__ import annotations

import re
from typing import List, Tuple

SECRET_PATTERNS: List[Tuple[re.Pattern, str]] = [
    (re.compile(r"\bAKIA[0-9A-Z]{16}\b"), "[AWS-ACCESS-KEY-REDACTED]"),
    (re.compile(r"\bghp_[A-Za-z0-9]{36}\b"), "[GITHUB-TOKEN-REDACTED]"),
    (re.compile(r"\bgho_[A-Za-z0-9]{36}\b"), "[GITHUB-OAUTH-REDACTED]"),
    (re.compile(r"\bsk-[A-Za-z0-9]{48}\b"), "[OPENAI-KEY-REDACTED]"),
    (re.compile(r"\bAIza[A-Za-z0-9_-]{35}\b"), "[GOOGLE-API-KEY-REDACTED]"),
    (re.compile(r"\bxox[baprs]-[A-Za-z0-9-]+\b"), "[SLACK-TOKEN-REDACTED]"),
    (re.compile(r"\beyJ[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+\.[A-Za-z0-9_.+/=-]*\b"), "[JWT-REDACTED]"),
    (re.compile(r"-----BEGIN (?:RSA |EC )?PRIVATE KEY-----[\s\S]+?-----END (?:RSA |EC )?PRIVATE KEY-----"), "[PRIVATE-KEY-REDACTED]"),
    (re.compile(r"-----BEGIN OPENSSH PRIVATE KEY-----[\s\S]+?-----END OPENSSH PRIVATE KEY-----"), "[SSH-KEY-REDACTED]"),
    (re.compile(r"\b(?:password|passwd|secret|api_key)\s*[:=]\s*['\"]?[^\s'\"]+['\"]?", re.I), "[SECRET-VALUE-REDACTED]"),
]


def redact_secrets(text: str) -> str:
    """Return text with secret-like substrings replaced by labels."""
    if not text:
        return text
    out = text
    for pattern, label in SECRET_PATTERNS:
        out = pattern.sub(label, out)
    return out
