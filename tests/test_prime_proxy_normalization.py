# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations


def test_prime_normalization_returns_changed_and_inserts_content() -> None:
    from bench.swebench.engines.openhands_engine import _normalize_openai_payload_for_strict_servers

    payload = {
        "messages": [
            {
                "role": "assistant",
                "tool_calls": [
                    {
                        "id": "1",
                        "type": "function",
                        "function": {"name": "x", "arguments": "{}"},
                    }
                ],
            }
        ]
    }

    normalized, changed = _normalize_openai_payload_for_strict_servers(payload)
    assert changed is True
    assert normalized["messages"][0]["content"] == ""


def test_prime_normalization_handles_none_content() -> None:
    from bench.swebench.engines.openhands_engine import _normalize_openai_payload_for_strict_servers

    payload = {
        "messages": [
            {
                "role": "assistant",
                "tool_calls": [
                    {
                        "id": "1",
                        "type": "function",
                        "function": {"name": "x", "arguments": "{}"},
                    }
                ],
                "content": None,
            }
        ]
    }

    normalized, changed = _normalize_openai_payload_for_strict_servers(payload)
    assert changed is True
    assert normalized["messages"][0]["content"] == ""

