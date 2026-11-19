"""Fail-closed coverage accounting for service-backed red-team harnesses.

A passing coverage result is a necessary execution condition, not a proof of
ABAC noninterference or correctness of the target service.
"""

from __future__ import annotations


def observation_failures(
    *,
    planned: int,
    recorded: int,
    valid_responses: int,
    positive_controls: int,
    violations: int,
) -> list[str]:
    """Report missing evidence or unsuccessful observations.

    `valid_responses` counts the cases that received and parsed an expected
    service response. `positive_controls` counts actual nonempty observations
    or detected blocks, not assertions constructed by the harness itself.
    """
    problems: list[str] = []
    if planned <= 0:
        problems.append("no requests were planned")
    if recorded != planned:
        problems.append(f"observed {recorded} of {planned} planned requests")
    if not 0 <= valid_responses <= recorded:
        problems.append("response accounting is inconsistent")
    elif valid_responses != recorded:
        problems.append(f"{recorded - valid_responses} requests lacked valid responses")
    if positive_controls <= 0:
        problems.append("no positive control observations were recorded")
    if violations < 0:
        problems.append("violation count is invalid")
    elif violations:
        problems.append(f"{violations} observed violations")
    return problems
