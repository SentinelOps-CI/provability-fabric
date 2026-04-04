# Engine adapters for SWE-bench (OpenHands, etc.)

try:
    from .openhands_engine import (
        OpenHandsConfig,
        EngineTrace,
        SolveResult,
        solve as openhands_solve,
    )
    from .direct_agent_engine import (
        DirectAgentConfig,
        solve as direct_agent_solve,
    )
except ImportError:
    from engines.openhands_engine import (  # type: ignore[no-redef]
        OpenHandsConfig,
        EngineTrace,
        SolveResult,
        solve as openhands_solve,
    )
    from engines.direct_agent_engine import (  # type: ignore[no-redef]
        DirectAgentConfig,
        solve as direct_agent_solve,
    )

__all__ = [
    "OpenHandsConfig",
    "SolveResult",
    "EngineTrace",
    "openhands_solve",
    "DirectAgentConfig",
    "direct_agent_solve",
]
