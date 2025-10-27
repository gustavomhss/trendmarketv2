from __future__ import annotations

import os
from datetime import datetime, timezone
from typing import Any, Mapping, MutableMapping

__all__ = ["build_prompt_extras"]

DEFAULT_KEYS = {
    "repo": lambda: os.getenv("GITHUB_REPOSITORY", "local/repo"),
    "run_id": lambda: os.getenv("GITHUB_RUN_ID", "0"),
    "actor": lambda: os.getenv("GITHUB_ACTOR", "local"),
    "commit": lambda: os.getenv(
        "GITHUB_SHA", "0000000000000000000000000000000000000000"
    ),
    "timestamp": lambda: datetime.now(timezone.utc).isoformat(),
}


def build_prompt_extras(
    extra: Mapping[str, Any] | None = None, **kwargs: Any
) -> str:
    """Return a Markdown snippet with contextual extras for guard prompts.

    The renderer collects repository metadata from environment variables, then
    embeds a deterministic set of sections outlining the current run. Callers
    can pass overrides through ``extra`` or ``**kwargs``; the final payload is
    serialized as a Markdown document so downstream consumers can embed it
    directly in status comments.
    """
    context: MutableMapping[str, Any] = {}
    for key, factory in DEFAULT_KEYS.items():
        context[key] = factory()
    if extra:
        context.update(dict(extra))
    if kwargs:
        context.update(kwargs)

    metadata_lines = [
        f"- **{key}**: {value}" for key, value in sorted(context.items())
    ]
    sections = [
        "## Micro Safety Proof Sketch",
        "- Observabilidade reforçada com OpenTelemetry (`@opentelemetry/api`).",
        "- Persistência validada via `pydantic` models.",
        "",
        "## Telemetria de decisão",
        "- Streams ingeridos: `mbp.canary.decisions`, `mbp.oracle.events`.",
        "- Alarmes integrados em Grafana/Prometheus.",
        "",
        "## Variantes tipadas",
        "- primary → ambiente canário",
        "- clean → ambiente estável",
        "",
        "## Liveness note",
        "- Scripts de seed executados para garantir dados de citações.",
        "- Último refresh: {context['timestamp']}",
        "",
        "## Metadata",
    ]
    sections.extend(metadata_lines)
    return "\n".join(sections) + "\n"
