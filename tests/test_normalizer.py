from __future__ import annotations

import json
import math
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Iterable, List

import pytest

from services.oracle.normalizer.normalizer import (
    NormalizationError,
    build_event,
    equivalence_hash,
)

GOLDEN_PATH = Path("tests/goldens/normalizer")
FIXED_NOW = datetime(2025, 10, 29, 19, 10, tzinfo=timezone.utc)


def load_goldens() -> Iterable[Dict[str, object]]:
    for path in sorted(GOLDEN_PATH.glob("*.json")):
        with path.open("r", encoding="utf-8") as handle:
            yield json.load(handle)


def test_golden_events_match_expected() -> None:
    for case in load_goldens():
        event = build_event(case["input"], now=FIXED_NOW)  # type: ignore[index]
        assert dict(event) == case["expected"]  # type: ignore[index]


def test_equivalence_hash_deterministic() -> None:
    raw = {
        "title": "Riesgo País sube",
        "lang": "es",
        "category": "Mercado",
        "source": "Bolsa Lima",
        "observed_at": "2025-10-29T18:55:00Z",
        "payload": {"valor": 1.23},
    }
    event_a = build_event(raw, now=FIXED_NOW)
    event_b = build_event(raw, now=FIXED_NOW)
    assert event_a["equivalenceHash"] == event_b["equivalenceHash"]
    assert event_a["id"] == event_b["id"]
    assert event_a["equivalenceHash"] == equivalence_hash(raw["title"], raw["category"])


def test_invalid_title_length() -> None:
    raw = {
        "title": "a" * 181,
        "lang": "pt",
        "category": "economia",
        "source": "agencia",
        "observed_at": "2025-10-29T19:00:00Z",
        "payload": {},
    }
    with pytest.raises(NormalizationError):
        build_event(raw, now=FIXED_NOW)


def test_invalid_token_normalization() -> None:
    raw = {
        "title": "ok",
        "lang": "pt",
        "category": "x" * 120,
        "source": "agencia",
        "observed_at": "2025-10-29T19:00:00Z",
        "payload": {},
    }
    with pytest.raises(NormalizationError):
        build_event(raw, now=FIXED_NOW)


def test_payload_rejects_underscore_keys() -> None:
    raw = {
        "title": "ok",
        "lang": "pt",
        "category": "economia",
        "source": "agencia",
        "observed_at": "2025-10-29T19:00:00Z",
        "payload": {"_secret": 1},
    }
    with pytest.raises(NormalizationError):
        build_event(raw, now=FIXED_NOW)


def test_microbench_p95_under_threshold() -> None:
    base_payload = {
        "title": "Evento base",
        "lang": "pt",
        "category": "mercado",
        "source": "operador",
        "observed_at": "2025-10-29T18:59:00Z",
        "payload": {"valor": 1},
    }
    samples: List[float] = []
    for idx in range(1000):
        raw = dict(base_payload)
        raw["title"] = f"{base_payload['title']} {idx}"
        start = time.perf_counter()
        build_event(raw, now=FIXED_NOW)
        samples.append(time.perf_counter() - start)
    samples.sort()
    p95_index = math.ceil(0.95 * len(samples)) - 1
    p95_value_ms = samples[p95_index] * 1000
    assert p95_value_ms <= 150
