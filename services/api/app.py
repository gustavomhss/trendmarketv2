from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional
import csv
import uuid

try:  # pragma: no cover - FastAPI optional in this environment
    from fastapi import Depends, FastAPI, HTTPException, Query
except Exception:  # pragma: no cover - provide lightweight fallbacks

    class HTTPException(Exception):
        def __init__(self, status_code: int, detail: str) -> None:
            super().__init__(detail)
            self.status_code = status_code
            self.detail = detail

    def Query(default: str, **_: object) -> str:
        return default

    def Depends(factory):
        return factory

    class FastAPI:  # minimal stub used for local execution and tests
        def __init__(self, title: str, version: str) -> None:
            self.title = title
            self.version = version
            self.routes: Dict[tuple[str, str], object] = {}

        def get(self, path: str, **_: object):
            def decorator(func):
                self.routes[("GET", path)] = func
                return func

            return decorator

        def post(self, path: str, **_: object):
            def decorator(func):
                self.routes[("POST", path)] = func
                return func

            return decorator


from services.auto_resolution.service import AutoResolutionService, TruthSourceSignal
from services.moderation.service import ModerationService
from services.oracles.aggregator import Quote, aggregate_quorum
from services.oracles.twap import TwapEngine
from services.telemetry import TelemetryManager, TelemetrySettings

DEFAULT_SYMBOL = "BRLUSD"

_TELEMETRY = TelemetryManager(TelemetrySettings(service_name="mbp-api"))


class QuoteRepository:
    def __init__(self, source: Path, symbol: str = DEFAULT_SYMBOL) -> None:
        self.source = source
        self.symbol = symbol
        self._cache: Optional[List[tuple[int, float]]] = None

    def _load(self) -> List[tuple[int, float]]:
        if self._cache is not None:
            return self._cache
        rows: List[tuple[int, float]] = []
        with self.source.open("r", encoding="utf-8") as handle:
            reader = csv.DictReader(handle)
            for row in reader:
                ts_raw = row["ts"].strip()
                price = float(row["price"])
                ts = datetime.fromisoformat(ts_raw.replace("Z", "+00:00"))
                rows.append((int(ts.timestamp() * 1000), price))
        if not rows:
            raise RuntimeError("Price stream seed is empty")
        self._cache = rows
        return rows

    def latest_quotes(self, limit: int = 3) -> List[Quote]:
        rows = self._load()[-limit:]
        quotes: List[Quote] = []
        sources = ["alpha", "beta", "gamma"]
        for idx, (ts_ms, price) in enumerate(reversed(rows)):
            source = sources[idx % len(sources)]
            jitter = 1 + (idx - 1) * 0.0002
            quotes.append(
                Quote(
                    symbol=self.symbol, price=price * jitter, ts_ms=ts_ms, source=source
                )
            )
        return quotes

    def all_samples(self) -> List[tuple[int, float]]:
        return self._load()


@dataclass
class OracleQuoteResponse:
    schema_version: int
    ts: datetime
    symbol: str
    price: float
    staleness_ms: int
    quorum_ok: bool
    divergence_pct: Optional[float]
    twap_60s: Optional[float]
    failover_source: Optional[str]
    trace_id: str

    def dict(self) -> Dict[str, object]:
        return {
            "schema_version": self.schema_version,
            "ts": self.ts.isoformat(),
            "symbol": self.symbol,
            "price": self.price,
            "staleness_ms": self.staleness_ms,
            "quorum_ok": self.quorum_ok,
            "divergence_pct": self.divergence_pct,
            "twap_60s": self.twap_60s,
            "failover_source": self.failover_source,
            "trace_id": self.trace_id,
        }


@dataclass
class ErrorResponse:
    code: str
    message: str
    trace_id: str


@dataclass
class ModerationAction:
    schema_version: int
    ts: datetime
    symbol: str
    action: str
    actor: str
    role: str
    status: str
    trace_id: str
    reason: Optional[str] = None
    evidence_uri: Optional[str] = None

    @classmethod
    def parse_obj(cls, data: Dict[str, object]) -> "ModerationAction":
        parsed = dict(data)
        ts_raw = parsed.get("ts")
        if isinstance(ts_raw, str):
            parsed["ts"] = datetime.fromisoformat(ts_raw.replace("Z", "+00:00"))
        return cls(**parsed)


@dataclass
class ResolveTruthPayload:
    value: float
    source: str
    ts: datetime

    @classmethod
    def parse_obj(cls, data: Dict[str, object]) -> "ResolveTruthPayload":
        parsed = dict(data)
        ts_raw = parsed.get("ts")
        if isinstance(ts_raw, str):
            parsed["ts"] = datetime.fromisoformat(ts_raw.replace("Z", "+00:00"))
        return cls(**parsed)


@dataclass
class ResolveQuorumPayload:
    value: float
    quorum_ok: bool
    diverg_pct: Optional[float] = None
    staleness_ms: Optional[int] = None

    @classmethod
    def parse_obj(cls, data: Dict[str, object]) -> "ResolveQuorumPayload":
        return cls(**data)


@dataclass
class ResolveApplyRequest:
    schema_version: int
    event_id: str
    truth: ResolveTruthPayload
    quorum_details: ResolveQuorumPayload
    truth_source: str
    quorum: bool
    symbol: Optional[str] = None
    manual_decision: Optional[str] = None
    reason: Optional[str] = None
    idempotency_key: Optional[str] = None
    resource_version: Optional[str] = None
    decision_id: Optional[str] = None
    payload: Optional[Dict[str, object]] = None
    actor: Optional[str] = None
    role: Optional[str] = None

    @classmethod
    def parse_obj(cls, data: Dict[str, object]) -> "ResolveApplyRequest":
        parsed = dict(data)
        parsed["truth"] = ResolveTruthPayload.parse_obj(parsed["truth"])
        parsed["quorum_details"] = ResolveQuorumPayload.parse_obj(
            parsed["quorum_details"]
        )
        return cls(**parsed)


@dataclass
class ResolveApplyResponse:
    decision_id: str
    outcome: Optional[str]
    rule: str
    trace_id: str
    resource_version: int


ORACLE_REPOSITORY = QuoteRepository(Path("seeds/s3/price_stream_sample.csv"))
MODERATION_SERVICE = ModerationService(audit_log=Path("out/moderation/audit.log"))
RESOLUTION_SERVICE = AutoResolutionService(
    audit_log=Path("out/resolve/audit.log"),
    event_log=Path("out/resolve/events.jsonl"),
    metrics_log=Path("out/resolve/metrics.jsonl"),
)

app = FastAPI(title="MBP Scale APIs", version="1.0.0")


def get_repository() -> QuoteRepository:
    return ORACLE_REPOSITORY


def get_moderation() -> ModerationService:
    return MODERATION_SERVICE


def get_auto_resolver() -> AutoResolutionService:
    return RESOLUTION_SERVICE


@app.get(
    "/oracle/quote",
    response_model=OracleQuoteResponse,
    responses={503: {"model": ErrorResponse}},
)
async def get_oracle_quote(
    symbol: str = Query(DEFAULT_SYMBOL),
    repo: QuoteRepository = Depends(get_repository),
) -> OracleQuoteResponse:
    trace_id = uuid.uuid4().hex
    with _TELEMETRY.span(
        "api.oracle.quote", attributes={"oracle.symbol": symbol, "trace_id": trace_id}
    ):
        try:
            quotes = repo.latest_quotes()
        except RuntimeError as exc:
            raise HTTPException(status_code=503, detail=str(exc)) from exc
        if not quotes:
            raise HTTPException(status_code=404, detail="symbol not found")
        now_ms = max(q.ts_ms for q in quotes)
        result = aggregate_quorum(symbol, quotes, now_ms=now_ms)
        twap_engine = TwapEngine(symbol)
        for ts_ms, price in repo.all_samples():
            twap_engine.ingest("primary", price, ts_ms)
        twap_snapshot = twap_engine.compute(now_ms=now_ms)

    if result.agg_price is None:
        raise HTTPException(status_code=503, detail="quorum not satisfied")

    response = OracleQuoteResponse(
        schema_version=1,
        ts=datetime.utcnow(),
        symbol=symbol,
        price=result.agg_price,
        staleness_ms=result.max_staleness_ms or 0,
        quorum_ok=result.quorum_ok,
        divergence_pct=result.divergence_pct,
        twap_60s=twap_snapshot.get("twap"),
        failover_source=twap_snapshot.get("source"),
        trace_id=trace_id,
    )
    return response


@app.post(
    "/moderation/pause",
    response_model=ModerationAction,
    responses={403: {"model": ErrorResponse}},
)
async def moderation_pause(
    payload: ModerationAction,
    service: ModerationService = Depends(get_moderation),
) -> ModerationAction:
    detected_at = payload.ts.timestamp()
    with _TELEMETRY.span(
        "api.moderation.pause",
        attributes={
            "moderation.symbol": payload.symbol,
            "moderation.trace_id": payload.trace_id,
        },
    ):
        record = service.pause(
            symbol=payload.symbol,
            reason=payload.reason or "pause",
            actor=payload.actor,
            role=payload.role,
            evidence_uri=payload.evidence_uri,
            trace_id=payload.trace_id,
            detected_at=detected_at,
        )
    response = ModerationAction(
        schema_version=1,
        ts=datetime.utcfromtimestamp(record.updated_at),
        symbol=record.symbol,
        action="pause",
        actor=payload.actor,
        role=payload.role,
        status=record.status,
        trace_id=record.trace_id,
        reason=record.reason,
        evidence_uri=record.evidence_uri,
    )
    return response


@app.post(
    "/resolve/apply",
    response_model=ResolveApplyResponse,
    responses={400: {"model": ErrorResponse}},
)
async def resolve_apply(
    request: ResolveApplyRequest,
    resolver: AutoResolutionService = Depends(get_auto_resolver),
) -> ResolveApplyResponse:
    actor = request.actor or "api-gateway"
    role = request.role or "system"
    truth_signal = TruthSourceSignal(
        source=request.truth.source,
        verdict=str(request.truth.value),
        confidence=1.0,
        observed_at=request.truth.ts.isoformat(),
        evidence_uri=request.payload.get("evidence_uri") if request.payload else None,
    ).with_status("final")
    votes = [
        {"verdict": request.quorum_details.value, "weight": 1.0},
        {"verdict": request.quorum_details.value * 0.999, "weight": 1.0},
        {"verdict": request.quorum_details.value * 1.001, "weight": 1.0},
    ]
    resolution = resolver.apply(
        event_id=request.event_id,
        actor=actor,
        role=role,
        resource_version=request.resource_version,
        idempotency_key=request.idempotency_key,
        quorum_votes={
            "votes": votes,
            "divergence_pct": request.quorum_details.diverg_pct or 0.0,
        },
        quorum=request.quorum,
        manual_override=request.manual_decision,
        manual_reason=request.reason,
        evidence_uri=request.payload.get("evidence_uri") if request.payload else None,
        metadata=request.payload,
        truth_source=truth_signal,
    )
    response = ResolveApplyResponse(
        decision_id=resolution.decision_id,
        outcome=resolution.outcome,
        rule=resolution.rule,
        trace_id=resolution.trace_id,
        resource_version=resolution.resource_version,
    )
    return response


__all__ = ["app"]
