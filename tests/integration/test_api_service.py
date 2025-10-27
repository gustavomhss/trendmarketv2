import asyncio
import importlib
import os
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in os.sys.path:
    os.sys.path.insert(0, str(ROOT))


@pytest.fixture
def api_module(tmp_path: Path):
    os.environ["MBP_ORACLE_EVENT_LOG"] = str(tmp_path / "oracle_events.jsonl")
    os.environ["MBP_TWAP_EVENT_LOG"] = str(tmp_path / "twap_events.jsonl")
    os.environ["MBP_MODERATION_EVENT_LOG"] = str(tmp_path / "moderation_events.jsonl")
    os.environ["MBP_SIM_EVENT_LOG"] = str(tmp_path / "sim_events.jsonl")
    module = importlib.import_module("services.api.app")
    importlib.reload(module)
    module.MODERATION_SERVICE = module.ModerationService(audit_log=tmp_path / "moderation.log")
    module.RESOLUTION_SERVICE = module.AutoResolutionService(
        audit_log=tmp_path / "resolve_audit.log",
        event_log=tmp_path / "resolve_events.jsonl",
        metrics_log=tmp_path / "metrics.jsonl",
    )
    return module


def test_oracle_quote_endpoint(api_module):
    data = asyncio.run(api_module.get_oracle_quote(symbol="BRLUSD", repo=api_module.get_repository()))
    assert data.schema_version == 1
    assert data.symbol == "BRLUSD"
    assert data.twap_60s is not None


def test_moderation_pause_endpoint(api_module):
    payload = {
        "schema_version": 1,
        "ts": "2024-01-01T00:00:00Z",
        "symbol": "BRLUSD",
        "action": "pause",
        "actor": "alice",
        "role": "moderator",
        "status": "paused",
        "trace_id": "trace-123",
        "reason": "divergence",
        "evidence_uri": "s3://evidence/mod",
    }
    action = api_module.ModerationAction.parse_obj(payload)
    result = asyncio.run(api_module.moderation_pause(action, service=api_module.get_moderation()))
    assert result.status == "paused"
    assert result.symbol == "BRLUSD"


def test_resolve_apply_endpoint(api_module):
    body = {
        "schema_version": 1,
        "event_id": "evt-1",
        "symbol": "BRLUSD",
        "truth": {"value": 101.2, "source": "oracle", "ts": "2024-01-01T00:00:00Z"},
        "quorum_details": {"value": 101.1, "quorum_ok": True, "diverg_pct": 0.001, "staleness_ms": 500},
        "truth_source": "oracle",
        "quorum": True,
        "payload": {"evidence_uri": "s3://evidence/resolve"},
        "actor": "alice",
        "role": "operator",
    }
    request = api_module.ResolveApplyRequest.parse_obj(body)
    response = asyncio.run(api_module.resolve_apply(request, resolver=api_module.get_auto_resolver()))
    assert response.decision_id
    assert response.rule
