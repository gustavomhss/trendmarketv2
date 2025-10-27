import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.moderation.service import ModerationService  # noqa: E402


def test_moderation_audit_trail(tmp_path: Path):
    audit_path = tmp_path / "audit" / "moderation.log"
    service = ModerationService(audit_log=audit_path)

    pause_record = service.pause(
        symbol="BRLUSD",
        reason="divergence",
        actor="alice",
        role="moderator",
        evidence_uri="s3://evidence/1",
        detected_at=10.0,
        trace_id="trace-1",
    )
    assert pause_record.status == "paused"

    resume_record = service.resume(
        symbol="BRLUSD", actor="alice", role="moderator", trace_id="trace-2"
    )
    assert resume_record.status == "active"

    appeal = service.appeal(
        symbol="BRLUSD",
        actor="bob",
        role="operator",
        reason="issue",
        evidence_uri="s3://evidence/2",
        trace_id="trace-3",
    )
    assert appeal["status"] == "under_review"

    report_path = tmp_path / "ops" / "report.json"
    report = service.generate_ops_report(report_path)
    assert report_path.exists()
    assert report["appeals_total"] >= 2  # includes auto appeal + manual appeal
    assert report["mttd_seconds"] is not None
    assert report["mttm_seconds"] is not None

    entries = service.load_audit_entries()
    actions = [entry["action"] for entry in entries]
    assert actions.count("pause") == 1
    assert actions.count("resume") == 1
    assert actions.count("appeal") >= 2

    with pytest.raises(PermissionError):
        service.pause(
            symbol="BRLUSD",
            reason="bad",
            actor="mallory",
            role="viewer",
            evidence_uri="s3://x",
        )
