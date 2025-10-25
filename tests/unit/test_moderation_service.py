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

    record = service.pause(symbol="BRLUSD", reason="divergence", actor="alice", role="moderator")
    assert record.status == "paused"

    resume = service.resume(symbol="BRLUSD", actor="alice", role="moderator")
    assert resume.status == "active"

    appeal = service.appeal(symbol="BRLUSD", actor="bob", role="operator", reason="issue")
    assert appeal["status"] == "under_review"

    entries = service.load_audit_entries()
    assert len(entries) == 3
    assert {entry["action"] for entry in entries} == {"pause", "resume", "appeal"}

    with pytest.raises(PermissionError):
        service.pause(symbol="BRLUSD", reason="bad", actor="mallory", role="viewer")


