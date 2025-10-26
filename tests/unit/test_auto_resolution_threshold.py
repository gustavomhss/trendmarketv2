import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from services.auto_resolution.service import AGREEMENT_THRESHOLD, AutoResolutionService  # noqa: E402


def test_quorum_requires_agreement_threshold(tmp_path: Path):
    service = AutoResolutionService(audit_log=tmp_path / "audit.log")
    votes = {"votes": [{"verdict": "yes", "weight": 0.5}, {"verdict": "no", "weight": 0.5}]}
    normalized, agreement, majority, quorum_ok, divergence = service._summarize_votes(votes)  # type: ignore[attr-defined]
    assert normalized
    assert majority in {"accepted", "rejected"}
    assert agreement < AGREEMENT_THRESHOLD
    assert not quorum_ok
