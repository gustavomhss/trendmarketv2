from __future__ import annotations

from pathlib import Path

import pytest

FALLBACK_MESSAGE = "⚠️ Relatório não encontrado. Veja GITHUB_STEP_SUMMARY para detalhes."


class SummaryStub:
    def __init__(self, path: Path) -> None:
        self.path = path
        self.lines: list[str] = []

    def addHeading(self, text: str) -> None:  # noqa: N802 (match GitHub API casing)
        self.lines.append(text)

    def addRaw(self, text: str) -> None:  # noqa: N802
        self.lines.append(text)

    def write(self) -> None:
        self.path.write_text("\n".join(self.lines) + "\n", encoding="utf-8")


def simulate_comment_step(report_dir: Path, heading: str, summary_path: Path) -> None:
    summary = SummaryStub(summary_path)
    comment_path = report_dir / "pr_comment.md"
    if comment_path.exists():
        body = comment_path.read_text(encoding="utf-8")
    else:
        body = FALLBACK_MESSAGE
    summary.addHeading(heading)
    summary.addRaw(body)
    summary.write()
    raise RuntimeError("GitHub API unavailable")


def test_scorecards_comment_fallback(tmp_path: Path) -> None:
    workflow_text = Path(".github/workflows/s6-scorecards.yml").read_text(encoding="utf-8")
    assert FALLBACK_MESSAGE in workflow_text
    summary_path = tmp_path / "summary.md"
    with pytest.raises(RuntimeError):
        simulate_comment_step(tmp_path, "S6 Scorecards", summary_path)
    summary_text = summary_path.read_text(encoding="utf-8")
    assert FALLBACK_MESSAGE in summary_text


def test_boss_final_comment_uses_report_body(tmp_path: Path) -> None:
    workflow_text = Path(".github/workflows/q1-boss-final.yml").read_text(encoding="utf-8")
    assert FALLBACK_MESSAGE in workflow_text
    comment_body = "✅ [Q1 Boss Final report](./report.md)\n"
    (tmp_path / "pr_comment.md").write_text(comment_body, encoding="utf-8")
    summary_path = tmp_path / "summary.md"
    with pytest.raises(RuntimeError):
        simulate_comment_step(tmp_path, "Q1 Boss Final", summary_path)
    summary_text = summary_path.read_text(encoding="utf-8")
    assert comment_body in summary_text
