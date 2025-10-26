from __future__ import annotations

from pathlib import Path

import pytest

from tests.utils.github_actions import post_comment_with_summary_fallback

FALLBACK_MESSAGE = "⚠️ Relatório não encontrado. Veja GITHUB_STEP_SUMMARY para detalhes."


def test_comment_failure_writes_summary_fallback(tmp_path: Path) -> None:
    summary = tmp_path / "summary.md"
    badge = tmp_path / "badge.svg"
    badge.write_text("<svg>badge</svg>", encoding="utf-8")
    comment_body = "✅ [Sprint 6 report](./report.md)"

    def failing(_: str) -> None:
        raise RuntimeError("HTTP 500")

    result = post_comment_with_summary_fallback(
        comment_body,
        summary_path=summary,
        badge_path=badge,
        post_comment=failing,
    )

    assert not result
    content = summary.read_text(encoding="utf-8")
    assert "GitHub comment fallback" in content
    assert "![Status]" in content
    assert "HTTP 500" in content
    assert comment_body in content


def test_comment_success_does_not_touch_summary(tmp_path: Path) -> None:
    summary = tmp_path / "summary.md"
    comment_body = "All good"
    calls: list[str] = []

    def succeed(body: str) -> None:
        calls.append(body)

    result = post_comment_with_summary_fallback(
        comment_body,
        summary_path=summary,
        post_comment=succeed,
    )

    assert result
    assert not summary.exists()
    assert calls == [comment_body]


def test_fallback_appends_on_reused_runner(tmp_path: Path) -> None:
    summary = tmp_path / "summary.md"
    badge = tmp_path / "badge.svg"
    badge.write_text("<svg>badge</svg>", encoding="utf-8")

    def fail_first(_: str) -> None:
        raise RuntimeError("first failure")

    def fail_second(_: str) -> None:
        raise RuntimeError("second failure")

    post_comment_with_summary_fallback(
        "First",
        summary_path=summary,
        badge_path=badge,
        post_comment=fail_first,
    )
    post_comment_with_summary_fallback(
        "Second",
        summary_path=summary,
        badge_path=badge,
        post_comment=fail_second,
    )

    content = summary.read_text(encoding="utf-8")
    assert content.count("GitHub comment fallback") == 2
    assert "first failure" in content
    assert "second failure" in content


class SummaryStub:
    def __init__(self, path: Path) -> None:
        self.path = path
        self.lines: list[str] = []

    def addHeading(self, text: str) -> None:  # noqa: N802
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
    comment_body = "✅ [Q1 Boss Final report](./report.md)"
    (tmp_path / "pr_comment.md").write_text(comment_body, encoding="utf-8")
    summary_path = tmp_path / "summary.md"
    with pytest.raises(RuntimeError):
        simulate_comment_step(tmp_path, "Q1 Boss Final", summary_path)
    summary_text = summary_path.read_text(encoding="utf-8")
    assert comment_body in summary_text
