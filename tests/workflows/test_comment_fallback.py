from pathlib import Path

from tests.utils.github_actions import post_comment_with_summary_fallback


def test_comment_failure_writes_summary_fallback(tmp_path: Path) -> None:
    summary = tmp_path / "summary.md"
    badge = tmp_path / "badge.svg"
    badge.write_text("<svg>badge</svg>\n", encoding="utf-8")
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
    badge.write_text("<svg>badge</svg>\n", encoding="utf-8")

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
