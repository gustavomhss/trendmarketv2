from __future__ import annotations

from pathlib import Path
from typing import Callable, Optional


def post_comment_with_summary_fallback(
    comment_body: str,
    *,
    summary_path: Path,
    badge_path: Optional[Path] = None,
    post_comment: Callable[[str], None],
) -> bool:
    """Attempt to post a PR comment and fall back to the job summary on failure."""
    try:
        post_comment(comment_body)
    except Exception as exc:
        summary_path.parent.mkdir(parents=True, exist_ok=True)
        existing = ""
        if summary_path.exists():
            existing = summary_path.read_text(encoding="utf-8").rstrip()
        fragments = []
        if existing:
            fragments.append(existing)
        fragments.append("## GitHub comment fallback")
        fragments.append(comment_body.strip())
        if badge_path is not None:
            fragments.append(f"![Status]({badge_path.as_posix()})")
        fragments.append(f"_fallback_reason: {exc}_")
        summary_path.write_text("\n\n".join(fragments) + "\n", encoding="utf-8")
        return False
    else:
        return True
