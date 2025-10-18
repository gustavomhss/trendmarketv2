"""Tests for the prompt extras Markdown renderer."""

from amm_obs import build_prompt_extras


def test_build_prompt_extras_contains_sections() -> None:
    markdown = build_prompt_extras()

    expected_sections = [
        "Micro Safety Proof Sketch",
        "Telemetria de decisão",
        "Variantes tipadas",
        "Liveness note",
    ]
    for section in expected_sections:
        assert section in markdown


def test_build_prompt_extras_includes_code_snippets() -> None:
    markdown = build_prompt_extras()

    assert "@opentelemetry/api" in markdown
    assert "pydantic" in markdown
    assert "mbp.canary.decisions" in markdown
