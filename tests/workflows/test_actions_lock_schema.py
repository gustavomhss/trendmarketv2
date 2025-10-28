"""Contract tests for the actions.lock YAML schema."""

from __future__ import annotations

from pathlib import Path

try:
    import yaml  # type: ignore
except ModuleNotFoundError:  # pragma: no cover
    import sys

    sys.path.append(str(Path(__file__).resolve().parents[2]))
    import yaml_fallback as yaml  # type: ignore

HEX40 = set("0123456789abcdef")


def is_hex40(value: str) -> bool:
    return len(value) == 40 and all(ch in HEX40 for ch in value.lower())


def test_actions_lock_contract() -> None:
    path = Path(".github/actions.lock")
    assert path.exists(), "actions.lock ausente"

    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    assert isinstance(data, dict), "Formato inválido"
    assert data.get("version") in (1, 2), "version inválida"

    generated = data.get("generated") or data.get("metadata")
    assert isinstance(generated, dict), "metadata/generated ausente"
    assert is_hex40(str(generated.get("sha", ""))), "generated.sha inválido"
    assert isinstance(generated.get("date"), str) and generated["date"].endswith("Z"), (
        "generated.date inválido"
    )

    actions = data.get("actions")
    assert isinstance(actions, list) and actions, "lista de actions vazia"

    for entry in actions:
        assert "key" in entry, "campo key ausente"
        assert "commit" in entry, "campo commit ausente"
        assert "source" in entry, "campo source ausente"
        assert is_hex40(entry["commit"]), "commit precisa ser SHA de 40 hex"
        if "resolved" in entry and entry["resolved"]:
            assert isinstance(entry["resolved"], str)
        if "checked_at" in entry and entry["checked_at"]:
            assert entry["checked_at"].endswith("Z"), "checked_at precisa ser ISO8601Z"
