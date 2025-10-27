"""Contract test for the actions.lock manifest."""

from __future__ import annotations

import json
import pathlib
import re


HEX40 = re.compile(r"^[0-9a-f]{40}$")


def test_actions_lock_contract() -> None:
    path = pathlib.Path(".github/actions.lock")
    assert path.exists(), "actions.lock ausente"

    data = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(data.get("actions"), list), "`actions` ausente/ inválido"
    assert isinstance(data.get("metadata"), dict), "`metadata` ausente/ inválido"

    for entry in data["actions"]:
        for key in ("uses", "sha", "date", "author", "rationale"):
            assert key in entry, f"campo {key} ausente em actions[*]"
        assert HEX40.match(entry.get("sha", "")), "SHA inválido (precisa 40 hex)"

    for meta_key in ("sha", "date", "author"):
        assert meta_key in data["metadata"], f"metadata.{meta_key} ausente"
    assert HEX40.match(data["metadata"].get("sha", "")), "metadata.sha inválido"
