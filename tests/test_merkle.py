from __future__ import annotations

import json
from pathlib import Path

from scripts.merkle.merkle_build import build_merkle_tree
from scripts.normalizer.normalize_batch import Decimal4Encoder, build_batch_document, normalize_records

FIXTURE_JSON = Path("tests/fixtures/data/dataset-a.json")
EXPECTED = Path("tests/fixtures/expected/hashes_dataset_a.json")


def test_merkle_root_matches_fixture(tmp_path: Path) -> None:
    records = normalize_records(FIXTURE_JSON)
    batch = build_batch_document(records)
    batch_path = tmp_path / "batch.json"
    batch_path.write_text(
        json.dumps(batch, cls=Decimal4Encoder, separators=(",", ":")),
        encoding="utf-8",
    )

    build_merkle_tree(batch_path, batch_path)
    loaded = json.loads(batch_path.read_text(encoding="utf-8"))

    expected = json.loads(EXPECTED.read_text(encoding="utf-8"))
    assert loaded["root"] == expected.get("root")
    assert loaded["entries_hash"] == expected.get("entries_hash")
    assert loaded.get("leaves") == expected.get("leaves")
