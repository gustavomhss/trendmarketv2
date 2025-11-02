from __future__ import annotations

import json
import hashlib
from pathlib import Path

from scripts.normalizer.normalize_batch import (
    Decimal4Encoder,
    build_batch_document,
    canonical_json,
    normalize_records,
    sort_key,
)

FIXTURE_JSON = Path("tests/fixtures/data/dataset-a.json")


def test_normalize_records_deterministic(tmp_path: Path) -> None:
    records = normalize_records(FIXTURE_JSON)
    assert len(records) == 3
    keys = [sort_key(record) for record in records]
    assert keys == sorted(keys)

    first = records[0]
    expected_hash = hashlib.sha256(
        f"{first['source']}|{first['product']}|{first['region']}|{first['observed_at']}|{first['value']:.4f}".encode("utf-8")
    ).hexdigest()
    assert first["idempotency_key"] == expected_hash

    batch = build_batch_document(records)
    assert batch["stats"]["count"] == 3
    assert batch["stats"]["min_observed_at"] <= batch["stats"]["max_observed_at"]

    serialized = canonical_json(records)
    assert hashlib.sha256(serialized).hexdigest() == batch["entries_hash"]

    out_path = tmp_path / "batch.json"
    out_path.write_text(json.dumps(batch, cls=Decimal4Encoder, separators=(",", ":")))
    loaded = json.loads(out_path.read_text())
    assert loaded["entries_hash"] == batch["entries_hash"]
