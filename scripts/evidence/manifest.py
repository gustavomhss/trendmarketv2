from __future__ import annotations

import argparse
import hashlib
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Iterable, List

DEFAULT_ROOT = Path("out")
DEFAULT_OUT = Path("out/MANIFEST.json")


def build_manifest(root: Path) -> List[dict]:
    entries: List[dict] = []
    for path in sorted(root.rglob("*")):
        if not path.is_file():
            continue
        entries.append(file_entry(path, root))
    return entries


def file_entry(path: Path, root: Path) -> dict:
    data = path.read_bytes()
    rel = path.relative_to(root).as_posix()
    return {
        "path": rel,
        "size": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def _sorted_entries(entries: List[dict]) -> List[dict]:
    return sorted(entries, key=lambda item: item["path"])


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Create evidence manifest")
    parser.add_argument("--root", default=str(DEFAULT_ROOT))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    args = parser.parse_args(list(argv) if argv is not None else None)

    root = Path(args.root)
    entries = build_manifest(root)
    payload = {
        "version": 1,
        "generated_at": datetime.now(tz=UTC).isoformat(timespec="seconds"),
        "entries": _sorted_entries(entries),
    }
    serialized = json.dumps(payload, separators=(",", ":"))
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(serialized, encoding="utf-8")

    manifest_entry = {
        "path": out_path.relative_to(root).as_posix(),
        "size": len(serialized.encode("utf-8")),
        "sha256": hashlib.sha256(serialized.encode("utf-8")).hexdigest(),
    }
    entries.append(manifest_entry)

    for extra in (
        root / "evidence" / "T8_pack" / "verify.json",
        root / "s7-evidence.zip",
    ):
        if extra.exists():
            entries.append(file_entry(extra, root))

    payload["entries"] = _sorted_entries(entries)
    out_path.write_text(json.dumps(payload, separators=(",", ":")), encoding="utf-8")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
