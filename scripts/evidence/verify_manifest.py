from __future__ import annotations

import argparse
import hashlib
import json
import zipfile
from pathlib import Path
from typing import Iterable


def load_manifest(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


IGNORE_PATHS = {"MANIFEST.json"}


def verify_manifest(zip_path: Path, manifest_path: Path) -> dict:
    manifest = load_manifest(manifest_path)
    expected = {entry["path"]: entry for entry in manifest.get("entries", [])}
    missing = []
    mismatched = []
    with zipfile.ZipFile(zip_path, "r") as handle:
        for info in handle.infolist():
            if info.filename in IGNORE_PATHS:
                continue
            data = handle.read(info.filename)
            sha256 = hashlib.sha256(data).hexdigest()
            record = expected.get(info.filename)
            if record is None:
                missing.append(info.filename)
                continue
            if record["sha256"] != sha256 or record["size"] != len(data):
                mismatched.append(info.filename)
    return {
        "ok": not missing and not mismatched,
        "missing": missing,
        "mismatched": mismatched,
    }


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Verify evidence manifest against ZIP")
    parser.add_argument("--zip", required=True)
    parser.add_argument("--manifest", required=True)
    parser.add_argument("--out", default="out/evidence/T8_pack/verify.json")
    args = parser.parse_args(list(argv) if argv is not None else None)

    result = verify_manifest(Path(args.zip), Path(args.manifest))
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(result, separators=(",", ":")), encoding="utf-8")
    return 0 if result["ok"] else 82


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
