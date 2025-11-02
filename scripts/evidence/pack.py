from __future__ import annotations

import argparse
import hashlib
import zipfile
from pathlib import Path
from typing import Iterable, Sequence

DEFAULT_ROOT = Path("out")
DEFAULT_OUT = Path("out/s7-evidence.zip")
DEFAULT_SHA256 = Path("out/sha256_s7_evidence.txt")


def build_file_list(root: Path, *, exclude: Sequence[Path] | None = None) -> list[Path]:
    excluded = {path.resolve() for path in (exclude or [])}
    files: list[Path] = []
    for candidate in sorted(root.rglob("*")):
        if not candidate.is_file():
            continue
        if candidate.resolve() in excluded:
            continue
        files.append(candidate)
    return files


def _write_summary(directory: Path, *, root: Path) -> None:
    if not directory.exists():
        return
    lines = ["# Evidence Summary", ""]
    entries: list[str] = []
    for file_path in sorted(directory.rglob("*")):
        if not file_path.is_file():
            continue
        if file_path.name == "SUMMARY.md":
            continue
        relative = file_path.relative_to(root).as_posix()
        data = file_path.read_bytes()
        entries.append(
            f"- `{relative}` — {len(data)} bytes — sha256={hashlib.sha256(data).hexdigest()}"
        )
    if entries:
        lines.extend(entries)
    else:
        lines.append("_No evidence artifacts present._")
    (directory / "SUMMARY.md").write_text("\n".join(lines), encoding="utf-8")


def generate_summaries(root: Path) -> None:
    evidence_dir = root / "evidence"
    if not evidence_dir.exists():
        return
    for subdir in sorted(evidence_dir.iterdir()):
        if subdir.is_dir() and subdir.name.startswith("T"):
            _write_summary(subdir, root=root)


def write_zip(
    root: Path,
    out_path: Path,
    *,
    compression: int = zipfile.ZIP_DEFLATED,
    compresslevel: int = 6,
    reproducible: bool = True,
) -> bytes:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    excluded = [out_path]
    file_list = build_file_list(root, exclude=excluded)
    with zipfile.ZipFile(out_path, "w", compression=compression, compresslevel=compresslevel) as bundle:
        for path in file_list:
            arcname = path.relative_to(root).as_posix()
            info = zipfile.ZipInfo(arcname)
            if reproducible:
                info.date_time = (1980, 1, 1, 0, 0, 0)
            info.compress_type = compression
            info.create_system = 3
            info.external_attr = 0o644 << 16
            with path.open("rb") as handle:
                data = handle.read()
            bundle.writestr(info, data)
    data = out_path.read_bytes()
    return data


def write_sha256(out_path: Path, sha_path: Path) -> None:
    sha_path.parent.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256(out_path.read_bytes()).hexdigest()
    sha_path.write_text(digest, encoding="utf-8")


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Pack ORR evidence as reproducible ZIP")
    parser.add_argument("--root", default=str(DEFAULT_ROOT))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--manifest")
    parser.add_argument("--sha256-out", dest="sha256_out", default=str(DEFAULT_SHA256))
    parser.add_argument("--compression", default="deflate", choices=["deflate", "stored"])
    parser.add_argument("--level", type=int, default=6)
    parser.add_argument("--no-reproducible", action="store_true")
    args = parser.parse_args(list(argv) if argv is not None else None)

    root = Path(args.root)
    out_path = Path(args.out)
    sha_out = Path(args.sha256_out)
    compression = zipfile.ZIP_STORED if args.compression == "stored" else zipfile.ZIP_DEFLATED
    generate_summaries(root)
    write_zip(
        root,
        out_path,
        compression=compression,
        compresslevel=max(0, args.level),
        reproducible=not args.no_reproducible,
    )
    write_sha256(out_path, sha_out)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
