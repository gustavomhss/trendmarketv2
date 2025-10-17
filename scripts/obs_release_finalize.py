#!/usr/bin/env python3
"""Persist release metadata derived from the ORR manifest."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Optional, Sequence


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from amm_obs.release import ReleaseManifestError, write_release_metadata


OUT = ROOT / "out" / "obs_gatecheck"


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=OUT,
        help="Diretório onde summary.json e manifest residem.",
    )
    parser.add_argument(
        "--version",
        help="Override the derived release version (format YYYYMMDD).",
    )
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    out_dir = args.out.resolve()

    try:
        metadata_path = write_release_metadata(out_dir, version=args.version)
    except FileNotFoundError as exc:
        sys.exit(str(exc))
    except ReleaseManifestError as exc:
        sys.exit(str(exc))

    print(f"RELEASE_METADATA_OK {metadata_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
