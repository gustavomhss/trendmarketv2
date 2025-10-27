#!/usr/bin/env python3
"""Finalize the CRD-8 release metadata for publication."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from amm_obs.release import ReleaseManifestError, write_release_metadata  # noqa: E402


OUT = ROOT / "out" / "obs_gatecheck"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--version",
        help="Override the derived release version (format YYYYMMDD).",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    try:
        metadata_path = write_release_metadata(OUT, version=args.version)
    except FileNotFoundError as exc:
        sys.exit(str(exc))
    except ReleaseManifestError as exc:
        sys.exit(str(exc))

    print(f"RELEASE_METADATA_OK {metadata_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
