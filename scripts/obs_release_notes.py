#!/usr/bin/env python3
"""Render deterministic release notes based on the gatecheck manifest."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Optional, Sequence


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from amm_obs.release import ReleaseManifestError, write_release_notes  # noqa: E402


OUT = ROOT / "out" / "obs_gatecheck"


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=OUT,
        help="Diretório contendo manifest, metadata e evidence do ORR.",
    )
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    out_dir = args.out.resolve()

    try:
        write_release_notes(out_dir)
    except FileNotFoundError as exc:
        sys.exit(str(exc))
    except ReleaseManifestError as exc:
        sys.exit(str(exc))

    print("RELEASE_NOTES_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
