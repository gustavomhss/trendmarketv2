#!/usr/bin/env python3
"""Render release notes for CRD-8 using the gatecheck metadata."""

from __future__ import annotations

import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from amm_obs.release import ReleaseManifestError, write_release_notes  # noqa: E402


OUT = ROOT / "out" / "obs_gatecheck"


def main() -> int:
    try:
        write_release_notes(OUT)
    except FileNotFoundError as exc:
        sys.exit(str(exc))
    except ReleaseManifestError as exc:
        sys.exit(str(exc))

    print("RELEASE_NOTES_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
