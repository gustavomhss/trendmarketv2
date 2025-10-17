#!/usr/bin/env python3
"""CLI wrapper to generate the CycloneDX SBOM for the ORR evidence bundle."""

from __future__ import annotations

import argparse
from pathlib import Path

import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from amm_obs.sbom import generate_sbom


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "output",
        nargs="?",
        default="out/obs_gatecheck/evidence/sbom.cdx.json",
        help="Path to the SBOM output file",
    )
    args = parser.parse_args()

    output_path = Path(args.output)
    generate_sbom(output_path)


if __name__ == "__main__":
    main()
