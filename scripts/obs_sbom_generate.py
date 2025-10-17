#!/usr/bin/env python3
"""CLI wrapper to generate the CycloneDX SBOM for the ORR evidence bundle."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Optional, Sequence

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from amm_obs.sbom import generate_sbom

DEFAULT_OUT = ROOT / "out" / "obs_gatecheck" / "evidence"
DEFAULT_FILENAME = "sbom.cdx.json"


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=DEFAULT_OUT,
        help="Diretório onde o SBOM deve ser escrito.",
    )
    parser.add_argument(
        "--filename",
        default=DEFAULT_FILENAME,
        help="Nome do arquivo de saída dentro do diretório informado.",
    )
    parser.add_argument(
        "--path",
        type=Path,
        help="Caminho completo a ser usado para o SBOM (substitui --out/--filename).",
    )
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)

    if args.path is not None:
        output_path = args.path
    else:
        output_path = args.out / args.filename

    output_path = output_path.resolve()
    generate_sbom(output_path)
    print(f"SBOM_GENERATED {output_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
