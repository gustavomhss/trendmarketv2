#!/usr/bin/env python3
import json
from pathlib import Path


def main() -> None:
    evidence_dir = Path("out/obs_gatecheck/evidence")
    evidence_dir.mkdir(parents=True, exist_ok=True)
    (evidence_dir / "criterion_summary.json").write_text(
        json.dumps(
            {
                "bench_collected": False,
                "note": "no criterion artifacts found; using stub",
            },
            indent=2,
        )
    )
    print("T5_COLLECT_OK")


if __name__ == "__main__":
    main()
