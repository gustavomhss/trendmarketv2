#!/usr/bin/env python3
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

STATUS_MAP = {
    "PASS": "PASS",
    "PASSED": "PASS",
    "pass": "PASS",
    "passed": "PASS",
    "Pass": "PASS",
    "FAIL": "FAIL",
    "FAILED": "FAIL",
    "fail": "FAIL",
    "failed": "FAIL",
    "Fail": "FAIL",
    "SKIP": "SKIP",
    "SKIPPED": "SKIP",
    "skip": "SKIP",
    "skipped": "SKIP",
    "Skip": "SKIP",
}
ALLOWED_VARIANT_KEYS = {"status", "notes", "timestamp_utc"}
REQUIRED_VARIANTS = ("primary", "clean")


def now_ts_utc() -> str:
    # ISO 8601 sem micros, com Z, para satisfazer schema format:"date-time"
    return datetime.now(tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def nstatus(value):
    if value is None:
        return None
    text = str(value).strip()
    if not text:
        return None
    return STATUS_MAP.get(text, text.upper())


def as_notes(value):
    return value if isinstance(value, str) else ""


def as_timestamp(value):
    if isinstance(value, str) and value.strip():
        # aceita um valor já presente; schema validará o formato
        return value.strip()
    return now_ts_utc()


def norm_variant(variant_dict, fallback_status):
    result = {}
    if isinstance(variant_dict, dict):
        status = nstatus(variant_dict.get("status")) or fallback_status or "FAIL"
        for key, val in variant_dict.items():
            if key in ALLOWED_VARIANT_KEYS:
                result[key] = val
        result["status"] = status
    else:
        result["status"] = fallback_status or "FAIL"
    result["notes"] = as_notes(result.get("notes"))
    result["timestamp_utc"] = as_timestamp(result.get("timestamp_utc"))
    return result


def stage_from_scalar(scalar):
    status = nstatus(scalar) or "FAIL"
    ts = now_ts_utc()
    return {
        "status": status,
        "notes": "",
        "variants": {
            "primary": {"status": status, "notes": "", "timestamp_utc": ts},
            "clean": {"status": status, "notes": "", "timestamp_utc": ts},
        },
    }


def norm_stage(stage_val):
    if isinstance(stage_val, str):
        return stage_from_scalar(stage_val)
    if not isinstance(stage_val, dict):
        return stage_from_scalar("FAIL")

    top_clean = stage_val.get("clean", None)
    st_top = nstatus(stage_val.get("status"))
    notes = as_notes(stage_val.get("notes"))

    variants_in = stage_val.get("variants")
    if not isinstance(variants_in, dict):
        variants_in = {}

    out_variants = {}
    for name, vd in variants_in.items():
        out_variants[name] = norm_variant(vd, st_top)

    for required in REQUIRED_VARIANTS:
        if required not in out_variants:
            if required == "clean" and isinstance(top_clean, (bool, str, int)):
                truthy = str(top_clean).strip().lower() in {
                    "1",
                    "true",
                    "yes",
                    "y",
                    "on",
                }
                out_variants[required] = {
                    "status": "PASS" if truthy else (st_top or "FAIL"),
                    "notes": "",
                    "timestamp_utc": now_ts_utc(),
                }
            else:
                out_variants[required] = {
                    "status": (st_top or "FAIL"),
                    "notes": "",
                    "timestamp_utc": now_ts_utc(),
                }

    st_final = nstatus(out_variants["primary"].get("status")) or "FAIL"

    cleaned_variants = {}
    for name, vd in out_variants.items():
        coerced = {
            "status": nstatus(vd.get("status")) or "FAIL",
            "notes": as_notes(vd.get("notes")),
            "timestamp_utc": as_timestamp(vd.get("timestamp_utc")),
        }
        cleaned_variants[name] = coerced

    return {"status": st_final, "notes": notes, "variants": cleaned_variants}


def apply_all(data):
    if not isinstance(data, dict):
        return data
    stages = data.get("stages")
    if isinstance(stages, dict):
        new_stages = {}
        for key, value in stages.items():
            new_stages[key] = norm_stage(value)
        data["stages"] = new_stages
    return data


def resolve_targets(cli_arg):
    if cli_arg:
        pth = Path(cli_arg)
        return [pth] if pth.is_file() else []

    candidates = [
        Path("out/boss_final/report.local.json"),
        Path("out/boss_final/report.json"),
        Path("out/summary/report.json"),
        Path("out/report.json"),
        Path("boss-final-report.json"),
    ]

    for pth in Path(".").rglob("report.json"):
        sp = str(pth.resolve())
        if "/_temp/boss-aggregate/" in sp or sp.endswith("/boss-aggregate/report.json"):
            candidates.append(pth)

    seen = set()
    result = []
    for c in candidates:
        try:
            rp = c.resolve()
        except Exception:
            continue
        if rp in seen:
            continue
        if c.is_file():
            seen.add(rp)
            result.append(c)
    return result


def main():
    arg = sys.argv[1] if len(sys.argv) > 1 else None
    targets = resolve_targets(arg)
    if not targets:
        print("[enforce] nenhum report.json encontrado", file=sys.stderr)
        sys.exit(0)

    for tgt in targets:
        try:
            raw = tgt.read_text(encoding="utf-8", errors="ignore")
            data = json.loads(raw)
        except Exception as exc:
            print(f"[enforce] JSON inválido em {tgt}: {exc}", file=sys.stderr)
            continue

        fixed = apply_all(data)
        tgt.write_text(
            json.dumps(fixed, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
        print(f"[enforce] normalizado: {tgt}")

    print("[enforce] DONE")


if __name__ == "__main__":
    main()
