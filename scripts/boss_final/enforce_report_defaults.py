#!/usr/bin/env python3
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

STATUS_MAP: Dict[str, str] = {
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

ALLOWED_VARIANT_KEYS: Set[str] = {"status", "notes", "timestamp_utc"}
REQUIRED_VARIANTS: Tuple[str, str] = ("primary", "clean")


def now_ts_utc() -> str:
    return datetime.now(tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def nstatus(value: Any) -> Optional[str]:
    if value is None:
        return None
    text = str(value).strip()
    if not text:
        return None
    return STATUS_MAP.get(text, text.upper())


def as_notes(value: Any) -> str:
    return value if isinstance(value, str) else ""


def as_timestamp(value: Any) -> str:
    if isinstance(value, str) and value.strip():
        return value.strip()
    return now_ts_utc()


def coerce_variant(obj: Any, fallback: Optional[str] = None) -> Dict[str, Any]:
    if isinstance(obj, str):
        st = nstatus(obj) or (fallback or "FAIL")
        return {"status": st, "notes": "", "timestamp_utc": now_ts_utc()}
    if isinstance(obj, dict):
        st = nstatus(obj.get("status")) or (fallback or "FAIL")
        return {
            "status": st,
            "notes": as_notes(obj.get("notes")),
            "timestamp_utc": as_timestamp(obj.get("timestamp_utc")),
        }
    st = fallback or "FAIL"
    return {"status": st, "notes": "", "timestamp_utc": now_ts_utc()}


def normalize_stage(value: Any) -> Dict[str, Any]:
    # Hints top-level, se existirem
    top_status: Optional[str] = None
    top_clean: Optional[str] = None
    top_notes: Optional[str] = None
    variants_in: Optional[Dict[str, Any]] = None

    if isinstance(value, str):
        top_status = nstatus(value) or "FAIL"
        top_notes = ""
    elif isinstance(value, dict):
        top_status = nstatus(value.get("status"))
        top_clean = nstatus(value.get("clean"))
        top_notes = as_notes(value.get("notes"))
        var = value.get("variants")
        if isinstance(var, dict):
            variants_in = var

    # Construir variants normalizados
    variants_out: Dict[str, Dict[str, Any]] = {}
    variants_out["primary"] = coerce_variant(
        variants_in.get("primary") if variants_in else None,
        fallback=top_status or "FAIL",
    )
    variants_out["clean"] = coerce_variant(
        variants_in.get("clean") if variants_in else None,
        fallback=top_clean or top_status or "FAIL",
    )

    # Sanitizar campos permitidos e garantir timestamp
    for name, obj in list(variants_out.items()):
        v = {k: obj[k] for k in ALLOWED_VARIANT_KEYS if k in obj}
        if "status" not in v:
            v["status"] = "FAIL"
        if "notes" not in v:
            v["notes"] = ""
        if "timestamp_utc" not in v:
            v["timestamp_utc"] = now_ts_utc()
        variants_out[name] = v

    # Garantir variantes obrigatórias
    for req in REQUIRED_VARIANTS:
        if req not in variants_out:
            variants_out[req] = {
                "status": "FAIL",
                "notes": "",
                "timestamp_utc": now_ts_utc(),
            }

    # status e notes top-level exigidos pelo validador local
    stage_status = nstatus(top_status) or variants_out["primary"]["status"]
    stage_notes = as_notes(top_notes)

    # Somente chaves esperadas
    return {"status": stage_status, "notes": stage_notes, "variants": variants_out}


def apply_all(data: Dict[str, Any]) -> Dict[str, Any]:
    if not isinstance(data, dict):
        return data
    stages = data.get("stages")
    if isinstance(stages, dict):
        out: Dict[str, Any] = {}
        for k, v in stages.items():
            out[k] = normalize_stage(v)
        data["stages"] = out
    return data


def overall_status(data: Dict[str, Any]) -> str:
    stages = data.get("stages", {})
    for v in stages.values():
        try:
            st = v["variants"]["primary"]["status"]
        except Exception:
            return "FAIL"
        if st != "PASS":
            return "FAIL"
    return "PASS"


def resolve_targets(cli_arg: Optional[str]) -> List[Path]:
    candidates: List[Path] = []
    if cli_arg:
        candidates.append(Path(cli_arg))
    candidates.extend(
        [
            Path("out/boss_final/report.local.json"),
            Path("out/boss_final/report.json"),
            Path("out/summary/report.json"),
            Path("out/report.json"),
        ]
    )
    # Também considerar o relatório do agregador (diretório temporário)
    try:
        for p in Path(".").rglob("report.json"):
            sp = str(p)
            if "/_temp/boss-aggregate/" in sp or sp.endswith(
                "/boss-aggregate/report.json"
            ):
                candidates.append(p)
    except Exception:
        pass

    seen: Set[Path] = set()
    out: List[Path] = []
    for c in candidates:
        try:
            rp = c.resolve()
            if rp in seen:
                continue
            if c.is_file():
                seen.add(rp)
                out.append(c)
        except Exception:
            pass
    return out


def write_guard_status(dir_path: Path, status: str) -> None:
    try:
        dir_path.mkdir(parents=True, exist_ok=True)
        out = dir_path / "guard_status.txt"
        out.write_text(status + "\n", encoding="utf-8")
        print(f"[enforce] guard_status: {out} -> {status}")
    except Exception as exc:
        print(
            f"[enforce] falha ao escrever guard_status em {dir_path}: {exc}",
            file=sys.stderr,
        )


def main() -> None:
    arg = sys.argv[1] if len(sys.argv) > 1 else None
    targets = resolve_targets(arg)
    if not targets:
        print("[enforce] nenhum report.json encontrado", file=sys.stderr)
        sys.exit(0)

    report_dir_env = os.environ.get("REPORT_DIR")
    report_dir_env_path = Path(report_dir_env) if report_dir_env else None

    for t in targets:
        try:
            data = json.loads(t.read_text(encoding="utf-8", errors="ignore"))
        except Exception as exc:
            print(f"[enforce] JSON inválido em {t}: {exc}", file=sys.stderr)
            continue

        fixed = apply_all(data)
        t.write_text(
            json.dumps(fixed, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )

        status = overall_status(fixed)

        # Sempre escrever ao lado do report.json
        write_guard_status(t.parent, status)

        # E também no REPORT_DIR (agregador), se definido
        if report_dir_env_path and report_dir_env_path.resolve() != t.parent.resolve():
            write_guard_status(report_dir_env_path, status)

        print(f"[enforce] normalizado: {t}")

    print("[enforce] DONE")


if __name__ == "__main__":
    main()
