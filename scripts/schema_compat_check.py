#!/usr/bin/env python3
"""Verifica compatibilidade retroativa de schemas MBP."""

from __future__ import annotations

import json
import os
import sys

SCHEMA_REGISTRY = os.path.join("data", "cdc", "schemas", "mbp", "quotes")
EVI_DIFF = os.path.join("out", "s4_orr", "EVI", "schema_diff.txt")


def load_schema(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def compare(old: dict, new: dict) -> list[str]:
    diffs: list[str] = []
    old_required = set(old.get("required", []))
    new_required = set(new.get("required", []))
    removed_required = old_required - new_required
    if removed_required:
        diffs.append(f"Campos obrigatórios removidos: {sorted(removed_required)}")
    old_props = old.get("properties", {})
    new_props = new.get("properties", {})
    for name, prop in old_props.items():
        if name not in new_props:
            diffs.append(f"Campo removido: {name}")
            continue
        if prop.get("type") != new_props[name].get("type"):
            diffs.append(
                f"Tipo alterado para {name}: {prop.get('type')} -> {new_props[name].get('type')}"
            )
    return diffs


def main() -> None:
    if len(sys.argv) != 2:
        print("Uso: schema_compat_check.py <novo_schema>", file=sys.stderr)
        sys.exit(2)
    new_schema_path = sys.argv[1]
    versions = sorted(
        [
            os.path.join(SCHEMA_REGISTRY, f)
            for f in os.listdir(SCHEMA_REGISTRY)
            if f.endswith(".json")
        ]
    )
    if not versions:
        print("Nenhuma versão anterior encontrada", file=sys.stderr)
        sys.exit(1)
    baseline_path = versions[-1]
    baseline = load_schema(baseline_path)
    new_schema = load_schema(new_schema_path)
    diffs = compare(baseline, new_schema)
    os.makedirs(os.path.dirname(EVI_DIFF), exist_ok=True)
    with open(EVI_DIFF, "w", encoding="utf-8") as handle:
        if diffs:
            handle.write("\n".join(diffs))
        else:
            handle.write("Sem diferenças incompatíveis\n")
    if diffs:
        for diff in diffs:
            print(diff)
        sys.exit(1)
    print("Schema compatível com baseline")


if __name__ == "__main__":
    main()
