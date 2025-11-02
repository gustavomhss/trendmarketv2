from __future__ import annotations

import argparse
import csv
import hashlib
import json
import unicodedata
from dataclasses import dataclass
from datetime import UTC, datetime
from decimal import ROUND_HALF_EVEN, Decimal
from pathlib import Path
from typing import Any, Iterable, List, Sequence

SCHEMA_VERSION = "1"
DEFAULT_OUT = Path("out/normalized/batch.json")
METRICS_PATH = Path("out/metrics/normalize.json")


@dataclass
class NormalizationError(RuntimeError):
    message: str
    exit_code: int

    def __str__(self) -> str:  # pragma: no cover
        return self.message


class Decimal4Encoder(json.JSONEncoder):
    def default(self, obj: Any) -> Any:
        if isinstance(obj, Decimal):
            quantized = obj.quantize(Decimal("0.0001"), rounding=ROUND_HALF_EVEN)
            return float(f"{quantized:.4f}")
        return super().default(obj)


def canonical_json(data: Any) -> bytes:
    return json.dumps(
        data,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        cls=Decimal4Encoder,
    ).encode("utf-8")


def nfkc(value: str) -> str:
    return unicodedata.normalize("NFKC", value).strip()


def normalize_source(value: str) -> str:
    return nfkc(value).lower()


def normalize_region(value: str) -> str:
    cleaned = nfkc(value).upper()
    if not cleaned.startswith("BR-"):
        raise NormalizationError("invalid_region", 21)
    return cleaned


def normalize_category(value: str) -> str:
    allowed = {"alimentos", "combustiveis", "energia", "transporte", "higiene", "outros"}
    cleaned = nfkc(value).lower()
    if cleaned not in allowed:
        raise NormalizationError("invalid_category", 21)
    return cleaned


def normalize_product(value: str) -> str:
    cleaned = nfkc(value)
    if not (2 <= len(cleaned) <= 64):
        raise NormalizationError("invalid_product", 21)
    return cleaned


def normalize_unit(value: str) -> str:
    allowed = {"kg", "g", "l", "ml", "un", "pct"}
    cleaned = nfkc(value).lower()
    if cleaned not in allowed:
        raise NormalizationError("invalid_unit", 21)
    return cleaned


def normalize_currency(value: str) -> str:
    cleaned = nfkc(value).upper()
    allowed = {"BRL", "USD"}
    if cleaned not in allowed:
        raise NormalizationError("invalid_currency", 21)
    return cleaned


def parse_decimal(value: Any) -> Decimal:
    if isinstance(value, (int, float, Decimal)):
        decimal_value = Decimal(str(value))
    elif isinstance(value, str):
        decimal_value = Decimal(value.replace(",", "."))
    else:
        raise NormalizationError("invalid_value", 21)
    quantized = decimal_value.quantize(Decimal("0.0001"), rounding=ROUND_HALF_EVEN)
    if quantized < 0 or quantized > Decimal("1000000"):
        raise NormalizationError("value_out_of_bounds", 21)
    return quantized


def parse_confidence(value: Any) -> float:
    if isinstance(value, (int, float, Decimal)):
        confidence = float(value)
    elif isinstance(value, str):
        confidence = float(value)
    else:
        raise NormalizationError("invalid_confidence", 21)
    if not 0.0 <= confidence <= 1.0:
        raise NormalizationError("confidence_out_of_bounds", 21)
    return round(confidence, 6)


def parse_datetime(value: str | None) -> datetime:
    if value is None:
        raise NormalizationError("missing_timestamp", 21)
    cleaned = nfkc(value)
    try:
        if cleaned.endswith("Z"):
            parsed = datetime.strptime(cleaned, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=UTC)
        elif "+" in cleaned or "-" in cleaned[10:]:
            parsed = datetime.fromisoformat(cleaned)
            if parsed.tzinfo is None:
                parsed = parsed.replace(tzinfo=UTC)
            parsed = parsed.astimezone(UTC)
        else:
            parsed = datetime.strptime(cleaned, "%Y-%m-%d %H:%M:%S").replace(tzinfo=UTC)
    except ValueError as exc:  # pragma: no cover - defensive
        raise NormalizationError("invalid_timestamp", 21) from exc
    return parsed


def isoformat(dt_value: datetime) -> str:
    return dt_value.astimezone(UTC).replace(tzinfo=UTC).isoformat(timespec="seconds").replace("+00:00", "Z")


def build_idempotency_key(source: str, product: str, region: str, observed_at: str, value: Decimal) -> str:
    payload = f"{source}|{product}|{region}|{observed_at}|{value:.4f}"
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def normalize_record(raw: dict[str, Any]) -> dict[str, Any]:
    source = normalize_source(str(raw.get("source", "")))
    region = normalize_region(str(raw.get("region", "")))
    category = normalize_category(str(raw.get("category", "")))
    product = normalize_product(str(raw.get("product", "")))
    value = parse_decimal(raw.get("value"))
    unit = normalize_unit(str(raw.get("unit", "")))
    currency = normalize_currency(str(raw.get("currency", "BRL")))
    observed_at_dt = parse_datetime(str(raw.get("observed_at")))
    ingested_input = raw.get("ingested_at")
    ingested_dt = parse_datetime(str(ingested_input)) if ingested_input else observed_at_dt
    if ingested_dt < observed_at_dt:
        ingested_dt = observed_at_dt
    quality = nfkc(str(raw.get("quality", "A"))).upper()
    if quality not in {"A", "B", "C"}:
        raise NormalizationError("invalid_quality", 21)
    confidence = parse_confidence(raw.get("confidence", 1.0))
    idempotency = build_idempotency_key(source, product, region, isoformat(observed_at_dt), value)
    return {
        "source": source,
        "region": region,
        "category": category,
        "product": product,
        "value": value,
        "unit": unit,
        "currency": currency,
        "observed_at": isoformat(observed_at_dt),
        "ingested_at": isoformat(ingested_dt),
        "quality": quality,
        "confidence": confidence,
        "idempotency_key": idempotency,
        "schema_version": SCHEMA_VERSION,
    }


def sort_key(record: dict[str, Any]) -> tuple[Any, ...]:
    return (
        record["observed_at"],
        record["source"],
        record["product"],
        record["region"],
        record["idempotency_key"],
    )


def load_json_file(path: Path) -> Iterable[dict[str, Any]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(data, list):
        for item in data:
            if isinstance(item, dict):
                yield item
            else:
                raise NormalizationError("invalid_record", 21)
    elif isinstance(data, dict) and "records" in data:
        items = data["records"]
        if not isinstance(items, list):
            raise NormalizationError("invalid_record", 21)
        for item in items:
            if isinstance(item, dict):
                yield item
            else:
                raise NormalizationError("invalid_record", 21)
    else:
        raise NormalizationError("invalid_input", 21)


def load_csv_file(path: Path) -> Iterable[dict[str, Any]]:
    try:
        with path.open("r", encoding="utf-8", newline="") as handle:
            reader = csv.DictReader(handle)
            for row in reader:
                yield dict(row)
    except csv.Error as exc:
        raise NormalizationError("csv_parse_error", 22) from exc


def iter_raw_records(path: Path) -> Iterable[dict[str, Any]]:
    if path.is_dir():
        for candidate in sorted(path.rglob("*")):
            if candidate.suffix.lower() == ".json":
                yield from load_json_file(candidate)
            elif candidate.suffix.lower() == ".csv":
                yield from load_csv_file(candidate)
    else:
        if path.suffix.lower() == ".json":
            yield from load_json_file(path)
        elif path.suffix.lower() == ".csv":
            yield from load_csv_file(path)
        else:
            raise NormalizationError("unsupported_input", 21)


def normalize_records(path: Path, *, max_records: int = 0, fail_on_invalid: bool = False) -> List[dict[str, Any]]:
    normalized: dict[tuple[Any, ...], dict[str, Any]] = {}
    for _, raw in enumerate(iter_raw_records(path), start=1):
        if max_records and len(normalized) >= max_records:
            break
        try:
            record = normalize_record(raw)
        except NormalizationError as exc:
            if fail_on_invalid:
                raise
            continue
        key = sort_key(record)
        normalized[key] = record
    return [normalized[key] for key in sorted(normalized.keys())]


def compute_stats(records: Sequence[dict[str, Any]]) -> dict[str, Any]:
    observed = [record["observed_at"] for record in records]
    sources = sorted({record["source"] for record in records})
    regions = sorted({record["region"] for record in records})
    return {
        "count": len(records),
        "min_observed_at": min(observed) if observed else None,
        "max_observed_at": max(observed) if observed else None,
        "sources": sources,
        "regions": regions,
    }


def build_batch_document(records: Sequence[dict[str, Any]], *, created_at: datetime | None = None) -> dict[str, Any]:
    if created_at is None:
        if records:
            ingested_times = [
                datetime.fromisoformat(record["ingested_at"].replace("Z", "+00:00"))
                for record in records
            ]
            created_at = max(ingested_times)
        else:
            created_at = datetime.now(tz=UTC)
    created_ts = isoformat(created_at)
    entries_hash = hashlib.sha256(canonical_json(records)).hexdigest()
    stats = compute_stats(records)
    return {
        "schema_version": SCHEMA_VERSION,
        "created_at": created_ts,
        "entries_hash": entries_hash,
        "records": list(records),
        "stats": stats,
    }


def write_metrics(path: Path, count: int, elapsed_ms: int) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {"normalize_records_count": count, "normalize_elapsed_ms": elapsed_ms}
    path.write_text(json.dumps(payload, separators=(",", ":")), encoding="utf-8")


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Normalize raw market data")
    parser.add_argument("--in", dest="input", required=True)
    parser.add_argument("--out", dest="output", default=str(DEFAULT_OUT))
    parser.add_argument("--fail_on_invalid", action="store_true")
    parser.add_argument("--max_records", type=int, default=0)
    args = parser.parse_args(list(argv) if argv is not None else None)

    input_path = Path(args.input)
    out_path = Path(args.output)
    try:
        start = datetime.now(tz=UTC)
        records = normalize_records(
            input_path,
            max_records=max(0, args.max_records),
            fail_on_invalid=args.fail_on_invalid,
        )
        batch = build_batch_document(records)
    except NormalizationError as exc:
        payload = {"ok": False, "exit_code": exc.exit_code, "error": exc.message}
        print(json.dumps(payload, separators=(",", ":")), flush=True)
        return exc.exit_code

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(batch, separators=(",", ":"), sort_keys=True, cls=Decimal4Encoder),
        encoding="utf-8",
    )
    elapsed_ms = int((datetime.now(tz=UTC) - start).total_seconds() * 1000)
    write_metrics(METRICS_PATH, len(records), elapsed_ms)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
