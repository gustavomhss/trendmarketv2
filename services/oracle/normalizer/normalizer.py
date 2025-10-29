"""Canonical normalisation for TrendMarket oracle events."""
from __future__ import annotations

import hashlib
import json
import re
import unicodedata
from collections import OrderedDict
from datetime import datetime, timedelta, timezone
from typing import Any, Dict, Iterable, Mapping

SPACE_RE = re.compile(r"\s+")
TOKEN_RE = re.compile(r"[^a-z0-9]+")
LANGS = {"pt", "es", "en"}
MAX_TITLE_LENGTH = 180
MAX_TOKEN_LENGTH = 80
MAX_FUTURE_SKEW = timedelta(minutes=5)


class NormalizationError(ValueError):
    """Raised when a payload cannot be normalised into a canonical event."""


def _require_string(value: Any, field: str) -> str:
    if not isinstance(value, str):
        raise NormalizationError(f"Field '{field}' must be a string")
    return value


def canon_text(value: str) -> str:
    """Normalise a human readable string to TrendMarket canonical form."""
    norm = unicodedata.normalize("NFKD", _require_string(value, "text"))
    ascii_only = norm.encode("ascii", "ignore").decode("ascii")
    lowered = ascii_only.lower()
    collapsed = SPACE_RE.sub(" ", lowered)
    return collapsed.strip()


def canon_token(value: str) -> str:
    """Normalise identifiers (category/source) to kebab-case tokens."""
    base = canon_text(value)
    token = TOKEN_RE.sub("-", base)
    token = token.strip("-")
    token = re.sub(r"-+", "-", token)
    if not token:
        raise NormalizationError("Canonical token is empty")
    if len(token) > MAX_TOKEN_LENGTH:
        raise NormalizationError("Canonical token exceeds maximum length")
    return token


def equivalence_hash(title: str, category: str) -> str:
    left = canon_text(title)
    right = canon_text(category)
    materialised = f"{left}|{right}".encode("utf-8")
    return hashlib.sha256(materialised).hexdigest()


def _normalise_payload(payload: Any) -> Dict[str, Any]:
    if not isinstance(payload, Mapping):
        raise NormalizationError("Payload must be a JSON object")
    for key in payload.keys():
        if not isinstance(key, str):
            raise NormalizationError("Payload keys must be strings")
        if key.startswith("_"):
            raise NormalizationError("Payload keys must not start with underscore")
    # ensure deterministic ordering of payload keys while keeping nested structures intact
    return json.loads(json.dumps(payload, sort_keys=True))


def _parse_observed_at(value: str, *, now: datetime | None = None) -> str:
    candidate = _require_string(value, "observed_at")
    normalised = candidate.replace("Z", "+00:00")
    try:
        parsed = datetime.fromisoformat(normalised)
    except ValueError as exc:
        raise NormalizationError("observed_at must be a valid ISO8601 timestamp") from exc
    if parsed.tzinfo is None:
        raise NormalizationError("observed_at must include timezone information")
    utc_value = parsed.astimezone(timezone.utc)
    reference = now.astimezone(timezone.utc) if now else datetime.now(tz=timezone.utc)
    if utc_value - reference > MAX_FUTURE_SKEW:
        raise NormalizationError("observed_at exceeds allowed future skew of 5 minutes")
    # canonical ISO 8601 (UTC with Z suffix)
    return utc_value.replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _validate_title(title: str) -> str:
    canonical = canon_text(title)
    if not canonical:
        raise NormalizationError("Title cannot be empty after normalisation")
    if len(canonical) > MAX_TITLE_LENGTH:
        raise NormalizationError("Title exceeds maximum length of 180 characters")
    return canonical


def build_event(raw: Mapping[str, Any], *, now: datetime | None = None) -> Dict[str, Any]:
    if not isinstance(raw, Mapping):
        raise NormalizationError("Event payload must be a mapping")

    required_fields = {"title", "lang", "category", "source", "observed_at", "payload"}
    missing = required_fields - raw.keys()
    if missing:
        raise NormalizationError(f"Missing required fields: {', '.join(sorted(missing))}")

    title = _validate_title(raw["title"])
    lang_value = canon_text(raw["lang"])
    if lang_value not in LANGS:
        raise NormalizationError("lang must be one of pt, es or en")

    category = canon_token(raw["category"])
    source = canon_token(raw["source"])
    observed_at = _parse_observed_at(raw["observed_at"], now=now)
    payload = _normalise_payload(raw["payload"])

    eq_hash = equivalence_hash(title, category)

    event_without_id: Dict[str, Any] = OrderedDict()
    event_without_id["category"] = category
    event_without_id["equivalenceHash"] = eq_hash
    event_without_id["lang"] = lang_value
    event_without_id["observed_at"] = observed_at
    event_without_id["payload"] = payload
    event_without_id["source"] = source
    event_without_id["title"] = title

    serialised = json.dumps(event_without_id, sort_keys=True, separators=(",", ":")).encode("utf-8")
    event_id = hashlib.sha256(serialised).hexdigest()

    event_with_id: Dict[str, Any] = OrderedDict()
    for key in sorted({"category", "equivalenceHash", "id", "lang", "observed_at", "payload", "source", "title"}):
        if key == "id":
            event_with_id[key] = event_id
        else:
            event_with_id[key] = event_without_id[key]
    return event_with_id


def build_events(raw_events: Iterable[Mapping[str, Any]], *, now: datetime | None = None) -> Iterable[Dict[str, Any]]:
    for item in raw_events:
        yield build_event(item, now=now)
