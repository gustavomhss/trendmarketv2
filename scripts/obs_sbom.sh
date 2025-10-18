#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
EVI="$ROOT/out/obs_gatecheck/evidence"
mkdir -p "$EVI"

SBOM_JSON="$EVI/sbom.cdx.json"
SBOM_SHA="$EVI/sbom.cdx.sha256"

generate_with_cargo() {
  local manifest="$ROOT/Cargo.toml"
  if [[ ! -f "$manifest" ]]; then
    return 1
  fi
  if ! command -v cargo >/dev/null 2>&1; then
    return 1
  fi
  if ! cargo cyclonedx --help >/dev/null 2>&1; then
    cargo install cargo-cyclonedx >/dev/null 2>&1 || true
  fi
  if ! cargo cyclonedx --help >/dev/null 2>&1; then
    return 1
  fi

  local tmp="${SBOM_JSON}.tmp"
  if ! cargo cyclonedx --format json >"$tmp"; then
    rm -f "$tmp"
    return 1
  fi
  mv "$tmp" "$SBOM_JSON"
  return 0
}

generate_fallback() {
  local tmp="${SBOM_JSON}.tmp"
  REPO_ROOT="$ROOT" SBOM_OUTPUT="$tmp" python3 <<'PY'
import hashlib
import json
import os
import subprocess
  python3 - "$ROOT" "$tmp" <<'PY'
import hashlib
import json
import subprocess
import sys
import uuid
from datetime import datetime, timezone
from pathlib import Path


def git_rev(repo_root: Path) -> str:
    try:
        result = subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=str(repo_root),
            stderr=subprocess.DEVNULL,
def git_rev(repo_root: Path) -> str:
    try:
        result = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=str(repo_root), stderr=subprocess.DEVNULL
        )
        return result.decode().strip()
    except Exception:
        return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def iter_components(repo_root: Path):
    include = ("src", "scripts", "ops", "docs/obs")
    for folder in include:
        base = repo_root / folder
        if not base.exists():
            continue
        for path in sorted(base.rglob("*")):
            if not path.is_file():
                continue
            rel = path.relative_to(repo_root).as_posix()
            if "/." in f"/{rel}":
                continue
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            yield {
                "bom-ref": f"file:{rel}",
                "type": "file",
                "name": rel,
                "hashes": [
                    {
                        "alg": "SHA-256",
                        "content": digest,
                    }
                ],
            }


def build_sbom(repo_root: Path) -> dict:
    return {
        "bomFormat": "CycloneDX",
        "specVersion": "1.4",
        "serialNumber": f"urn:uuid:{uuid.uuid4()}",
        "version": 1,
        "metadata": {
            "timestamp": datetime.now(timezone.utc)
            .isoformat()
            .replace("+00:00", "Z"),
            "timestamp": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
            "tools": [
                {
                    "vendor": "trendmarketv2",
                    "name": "obs_sbom.sh fallback",
                    "version": "1.0",
                }
            ],
            "component": {
                "bom-ref": f"app:{repo_root.name}",
                "type": "application",
                "name": repo_root.name,
                "version": git_rev(repo_root),
            },
        },
        "components": list(iter_components(repo_root)),
    }


def main() -> None:
    repo_root = Path(os.environ["REPO_ROOT"]).resolve()
    sbom_path = Path(os.environ["SBOM_OUTPUT"]).resolve()
    repo_root = Path(sys.argv[1]).resolve()
    sbom_path = Path(sys.argv[2]).resolve()
    sbom = build_sbom(repo_root)
    sbom_path.write_text(json.dumps(sbom, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
PY
  mv "$tmp" "$SBOM_JSON"
}

write_sha256() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$SBOM_JSON" >"$SBOM_SHA"
    return
  fi
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$SBOM_JSON" >"$SBOM_SHA"
    return
  fi

  SBOM_INPUT="$SBOM_JSON" SHA_OUTPUT="$SBOM_SHA" python3 <<'PY'
import hashlib
import os
from pathlib import Path


sbom_path = Path(os.environ["SBOM_INPUT"]).resolve()
sha_path = Path(os.environ["SHA_OUTPUT"]).resolve()
main() {
  if ! generate_with_cargo; then
    generate_fallback
  fi

  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$SBOM_JSON" >"$SBOM_SHA"
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$SBOM_JSON" >"$SBOM_SHA"
  else
    python3 - "$SBOM_JSON" "$SBOM_SHA" <<'PY'
import hashlib
import sys
from pathlib import Path

sbom_path = Path(sys.argv[1]).resolve()
sha_path = Path(sys.argv[2]).resolve()

digest = hashlib.sha256(sbom_path.read_bytes()).hexdigest()
sha_path.write_text(f"{digest}  {sbom_path.name}\n", encoding="utf-8")
PY
}

main() {
  rm -f "$SBOM_JSON" "$SBOM_SHA"

  if ! generate_with_cargo; then
    generate_fallback
  fi

  write_sha256

  echo SBOM_OK
}

main "$@"
  fi

  echo SBOM_OK
}

main "$@"
EVI="${EVI:-out/obs_gatecheck/evidence}"; mkdir -p "$EVI"
SBOM_PATH="$EVI/sbom.cdx.json"
HASH_PATH="$EVI/sbom.cdx.sha256"
export SBOM_PATH HASH_PATH

hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$SBOM_PATH" > "$HASH_PATH"
  else
    shasum -a 256 "$SBOM_PATH" > "$HASH_PATH"
  fi
}

if [ -f Cargo.toml ]; then
  if command -v cargo >/dev/null 2>&1; then
    cargo install cargo-cyclonedx >/dev/null 2>&1 || true
    if cargo cyclonedx --help >/dev/null 2>&1; then
      cargo cyclonedx --format json | tee "$SBOM_PATH" >/dev/null
      hash_file
      echo SBOM_OK
      exit 0
    else
      echo "cargo cyclonedx indisponível — SBOM skip"
      exit 0
    fi
  else
    echo "cargo indisponível — SBOM skip"
    exit 0
  fi
fi

if command -v python3 >/dev/null 2>&1; then
  python3 -m pip install --quiet --user cyclonedx-bom >/dev/null 2>&1 || true
  CYC_BIN="$(python3 -c 'import os, shutil, site; import sys
path = shutil.which("cyclonedx-bom")
if path:
    print(path)
else:
    user_bin = os.path.join(site.USER_BASE, "bin", "cyclonedx-bom")
    print(user_bin if os.path.exists(user_bin) else "")
')"
  if [ -n "$CYC_BIN" ] && [ -x "$CYC_BIN" ]; then
    "$CYC_BIN" -o "$SBOM_PATH" >/dev/null
    hash_file
    echo SBOM_OK
  else
    echo "cyclonedx-bom indisponível — gerando fallback"
    python3 <<'PY'
import datetime
import json
import os
import subprocess
import sys
from pathlib import Path

sbom_path = Path(os.environ.get("SBOM_PATH", "out/obs_gatecheck/evidence/sbom.cdx.json"))
components = []
try:
    output = subprocess.check_output([sys.executable, "-m", "pip", "list", "--format", "json"], text=True)
    for pkg in json.loads(output):
        components.append({
            "type": "library",
            "name": pkg.get("name"),
            "version": pkg.get("version"),
        })
except Exception:
    components = []

bom = {
    "bomFormat": "CycloneDX",
    "specVersion": "1.4",
    "version": 1,
    "metadata": {
        "timestamp": datetime.datetime.utcnow().isoformat() + "Z",
        "tools": [
            {
                "vendor": "trendmarketv2",
                "name": "obs_sbom_fallback",
                "version": "1.0",
            }
        ],
    },
    "components": components,
}

sbom_path.parent.mkdir(parents=True, exist_ok=True)
sbom_path.write_text(json.dumps(bom, indent=2))
PY
    hash_file
    echo SBOM_OK
  fi
  if ! command -v cargo >/dev/null 2>&1; then
    return 1
  fi
  if ! cargo cyclonedx --help >/dev/null 2>&1; then
    cargo install cargo-cyclonedx >/dev/null 2>&1 || true
  fi
  if ! cargo cyclonedx --help >/dev/null 2>&1; then
    return 1
  fi

  tmp="${SBOM_JSON}.tmp"
  if ! cargo cyclonedx --format json >"$tmp"; then
    rm -f "$tmp"
    return 1
  fi
  mv "$tmp" "$SBOM_JSON"
  return 0
}

generate_fallback() {
  tmp="${SBOM_JSON}.tmp"
  ROOT="$ROOT" SBOM_JSON="$tmp" python3 - <<'PY'
import hashlib
import json
import os
import subprocess
import sys
import uuid
from datetime import datetime, timezone
from pathlib import Path

root = Path(os.environ["ROOT"]).resolve()
sbom_json = Path(os.environ["SBOM_JSON"]).resolve()

def git_rev() -> str:
    try:
        result = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, stderr=subprocess.DEVNULL
        )
        return result.decode().strip()
    except Exception:
        return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")

def file_components() -> list[dict[str, object]]:
    include = ["src", "scripts", "ops", "docs/obs"]
    components: list[dict[str, object]] = []
    for folder in include:
        base = root / folder
        if not base.exists():
            continue
        for path in sorted(base.rglob("*")):
            if not path.is_file():
                continue
            rel = path.relative_to(root).as_posix()
            if "/." in f"/{rel}":
                continue
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            components.append(
                {
                    "bom-ref": f"file:{rel}",
                    "type": "file",
                    "name": rel,
                    "hashes": [
                        {
                            "alg": "SHA-256",
                            "content": digest,
                        }
                    ],
                }
            )
    return components


sbom = {
    "bomFormat": "CycloneDX",
    "specVersion": "1.4",
    "serialNumber": f"urn:uuid:{uuid.uuid4()}",
    "version": 1,
    "metadata": {
        "timestamp": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "tools": [
            {
                "vendor": "trendmarketv2",
                "name": "obs_sbom.sh fallback",
                "version": "1.0",
            }
        ],
        "component": {
            "bom-ref": f"app:{root.name}",
            "type": "application",
            "name": root.name,
            "version": git_rev(),
        },
    },
    "components": file_components(),
}

sbom_json.write_text(json.dumps(sbom, indent=2), encoding="utf-8")
PY
  mv "$tmp" "$SBOM_JSON"
}

if ! generate_with_cargo; then
  generate_fallback
fi

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum "$SBOM_JSON" >"$SBOM_SHA"
else
  shasum -a 256 "$SBOM_JSON" >"$SBOM_SHA"
  echo "python3 indisponível — SBOM skip"
fi

echo SBOM_OK
