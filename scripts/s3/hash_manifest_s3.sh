#!/usr/bin/env bash
set -euo pipefail
EVID="${1:-out/s3_gatecheck/evidence}"
find "$EVID" -maxdepth 2 -type f -print0 | xargs -0 sha256sum | LC_ALL=C sort -k2 > "$EVID/hashes_manifest.txt"
