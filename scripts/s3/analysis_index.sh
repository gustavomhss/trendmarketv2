#!/usr/bin/env bash
set -euo pipefail
EVID="${1:-out/s3_gatecheck/evidence}"
mkdir -p "$EVID/analysis"
cat > "$EVID/analysis/index.html" <<HTML
<!doctype html><meta charset=utf-8>
<title>MBP S3 — Evidence Index</title>
<h1>MBP S3 — Evidence Index</h1>
<ul>
<li><a href="twap.csv">twap.csv</a></li>
<li><a href="abuse_flags.json">abuse_flags.json</a></li>
<li><a href="policy_hash_s3.txt">policy_hash_s3.txt</a></li>
<li><a href="hashes_manifest.txt">hashes_manifest.txt</a></li>
</ul>
HTML
