#!/usr/bin/env bash
set -euo pipefail
EVID="${1:-out/s3_gatecheck/evidence}"
mkdir -p "$EVID"
cat configs/policies/mbp_s3.yml | sha256sum | awk '{print $1}' > "$EVID/policy_hash_s3.txt"
