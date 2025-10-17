#!/usr/bin/env bash
set -euo pipefail
EVI="out/obs_gatecheck/evidence"; mkdir -p "$EVI"
STATUS="SKIPPED"
if command -v promtool >/dev/null 2>&1 && ls ops/watchers/tests/*.yaml >/dev/null 2>&1; then
if promtool test rules ops/watchers/tests/*.yaml; then STATUS="OK"; else STATUS="FAIL"; fi
fi
# <<< A linha abaixo estava quebrada. Mantemos tudo em **uma linha**
printf '{"promtool":"%s"}\n' "$STATUS" > "$EVI/goldens_queries.json"
[ "$STATUS" != "FAIL" ] || exit 1
