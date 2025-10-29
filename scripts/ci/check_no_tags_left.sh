#!/usr/bin/env bash
set -euo pipefail

if grep -RIn --line-number -E "^\s*(-\s*)?uses:\s+[^\s]+@v[0-9]" .github/workflows; then
  echo "[sanity] Found unpinned action tags (@vX). Please pin to a commit SHA." >&2
  exit 1
fi

echo "[sanity] No tag-based actions found. OK."
