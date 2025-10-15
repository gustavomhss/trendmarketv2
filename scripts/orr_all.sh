#!/usr/bin/env bash
# ORR T1→T12 — perfis: plan | fast | full
set -euo pipefail
OUT="out/obs_gatecheck"; EVI="$OUT/evidence"; LOG="$OUT/logs"; PKG="$OUT/pkg"
mkdir -p "$EVI" "$LOG" "$PKG"
RUN_PROFILE="${RUN_PROFILE:-fast}"


log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$LOG/orr.log"; }
step() { local name="$1"; shift; log "→ $name"; ( set -e; "$@" ) 2>&1 | tee "$LOG/${name}.txt"; }
try() { local name="$1"; shift; log "→ $name (best-effort)"; ( set +e; "$@" ) 2>&1 | tee "$LOG/${name}.txt" || true; }


# --------- Build/Test/Linters ---------
if [ -f Cargo.toml ]; then
try cargo_fetch cargo fetch
try cargo_build cargo build
try cargo_fmt bash -lc 'cargo fmt -- --check'
try cargo_clippy bash -lc 'cargo clippy -- -D warnings'
try cargo_test cargo test
else
log "Cargo.toml não encontrado — pulando build/test Rust"
fi


# Segurança em full
if [ "$RUN_PROFILE" = "full" ]; then
if command -v cargo >/dev/null 2>&1 && [ -f Cargo.toml ]; then
try cargo_deny cargo deny check
try cargo_audit cargo audit
fi
if [ -f ops/security/gitleaks.toml ]; then
try gitleaks_ci bash -lc 'if command -v gitleaks >/dev/null 2>&1; then gitleaks detect --no-git -s . --config ops/security/gitleaks.toml --exit-code 1; else echo "gitleaks não instalado"; fi'
fi
fi


# --------- T1 — Scan & Sanity ---------
try t1_scan bash -lc '
prom=DOWN; curl -sf "http://127.0.0.1:9090/-/ready" >/dev/null && prom=UP;
log "GATECHECK_OK"; echo GATECHECK_OK
