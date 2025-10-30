#!/usr/bin/env bash
set -euo pipefail
# Garante ~/.local/bin no PATH para esta sessão
case :$PATH: in
  *:"$HOME/.local/bin":*) ;;
  *) echo "[hint] Adicione export PATH=\"$HOME/.local/bin:$PATH\" ao ~/.bashrc" ;;
 esac
# yamllint via pip --user
python -m pip install --user --upgrade pip >/dev/null 2>&1 || true
python -m pip install --user yamllint==1.35.1
# gitleaks v8.18.1 em ~/.local/bin
VER=8.18.1
URL="https://github.com/gitleaks/gitleaks/releases/download/v${VER}/gitleaks_${VER}_linux_x64.tar.gz"
TMP="$(mktemp -d)" && cd "$TMP"
curl -fsSL "$URL" -o gitleaks.tgz
tar -xzf gitleaks.tgz gitleaks
mkdir -p "$HOME/.local/bin"
install -m 0755 gitleaks "$HOME/.local/bin/gitleaks"
cd - >/dev/null 2>&1 || true
rm -rf "$TMP"
# Mostrar versões
echo "yamllint: $(yamllint --version || echo not-in-PATH)"
echo "gitleaks: $(gitleaks version 2>/dev/null | head -n1 || echo not-in-PATH)"
