#!/usr/bin/env python3
import json
import os
import pathlib
import re
import sys
import urllib.request
from typing import Dict, Optional

ROOT = pathlib.Path(__file__).resolve().parents[2]
WF_DIR = ROOT / ".github" / "workflows"
OUT_DIR = ROOT / "out" / "guard" / "s4"
OUT_DIR.mkdir(parents=True, exist_ok=True)
LOCK_PATH = OUT_DIR / "actions.lock.json"
GITHUB_TOKEN = os.environ.get("GITHUB_TOKEN", "")

USES_RE = re.compile(
    r"^(?P<owner>[A-Za-z0-9_.-]+)/(?P<repo>[A-Za-z0-9_.-]+)@(?P<ref>[A-Za-z0-9_.-]+)$"
)
HEX40_RE = re.compile(r"^[0-9a-fA-F]{40}$")


def gh_api(url: str) -> dict:
    req = urllib.request.Request(url)
    if GITHUB_TOKEN:
        req.add_header("Authorization", f"Bearer {GITHUB_TOKEN}")
    req.add_header("Accept", "application/vnd.github+json")
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.loads(r.read().decode("utf-8"))


def resolve_tag_to_sha(owner: str, repo: str, ref: str) -> Optional[str]:
    # Tenta refs/tags/{ref}; se apontar para annotated tag, segue o objeto
    try:
        data = gh_api(f"https://api.github.com/repos/{owner}/{repo}/git/ref/tags/{ref}")
        obj = data.get("object", {})
        if obj.get("type") == "tag":
            tagobj = gh_api(
                f"https://api.github.com/repos/{owner}/{repo}/git/tags/{obj['sha']}"
            )
            return tagobj.get("object", {}).get("sha")
        return obj.get("sha")
    except Exception:
        # fallback: lista tags e tenta casar
        try:
            tags = gh_api(
                f"https://api.github.com/repos/{owner}/{repo}/tags?per_page=200"
            )
            for t in tags:
                if t.get("name") == ref and t.get("commit", {}).get("sha"):
                    return t["commit"]["sha"]
        except Exception:
            return None
    return None


def collect_uses() -> Dict[str, str]:
    import yaml  # PyYAML disponível no runner

    uses = {}
    for yml in sorted(WF_DIR.glob("*.yml")) + sorted(WF_DIR.glob("*.yaml")):
        with open(yml, "r", encoding="utf-8", errors="ignore") as f:
            try:
                doc = yaml.safe_load(f) or {}
            except Exception:
                continue
        for job in (doc.get("jobs") or {}).values():
            for step in job.get("steps") or []:
                u = (step or {}).get("uses")
                if not u:
                    continue
                if str(u).startswith("./") or str(u).startswith(".\\"):
                    continue  # ação local
                if str(u).startswith("docker://"):
                    continue  # imagens docker não entram no lock
                m = USES_RE.match(str(u).strip())
                if not m:
                    continue
                key = f"{m.group('owner')}/{m.group('repo')}"
                uses[key] = m.group("ref")
    return uses


def main() -> int:
    uses = collect_uses()
    lock: Dict[str, Dict[str, str]] = {}
    for key, ref in sorted(uses.items()):
        owner, repo = key.split("/")
        if HEX40_RE.match(ref):
            sha = ref.lower()
        else:
            sha = resolve_tag_to_sha(owner, repo, ref)
            if not sha:
                print(f"[gen-lock] Falha ao resolver {key}@{ref}", file=sys.stderr)
                return 2
        lock[key] = {"ref": ref, "sha": sha}
    tmp = LOCK_PATH.with_suffix(".tmp.json")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(lock, f, indent=2, sort_keys=True)
    os.replace(tmp, LOCK_PATH)
    print(f"[gen-lock] lock escrito em {LOCK_PATH}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
