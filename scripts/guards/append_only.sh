#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE' >&2
Usage: scripts/guards/append_only.sh --out-dir <path> [options]

Options:
  --out-dir <path>       Directory to store summary and violation reports (required)
  --summary <path>       Path to write the human-readable summary (default: <out-dir>/summary.txt)
  --violations <path>    Path to write the JSON violations report (default: <out-dir>/violations.json)
  --base <ref>           Base git ref/commit for diff detection
  --head <ref>           Head git ref/commit for diff detection (default: GITHUB_SHA or HEAD)
  --paths <pathspec>     Additional git pathspec to protect (can be repeated)
  -h, --help             Show this help message
USAGE
}

out_dir=""
summary_path=""
violations_path=""
base_ref=""
head_ref=""
declare -a protected_paths=()

while (($#)); do
  case "$1" in
    --out-dir)
      out_dir="$2"
      shift 2
      ;;
    --summary)
      summary_path="$2"
      shift 2
      ;;
    --violations)
      violations_path="$2"
      shift 2
      ;;
    --base)
      base_ref="$2"
      shift 2
      ;;
    --head)
      head_ref="$2"
      shift 2
      ;;
    --paths)
      protected_paths+=("$2")
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "Unknown option: $1" >&2
      usage
      exit 2
      ;;
  esac
done

if [[ -z "$out_dir" ]]; then
  echo "--out-dir is required" >&2
  usage
  exit 2
fi

mkdir -p "$out_dir"
[[ -n "$summary_path" ]] || summary_path="$out_dir/summary.txt"
[[ -n "$violations_path" ]] || violations_path="$out_dir/violations.json"

if [[ ${#protected_paths[@]} -eq 0 ]]; then
  protected_paths+=(":(glob)data/append_only/**")
  protected_paths+=(":(glob)out/evidence/S7_event_model/**")
fi

if [[ -z "$head_ref" ]]; then
  if [[ -n "${GITHUB_SHA:-}" ]]; then
    head_ref="$GITHUB_SHA"
  else
    head_ref=$(git rev-parse HEAD)
  fi
fi

if [[ -z "$base_ref" ]]; then
  if [[ -n "${GITHUB_EVENT_PATH:-}" && -f "$GITHUB_EVENT_PATH" ]]; then
    if command -v jq >/dev/null 2>&1; then
      base_ref=$(jq -r '(.pull_request.base.sha // .before // empty)' "$GITHUB_EVENT_PATH" 2>/dev/null || true)
      if [[ "$base_ref" == "null" ]]; then
        base_ref=""
      fi
    fi
  fi
fi

if [[ -z "$base_ref" ]]; then
  candidate="${GITHUB_SHA:-HEAD}^"
  if git rev-parse --verify "$candidate" >/dev/null 2>&1; then
    base_ref=$(git rev-parse "$candidate")
  fi
fi

empty_tree=$(git hash-object -t tree /dev/null)
if [[ -z "$base_ref" ]]; then
  base_ref="$empty_tree"
fi

if ! git rev-parse --verify "$base_ref^{commit}" >/dev/null 2>&1; then
  base_ref="$empty_tree"
fi

mapfile -t diff_lines < <(git diff --name-status "$base_ref" "$head_ref" -- "${protected_paths[@]}" 2>/dev/null || true)

printf '%s
' "${diff_lines[@]}" | \
  BASE_REF="$base_ref" \
  HEAD_REF="$head_ref" \
  SUMMARY_PATH="$summary_path" \
  VIOLATIONS_PATH="$violations_path" \
  python - <<'PY'
import json
import os
import subprocess
import sys
from pathlib import Path

base = os.environ["BASE_REF"]
head = os.environ["HEAD_REF"]
summary_path = Path(os.environ["SUMMARY_PATH"])
violations_path = Path(os.environ["VIOLATIONS_PATH"])

diff_lines = [line.strip() for line in sys.stdin if line.strip()]
violations: list[dict] = []
summary_lines: list[str] = []

for raw_line in diff_lines:
    parts = raw_line.split("\t")
    status = parts[0]
    if status.startswith("R") or status.startswith("C"):
        old_path = parts[1] if len(parts) > 1 else ""
        new_path = parts[2] if len(parts) > 2 else ""
        summary_lines.append(f"{status}: {old_path} -> {new_path}")
        diff_proc = subprocess.run(
            ["git", "diff", base, head, "--", old_path],
            check=False,
            capture_output=True,
            text=True,
        )
        violations.append(
            {
                "status": status,
                "path": old_path,
                "new_path": new_path,
                "diff": diff_proc.stdout,
            }
        )
    else:
        path = parts[1] if len(parts) > 1 else ""
        summary_lines.append(f"{status}: {path}")
        if status in {"M", "D", "T"} or status not in {"A", ""}:
            diff_proc = subprocess.run(
                ["git", "diff", base, head, "--", path],
                check=False,
                capture_output=True,
                text=True,
            )
            if status in {"M", "D", "T"}:
                violations.append(
                    {
                        "status": status,
                        "path": path,
                        "diff": diff_proc.stdout,
                    }
                )
            elif status not in {"A"}:
                violations.append(
                    {
                        "status": status,
                        "path": path,
                        "diff": diff_proc.stdout,
                    }
                )

if not diff_lines:
    summary_lines.append("No changes detected for append-only paths.")
elif not violations:
    summary_lines.append("No append-only violations detected.")
else:
    summary_lines.append(f"{len(violations)} append-only violation(s) detected.")

summary_path.parent.mkdir(parents=True, exist_ok=True)
summary_path.write_text("\n".join(summary_lines) + "\n", encoding="utf-8")
violations_path.parent.mkdir(parents=True, exist_ok=True)
violations_path.write_text(json.dumps(violations, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

if violations:
    raise SystemExit(61)
PY

exit $?
