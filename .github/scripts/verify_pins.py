import json
import os
import re
import sys
import urllib.error
import urllib.request

INLINE_RE = re.compile(r'^\s*(?:-\s*)?uses:\s*(["\']?)([\w_.-]+\/[\w_.-]+)@([^"\'\s#]+)\1\s*$')
KEY_RE = re.compile(r'^\s*(?:-\s*)?uses:\s*$')
VALUE_RE = re.compile(r'^\s*(["\']?)([\w_.-]+\/[\w_.-]+)@([^"\'\s#]+)\1\s*$')
GITHUB_API = "https://api.github.com/repos/{repo}/commits/{ref}"


def list_yaml_files(base_dir: str = ".github"):
    for root, _, files in os.walk(base_dir):
        for filename in files:
            if filename.endswith((".yml", ".yaml")):
                yield os.path.join(root, filename)


def extract_uses(path: str):
    entries = []
    with open(path, "r", encoding="utf-8", errors="ignore") as handle:
        lines = handle.read().splitlines()
    idx = 0
    while idx < len(lines):
        line = lines[idx]
        line_clean = line.split('#', 1)[0]
        match = INLINE_RE.match(line_clean)
        if match:
            _, repo, ref = match.groups()
            if not (repo.startswith("./") or repo.startswith("docker://")):
                entries.append((repo, ref, idx + 1))
            idx += 1
            continue
        if KEY_RE.match(line_clean) and idx + 1 < len(lines):
            next_line = lines[idx + 1]
            next_line_clean = next_line.split('#', 1)[0]
            match_val = VALUE_RE.match(next_line_clean)
            if match_val:
                _, repo, ref = match_val.groups()
                if not (repo.startswith("./") or repo.startswith("docker://")):
                    entries.append((repo, ref, idx + 2))
                idx += 2
                continue
        idx += 1
    return entries


def http_status(repo: str, ref: str, headers: dict) -> int:
    url = GITHUB_API.format(repo=repo, ref=ref)
    request = urllib.request.Request(url, headers=headers)
    try:
        with urllib.request.urlopen(request) as response:
            return response.getcode()
    except urllib.error.HTTPError as exc:  # pragma: no cover - network failure path
        return exc.code
    except urllib.error.URLError:
        return 0


def build_summary(path: str, lines: list[str]):
    if not path:
        return
    with open(path, "a", encoding="utf-8") as handle:
        handle.write("\n".join(lines) + "\n")


def main():
    github_token = os.getenv("GH_TOKEN") or os.getenv("GITHUB_TOKEN")
    headers = {
        "User-Agent": "trendmarketv2-actions-sanity",
        "Accept": "application/vnd.github+json",
    }
    if github_token:
        headers["Authorization"] = f"Bearer {github_token}"

    files = sorted(list(list_yaml_files()))
    occurrences = []
    for file_path in files:
        for repo, ref, line in extract_uses(file_path):
            occurrences.append((file_path, repo, ref, line))

    issues = []
    checked_status: dict[tuple[str, str], int] = {}
    sha_pattern = re.compile(r"^[0-9a-fA-F]{40}$")
    for file_path, repo, ref, line in occurrences:
        if not sha_pattern.fullmatch(ref):
            issues.append(
                {
                    "file": file_path,
                    "line": line,
                    "repo": repo,
                    "ref": ref,
                    "reason": "Ref não é SHA(40)",
                }
            )
            continue
        key = (repo, ref)
        if key not in checked_status:
            checked_status[key] = http_status(repo, ref, headers)
        status = checked_status[key]
        if status != 200:
            issues.append(
                {
                    "file": file_path,
                    "line": line,
                    "repo": repo,
                    "ref": ref,
                    "reason": f"Commit inexistente ou inacessível (status {status})",
                }
            )

    summary_lines = [
        "### Sanity — Actions Pins",
        "",
        f"* Arquivos analisados: {len(files)}",
        f"* Referências verificadas: {len(occurrences)}",
        f"* Commits consultados: {len(checked_status)}",
        "",
    ]

    if issues:
        summary_lines.append("**Problemas encontrados:**")
        for entry in issues:
            summary_lines.append(
                f"- `{entry['repo']}@{entry['ref']}` em `{entry['file']}` (linha {entry['line']}): {entry['reason']}"
            )
    else:
        summary_lines.append("Tudo OK — todas as actions usam SHAs de 40 caracteres válidos.")

    build_summary(os.getenv("GITHUB_STEP_SUMMARY", ""), summary_lines)

    if issues:
        for entry in issues:
            print(
                json.dumps(
                    {
                        "file": entry["file"],
                        "line": entry["line"],
                        "action": entry["repo"],
                        "ref": entry["ref"],
                        "reason": entry["reason"],
                    },
                    ensure_ascii=False,
                )
            )
        sys.exit(1)

    print("OK")


if __name__ == "__main__":
    main()
