import os
import re

PAT_INLINE = re.compile(r"^\s*uses:\s*(['\"]?)([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+)@([^'\"\s#]+)\1\s*$")
PAT_KEY = re.compile(r"^\s*uses:\s*$")
PAT_VAL = re.compile(r"^\s*(['\"]?)([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+)@([^'\"\s#]+)\1\s*$")


def _iter_workflow_files(base_dir: str) -> list[str]:
    files: list[str] = []
    for root, _, filenames in os.walk(base_dir):
        for filename in filenames:
            if filename.endswith((".yml", ".yaml")):
                files.append(os.path.join(root, filename))
    files.sort()
    return files


def main() -> None:
    for path in _iter_workflow_files(".github"):
        with open(path, "r", encoding="utf-8", errors="ignore") as handle:
            lines = handle.readlines()
        index = 0
        while index < len(lines):
            line = lines[index]
            match_inline = PAT_INLINE.match(line)
            if match_inline:
                _, action, reference = match_inline.groups()
                if not (action.startswith("./") or action.startswith("docker://")):
                    print(f"{path}\t{action}\t{reference}")
                index += 1
                continue
            if PAT_KEY.match(line) and index + 1 < len(lines):
                value = lines[index + 1]
                match_value = PAT_VAL.match(value)
                if match_value:
                    _, action, reference = match_value.groups()
                    if not (action.startswith("./") or action.startswith("docker://")):
                        print(f"{path}\t{action}\t{reference}")
                    index += 2
                    continue
            index += 1


if __name__ == "__main__":
    main()
