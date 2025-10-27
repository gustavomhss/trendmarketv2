from __future__ import annotations

import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Iterator, Optional

import pytest

from scripts.actions_lock_apply import ActionsLockApply, GitCLIError, GitHubAPIError


class FakeGitHubAPI:
    def __init__(
        self,
        *,
        refs: Optional[Dict[tuple[str, str, str, str], Dict[str, str]]] = None,
        tags: Optional[Dict[str, Dict[str, str]]] = None,
        commits: Optional[Dict[tuple[str, str, str], Dict[str, str]]] = None,
        error: Optional[Exception] = None,
    ) -> None:
        self.refs = refs or {}
        self.tags = tags or {}
        self.commits = commits or {}
        self.error = error

    def close(self) -> None:  # pragma: no cover - mimic real client
        pass

    def _maybe_raise(self) -> None:
        if self.error is not None:
            raise self.error

    def get_ref(
        self, owner: str, repo: str, namespace: str, ref: str
    ) -> Dict[str, str]:
        self._maybe_raise()
        key = (owner, repo, namespace, ref)
        if key not in self.refs:
            raise GitHubAPIError("Not found", transient=False)
        return {"object": self.refs[key]}

    def get_tag(self, owner: str, repo: str, sha: str) -> Dict[str, str]:
        self._maybe_raise()
        if sha not in self.tags:
            raise GitHubAPIError("Not found", transient=False)
        return {"object": self.tags[sha]}

    def get_commit(self, owner: str, repo: str, ref: str) -> Dict[str, str]:
        self._maybe_raise()
        key = (owner, repo, ref)
        if key not in self.commits:
            raise GitHubAPIError("Not found", transient=False)
        return {"sha": self.commits[key]["sha"]}


class FakeGitInterface:
    def __init__(self, mapping: Dict[tuple[str, str, str], str]) -> None:
        self.mapping = mapping

    def ls_remote(self, owner: str, repo: str, ref: str) -> str:
        key = (owner, repo, ref)
        if key not in self.mapping:
            raise GitCLIError("missing", transient=True)
        return self.mapping[key]


def fixed_times(*values: datetime) -> Iterator[datetime]:
    for value in values:
        yield value
    while True:
        yield values[-1]


def read_json(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def write_workflow(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents, encoding="utf-8")


def git_hash(path: Path, cwd: Path) -> str:
    proc = subprocess.run(
        ["git", "hash-object", str(path)],
        stdout=subprocess.PIPE,
        check=True,
        cwd=cwd,
        text=True,
    )
    return proc.stdout.strip()


def compute_metadata_sha(path: Path, cwd: Path) -> str:
    data = read_json(path)
    data["metadata"]["sha"] = ""
    content = (json.dumps(data, indent=2) + "\n").encode()
    proc = subprocess.run(
        ["git", "hash-object", "--stdin"],
        input=content,
        stdout=subprocess.PIPE,
        cwd=cwd,
        check=True,
    )
    return proc.stdout.decode().strip()


def build_resolver(
    root: Path,
    *,
    github_api,
    git_interface,
    now_iter: Iterator[datetime],
) -> ActionsLockApply:
    return ActionsLockApply(
        root,
        github_api=github_api,
        git_interface=git_interface,
        now_provider=now_iter,
    )


@pytest.fixture
def base_times() -> Iterator[datetime]:
    start = datetime(2024, 1, 1, 0, 0, tzinfo=timezone.utc)
    return fixed_times(
        start,
        start.replace(hour=1),
        start.replace(hour=2),
        start.replace(hour=3),
        start.replace(hour=4),
        start.replace(hour=5),
    )


def test_apply_pins_lightweight_tag(
    tmp_path: Path, base_times: Iterator[datetime]
) -> None:
    workflow = tmp_path / ".github/workflows/main.yml"
    write_workflow(
        workflow,
        """
name: CI
on: push
jobs:
  test:
    steps:
      - uses: actions/checkout@v4
""".strip(),
    )

    sha = "a" * 40
    fake_api = FakeGitHubAPI(
        refs={("actions", "checkout", "tags", "v4"): {"type": "commit", "sha": sha}},
    )
    fake_git = FakeGitInterface({})
    resolver = build_resolver(
        tmp_path, github_api=fake_api, git_interface=fake_git, now_iter=base_times
    )

    code = resolver.apply(
        apply_changes=True,
        commit_changes=False,
        log_path=Path("out/s4-actions-lock/resolve.log"),
        report_path=Path("out/s4-actions-lock/report.json"),
    )
    assert code == 0

    updated = workflow.read_text(encoding="utf-8")
    assert f"actions/checkout@{sha}" in updated

    lock = read_json(tmp_path / ".github/actions.lock")
    assert lock["version"] == 1
    assert lock["actions"][0]["sha"] == sha
    lock_sha = lock["metadata"]["sha"]
    expected_sha = compute_metadata_sha(tmp_path / ".github/actions.lock", tmp_path)
    assert lock_sha == expected_sha

    metadata = read_json(tmp_path / ".github/actions.metadata.json")
    assert metadata["stats"]["pinned"] == 1
    assert metadata["stats"]["unchanged"] == 0
    report = read_json(tmp_path / "out/s4-actions-lock/report.json")
    assert report["pinned"][0]["uses"] == "actions/checkout@v4"


def test_resolves_annotated_tag(tmp_path: Path, base_times: Iterator[datetime]) -> None:
    workflow = tmp_path / ".github/workflows/annotated.yml"
    write_workflow(
        workflow,
        """
name: CI
on: push
jobs:
  test:
    steps:
      - uses: org/action@release
""".strip(),
    )

    fake_api = FakeGitHubAPI(
        refs={("org", "action", "tags", "release"): {"type": "tag", "sha": "t" * 40}},
        tags={"t" * 40: {"type": "commit", "sha": "c" * 40}},
    )
    fake_git = FakeGitInterface({})
    resolver = build_resolver(
        tmp_path, github_api=fake_api, git_interface=fake_git, now_iter=base_times
    )
    code = resolver.apply(
        apply_changes=True,
        commit_changes=False,
        log_path=Path("out/s4-actions-lock/resolve.log"),
        report_path=Path("out/s4-actions-lock/report.json"),
    )
    assert code == 0
    content = workflow.read_text(encoding="utf-8")
    assert "org/action@" + "c" * 40 in content


def test_branch_resolution(tmp_path: Path, base_times: Iterator[datetime]) -> None:
    workflow = tmp_path / ".github/workflows/branch.yml"
    write_workflow(
        workflow,
        """
name: CI
on: push
jobs:
  test:
    steps:
      - uses: docker/setup-buildx-action@main
""".strip(),
    )

    fake_api = FakeGitHubAPI(
        refs={
            ("docker", "setup-buildx-action", "heads", "main"): {
                "type": "commit",
                "sha": "1" * 40,
            }
        },
    )
    fake_git = FakeGitInterface({})
    resolver = build_resolver(
        tmp_path, github_api=fake_api, git_interface=fake_git, now_iter=base_times
    )
    resolver.apply(
        apply_changes=True,
        commit_changes=False,
        log_path=Path("out/s4-actions-lock/resolve.log"),
        report_path=Path("out/s4-actions-lock/report.json"),
    )
    assert "docker/setup-buildx-action@" + "1" * 40 in workflow.read_text(
        encoding="utf-8"
    )


def test_resolves_action_in_subdirectory(
    tmp_path: Path, base_times: Iterator[datetime]
) -> None:
    workflow = tmp_path / ".github/workflows/subdir.yml"
    write_workflow(
        workflow,
        """
name: CI
on: push
jobs:
  test:
    steps:
      - uses: owner/repo/path/to/action@v1
""".strip(),
    )

    fake_api = FakeGitHubAPI(
        refs={("owner", "repo", "tags", "v1"): {"type": "commit", "sha": "5" * 40}},
    )
    fake_git = FakeGitInterface({})
    resolver = build_resolver(
        tmp_path, github_api=fake_api, git_interface=fake_git, now_iter=base_times
    )
    resolver.apply(
        apply_changes=True,
        commit_changes=False,
        log_path=Path("out/s4-actions-lock/resolve.log"),
        report_path=Path("out/s4-actions-lock/report.json"),
    )
    assert "owner/repo/path/to/action@" + "5" * 40 in workflow.read_text(
        encoding="utf-8"
    )


def test_already_pinned_is_unchanged(
    tmp_path: Path, base_times: Iterator[datetime]
) -> None:
    sha = "9" * 40
    workflow = tmp_path / ".github/workflows/pinned.yml"
    write_workflow(
        workflow,
        f"""
name: CI
on: push
jobs:
  test:
    steps:
      - uses: actions/cache@{sha}
""".strip(),
    )

    fake_api = FakeGitHubAPI()
    fake_git = FakeGitInterface({})
    resolver = build_resolver(
        tmp_path, github_api=fake_api, git_interface=fake_git, now_iter=base_times
    )
    resolver.apply(
        apply_changes=True,
        commit_changes=False,
        log_path=Path("out/s4-actions-lock/resolve.log"),
        report_path=Path("out/s4-actions-lock/report.json"),
    )
    metadata = read_json(tmp_path / ".github/actions.metadata.json")
    assert metadata["stats"]["pinned"] == 0
    assert metadata["stats"]["unchanged"] == 1


def test_skips_local_actions(tmp_path: Path, base_times: Iterator[datetime]) -> None:
    workflow = tmp_path / ".github/workflows/local.yml"
    write_workflow(
        workflow,
        """
name: CI
on: push
jobs:
  test:
    steps:
      - uses: ./local/action
      - uses: actions/checkout@v4
""".strip(),
    )

    fake_api = FakeGitHubAPI(
        refs={
            ("actions", "checkout", "tags", "v4"): {"type": "commit", "sha": "2" * 40}
        },
    )
    fake_git = FakeGitInterface({})
    resolver = build_resolver(
        tmp_path, github_api=fake_api, git_interface=fake_git, now_iter=base_times
    )
    resolver.apply(
        apply_changes=True,
        commit_changes=False,
        log_path=Path("out/s4-actions-lock/resolve.log"),
        report_path=Path("out/s4-actions-lock/report.json"),
    )
    report = read_json(tmp_path / "out/s4-actions-lock/report.json")
    assert report["stats"]["skipped_local"] == 1
    assert report["skipped"][0]["reason"] == "local-action"


def test_git_fallback_when_api_fails(
    tmp_path: Path, base_times: Iterator[datetime]
) -> None:
    workflow = tmp_path / ".github/workflows/fallback.yml"
    write_workflow(
        workflow,
        """
name: CI
on: push
jobs:
  test:
    steps:
      - uses: org/action@v1
""".strip(),
    )

    api_error = GitHubAPIError("boom", transient=True)
    fake_api = FakeGitHubAPI(error=api_error)
    fake_git = FakeGitInterface({("org", "action", "v1"): "3" * 40})
    resolver = build_resolver(
        tmp_path, github_api=fake_api, git_interface=fake_git, now_iter=base_times
    )
    resolver.apply(
        apply_changes=True,
        commit_changes=False,
        log_path=Path("out/s4-actions-lock/resolve.log"),
        report_path=Path("out/s4-actions-lock/report.json"),
    )
    text = (tmp_path / "out/s4-actions-lock/resolve.log").read_text(encoding="utf-8")
    assert "[INFO] org/action@v1 ->" in text


def test_idempotent_second_run(tmp_path: Path, base_times: Iterator[datetime]) -> None:
    workflow = tmp_path / ".github/workflows/idempotent.yml"
    write_workflow(
        workflow,
        """
name: CI
on: push
jobs:
  test:
    steps:
      - uses: actions/checkout@v4
""".strip(),
    )

    fake_api = FakeGitHubAPI(
        refs={
            ("actions", "checkout", "tags", "v4"): {"type": "commit", "sha": "4" * 40}
        },
    )
    fake_git = FakeGitInterface({})

    resolver1 = build_resolver(
        tmp_path, github_api=fake_api, git_interface=fake_git, now_iter=base_times
    )
    resolver1.apply(
        apply_changes=True,
        commit_changes=False,
        log_path=Path("out/s4-actions-lock/resolve.log"),
        report_path=Path("out/s4-actions-lock/report.json"),
    )

    # Second run with new resolver and same workflow should mark unchanged
    second_times = fixed_times(
        datetime(2024, 1, 2, 0, 0, tzinfo=timezone.utc),
        datetime(2024, 1, 2, 1, 0, tzinfo=timezone.utc),
    )
    resolver2 = build_resolver(
        tmp_path, github_api=fake_api, git_interface=fake_git, now_iter=second_times
    )
    resolver2.apply(
        apply_changes=True,
        commit_changes=False,
        log_path=Path("out/s4-actions-lock/resolve.log"),
        report_path=Path("out/s4-actions-lock/report.json"),
    )
    metadata = read_json(tmp_path / ".github/actions.metadata.json")
    assert metadata["stats"]["pinned"] == 0
    assert metadata["stats"]["unchanged"] == 1
