r"""Static guards against common GitHub Actions workflow mistakes.

Verifies that workflow ``run:`` scripts never embed a literal ``\n`` line
continuation, that release workflows pass extracted changelog notes cleanly,
that third-party actions pin full commit SHAs, and that workflows lock down
top-level token permissions.
"""

import re
from pathlib import Path

import pytest
import yaml

ROOT = Path(__file__).resolve().parents[1]
LITERAL_NEWLINE = re.compile(r"\\n")
SHA_PIN = re.compile(r"^[^@]+@[0-9a-f]{40}$")
WORKFLOWS = ["ci.yml", "release.yml"]


def _load_workflow(name: str) -> dict[str, object]:
    raw = (ROOT / ".github" / "workflows" / name).read_text(encoding="utf-8")
    loaded = yaml.safe_load(raw)
    assert isinstance(loaded, dict)
    return loaded


def _run_blocks(name: str) -> list[tuple[str, str]]:
    """Return every ``run:`` script in a workflow as ``(where, script)``."""
    document = _load_workflow(name)
    jobs = document["jobs"]
    assert isinstance(jobs, dict)
    return [
        (f"{name}:{job}:{step.get('name', '?')}", step["run"])
        for job, definition in jobs.items()
        for step in definition.get("steps", ())
        if "run" in step
    ]


def _uses_refs(name: str) -> list[tuple[str, str]]:
    """Return every ``uses:`` reference in a workflow as ``(where, ref)``."""
    document = _load_workflow(name)
    jobs = document["jobs"]
    assert isinstance(jobs, dict)
    refs: list[tuple[str, str]] = []
    for job, definition in jobs.items():
        if "uses" in definition and not definition["uses"].startswith("./"):
            refs.append((f"{name}:{job}", definition["uses"]))
        refs.extend(
            (f"{name}:{job}:{step.get('name', '?')}", step["uses"])
            for step in definition.get("steps", ())
            if "uses" in step and not step["uses"].startswith("./")
        )
    return refs


@pytest.mark.parametrize("name", WORKFLOWS)
def test_no_step_carries_a_literal_backslash_n(name: str) -> None:
    offences = [
        f"{where}: {script.strip()[:80]!r}" for where, script in _run_blocks(name) if LITERAL_NEWLINE.search(script)
    ]
    assert not offences, "literal backslash-n in workflow script:\n" + "\n".join(offences)


@pytest.mark.parametrize("name", WORKFLOWS)
def test_the_walk_found_steps_to_check(name: str) -> None:
    assert _run_blocks(name), f"{name} yielded no run blocks"


@pytest.mark.parametrize("name", WORKFLOWS)
def test_third_party_actions_are_sha_pinned(name: str) -> None:
    unpinned = [f"{where}: {ref}" for where, ref in _uses_refs(name) if not SHA_PIN.match(ref)]
    assert not unpinned, "third-party action is not pinned to a 40-char SHA:\n" + "\n".join(unpinned)


@pytest.mark.parametrize("name", WORKFLOWS)
def test_top_level_permissions_are_empty(name: str) -> None:
    assert _load_workflow(name).get("permissions") == {}


def test_the_shape_that_broke_is_caught() -> None:
    shipped = 'gh release create "${TAG}" ' + chr(92) + 'n            --title "${TAG}"'
    assert LITERAL_NEWLINE.search(shipped)


def test_a_real_continuation_is_not_caught() -> None:
    fine = 'gh release create "${TAG}" ' + chr(92) + '\n  --title "${TAG}"'
    assert not LITERAL_NEWLINE.search(fine)


def test_the_release_step_reads_the_file_the_step_before_it_writes() -> None:
    scripts = dict(_run_blocks("release.yml"))
    writers = [script for script in scripts.values() if "> release-notes.md" in script]
    cutters = [script for script in scripts.values() if "gh release create" in script]
    assert len(writers) == 1, writers
    assert len(cutters) == 1, cutters
    assert "--notes-file release-notes.md" in cutters[0]
