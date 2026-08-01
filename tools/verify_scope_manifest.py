#!/usr/bin/env python3
"""Verify line-union counts in scope/semantic_slice.json.

The manifest is the auditable boundary between target source and the separately
reported parser/tooling footprint.  This verifier never writes a sliced C file.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def mask_comments(text: str) -> str:
    """Blank C comments, preserving newlines and literal contents."""

    out: list[str] = []
    index = 0
    state = "code"
    while index < len(text):
        char = text[index]
        nxt = text[index + 1] if index + 1 < len(text) else ""
        if state == "code":
            if char == "/" and nxt == "*":
                out.extend((" ", " "))
                index += 2
                state = "block_comment"
            elif char == "/" and nxt == "/":
                out.extend((" ", " "))
                index += 2
                state = "line_comment"
            elif char == '"':
                out.append(char)
                index += 1
                state = "string"
            elif char == "'":
                out.append(char)
                index += 1
                state = "character"
            else:
                out.append(char)
                index += 1
        elif state == "block_comment":
            if char == "*" and nxt == "/":
                out.extend((" ", " "))
                index += 2
                state = "code"
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
        elif state == "line_comment":
            out.append("\n" if char == "\n" else " ")
            index += 1
            if char == "\n":
                state = "code"
        else:
            out.append(char)
            index += 1
            if char == "\\" and index < len(text):
                out.append(text[index])
                index += 1
            elif (state == "string" and char == '"') or (
                state == "character" and char == "'"
            ):
                state = "code"
    return "".join(out)


def expand_intervals(specifications: list[str], line_count: int) -> list[int]:
    selected: set[int] = set()
    for specification in specifications:
        if "-" in specification:
            first_text, last_text = specification.split("-", 1)
            first, last = int(first_text), int(last_text)
        else:
            first = last = int(specification)
        if first < 1 or last < first or last > line_count:
            raise ValueError(
                f"invalid interval {specification!r} for {line_count} lines"
            )
        selected.update(range(first, last + 1))
    return sorted(selected)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "manifest", nargs="?", type=Path, default=Path("scope/semantic_slice.json")
    )
    args = parser.parse_args()

    manifest_path = args.manifest.resolve()
    project_root = manifest_path.parent.parent
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    source_root = project_root / manifest["source_root"]
    totals = {"physical": 0, "nonblank": 0, "nonblank_noncomment": 0}
    files: list[dict[str, object]] = []

    for relative_name, intervals in manifest["files"].items():
        path = source_root / relative_name
        raw_bytes = path.read_bytes()
        text = raw_bytes.decode("latin-1")
        original_lines = text.splitlines()
        comment_free_lines = mask_comments(text).splitlines()
        selected = expand_intervals(intervals, len(original_lines))
        counts = {
            "physical": len(selected),
            "nonblank": sum(bool(original_lines[line - 1].strip()) for line in selected),
            "nonblank_noncomment": sum(
                bool(comment_free_lines[line - 1].strip()) for line in selected
            ),
        }
        for key, value in counts.items():
            totals[key] += value
        files.append(
            {
                "file": relative_name,
                **counts,
                "sha256": hashlib.sha256(raw_bytes).hexdigest().upper(),
            }
        )

    expected = manifest["expected_totals"]
    report = {
        "manifest": manifest_path.as_posix(),
        "files": files,
        "totals": totals,
        "expected_totals": expected,
        "matches": totals == expected,
    }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["matches"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
