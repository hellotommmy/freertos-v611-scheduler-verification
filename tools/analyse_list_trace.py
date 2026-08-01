#!/usr/bin/env python3
"""Extract invariant evidence from the executable stock-list trace.

This tool deliberately does not call an observation a proof.  It checks the
trace schema, reports invariants that every recorded state satisfies, and
returns the first concrete witness for several tempting false invariants.
The universal preservation obligations remain Isabelle theorems.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Iterable


CORE_KILLERS = {
    "cursor_always_end",
    "real_cursor_always_ring_tail",
    "every_list_is_key_sorted",
    "new_equal_key_precedes_existing_equal_key",
    "removing_cursor_does_not_move_cursor",
}


def _first(rows: Iterable[dict[str, Any]], predicate: Any) -> dict[str, Any] | None:
    return next((row for row in rows if predicate(row)), None)


def load_trace(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise ValueError(f"line {line_number}: invalid JSON: {exc}") from exc
        if not isinstance(row, dict):
            raise ValueError(f"line {line_number}: state is not an object")
        rows.append(row)
    if not rows:
        raise ValueError("trace is empty")
    validate_trace(rows)
    return rows


def validate_trace(rows: list[dict[str, Any]]) -> None:
    seen_steps: set[str] = set()
    for index, row in enumerate(rows):
        step = row.get("step")
        count = row.get("count")
        cursor = row.get("cursor")
        ring = row.get("ring")
        if not isinstance(step, str) or not step:
            raise ValueError(f"state {index}: invalid step")
        if step in seen_steps:
            raise ValueError(f"state {index}: duplicate step {step!r}")
        seen_steps.add(step)
        if not isinstance(ring, list) or not isinstance(count, int):
            raise ValueError(f"state {index}: invalid ring/count")
        if count != len(ring):
            raise ValueError(f"state {index}: count {count} != ring length {len(ring)}")

        ids: list[str] = []
        for item_index, item in enumerate(ring):
            if not isinstance(item, dict):
                raise ValueError(f"state {index}, item {item_index}: not an object")
            item_id, key = item.get("id"), item.get("key")
            if not isinstance(item_id, str) or not item_id:
                raise ValueError(f"state {index}, item {item_index}: invalid id")
            if not isinstance(key, int) or not 0 <= key <= 0xFFFFFFFF:
                raise ValueError(f"state {index}, item {item_index}: invalid 32-bit key")
            ids.append(item_id)
        if len(ids) != len(set(ids)):
            raise ValueError(f"state {index}: duplicate real-node id")
        if cursor != "END" and cursor not in ids:
            raise ValueError(f"state {index}: cursor {cursor!r} is neither END nor a member")


def _witness(name: str, row: dict[str, Any], detail: dict[str, Any]) -> dict[str, Any]:
    return {"candidate": name, "status": "KILLED", "step": row["step"], "detail": detail}


def analyse(rows: list[dict[str, Any]], source_sha256: str) -> dict[str, Any]:
    killed: list[dict[str, Any]] = []

    row = _first(rows, lambda r: r["cursor"] != "END")
    if row:
        killed.append(_witness("cursor_always_end", row, {"cursor": row["cursor"]}))

    row = _first(
        rows,
        lambda r: bool(r["ring"])
        and r["cursor"] != "END"
        and r["cursor"] != r["ring"][-1]["id"],
    )
    if row:
        killed.append(
            _witness(
                "real_cursor_always_ring_tail",
                row,
                {"cursor": row["cursor"], "ring_tail": row["ring"][-1]["id"]},
            )
        )

    row = _first(
        rows,
        lambda r: any(
            left["key"] > right["key"] for left, right in zip(r["ring"], r["ring"][1:])
        ),
    )
    if row:
        keys = [item["key"] for item in row["ring"]]
        killed.append(_witness("every_list_is_key_sorted", row, {"keys": keys}))

    for before, after in zip(rows, rows[1:]):
        old_ids = {item["id"] for item in before["ring"]}
        added = [item for item in after["ring"] if item["id"] not in old_ids]
        if len(added) != 1:
            continue
        new_item = added[0]
        equal_old = [item for item in before["ring"] if item["key"] == new_item["key"]]
        if equal_old and all(
            next(i for i, item in enumerate(after["ring"]) if item["id"] == old["id"])
            < next(i for i, item in enumerate(after["ring"]) if item["id"] == new_item["id"])
            for old in equal_old
        ):
            killed.append(
                _witness(
                    "new_equal_key_precedes_existing_equal_key",
                    after,
                    {"existing": [item["id"] for item in equal_old], "inserted": new_item["id"]},
                )
            )
            break

    for before, after in zip(rows, rows[1:]):
        before_ids = {item["id"] for item in before["ring"]}
        after_ids = {item["id"] for item in after["ring"]}
        removed = before_ids - after_ids
        if before["cursor"] in removed and after["cursor"] != before["cursor"]:
            killed.append(
                _witness(
                    "removing_cursor_does_not_move_cursor",
                    after,
                    {
                        "removed_cursor": before["cursor"],
                        "new_cursor": after["cursor"],
                    },
                )
            )
            break

    active_checks = [
        {
            "candidate": "count_equals_number_of_real_ring_nodes",
            "status": "TRACE_CHECKED",
            "states": len(rows),
        },
        {
            "candidate": "cursor_is_end_or_a_counted_real_member",
            "status": "TRACE_CHECKED",
            "states": len(rows),
        },
    ]
    ordered_rows = [row for row in rows if row["step"].startswith("ordered.")]
    if ordered_rows:
        active_checks.append(
            {
                "candidate": "ordered_role_keys_are_nondecreasing",
                "status": "TRACE_CHECKED",
                "states": len(ordered_rows),
                "holds": all(
                    all(a["key"] <= b["key"] for a, b in zip(row["ring"], row["ring"][1:]))
                    for row in ordered_rows
                ),
            }
        )

    return {
        "evidence_class": "EXECUTABLE_OBSERVATION_NOT_PROOF",
        "source_trace_sha256": source_sha256,
        "state_count": len(rows),
        "killed_invariants": killed,
        "active_trace_checks": active_checks,
        "fifo_cursor_sequence": [
            row["cursor"] for row in rows if row["step"].startswith("fifo.next.")
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("trace", type=Path)
    parser.add_argument("--require-core-witnesses", action="store_true")
    args = parser.parse_args()

    raw = args.trace.read_bytes()
    result = analyse(load_trace(args.trace), hashlib.sha256(raw).hexdigest().upper())
    killed_names = {item["candidate"] for item in result["killed_invariants"]}
    if args.require_core_witnesses:
        missing = sorted(CORE_KILLERS - killed_names)
        if missing:
            raise SystemExit("missing core invariant-killing witnesses: " + ", ".join(missing))
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
