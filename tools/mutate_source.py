#!/usr/bin/env python3
"""Create one named, provenance-recorded source mutant for non-vacuity tests."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


MUTATIONS = {
    "drop-remove-reverse-link": (
        "\tpxItemToRemove->pxNext->pxPrevious = pxItemToRemove->pxPrevious;",
        "\t/* MUTANT drop-remove-reverse-link: reverse link update omitted. */",
    )
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def create_mutant(source: Path, destination: Path, mutation_id: str) -> dict[str, object]:
    old, new = MUTATIONS[mutation_id]
    raw = source.read_bytes()
    text = raw.decode("utf-8")
    occurrences = text.count(old)
    if occurrences != 1:
        raise ValueError(
            f"mutation anchor occurs {occurrences} times, expected exactly once: {old!r}"
        )
    line = text[: text.index(old)].count("\n") + 1
    mutated_text = text.replace(old, new, 1)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(mutated_text, encoding="utf-8", newline="")
    mutated_raw = destination.read_bytes()
    return {
        "mutation_id": mutation_id,
        "source": str(source.resolve()),
        "destination": str(destination.resolve()),
        "source_line": line,
        "anchor": old.strip(),
        "replacement": new.strip(),
        "source_sha256": sha256(raw),
        "mutant_sha256": sha256(mutated_raw),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("mutation_id", choices=sorted(MUTATIONS))
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    print(json.dumps(create_mutant(args.source, args.destination, args.mutation_id), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
