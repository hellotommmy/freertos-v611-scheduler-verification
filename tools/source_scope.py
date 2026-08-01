#!/usr/bin/env python3
"""Conservative, source-only C scope inventory for the blind experiment.

This is deliberately not a semantic slicer.  It inventories function bodies,
function-to-function calls, and referenced macros while keeping exact source
line intervals.  Every unresolved identifier remains visible for manual
classification as a type, macro, external contract, or missed dependency.
"""

from __future__ import annotations

import argparse
import bisect
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


CONTROL_WORDS = {"if", "for", "while", "switch", "sizeof", "return"}


@dataclass(frozen=True)
class Function:
    name: str
    file: str
    start_line: int
    end_line: int
    physical_lines: int
    nonblank_lines: int
    nonblank_noncomment_lines: int
    calls: tuple[str, ...]
    macros: tuple[str, ...]


@dataclass(frozen=True)
class Macro:
    name: str
    file: str
    start_line: int
    end_line: int
    physical_lines: int
    nonblank_lines: int
    nonblank_noncomment_lines: int
    calls: tuple[str, ...]
    macros: tuple[str, ...]


def _line_starts(text: str) -> list[int]:
    starts = [0]
    starts.extend(match.end() for match in re.finditer("\n", text))
    return starts


def _line_of(starts: list[int], offset: int) -> int:
    return bisect.bisect_right(starts, offset)


def _blank_preprocessor_logical_lines(text: str) -> str:
    """Blank directives and continuations, preserving every newline."""

    result: list[str] = []
    continuation = False
    for line in text.splitlines(keepends=True):
        directive = continuation or re.match(r"^\s*#", line) is not None
        continuation = directive and line.rstrip("\r\n").rstrip().endswith("\\")
        if directive:
            result.append("\n" if line.endswith("\n") else "")
        else:
            result.append(line)
    return "".join(result)


def _mask_comments_and_literals(text: str) -> str:
    """Replace comments/literal contents with spaces while preserving layout."""

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
                out.append(" ")
                index += 1
                state = "string"
            elif char == "'":
                out.append(" ")
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
            terminator = '"' if state == "string" else "'"
            if char == "\\" and nxt:
                out.extend((" ", "\n" if nxt == "\n" else " "))
                index += 2
            elif char == terminator:
                out.append(" ")
                index += 1
                state = "code"
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
    return "".join(out)


def _macro_inventory(
    path: Path, text: str, global_macro_names: set[str] | None = None
) -> list[Macro]:
    lines = text.splitlines()
    ranges: list[tuple[str, int, int]] = []
    line_number = 1
    while line_number <= len(lines):
        match = re.match(r"^\s*#\s*define\s+([A-Za-z_]\w*)", lines[line_number - 1])
        if match is None:
            line_number += 1
            continue
        end = line_number
        while end < len(lines) and lines[end - 1].rstrip().endswith("\\"):
            end += 1
        ranges.append((match.group(1), line_number, end))
        line_number = end + 1
    macro_names = (global_macro_names or set()) | {name for name, _, _ in ranges}
    result: list[Macro] = []
    for name, start, end in ranges:
        original_segment = lines[start - 1 : end]
        code_segment_lines = _mask_comments_and_literals(
            "\n".join(original_segment)
        ).splitlines()
        code_segment = "\n".join(code_segment_lines)
        identifiers = set(re.findall(r"\b[A-Za-z_]\w*\b", code_segment))
        calls = _identifiers_followed_by_paren(code_segment)
        calls.discard(name)
        calls.difference_update(macro_names)
        result.append(
            Macro(
                name=name,
                file=path.as_posix(),
                start_line=start,
                end_line=end,
                physical_lines=end - start + 1,
                nonblank_lines=sum(bool(line.strip()) for line in original_segment),
                nonblank_noncomment_lines=sum(
                    bool(line.strip()) for line in code_segment_lines
                ),
                calls=tuple(sorted(calls)),
                macros=tuple(sorted((identifiers & macro_names) - {name})),
            )
        )
    return result


def _function_spans(text: str) -> list[tuple[str, int, int]]:
    no_directives = _blank_preprocessor_logical_lines(text)
    code = _mask_comments_and_literals(no_directives)
    starts = _line_starts(code)
    depth = 0
    current: tuple[str, int] | None = None
    spans: list[tuple[str, int, int]] = []

    for offset, char in enumerate(code):
        if char == "{":
            if depth == 0:
                prefix_start = max(0, offset - 1600)
                prefix = code[prefix_start:offset]
                signature = re.search(
                    r"([A-Za-z_]\w*)\s*\([^;{}]*\)\s*$", prefix, re.DOTALL
                )
                if signature is not None and signature.group(1) not in CONTROL_WORDS:
                    name = signature.group(1)
                    name_offset = prefix_start + signature.start(1)
                    current = (name, _line_of(starts, name_offset))
            depth += 1
        elif char == "}":
            depth -= 1
            if depth < 0:
                raise ValueError("unbalanced closing brace")
            if depth == 0 and current is not None:
                spans.append((current[0], current[1], _line_of(starts, offset)))
                current = None
    if depth != 0:
        raise ValueError("unbalanced braces after preprocessing directives were blanked")
    return spans


def _identifiers_followed_by_paren(code: str) -> set[str]:
    return {
        match.group(1)
        for match in re.finditer(r"\b([A-Za-z_]\w*)\s*\(", code)
        if match.group(1) not in CONTROL_WORDS
    }


def parse_file(path: Path, known_macro_names: set[str]) -> list[Function]:
    text = path.read_text(encoding="latin-1")
    source_lines = text.splitlines()
    comment_free_lines = _mask_comments_and_literals(text).splitlines()
    functions: list[Function] = []

    for name, start_line, end_line in _function_spans(text):
        original_segment = source_lines[start_line - 1 : end_line]
        code_segment_lines = comment_free_lines[start_line - 1 : end_line]
        code_segment = "\n".join(code_segment_lines)
        identifiers = set(re.findall(r"\b[A-Za-z_]\w*\b", code_segment))
        calls = _identifiers_followed_by_paren(code_segment)
        # The declaration at the start of the inclusive interval is not a call.
        calls.discard(name)
        # Function-like macros are dependencies, but not C function calls.
        calls.difference_update(known_macro_names)
        functions.append(
            Function(
                name=name,
                file=path.as_posix(),
                start_line=start_line,
                end_line=end_line,
                physical_lines=end_line - start_line + 1,
                nonblank_lines=sum(bool(line.strip()) for line in original_segment),
                nonblank_noncomment_lines=sum(
                    bool(line.strip()) for line in code_segment_lines
                ),
                calls=tuple(sorted(calls)),
                macros=tuple(sorted(identifiers & known_macro_names)),
            )
        )
    return functions


def transitive_closure(
    functions: dict[str, Function], roots: Iterable[str]
) -> tuple[list[str], list[str]]:
    pending = list(dict.fromkeys(roots))
    reached: set[str] = set()
    unresolved: set[str] = set()
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        function = functions.get(name)
        if function is None:
            unresolved.add(name)
            continue
        reached.add(name)
        for called in function.calls:
            if called in functions and called not in reached:
                pending.append(called)
            elif called not in functions:
                unresolved.add(called)
    return sorted(reached), sorted(unresolved)


def dependency_closure(
    functions: dict[str, Function], macros: dict[str, Macro], roots: Iterable[str]
) -> tuple[list[str], list[str], list[str]]:
    """Close function roots through both C calls and function-like macros."""

    pending_functions = list(dict.fromkeys(roots))
    pending_macros: list[str] = []
    reached_functions: set[str] = set()
    reached_macros: set[str] = set()
    unresolved: set[str] = set()
    while pending_functions or pending_macros:
        if pending_functions:
            name = pending_functions.pop()
            if name in reached_functions:
                continue
            function = functions.get(name)
            if function is None:
                unresolved.add(name)
                continue
            reached_functions.add(name)
            pending_macros.extend(function.macros)
            for called in function.calls:
                if called in functions:
                    pending_functions.append(called)
                else:
                    unresolved.add(called)
        else:
            name = pending_macros.pop()
            if name in reached_macros:
                continue
            macro = macros.get(name)
            if macro is None:
                unresolved.add(name)
                continue
            reached_macros.add(name)
            pending_macros.extend(macro.macros)
            for called in macro.calls:
                if called in functions:
                    pending_functions.append(called)
                else:
                    unresolved.add(called)
    return (
        sorted(reached_functions),
        sorted(reached_macros),
        sorted(unresolved),
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--file", action="append", required=True, type=Path)
    parser.add_argument("--root", action="append", default=[])
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    texts = {path: path.read_text(encoding="latin-1") for path in args.file}
    all_macro_names = {
        match.group(1)
        for text in texts.values()
        for match in re.finditer(r"^\s*#\s*define\s+([A-Za-z_]\w*)", text, re.MULTILINE)
    }
    macros = [
        macro
        for path, text in texts.items()
        for macro in _macro_inventory(path, text, all_macro_names)
    ]
    macro_names = {macro.name for macro in macros}
    parsed = [
        function
        for path in args.file
        for function in parse_file(path, macro_names)
    ]
    duplicate_names = sorted(
        name
        for name in {function.name for function in parsed}
        if sum(function.name == name for function in parsed) > 1
    )
    if duplicate_names:
        raise ValueError(f"duplicate function names: {', '.join(duplicate_names)}")
    by_name = {function.name: function for function in parsed}
    macros_by_name = {macro.name: macro for macro in macros}
    reached, reached_macros, unresolved = dependency_closure(
        by_name, macros_by_name, args.root
    )
    reached_functions = [by_name[name] for name in reached]
    reached_macro_objects = [macros_by_name[name] for name in reached_macros]
    report = {
        "counting_rule": {
            "physical": "inclusive source interval from function name through closing brace",
            "nonblank": "physical interval excluding empty/whitespace-only lines",
            "nonblank_noncomment": "nonblank after masking comments and literal contents; preprocessor directives remain counted",
            "warning": "inventory only; unresolved calls/declarations and conditional duplicate macro definitions require a configuration-aware preprocessor audit",
            "macro_name_resolution": "dependency discovery currently uses the last textual definition for a duplicate macro name; every definition remains in the macro inventory",
        },
        "roots": args.root,
        "closure": reached,
        "macro_closure": reached_macros,
        "unresolved_calls": unresolved,
        "totals_selected_definition_intervals": {
            "functions": len(reached_functions),
            "macros": len(reached_macro_objects),
            "function_physical_lines": sum(
                function.physical_lines for function in reached_functions
            ),
            "macro_physical_lines": sum(
                macro.physical_lines for macro in reached_macro_objects
            ),
            "function_plus_macro_physical_lines":
                sum(function.physical_lines for function in reached_functions)
                + sum(macro.physical_lines for macro in reached_macro_objects),
            "function_nonblank_lines": sum(
                function.nonblank_lines for function in reached_functions
            ),
            "function_nonblank_noncomment_lines": sum(
                function.nonblank_noncomment_lines for function in reached_functions
            ),
        },
        "functions": [asdict(function) for function in parsed],
        "macros": [asdict(macro) for macro in macros],
    }
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
