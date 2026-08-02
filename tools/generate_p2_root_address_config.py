#!/usr/bin/env python3
"""Fail-closed bridge from the frozen ELF ledger to CParser configuration."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys


EXPECTED_BASE_SYMBOLS = (
    ("pxReadyTasksLists", 80),
    ("xDelayedTaskList1", 20),
    ("xDelayedTaskList2", 20),
    ("xPendingReadyList", 20),
    ("xSuspendedTaskList", 20),
    ("xTasksWaitingTermination", 20),
)

EXPECTED_ROOTS = (
    ("ready[0]", "pxReadyTasksLists", 0),
    ("ready[1]", "pxReadyTasksLists", 20),
    ("ready[2]", "pxReadyTasksLists", 40),
    ("ready[3]", "pxReadyTasksLists", 60),
    ("delayed-A", "xDelayedTaskList1", 0),
    ("delayed-B", "xDelayedTaskList2", 0),
    ("pending-ready", "xPendingReadyList", 0),
    ("suspended", "xSuspendedTaskList", 0),
)

EXPECTED_DWARF_SIZES = {
    "xLIST": 20,
    "xLIST_ITEM": 20,
    "xMINI_LIST_ITEM": 12,
    "tskTaskControlBlock": 68,
}

ELF32_HEADER_SIZE = 52
ELF_MAGIC = b"\x7fELF"
ELFCLASS32 = 1
ELFDATA2LSB = 1
EV_CURRENT = 1
ET_EXEC = 2
EM_386 = 3

CANONICAL_PROJECT_ROOT = "/workspace/freertos_v611_scheduler"
WINDOWS_DRIVE_PATH = re.compile(r"(?i)(?:^|[^A-Za-z0-9_])[a-z]:[\\/]")
WSL_MOUNT_PATH = re.compile(r"(?i)(?:^|[^A-Za-z0-9_])/mnt/[a-z]/")
USER_HOME_PATH = re.compile(r"(?:^|[^A-Za-z0-9_])/home/[^/\s]+")
TEXT_EVIDENCE_SUFFIXES = (".txt", ".map", ".sha256", ".json")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def verify_elf_header(elf_path: Path) -> None:
    """Independently verify the ABI facts that can be read from the ELF header."""
    with elf_path.open("rb") as stream:
        header = stream.read(ELF32_HEADER_SIZE)
    require(len(header) >= ELF32_HEADER_SIZE, "ELF header is truncated")
    require(header[:4] == ELF_MAGIC, "artifact has no ELF magic")
    require(header[4] == ELFCLASS32, "artifact ELF class is not ELF32")
    require(header[5] == ELFDATA2LSB, "artifact ELF data encoding is not little-endian")
    require(header[6] == EV_CURRENT, "artifact ELF identification version is not current")
    require(int.from_bytes(header[16:18], "little") == ET_EXEC, "artifact ELF type is not ET_EXEC")
    require(int.from_bytes(header[18:20], "little") == EM_386, "artifact ELF machine is not i386")
    require(int.from_bytes(header[20:24], "little") == EV_CURRENT, "artifact ELF version is not current")


def require_hex_address(
    record: dict[str, object], key: str, expected: int, label: str
) -> None:
    raw_value = record.get(key)
    require(isinstance(raw_value, str), f"missing {key} for {label}")
    try:
        observed = int(raw_value, 16)
    except ValueError as error:
        raise ValueError(f"malformed {key} for {label}") from error
    require(observed == expected, f"{key} mismatch: {label}")


def require_pairwise_disjoint(
    regions: list[tuple[str, int, int]], label: str
) -> None:
    for index, (left_name, left_start, left_size) in enumerate(regions):
        left_end = left_start + left_size
        for right_name, right_start, right_size in regions[index + 1 :]:
            right_end = right_start + right_size
            require(
                left_end <= right_start or right_end <= left_start,
                f"overlapping {label}: {left_name} and {right_name}",
            )


def iter_json_strings(value: object, location: str = "ledger"):
    if isinstance(value, str):
        yield location, value
    elif isinstance(value, dict):
        for key, child in value.items():
            yield from iter_json_strings(child, f"{location}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from iter_json_strings(child, f"{location}[{index}]")


def reject_host_paths(text: str, location: str) -> None:
    require(
        WINDOWS_DRIVE_PATH.search(text) is None,
        f"Windows drive path is forbidden in {location}",
    )
    require(
        WSL_MOUNT_PATH.search(text) is None,
        f"WSL /mnt/<drive> path is forbidden in {location}",
    )
    require(
        USER_HOME_PATH.search(text) is None,
        f"user home path is forbidden in {location}",
    )


def require_project_relative_path(raw_path: str, label: str) -> None:
    require(raw_path != "", f"{label} has no path")
    require("\\" not in raw_path, f"{label} path is not POSIX-normalised: {raw_path}")
    path = PurePosixPath(raw_path)
    require(not path.is_absolute(), f"{label} path is not project-relative: {raw_path}")
    require(
        all(part not in ("", ".", "..") for part in path.parts),
        f"{label} path is not normalised: {raw_path}",
    )


def require_canonical_project_path(raw_path: object, label: str) -> None:
    require(isinstance(raw_path, str), f"{label} is not a string")
    require(
        raw_path == CANONICAL_PROJECT_ROOT
        or raw_path.startswith(CANONICAL_PROJECT_ROOT + "/"),
        f"{label} is not under the canonical project root",
    )


def verify_portable_ledger_fields(ledger: dict[str, object]) -> None:
    require(
        ledger.get("project_root") == CANONICAL_PROJECT_ROOT,
        "project_root is not canonical",
    )
    require("wsl_distribution" not in ledger, "wsl_distribution is forbidden")
    tools = ledger.get("tools")
    require(isinstance(tools, dict), "tools record is missing")
    require("kernel" not in tools, "tools.kernel is forbidden")

    for location, value in iter_json_strings(ledger):
        reject_host_paths(value, location)

    compile_flags = ledger.get("compile_flags")
    include_flags = ledger.get("include_flags")
    link_flags = ledger.get("link_flags")
    require(
        isinstance(compile_flags, list)
        and all(isinstance(flag, str) for flag in compile_flags),
        "compile_flags is malformed",
    )
    require(
        isinstance(include_flags, list)
        and all(isinstance(flag, str) for flag in include_flags),
        "include_flags is malformed",
    )
    require(
        isinstance(link_flags, list)
        and all(isinstance(flag, str) for flag in link_flags),
        "link_flags is malformed",
    )

    expected_prefix_maps = {
        f"-{kind}-prefix-map={CANONICAL_PROJECT_ROOT}={CANONICAL_PROJECT_ROOT}"
        for kind in ("fdebug", "ffile", "fmacro")
    }
    require(
        expected_prefix_maps.issubset(set(compile_flags)),
        "compiler project prefix maps are not canonical",
    )

    for index, flag in enumerate(include_flags):
        if flag in ("-I", "-iquote"):
            require(index + 1 < len(include_flags), f"missing path after {flag}")
            require_canonical_project_path(
                include_flags[index + 1], f"include_flags[{index + 1}]"
            )
    require("-T" in link_flags, "link_flags has no linker-script path")
    linker_index = link_flags.index("-T")
    require(linker_index + 1 < len(link_flags), "missing path after -T")
    require_canonical_project_path(
        link_flags[linker_index + 1], f"link_flags[{linker_index + 1}]"
    )


def resolve_ledger_path(project_root: Path, raw_path: str) -> Path:
    require_project_relative_path(raw_path, "ledger entry")
    return project_root / Path(*PurePosixPath(raw_path).parts)


def verify_hashed_entries(
    project_root: Path, entries: list[dict[str, object]], label: str
) -> None:
    seen: set[str] = set()
    for entry in entries:
        require(isinstance(entry, dict), f"malformed {label} entry")
        raw_path = str(entry.get("path", ""))
        expected = str(entry.get("sha256", "")).lower()
        require(raw_path != "", f"{label} entry has no path")
        require(raw_path not in seen, f"duplicate {label} path: {raw_path}")
        seen.add(raw_path)
        path = resolve_ledger_path(project_root, raw_path)
        require(path.is_file(), f"missing {label} file: {path}")
        require(
            sha256(path) == expected,
            f"{label} SHA-256 mismatch: {raw_path}",
        )


def verify_text_evidence_portability(
    project_root: Path, entries: list[dict[str, object]]
) -> None:
    for entry in entries:
        raw_path = str(entry.get("path", ""))
        if not raw_path.lower().endswith(TEXT_EVIDENCE_SUFFIXES):
            continue
        path = resolve_ledger_path(project_root, raw_path)
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError as error:
            raise ValueError(f"text evidence is not UTF-8: {raw_path}") from error
        reject_host_paths(text, f"evidence {raw_path}")


def verify_and_render(
    project_root: Path,
    ledger_path: Path,
    elf_path: Path,
    expected_elf_sha256: str,
) -> str:
    ledger_bytes = ledger_path.read_bytes()
    ledger = json.loads(ledger_bytes)
    require(ledger.get("schema") == 1, "unexpected ledger schema")
    require(ledger.get("status") == "valid", "ledger status is not valid")
    verify_portable_ledger_fields(ledger)

    artifact = ledger.get("artifact")
    require(isinstance(artifact, dict), "artifact record is missing")
    require_project_relative_path(str(artifact.get("path", "")), "artifact")
    actual_elf_sha256 = sha256(elf_path)
    expected_elf_sha256 = expected_elf_sha256.lower()
    require(actual_elf_sha256 == expected_elf_sha256, "frozen ELF hash changed")
    require(
        str(artifact.get("sha256", "")).lower() == actual_elf_sha256,
        "ledger ELF hash does not match the ELF",
    )
    verify_elf_header(elf_path)
    require(artifact.get("class") == "ELF32", "artifact is not ELF32")
    require(artifact.get("endianness") == "little", "artifact is not little-endian")
    require(artifact.get("machine") == "Intel 80386", "artifact is not i386")
    require(artifact.get("type") == "ET_EXEC", "artifact is not ET_EXEC")
    require(artifact.get("pie") is False, "artifact is PIE")
    require(artifact.get("interpreter") is False, "artifact has an interpreter")
    require(artifact.get("dynamic_section") is False, "artifact is dynamic")
    require(artifact.get("stripped") is False, "artifact is stripped")
    require(artifact.get("dwarf") is True, "artifact has no DWARF")
    require(
        artifact.get("deterministic_relink_sha256_match") is True,
        "deterministic relink check failed",
    )

    base_records = ledger.get("base_symbols")
    require(isinstance(base_records, list), "base_symbols is missing")
    require(len(base_records) == len(EXPECTED_BASE_SYMBOLS), "wrong base-symbol count")
    by_name: dict[str, dict[str, object]] = {}
    for record in base_records:
        require(isinstance(record, dict), "malformed base-symbol record")
        name = str(record.get("symbol", ""))
        require(name not in by_name, f"duplicate base symbol: {name}")
        by_name[name] = record
    require(
        set(by_name) == {name for name, _ in EXPECTED_BASE_SYMBOLS},
        "base-symbol set differs from the six addressed scheduler objects",
    )

    addresses: dict[str, int] = {}
    base_regions: list[tuple[str, int, int]] = []
    for name, size in EXPECTED_BASE_SYMBOLS:
        record = by_name[name]
        address = record.get("address_decimal")
        require(isinstance(address, int), f"non-integer address for {name}")
        require(0 <= address <= 0xFFFFFFFF, f"address outside 32-bit range: {name}")
        require(address + size <= 0x100000000, f"symbol region outside 32-bit range: {name}")
        require(address % 4 == 0, f"symbol address is not 4-byte aligned: {name}")
        require(record.get("size") == size, f"wrong symbol size: {name}")
        require(record.get("expected_size") == size, f"wrong expected size: {name}")
        require(record.get("readelf_size") == size, f"readelf size mismatch: {name}")
        require(record.get("nm_size") == size, f"nm size mismatch: {name}")
        require(record.get("readelf_nm_match") is True, f"readelf/nm mismatch: {name}")
        require(record.get("map_present") is True, f"symbol absent from map: {name}")
        require(record.get("bind") == "LOCAL", f"wrong symbol binding: {name}")
        require(record.get("nm_type") == "b", f"wrong nm symbol type: {name}")
        require_hex_address(record, "address_hex", address, name)
        require_hex_address(record, "readelf_address_hex", address, name)
        require_hex_address(record, "nm_address_hex", address, name)
        addresses[name] = address
        base_regions.append((name, address, size))

    require_pairwise_disjoint(base_regions, "base-symbol regions")

    roots = ledger.get("physical_roots")
    require(isinstance(roots, list), "physical_roots is missing")
    require(len(roots) == len(EXPECTED_ROOTS), "wrong physical-root count")
    root_regions: list[tuple[str, int, int]] = []
    for record, (logical_name, base_name, offset) in zip(roots, EXPECTED_ROOTS):
        require(isinstance(record, dict), "malformed physical-root record")
        require(record.get("logical_name") == logical_name, "physical-root order/name mismatch")
        require(record.get("base_symbol") == base_name, f"wrong base for {logical_name}")
        require(record.get("offset") == offset, f"wrong offset for {logical_name}")
        require(record.get("size") == 20, f"wrong root size for {logical_name}")
        root_address = record.get("address_decimal")
        require(
            root_address == addresses[base_name] + offset,
            f"wrong derived address for {logical_name}",
        )
        require(isinstance(root_address, int), f"non-integer root address: {logical_name}")
        require(root_address % 4 == 0, f"root address is not 4-byte aligned: {logical_name}")
        require(root_address + 20 <= 0x100000000, f"root region outside 32-bit range: {logical_name}")
        require(record.get("readelf_size") == 20, f"readelf root size mismatch: {logical_name}")
        require(record.get("nm_size") == 20, f"nm root size mismatch: {logical_name}")
        require(record.get("readelf_nm_match") is True, f"root extractor mismatch: {logical_name}")
        require_hex_address(record, "address_hex", root_address, logical_name)
        require_hex_address(record, "readelf_address_hex", root_address, logical_name)
        require_hex_address(record, "nm_address_hex", root_address, logical_name)
        root_regions.append((logical_name, root_address, 20))

    require_pairwise_disjoint(root_regions, "physical-root regions")

    checks = ledger.get("checks")
    require(isinstance(checks, dict), "checks record is missing")
    expected_checks = {
        "base_symbol_count": 6,
        "physical_root_count": 8,
        "ready_array_size": 80,
        "ready_element_size": 20,
        "ready_stride": 20,
        "all_base_symbols_readelf_nm_equal": True,
        "all_base_symbols_in_link_map": True,
        "all_base_regions_pairwise_disjoint": True,
        "all_root_regions_pairwise_disjoint": True,
        "all_addresses_4_byte_aligned": True,
        "all_regions_inside_32_bit_address_space": True,
    }
    for key, expected in expected_checks.items():
        require(checks.get(key) == expected, f"ledger check failed: {key}")

    dwarf = ledger.get("dwarf_structures")
    require(isinstance(dwarf, list), "dwarf_structures is missing")
    dwarf_by_name = {str(item.get("structure")): item for item in dwarf}
    require(set(dwarf_by_name) == set(EXPECTED_DWARF_SIZES), "unexpected DWARF structure set")
    for name, size in EXPECTED_DWARF_SIZES.items():
        item = dwarf_by_name[name]
        require(item.get("expected_size") == size, f"wrong DWARF expected size: {name}")
        require(item.get("observed_sizes") == [size], f"wrong DWARF observed size: {name}")
        require(item.get("expected_present") is True, f"DWARF type absent: {name}")

    tcb_policy = ledger.get("tcb_policy")
    require(isinstance(tcb_policy, dict), "tcb_policy is missing")
    require(tcb_policy.get("elf_symbols") is False, "TCBs must remain runtime objects")
    require(tcb_policy.get("detected_68_byte_object_symbols") == [], "unexpected static TCB")

    inputs = ledger.get("inputs")
    evidence = ledger.get("evidence")
    require(isinstance(inputs, list) and inputs, "inputs is missing or empty")
    require(isinstance(evidence, list) and evidence, "evidence is missing or empty")
    verify_hashed_entries(project_root, inputs, "input")
    verify_hashed_entries(project_root, evidence, "evidence")
    verify_text_evidence_portability(project_root, evidence)

    configuration = ",".join(f"{name}={addresses[name]}" for name, _ in EXPECTED_BASE_SYMBOLS)
    ledger_sha256 = hashlib.sha256(ledger_bytes).hexdigest()
    names_ml = ", ".join(f'"{name}"' for name, _ in EXPECTED_BASE_SYMBOLS)
    return (
        "(* Generated by tools/generate_p2_root_address_config.py; do not edit. *)\n"
        "structure P2_Root_Address_Config =\n"
        "struct\n"
        f'  val elf_sha256 = "{actual_elf_sha256}"\n'
        f'  val ledger_sha256 = "{ledger_sha256}"\n'
        f"  val required_names = [{names_ml}]\n"
        f'  val configuration = "{configuration}"\n'
        "end\n"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project-root", type=Path, required=True)
    parser.add_argument("--ledger", type=Path, required=True)
    parser.add_argument("--elf", type=Path, required=True)
    parser.add_argument("--expected-elf-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    project_root = args.project_root.resolve()
    ledger_path = args.ledger.resolve()
    elf_path = args.elf.resolve()
    output_path = args.output.resolve()
    require(ledger_path.is_file(), f"ledger is missing: {ledger_path}")
    require(elf_path.is_file(), f"ELF is missing: {elf_path}")
    rendered = verify_and_render(
        project_root, ledger_path, elf_path, args.expected_elf_sha256
    )
    output_path.parent.mkdir(parents=True, exist_ok=True)
    temporary = output_path.with_suffix(output_path.suffix + ".tmp")
    temporary.write_text(rendered, encoding="utf-8", newline="\n")
    os.replace(temporary, output_path)
    print(f"generated={output_path}")
    print(f"sha256={sha256(output_path)}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)
