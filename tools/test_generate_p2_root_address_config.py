import json
import tempfile
import unittest
from pathlib import Path

import generate_p2_root_address_config as generator


BASE_ADDRESSES = {
    "pxReadyTasksLists": 0x00102020,
    "xDelayedTaskList1": 0x0010208C,
    "xDelayedTaskList2": 0x001020A0,
    "xPendingReadyList": 0x001020BC,
    "xSuspendedTaskList": 0x001020D4,
    "xTasksWaitingTermination": 0x001020E8,
}


def address_hex(address: int) -> str:
    return f"0x{address:08x}"


def elf32_exec_i386() -> bytes:
    header = bytearray(generator.ELF32_HEADER_SIZE)
    header[:4] = generator.ELF_MAGIC
    header[4] = generator.ELFCLASS32
    header[5] = generator.ELFDATA2LSB
    header[6] = generator.EV_CURRENT
    header[16:18] = generator.ET_EXEC.to_bytes(2, "little")
    header[18:20] = generator.EM_386.to_bytes(2, "little")
    header[20:24] = generator.EV_CURRENT.to_bytes(4, "little")
    header[40:42] = generator.ELF32_HEADER_SIZE.to_bytes(2, "little")
    return bytes(header)


class RootAddressConfigTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.elf_path = self.root / "fixture.elf"
        self.input_path = self.root / "input.txt"
        self.evidence_path = self.root / "evidence.txt"
        self.ledger_path = self.root / "layout_ledger.json"
        self.elf_path.write_bytes(elf32_exec_i386())
        self.input_path.write_text("frozen input\n", encoding="utf-8")
        self.evidence_path.write_text("frozen evidence\n", encoding="utf-8")
        self.ledger = self._valid_ledger()
        self._write_ledger()

    def _base_record(self, name: str, size: int) -> dict[str, object]:
        address = BASE_ADDRESSES[name]
        hexadecimal = address_hex(address)
        return {
            "symbol": name,
            "address_hex": hexadecimal,
            "address_decimal": address,
            "size": size,
            "readelf_address_hex": hexadecimal,
            "readelf_size": size,
            "nm_address_hex": hexadecimal,
            "nm_size": size,
            "expected_size": size,
            "bind": "LOCAL",
            "nm_type": "b",
            "readelf_nm_match": True,
            "map_present": True,
        }

    def _root_record(
        self, logical_name: str, base_name: str, offset: int
    ) -> dict[str, object]:
        address = BASE_ADDRESSES[base_name] + offset
        hexadecimal = address_hex(address)
        return {
            "logical_name": logical_name,
            "base_symbol": base_name,
            "offset": offset,
            "address_hex": hexadecimal,
            "address_decimal": address,
            "size": 20,
            "readelf_address_hex": hexadecimal,
            "readelf_size": 20,
            "nm_address_hex": hexadecimal,
            "nm_size": 20,
            "readelf_nm_match": True,
        }

    def _valid_ledger(self) -> dict[str, object]:
        elf_hash = generator.sha256(self.elf_path)
        return {
            "schema": 1,
            "status": "valid",
            "project_root": generator.CANONICAL_PROJECT_ROOT,
            "compile_flags": [
                f"-{kind}-prefix-map={generator.CANONICAL_PROJECT_ROOT}="
                f"{generator.CANONICAL_PROJECT_ROOT}"
                for kind in ("fdebug", "ffile", "fmacro")
            ],
            "include_flags": [
                "-iquote",
                f"{generator.CANONICAL_PROJECT_ROOT}/proof_port/scheduler",
                "-I",
                f"{generator.CANONICAL_PROJECT_ROOT}/upstream/Source/include",
            ],
            "link_flags": [
                "-T",
                f"{generator.CANONICAL_PROJECT_ROOT}/artifacts/frozen.ld",
            ],
            "tools": {},
            "artifact": {
                "path": self.elf_path.name,
                "sha256": elf_hash,
                "class": "ELF32",
                "endianness": "little",
                "machine": "Intel 80386",
                "type": "ET_EXEC",
                "pie": False,
                "interpreter": False,
                "dynamic_section": False,
                "stripped": False,
                "dwarf": True,
                "deterministic_relink_sha256_match": True,
            },
            "base_symbols": [
                self._base_record(name, size)
                for name, size in generator.EXPECTED_BASE_SYMBOLS
            ],
            "physical_roots": [
                self._root_record(logical_name, base_name, offset)
                for logical_name, base_name, offset in generator.EXPECTED_ROOTS
            ],
            "checks": {
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
            },
            "dwarf_structures": [
                {
                    "structure": name,
                    "observed_sizes": [size],
                    "expected_size": size,
                    "expected_present": True,
                }
                for name, size in generator.EXPECTED_DWARF_SIZES.items()
            ],
            "tcb_policy": {
                "elf_symbols": False,
                "detected_68_byte_object_symbols": [],
            },
            "inputs": [
                {"path": self.input_path.name, "sha256": generator.sha256(self.input_path)}
            ],
            "evidence": [
                {
                    "path": self.evidence_path.name,
                    "sha256": generator.sha256(self.evidence_path),
                },
                {"path": self.elf_path.name, "sha256": elf_hash},
            ],
        }

    def _write_ledger(self) -> None:
        self.ledger_path.write_text(
            json.dumps(self.ledger, indent=2) + "\n", encoding="utf-8"
        )

    def _verify(self, expected_elf_hash: str | None = None) -> str:
        self._write_ledger()
        return generator.verify_and_render(
            self.root,
            self.ledger_path,
            self.elf_path,
            expected_elf_hash or generator.sha256(self.elf_path),
        )

    def _sync_elf_hash(self) -> None:
        elf_hash = generator.sha256(self.elf_path)
        self.ledger["artifact"]["sha256"] = elf_hash
        for entry in self.ledger["evidence"]:
            if entry["path"] == self.elf_path.name:
                entry["sha256"] = elf_hash

    def _set_symbol_address(self, name: str, address: int) -> None:
        for record in self.ledger["base_symbols"]:
            if record["symbol"] == name:
                record["address_decimal"] = address
                for key in ("address_hex", "readelf_address_hex", "nm_address_hex"):
                    record[key] = address_hex(address)
        for record in self.ledger["physical_roots"]:
            if record["base_symbol"] == name:
                root_address = address + record["offset"]
                record["address_decimal"] = root_address
                for key in ("address_hex", "readelf_address_hex", "nm_address_hex"):
                    record[key] = address_hex(root_address)

    def test_valid_fixture_renders_exact_six_entry_configuration(self) -> None:
        rendered = self._verify()
        expected = ",".join(
            f"{name}={BASE_ADDRESSES[name]}"
            for name, _ in generator.EXPECTED_BASE_SYMBOLS
        )
        self.assertIn(f'val configuration = "{expected}"', rendered)

    def test_elf_hash_mutation_is_rejected(self) -> None:
        pinned_hash = generator.sha256(self.elf_path)
        data = bytearray(self.elf_path.read_bytes())
        data[-1] ^= 1
        self.elf_path.write_bytes(data)
        with self.assertRaisesRegex(ValueError, "frozen ELF hash changed"):
            self._verify(pinned_hash)

    def test_missing_addressed_symbol_is_rejected(self) -> None:
        self.ledger["base_symbols"].pop()
        with self.assertRaisesRegex(ValueError, "wrong base-symbol count"):
            self._verify()

    def test_extra_unused_addressed_symbol_is_rejected(self) -> None:
        extra = dict(self.ledger["base_symbols"][0])
        extra["symbol"] = "unusedSchedulerGlobal"
        self.ledger["base_symbols"].append(extra)
        with self.assertRaisesRegex(ValueError, "wrong base-symbol count"):
            self._verify()

    def test_aliased_symbol_regions_are_rejected_even_if_ledger_check_is_true(self) -> None:
        self._set_symbol_address(
            "xDelayedTaskList2", BASE_ADDRESSES["xDelayedTaskList1"]
        )
        with self.assertRaisesRegex(ValueError, "overlapping base-symbol regions"):
            self._verify()

    def test_misaligned_symbol_address_is_rejected(self) -> None:
        self._set_symbol_address(
            "xDelayedTaskList2", BASE_ADDRESSES["xDelayedTaskList2"] + 1
        )
        with self.assertRaisesRegex(ValueError, "symbol address is not 4-byte aligned"):
            self._verify()

    def test_symbol_size_20_to_16_is_rejected(self) -> None:
        self.ledger["base_symbols"][1]["size"] = 16
        with self.assertRaisesRegex(ValueError, "wrong symbol size"):
            self._verify()

    def test_elf64_header_is_rejected_after_all_hashes_are_synchronised(self) -> None:
        data = bytearray(self.elf_path.read_bytes())
        data[4] = 2
        self.elf_path.write_bytes(data)
        self._sync_elf_hash()
        with self.assertRaisesRegex(ValueError, "artifact ELF class is not ELF32"):
            self._verify()

    def test_et_dyn_header_is_rejected_after_all_hashes_are_synchronised(self) -> None:
        data = bytearray(self.elf_path.read_bytes())
        data[16:18] = (3).to_bytes(2, "little")
        self.elf_path.write_bytes(data)
        self._sync_elf_hash()
        with self.assertRaisesRegex(ValueError, "artifact ELF type is not ET_EXEC"):
            self._verify()

    def test_input_payload_hash_change_is_rejected(self) -> None:
        self.input_path.write_text("mutated input\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "input SHA-256 mismatch"):
            self._verify()

    def test_evidence_payload_hash_change_is_rejected(self) -> None:
        self.evidence_path.write_text("mutated evidence\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "evidence SHA-256 mismatch"):
            self._verify()

    def test_windows_drive_path_in_ledger_is_rejected(self) -> None:
        self.ledger["host_path"] = r"C:\Users\alice\freertos_v611_scheduler"
        with self.assertRaisesRegex(ValueError, "Windows drive path is forbidden"):
            self._verify()

    def test_wsl_mount_path_in_ledger_is_rejected(self) -> None:
        self.ledger["host_path"] = "/mnt/c/Users/alice/freertos_v611_scheduler"
        with self.assertRaisesRegex(ValueError, r"WSL /mnt/<drive> path is forbidden"):
            self._verify()

    def test_user_home_path_in_ledger_is_rejected(self) -> None:
        self.ledger["host_path"] = "/home/alice/freertos_v611_scheduler"
        with self.assertRaisesRegex(ValueError, "user home path is forbidden"):
            self._verify()

    def test_tools_kernel_is_rejected(self) -> None:
        self.ledger["tools"]["kernel"] = "Linux host-specific"
        with self.assertRaisesRegex(ValueError, r"tools\.kernel is forbidden"):
            self._verify()

    def test_wsl_distribution_field_is_rejected(self) -> None:
        self.ledger["wsl_distribution"] = "Ubuntu"
        with self.assertRaisesRegex(ValueError, "wsl_distribution is forbidden"):
            self._verify()

    def test_noncanonical_project_root_is_rejected(self) -> None:
        self.ledger["project_root"] = "/workspace/other"
        with self.assertRaisesRegex(ValueError, "project_root is not canonical"):
            self._verify()

    def test_noncanonical_include_project_path_is_rejected(self) -> None:
        self.ledger["include_flags"][1] = "/workspace/other/proof_port"
        with self.assertRaisesRegex(ValueError, "canonical project root"):
            self._verify()

    def test_host_path_in_hashed_text_evidence_is_rejected(self) -> None:
        self.evidence_path.write_text(
            "/mnt/d/alice/freertos_v611_scheduler/output\n", encoding="utf-8"
        )
        for entry in self.ledger["evidence"]:
            if entry["path"] == self.evidence_path.name:
                entry["sha256"] = generator.sha256(self.evidence_path)
        with self.assertRaisesRegex(ValueError, r"WSL /mnt/<drive> path is forbidden"):
            self._verify()


if __name__ == "__main__":
    unittest.main()
