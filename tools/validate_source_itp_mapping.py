#!/usr/bin/env python3
"""Validate the blind source-to-ITP mapping manifest.

The validator deliberately treats translation, abstract-model proofs, and
source-to-model refinement as three different stages.  In particular, a green
AutoCorres smoke build is never accepted as evidence of refinement.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any


LIST_OPERATIONS = (
    "vListInitialise",
    "vListInitialiseItem",
    "vListInsertEnd",
    "vListInsert",
    "vListRemove",
)
STAGES = ("translated", "abstract_model", "refined")
REFINEMENT_RUNG_SCOPES = {
    "Raw-R5": "fixed_empty_to_singleton",
    "Raw-R5-remove": "fixed_singleton_to_empty",
    "Raw-R6-remove-general": "general_N_member_remove",
    "Raw-R6-insert-general": "general_N_fresh_insert_end",
    "Raw-R6-remove-insert-sequence": "general_N_member_remove_then_insert_end",
    "Raw-R6-ordered-insert-empty": "restricted_empty_list_ordered_insert",
    "Raw-R6-initialise-item-insert-remove-sequence": "fixed_initialise_item_insert_end_remove_roundtrip",
    "Scheduler-Tick-Read": "quiescent_tick_read_boundary",
    "Scheduler-Switch-Suspended": "suspended_scheduler_control_boundary",
    "Scheduler-Increment-Tick-Suspended": "suspended_no_wrap_scheduler_control_boundary",
    "Scheduler-Delay-Zero": "zero_delay_no_wrap_scheduler_control_boundary",
    "Scheduler-Delay-Until-Suspended-No-Delay": "suspended_no_delay_scheduler_boundary",
    "Scheduler-P2-Frozen-Preimage": "artifact_bound_frozen_p2_positive_delay",
}
REFINEMENT_RUNG_RESULT_FRAGMENTS = {
    "Raw-R5": "Result ()",
    "Raw-R5-remove": "Result ()",
    "Raw-R6-remove-general": "Result ()",
    "Raw-R6-insert-general": "Result ()",
    "Raw-R6-remove-insert-sequence": "Result ()",
    "Raw-R6-ordered-insert-empty": "Result ()",
    "Raw-R6-initialise-item-insert-remove-sequence": "Result ()",
    "Scheduler-Tick-Read": "Result (fst (task_get_tick_abs a))",
    "Scheduler-Switch-Suspended": "Result ()",
    "Scheduler-Increment-Tick-Suspended": "Result ()",
    "Scheduler-Delay-Zero": "Result ()",
    "Scheduler-Delay-Until-Suspended-No-Delay": "Result ()",
    "Scheduler-P2-Frozen-Preimage": "Result ()",
}
REFINEMENT_RUNG_GENERALITY = {
    "Raw-R5": False,
    "Raw-R5-remove": False,
    "Raw-R6-remove-general": True,
    "Raw-R6-insert-general": True,
    "Raw-R6-remove-insert-sequence": True,
    "Raw-R6-ordered-insert-empty": False,
    "Raw-R6-initialise-item-insert-remove-sequence": False,
    "Scheduler-Tick-Read": False,
    "Scheduler-Switch-Suspended": False,
    "Scheduler-Increment-Tick-Suspended": False,
    "Scheduler-Delay-Zero": False,
    "Scheduler-Delay-Until-Suspended-No-Delay": False,
    "Scheduler-P2-Frozen-Preimage": False,
}
GENERAL_REMOVE_PRECONDITIONS = {"membership": "p is in set (ring xs)"}
GENERAL_REMOVE_SUPPORTING_LAYERS = (
    "Raw-R6-remove-metadata",
    "Raw-R6-remove-source-effects",
    "Raw-R6-remove-index-effect",
    "Raw-R6-remove-payload-effect",
    "Raw-R6-remove-topology-effect",
)
GENERAL_INSERT_PRECONDITIONS = {
    "freshness": "raw_fresh_for_insert lp (ring xs) p",
    "count_increment": "raw_count_can_increment xs",
}
GENERAL_INSERT_SUPPORTING_LAYERS = (
    "Raw-R6-insert-relation",
    "Raw-R6-insert-source-effects",
)
ORDERED_INSERT_EMPTY_PRECONDITIONS = {
    "empty_ring": "ring xs = []",
    "freshness": "raw_fresh_for_insert lp (ring xs) p",
    "sentinel_key": "raw_sentinel_max (hrs_mem (t_hrs_' s)) lp",
}
ORDERED_INSERT_EMPTY_SUPPORTING_LAYERS = (
    "Raw-R6-ordered-insert-empty-source",
)
ORDERED_INSERT_EMPTY_COROLLARIES = (
    "raw_vListInsert_ordered_empty_refines_ordered",
    "raw_vListInsert_ordered_empty_max_refines",
)
REMOVE_INSERT_SEQUENCE_OPERATION_IDS = ("LIST-REMOVE", "LIST-INSERT-END")
REMOVE_INSERT_SEQUENCE_SUPPORTING_RUNGS = (
    "Raw-R6-remove-general",
    "Raw-R6-insert-general",
)
REMOVE_INSERT_SEQUENCE_BRIDGES = {
    "freshness": "raw_remove_post_fresh_for_insert",
    "count_headroom": "raw_remove_post_count_can_increment",
    "key_preservation": "raw_remove_concrete_heap_preserves_item_key",
}
REMOVE_INSERT_SEQUENCE_INTERMEDIATE_THEOREMS = (
    "raw_vListRemove_general_sequence_ready",
    "raw_vListInsertEnd_sequence_continuation",
    "raw_vListInsertEnd_sequence_continuation_res",
)
FOUR_CALL_SEQUENCE_OPERATION_IDS = (
    "LIST-INITIALISE",
    "LIST-INITIALISE-ITEM",
    "LIST-INSERT-END",
    "LIST-REMOVE",
)
FOUR_CALL_SEQUENCE_SOURCE_FUNCTIONS = (
    "vListInitialise'",
    "vListInitialiseItem'",
    "vListInsertEnd'",
    "vListRemove'",
)
FOUR_CALL_SEQUENCE_SUPPORTING_RUNGS = (
    "Raw-R6-insert-general",
    "Raw-R6-remove-general",
)
FOUR_CALL_SEQUENCE_DEFINITION = "raw_initialise_insert_remove_needle'"
FOUR_CALL_SEQUENCE_COROLLARY = (
    "raw_vListInitialise_insert_end_remove_empty_refines"
)
SCHEDULER_P2_FROZEN_BOUNDARY_CONDITIONS = {
    "delay_argument": 2,
    "pre_phase": "StableRunning",
    "post_phase": "YieldPending",
    "prestate": "p2_pre",
    "poststate": "task_delay_abs 2 p2_pre",
    "runtime_tcb_addresses": "fresh logical witnesses",
    "allocator_boot_reachability": False,
}
FROZEN_MAPPED_BASES = (
    ("pxReadyTasksLists", "0x00102020", 80),
    ("xDelayedTaskList1", "0x0010208c", 20),
    ("xDelayedTaskList2", "0x001020a0", 20),
    ("xPendingReadyList", "0x001020bc", 20),
    ("xSuspendedTaskList", "0x001020d4", 20),
    ("xTasksWaitingTermination", "0x001020e8", 20),
)
FROZEN_STATIC_XLIST_REGIONS = (
    ("ready[0]", "0x00102020"),
    ("ready[1]", "0x00102034"),
    ("ready[2]", "0x00102048"),
    ("ready[3]", "0x0010205c"),
    ("delayed-A", "0x0010208c"),
    ("delayed-B", "0x001020a0"),
    ("pending-ready", "0x001020bc"),
    ("suspended", "0x001020d4"),
    ("termination-wait", "0x001020e8"),
)
FROZEN_P2_RELATION_ROOTS = FROZEN_STATIC_XLIST_REGIONS[:8]
FROZEN_ELF_SHA256 = (
    "DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A"
)
FROZEN_LEDGER_SHA256 = (
    "CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02"
)
FROZEN_ADDRESS_CONFIG_SHA256 = (
    "27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712"
)
ADDRESSED_GLOBAL_PATCH_SHA256 = (
    "44160F97B133D0A66E515E505636D641907DC14811D43DA071EA15C706C8E604"
)
UPSTREAM_CALCULATE_STATE_SHA256 = (
    "EA51ECAA01947E53AD38A684B0E97ED360339363A75C6AE16DCFBA7713562898"
)
PATCHED_CALCULATE_STATE_SHA256 = (
    "FD244D8228E79EC3626A5CE312446CE49DF550970B758B68D3BBE953CAC8CFA9"
)
SCHEDULER_TICK_BOUNDARY_CONDITIONS = {
    "eal6_port_critical_depth_'": 0,
    "eal6_port_interrupts_disabled_'": 0,
    "committed_tick_equality": "xTickCount_' = sa_tick",
    "returned_value": "committed_tick",
    "excluded_value": "sa_missed_ticks",
}
SCHEDULER_SWITCH_SUSPENDED_BOUNDARY_CONDITIONS = {
    "sa_suspend_depth": "nonzero",
    "uxSchedulerSuspended_'": "nonzero",
    "source_effect": "xMissedYield_' := 1",
    "abstract_effect": "sa_missed_yield := True",
    "ready_list_access": False,
    "proof_port_yield": False,
}
SCHEDULER_INCREMENT_TICK_SUSPENDED_BOUNDARY_CONDITIONS = {
    "sa_suspend_depth": "nonzero",
    "uxSchedulerSuspended_'": "nonzero",
    "scheduler_missed_tick_no_wrap": True,
    "source_effect": "uxMissedTicks_' := uxMissedTicks_' + 1",
    "abstract_effect": "sa_missed_ticks := Suc sa_missed_ticks",
    "committed_tick_changed": False,
    "delayed_list_access": False,
}
SCHEDULER_DELAY_ZERO_BOUNDARY_CONDITIONS = {
    "delay_argument": 0,
    "scheduler_yield_count_no_wrap": True,
    "source_effect": "eal6_port_yield_count_' := eal6_port_yield_count_' + 1",
    "abstract_effect": "sa_yield_count := Suc sa_yield_count",
    "scheduler_suspend_protocol": False,
    "current_tcb_access": False,
    "list_access": False,
}
SCHEDULER_DELAY_UNTIL_NO_DELAY_BOUNDARY_CONDITIONS = {
    "source_suspend_depth": 1,
    "internal_suspend_resume_depth": "1 -> 2 -> 1",
    "eal6_port_critical_depth_'": 0,
    "eal6_port_interrupts_disabled_'": 0,
    "previous_pointer_guard": True,
    "should_delay_until": False,
    "scheduler_yield_count_no_wrap": True,
    "abstract_wake_result": "previous + increment",
    "abstract_state_effect": "sa_yield_count := Suc sa_yield_count",
    "current_task_blocked": False,
    "list_migration": False,
    "proof_port_yield_count_increment": 1,
}
NON_REFINEMENT_LAYER_KINDS = {
    "Raw-R5-cycle": "raw_representation_lemma_layer",
    "Raw-R6-generic-prefix": "raw_representation_lemma_layer",
    "Raw-R6-dynamic-guards": "raw_representation_lemma_layer",
    "Raw-R6-unlink-locality": "raw_positive_execution_layer",
    "Raw-R6-remove-relation": "pure_relation_assembler",
    "Raw-R6-insert-relation": "pure_relation_assembler",
    "Raw-R6-insert-source-effects": "raw_source_heap_effect_layer",
    "Raw-R6-unlink-projection": "pure_alias_projection_layer",
    "Raw-R6-remove-metadata": "pure_effect_assembler",
    "Raw-R6-remove-source-effects": "raw_source_heap_effect_layer",
    "Raw-R6-remove-index-effect": "source_effect_projection_layer",
    "Raw-R6-remove-payload-effect": "source_effect_projection_layer",
    "Raw-R6-remove-topology-effect": "source_effect_projection_layer",
    "Raw-R6-ordered-insert-empty-source": "raw_source_heap_effect_layer",
    "Scheduler-ABS": "pure_abstract_model",
    "Scheduler-P2": "pure_abstract_model_witness",
    "Scheduler-Raw-List-Relabel": "pure_scheduler_list_relabel_layer",
    "Scheduler-P2-Generated-Layout": "generated_layout_diagnostic",
    "Scheduler-List-ABI-Bridge": "translation_unit_abi_bridge_layer",
    "Scheduler-List-ABI-Write-Bridge": "translation_unit_abi_write_bridge_layer",
    "Scheduler-P2-Raw-Relation": "conditional_scheduler_raw_relation_layer",
}
NON_REFINEMENT_LAYERS_OPENING_GENERATED_C = {
    "Raw-R6-unlink-locality",
    "Raw-R6-insert-source-effects",
    "Raw-R6-remove-source-effects",
    "Raw-R6-ordered-insert-empty-source",
}
HASHED_RUN_EVIDENCE_IDS = {
    "Raw-R6-ordered-insert-empty-source",
    "Raw-R6-ordered-insert-empty",
    "Scheduler-P2",
    "Scheduler-Raw-List-Relabel",
    "Scheduler-P2-Generated-Layout",
    "Scheduler-List-ABI-Bridge",
    "Scheduler-List-ABI-Write-Bridge",
    "Scheduler-P2-Raw-Relation",
    "Raw-R6-initialise-item-insert-remove-sequence",
    "Scheduler-P2-Frozen-Preimage",
}
EXPECTED_DEVELOPMENT_COSTS = {
    "Raw-R6-ordered-insert-empty-source": {
        "checker_calls": 18,
        "checker_green": 5,
        "elapsed_seconds": 534.339,
        "final_elapsed_seconds": 39.848,
    },
    "Raw-R6-ordered-insert-empty": {
        "checker_calls": 3,
        "checker_green": 1,
        "elapsed_seconds": 167.993,
        "final_elapsed_seconds": 89.835,
    },
    "Scheduler-P2": {
        "checker_calls": 6,
        "checker_green": 2,
        "elapsed_seconds": 115.266,
        "final_elapsed_seconds": 12.597,
    },
    "Scheduler-Raw-List-Relabel": {
        "checker_calls": 2,
        "checker_green": 1,
        "elapsed_seconds": 57.276,
        "final_elapsed_seconds": 29.046,
    },
    "Scheduler-P2-Generated-Layout": {
        "checker_calls": 4,
        "checker_green": 1,
        "elapsed_seconds": 236.199,
        "final_elapsed_seconds": 58.491,
    },
    "Scheduler-List-ABI-Bridge": {
        "checker_calls": 3,
        "checker_green": 3,
        "elapsed_seconds": 112.143,
        "final_elapsed_seconds": 23.281,
    },
    "Scheduler-List-ABI-Write-Bridge": {
        "checker_calls": 2,
        "checker_green": 2,
        "elapsed_seconds": 42.023,
        "final_elapsed_seconds": 20.882,
    },
    "Scheduler-P2-Raw-Relation": {
        "checker_calls": 8,
        "checker_green": 4,
        "elapsed_seconds": 251.043,
        "final_elapsed_seconds": 28.897,
    },
}
SCHEDULER_RELABEL_DEFINITIONS = (
    "xlist_relabel",
    "sched_xlist_rel",
)
SCHEDULER_RELABEL_FACTS = (
    "list_all2_decoder_left_closed",
    "list_all2_decoder_right_closed",
    "xlist_relabel_ring_length",
    "xlist_relabel_decoder_left_closed",
    "xlist_relabel_decoder_right_closed",
    "xlist_relabel_key_agreementD",
    "xlist_relabel_emptyI",
    "xlist_relabel_ready_singletonI",
    "xlist_relabel_ordered_singletonI",
    "sched_xlist_rel_emptyI",
    "sched_xlist_rel_ready_singletonI",
    "sched_xlist_rel_ordered_singletonI",
)
SCHEDULER_LAYOUT_DIAGNOSTICS = (
    "scheduler heap has the common effective carrier 32 word -> 8 word",
    "scheduler and raw-list xLIST_C pointer types clash",
    "scheduler and raw-list xLIST_ITEM_C pointer types clash",
    "function-address all_distinct does not establish scheduler object separation",
)
SCHEDULER_ABI_DEFINITIONS = (
    "abi_list_ptr",
    "abi_item_ptr",
    "scheduler_list_region",
    "scheduler_item_region",
    "abi_ready_list_root",
    "abi_delayed_list1_root",
    "abi_delayed_list2_root",
    "abi_pending_ready_list_root",
    "abi_suspended_list_root",
    "abi_current_delayed_list",
    "abi_overflow_delayed_list",
    "abi_generic_list_item_ptr",
    "abi_event_list_item_ptr",
)
SCHEDULER_ABI_FACTS = (
    "abi_list_ptr_ptr_val",
    "abi_item_ptr_ptr_val",
    "abi_list_ptr_eq_iff",
    "abi_item_ptr_eq_iff",
    "abi_list_ptr_NULL_iff",
    "abi_item_ptr_NULL_iff",
    "abi_list_ptr_NULL",
    "abi_item_ptr_NULL",
    "abi_xLIST_C_size",
    "abi_xLIST_C_align",
    "abi_xLIST_ITEM_C_size",
    "abi_xLIST_ITEM_C_align",
    "abi_xMINI_LIST_ITEM_C_size",
    "abi_xMINI_LIST_ITEM_C_align",
    "abi_list_ptr_c_guard",
    "abi_item_ptr_c_guard",
    "abi_list_region_eq",
    "abi_item_region_eq",
    "abi_ready_list_root_ptr_val",
    "abi_delayed_list1_root_ptr_val",
    "abi_delayed_list2_root_ptr_val",
    "abi_current_delayed_list_ptr_val",
    "abi_overflow_delayed_list_ptr_val",
    "abi_generic_list_item_ptr_ptr_val",
    "abi_event_list_item_ptr_ptr_val",
    "abi_xLIST_C_uxNumberOfItems_C_offset",
    "abi_xLIST_C_pxIndex_C_offset",
    "abi_xLIST_C_xListEnd_C_offset",
    "abi_xLIST_ITEM_C_xItemValue_C_offset",
    "abi_xLIST_ITEM_C_pxNext_C_offset",
    "abi_xLIST_ITEM_C_pxPrevious_C_offset",
    "abi_xLIST_ITEM_C_pvOwner_C_offset",
    "abi_xLIST_ITEM_C_pvContainer_C_offset",
    "abi_sentinel_field_address_commutes",
    "abi_list_h_val_packed",
    "abi_item_h_val_packed",
)
SCHEDULER_ABI_DESIGN_PLAN = {
    "path": "notes/SCHEDULER_TRANSLATION_UNIT_ABI_BRIDGE_PLAN.md",
    "status": "design_only_static",
    "sha256": "40B17DFB17C82FEE8869B45679B664CB595B98872E09FA0E8EA55AAC56231F6C",
    "checker_calls": 0,
    "is_checker_evidence": False,
    "is_source_to_abstract_refinement": False,
}
SCHEDULER_ABI_WRITE_DEFINITIONS = (
    "scheduler_generic_item_key_ptr",
    "raw_generic_item_key_ptr",
)
SCHEDULER_ABI_WRITE_FACTS = (
    "abi_generic_item_key_field_address",
    "abi_generic_item_key_field_write",
    "heap_update_pointer_value_coerce",
    "abi_item_next_field_address",
    "abi_item_next_field_write",
    "abi_item_previous_field_address",
    "abi_item_previous_field_write",
    "abi_item_container_field_address",
    "abi_item_container_field_write",
    "abi_list_index_field_address",
    "abi_list_index_field_write",
    "abi_list_count_field_address",
    "abi_list_count_field_write",
)
SCHEDULER_P2_RAW_RELATION_DEFINITIONS = (
    "generated_scheduler_roots",
    "scheduler_decode_rel",
    "scheduler_lists_rel",
    "scheduler_role_rel",
    "scheduler_scalar_rel",
    "scheduler_current_rel",
    "scheduler_boundary_rel",
    "raw_scheduler_rel",
    "yield_pending_wf",
)
SCHEDULER_P2_RAW_RELATION_FACTS = (
    "generated_scheduler_roots_fields",
    "scheduler_tcb_decode_iff",
    "scheduler_node_decode_Generic_iff",
    "scheduler_node_decode_Event_iff",
    "raw_scheduler_relI",
    "sched_xlist_rel_emptyE",
    "p2_pre_ready2_raw_singletonE",
    "p2_pre_delayed_a_raw_emptyE",
    "p2_pre_pending_raw_emptyE",
    "p2_pre_conditional_endpointI",
    "p2_post_conditional_endpointI",
)
NON_REFINEMENT_TRANSLATION_GATE_SCHEMAS = {
    "Scheduler-Parse": {
        "kind": "cparser_parse_gate",
        "translation_route": "cparser_unmodified_source_composition_unit",
        "covered_operation_ids": [],
    },
    "Scheduler-Tick-Raw": {
        "kind": "raw_heap_autocorres_translation_gate",
        "translation_route": "skip_heap_abs",
        "covered_operation_ids": ["ROOT-GET-TICK"],
    },
    "Scheduler-Delay-Raw": {
        "kind": "raw_heap_autocorres_translation_gate",
        "translation_route": "skip_heap_abs",
        "covered_operation_ids": [
            "ROOT-DELAY",
            "ROOT-INCREMENT-TICK",
            "HELPER-SUSPEND-ALL",
            "HELPER-RESUME-ALL",
        ],
    },
    "Scheduler-Roots-Raw": {
        "kind": "raw_heap_autocorres_translation_gate",
        "translation_route": "skip_heap_abs",
        "covered_operation_ids": [
            "ROOT-DELAY-UNTIL",
            "ROOT-SWITCH-CONTEXT",
        ],
    },
}
HEX_SHA256 = re.compile(r"^[0-9A-F]{64}$")
LINE_RANGE = re.compile(r"^(?P<first>[1-9][0-9]*)(?:-(?P<last>[1-9][0-9]*))?$")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _range_bounds(specification: str) -> tuple[int, int]:
    match = LINE_RANGE.fullmatch(specification)
    if not match:
        raise ValueError(f"invalid line range {specification!r}")
    first = int(match.group("first"))
    last = int(match.group("last") or first)
    if last < first:
        raise ValueError(f"reversed line range {specification!r}")
    return first, last


def _expand_ranges(specifications: list[str]) -> set[int]:
    result: set[int] = set()
    for specification in specifications:
        first, last = _range_bounds(specification)
        result.update(range(first, last + 1))
    return result


def _parse_sha256sums(path: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for raw_line in path.read_text(encoding="ascii").splitlines():
        if not raw_line.strip():
            continue
        digest, relative_name = raw_line.split(maxsplit=1)
        result[relative_name.replace("\\", "/")] = digest.upper()
    return result


def _parse_status(path: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        if "=" in raw_line:
            key, value = raw_line.split("=", 1)
            result[key] = value
    return result


def _validate_run_artifact_hashes(
    errors: list[str],
    project_root: Path,
    prefix: str,
    record: dict[str, Any],
) -> None:
    """Validate the explicitly sealed status/stdout bytes for new evidence."""

    run_id = record.get("run_id")
    status_name = record.get("status_file")
    status_digest = record.get("status_sha256")
    stdout_name = record.get("stdout_file")
    stdout_digest = record.get("stdout_sha256")

    if not isinstance(status_name, str) or not isinstance(
        status_digest, str
    ) or not HEX_SHA256.fullmatch(status_digest):
        errors.append(f"{prefix}: status_sha256 must seal the recorded status file")
    else:
        status_path = project_root / status_name
        if status_path.is_file():
            actual = hashlib.sha256(status_path.read_bytes()).hexdigest().upper()
            if actual != status_digest:
                errors.append(f"{prefix}: status_sha256 disagrees with status file")

    expected_stdout = f"runs/{run_id}/stdout.log" if isinstance(run_id, str) else None
    if (
        not isinstance(stdout_name, str)
        or stdout_name.replace("\\", "/") != expected_stdout
    ):
        errors.append(f"{prefix}: stdout_file path disagrees with run_id")
        return
    if not isinstance(stdout_digest, str) or not HEX_SHA256.fullmatch(stdout_digest):
        errors.append(f"{prefix}: stdout_sha256 must seal the recorded stdout file")
        return

    stdout_path = project_root / stdout_name
    if not stdout_path.is_file():
        errors.append(f"{prefix}: missing stdout file {stdout_name}")
        return
    actual_stdout = hashlib.sha256(stdout_path.read_bytes()).hexdigest().upper()
    if actual_stdout != stdout_digest:
        errors.append(f"{prefix}: stdout_sha256 disagrees with stdout file")

    if isinstance(status_name, str):
        status_path = project_root / status_name
        if status_path.is_file():
            status = _parse_status(status_path)
            if status.get("stdout_sha256") != stdout_digest:
                errors.append(f"{prefix}: stdout_sha256 disagrees with status contents")


def _validate_portable_artifact_identity(
    errors: list[str], prefix: str, status: dict[str, str]
) -> None:
    """Require a run to belong to the current portable frozen-artifact universe."""

    for status_key, expected, label in (
        ("frozen_layout_elf_sha256", FROZEN_ELF_SHA256, "ELF"),
        ("frozen_layout_ledger_sha256", FROZEN_LEDGER_SHA256, "ledger"),
        (
            "generated_address_config_sha256",
            FROZEN_ADDRESS_CONFIG_SHA256,
            "generated config",
        ),
    ):
        if status.get(status_key) != expected:
            errors.append(f"{prefix} {label} identity drifted")


def _validate_frozen_artifact_binding(
    errors: list[str], project_root: Path, manifest: dict[str, Any]
) -> None:
    """Validate the six-base -> nine-region -> eight-P2-root evidence ledger."""

    prefix = "frozen_artifact_binding"
    binding = manifest.get(prefix)
    if not isinstance(binding, dict):
        errors.append(f"{prefix} must be an object")
        return
    if binding.get("status") != "checker_green":
        errors.append(f"{prefix}.status must be 'checker_green'")

    def checked_file(record_name: str, expected_digest: str | None = None) -> Path | None:
        record = binding.get(record_name)
        record_prefix = f"{prefix}.{record_name}"
        if not isinstance(record, dict):
            errors.append(f"{record_prefix} must be an object")
            return None
        relative = record.get("path")
        digest = record.get("sha256")
        if not isinstance(relative, str) or not relative:
            errors.append(f"{record_prefix}.path must be a non-empty string")
            return None
        path = project_root / relative
        if not path.is_file():
            errors.append(f"{record_prefix}: missing file {relative}")
            return None
        actual = hashlib.sha256(path.read_bytes()).hexdigest().upper()
        if digest != actual:
            errors.append(f"{record_prefix}.sha256 disagrees with file")
        if expected_digest is not None and digest != expected_digest:
            errors.append(f"{record_prefix}.sha256 disagrees with frozen identity")
        return path

    elf_path = checked_file("elf", FROZEN_ELF_SHA256)
    ledger_path = checked_file("ledger", FROZEN_LEDGER_SHA256)
    if elf_path is not None and ledger_path is not None:
        try:
            ledger = _read_json(ledger_path)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            errors.append(f"{prefix}.ledger is not valid JSON: {exc}")
            ledger = {}
        artifact = ledger.get("artifact", {})
        if str(artifact.get("sha256", "")).upper() != FROZEN_ELF_SHA256:
            errors.append(f"{prefix}.ledger artifact hash disagrees with frozen ELF")
        if artifact.get("deterministic_relink_sha256_match") is not True:
            errors.append(f"{prefix}.ledger does not certify deterministic relinking")

        ledger_bases = tuple(
            (entry.get("symbol"), entry.get("address_hex"), entry.get("size"))
            for entry in ledger.get("base_symbols", [])
            if isinstance(entry, dict)
        )
        if ledger_bases != FROZEN_MAPPED_BASES:
            errors.append(f"{prefix}.ledger does not contain the exact six mapped bases")
        ledger_roots = tuple(
            (entry.get("logical_name"), entry.get("address_hex"))
            for entry in ledger.get("physical_roots", [])
            if isinstance(entry, dict)
        )
        if ledger_roots != FROZEN_P2_RELATION_ROOTS:
            errors.append(f"{prefix}.ledger does not contain the exact eight P2 roots")

    mapped_bases = tuple(
        (entry.get("symbol"), entry.get("address_hex"), entry.get("size"))
        for entry in binding.get("mapped_bases", [])
        if isinstance(entry, dict)
    )
    if mapped_bases != FROZEN_MAPPED_BASES:
        errors.append(f"{prefix}.mapped_bases must record the exact six ELF bases")
    static_regions = tuple(
        (entry.get("logical_name"), entry.get("address_hex"))
        for entry in binding.get("static_xlist_regions", [])
        if isinstance(entry, dict)
    )
    if static_regions != FROZEN_STATIC_XLIST_REGIONS:
        errors.append(f"{prefix}.static_xlist_regions must record the exact nine regions")
    p2_roots = tuple(
        (entry.get("logical_name"), entry.get("address_hex"))
        for entry in binding.get("p2_relation_roots", [])
        if isinstance(entry, dict)
    )
    if p2_roots != FROZEN_P2_RELATION_ROOTS:
        errors.append(f"{prefix}.p2_relation_roots must record the exact eight roots")
    if binding.get("counts") != {
        "mapped_bases": 6,
        "static_xlist_regions": 9,
        "p2_relation_roots": 8,
    }:
        errors.append(f"{prefix}.counts must be exactly six/nine/eight")
    if binding.get("runtime_tcb_policy") != "fresh_logical_witness_addresses":
        errors.append(f"{prefix}.runtime_tcb_policy must keep TCBs logical")

    parser = binding.get("patched_parser")
    if not isinstance(parser, dict):
        errors.append(f"{prefix}.patched_parser must be an object")
    else:
        patch_name = parser.get("patch_path")
        patch_path = project_root / patch_name if isinstance(patch_name, str) else None
        if patch_path is None or not patch_path.is_file():
            errors.append(f"{prefix}.patched_parser patch is missing")
        elif hashlib.sha256(patch_path.read_bytes()).hexdigest().upper() != parser.get(
            "patch_sha256"
        ):
            errors.append(f"{prefix}.patched_parser patch_sha256 disagrees with file")
        if parser.get("patch_sha256") != ADDRESSED_GLOBAL_PATCH_SHA256:
            errors.append(f"{prefix}.patched_parser patch identity is not pinned")
        if parser.get("upstream_calculate_state_sha256") != UPSTREAM_CALCULATE_STATE_SHA256:
            errors.append(f"{prefix}.patched_parser upstream calculate_state hash is wrong")
        if parser.get("staged_calculate_state_sha256") != PATCHED_CALCULATE_STATE_SHA256:
            errors.append(f"{prefix}.patched_parser staged calculate_state hash is wrong")
        if parser.get("generated_address_config_sha256") != FROZEN_ADDRESS_CONFIG_SHA256:
            errors.append(f"{prefix}.patched_parser generated config hash is wrong")
        if parser.get("config_option") != "c_parser_addressed_global_definitions":
            errors.append(f"{prefix}.patched_parser config option is wrong")

        parser_theory_name = parser.get("theory")
        parser_theory = (
            project_root / parser_theory_name
            if isinstance(parser_theory_name, str)
            else None
        )
        if parser_theory is None or not parser_theory.is_file():
            errors.append(f"{prefix}.patched_parser theory is missing")
        else:
            actual = hashlib.sha256(parser_theory.read_bytes()).hexdigest().upper()
            if parser.get("theory_sha256") != actual:
                errors.append(f"{prefix}.patched_parser theory_sha256 disagrees with file")
            parser_text = parser_theory.read_text(encoding="utf-8")
            for needle in (
                "P2_Root_Address_Config.configuration",
                "CalculateState.addressed_global_definitions",
            ):
                if needle not in parser_text:
                    errors.append(f"{prefix}.patched_parser theory omits {needle!r}")

        generated = project_root / "build/generated/P2_Root_Address_Config.ML"
        if generated.is_file():
            actual = hashlib.sha256(generated.read_bytes()).hexdigest().upper()
            if actual != FROZEN_ADDRESS_CONFIG_SHA256:
                errors.append(f"{prefix}.patched_parser generated config bytes drifted")

        parser_evidence = parser.get("evidence")
        parser_prefix = f"{prefix}.patched_parser.evidence"
        if not isinstance(parser_evidence, dict):
            errors.append(f"{parser_prefix} must be an object")
        else:
            _validate_run_artifact_hashes(
                errors, project_root, parser_prefix, parser_evidence
            )
            expected_session = "EAL6_FreeRTOS_V611_Scheduler_Parse"
            if parser_evidence.get("session") != expected_session:
                errors.append(f"{parser_prefix} session is wrong")
            run_id = parser_evidence.get("run_id")
            status_name = parser_evidence.get("status_file")
            expected_status = (
                f"runs/{run_id}/status.txt" if isinstance(run_id, str) else None
            )
            if (
                not isinstance(status_name, str)
                or status_name.replace("\\", "/") != expected_status
            ):
                errors.append(f"{parser_prefix} status path disagrees with run_id")
            else:
                status_path = project_root / status_name
                if not status_path.is_file():
                    errors.append(f"{parser_prefix} status file is missing")
                else:
                    status = _parse_status(status_path)
                    if status.get("run_id") != run_id:
                        errors.append(f"{parser_prefix} run_id disagrees with status")
                    if status.get("session") != expected_session:
                        errors.append(f"{parser_prefix} session disagrees with status")
                    if (
                        status.get("exit_code") != "0"
                        or status.get("quick_and_dirty") != "false"
                        or status.get("timed_out") != "false"
                    ):
                        errors.append(f"{parser_prefix} is not kernel-green")
                    _validate_portable_artifact_identity(
                        errors, parser_prefix, status
                    )

    geometry = binding.get("static_geometry")
    if not isinstance(geometry, dict):
        errors.append(f"{prefix}.static_geometry must be an object")
    else:
        theory_name = geometry.get("theory")
        if geometry.get("theorem") != "frozen_addressed_xlist_geometry":
            errors.append(f"{prefix}.static_geometry theorem is wrong")
        if geometry.get("p2_projection_theorem") != "frozen_p2_static_root_geometry":
            errors.append(f"{prefix}.static_geometry P2 projection theorem is wrong")
        theory_path = project_root / theory_name if isinstance(theory_name, str) else None
        if theory_path is None or not theory_path.is_file():
            errors.append(f"{prefix}.static_geometry theory is missing")
        else:
            actual = hashlib.sha256(theory_path.read_bytes()).hexdigest().upper()
            if geometry.get("theory_sha256") != actual:
                errors.append(f"{prefix}.static_geometry theory_sha256 disagrees with file")
            theory_text = theory_path.read_text(encoding="utf-8")
            for fact in (
                "frozen_addressed_global_pointers",
                "frozen_addressed_xlist_roots_exact",
                "frozen_addressed_xlist_geometry",
                "frozen_p2_static_root_geometry",
            ):
                if not _declares_isabelle_fact(theory_text, fact):
                    errors.append(f"{prefix}.static_geometry omits fact {fact!r}")

    evidence = binding.get("binding_evidence")
    if not isinstance(evidence, dict):
        errors.append(f"{prefix}.binding_evidence must be an object")
    else:
        _validate_run_artifact_hashes(errors, project_root, f"{prefix}.binding_evidence", evidence)
        if evidence.get("session") != (
            "EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Static_Layout"
        ):
            errors.append(f"{prefix}.binding_evidence must check the static layout session")
        run_id = evidence.get("run_id")
        status_name = evidence.get("status_file")
        expected_status = f"runs/{run_id}/status.txt" if isinstance(run_id, str) else None
        if not isinstance(status_name, str) or status_name.replace("\\", "/") != expected_status:
            errors.append(f"{prefix}.binding_evidence status path disagrees with run_id")
        else:
            status_path = project_root / status_name
            if not status_path.is_file():
                errors.append(f"{prefix}.binding_evidence status file is missing")
            else:
                status = _parse_status(status_path)
                if status.get("session") != evidence.get("session"):
                    errors.append(f"{prefix}.binding_evidence session disagrees with status")
                if (
                    status.get("exit_code") != "0"
                    or status.get("quick_and_dirty") != "false"
                    or status.get("timed_out") != "false"
                ):
                    errors.append(f"{prefix}.binding_evidence is not kernel-green")
                _validate_portable_artifact_identity(
                    errors, f"{prefix}.binding_evidence", status
                )

    for record_name, expected_session, expected_facts, require_frozen_hashes in (
        (
            "stock_layout_no_go",
            "EAL6_FreeRTOS_V611_Scheduler_P2_Layout_No_Go",
            ("p2_source_footprint_delayed_alias_no_go",),
            True,
        ),
        (
            "dynamic_geometry",
            "EAL6_FreeRTOS_V611_Scheduler_P2_Frozen_Dynamic_Geometry",
            (
                "frozen_p2_tcb_addressed_xlist_separation",
                "frozen_p2_nonheap_geometry",
            ),
            True,
        ),
    ):
        record_prefix = f"{prefix}.{record_name}"
        record = binding.get(record_name)
        if not isinstance(record, dict):
            errors.append(f"{record_prefix} must be an object")
            continue
        theory_name = record.get("theory")
        theory_path = project_root / theory_name if isinstance(theory_name, str) else None
        if theory_path is None or not theory_path.is_file():
            errors.append(f"{record_prefix} theory is missing")
        else:
            actual = hashlib.sha256(theory_path.read_bytes()).hexdigest().upper()
            if record.get("theory_sha256") != actual:
                errors.append(f"{record_prefix} theory_sha256 disagrees with file")
            theory_text = theory_path.read_text(encoding="utf-8")
            for fact in expected_facts:
                if not _declares_isabelle_fact(theory_text, fact):
                    errors.append(f"{record_prefix} omits fact {fact!r}")
        if record.get("theorem") != expected_facts[-1]:
            errors.append(f"{record_prefix} principal theorem is wrong")
        if record_name == "dynamic_geometry":
            if record.get("tcb_separation_theorem") != expected_facts[0]:
                errors.append(f"{record_prefix} TCB separation theorem is wrong")
            if record.get("separated_static_region_count") != 9:
                errors.append(f"{record_prefix} must separate TCBs from all nine regions")

        record_evidence = record.get("evidence")
        if not isinstance(record_evidence, dict):
            errors.append(f"{record_prefix}.evidence must be an object")
            continue
        _validate_run_artifact_hashes(
            errors, project_root, f"{record_prefix}.evidence", record_evidence
        )
        if record_evidence.get("session") != expected_session:
            errors.append(f"{record_prefix}.evidence session is wrong")
        status_name = record_evidence.get("status_file")
        status_path = project_root / status_name if isinstance(status_name, str) else None
        if status_path is None or not status_path.is_file():
            errors.append(f"{record_prefix}.evidence status file is missing")
            continue
        status = _parse_status(status_path)
        if status.get("run_id") != record_evidence.get("run_id"):
            errors.append(f"{record_prefix}.evidence run_id disagrees with status")
        if status.get("session") != expected_session:
            errors.append(f"{record_prefix}.evidence session disagrees with status")
        if (
            status.get("exit_code") != "0"
            or status.get("quick_and_dirty") != "false"
            or status.get("timed_out") != "false"
        ):
            errors.append(f"{record_prefix}.evidence is not kernel-green")
        if require_frozen_hashes:
            _validate_portable_artifact_identity(
                errors, f"{record_prefix}.evidence", status
            )


def _validate_green_evidence(
    errors: list[str],
    project_root: Path,
    operation_name: str,
    stage_name: str,
    stage: dict[str, Any],
    required_kind: str,
) -> None:
    evidence = stage.get("evidence")
    prefix = f"{operation_name}.{stage_name}"
    if not isinstance(evidence, dict):
        errors.append(f"{prefix}: checker-green claim lacks evidence")
        return

    actual_kind = evidence.get("kind")
    if actual_kind != required_kind:
        errors.append(
            f"{prefix}: requires evidence kind {required_kind!r}, got {actual_kind!r}"
        )
        if stage_name == "refined" and actual_kind == "translation_smoke":
            errors.append(
                f"{prefix}: translation_smoke cannot establish refinement"
            )

    status_name = evidence.get("status_file")
    if not isinstance(status_name, str):
        errors.append(f"{prefix}: evidence lacks status_file")
        return
    status_path = project_root / status_name
    if not status_path.is_file():
        errors.append(f"{prefix}: missing evidence file {status_name}")
        return

    status = _parse_status(status_path)
    if status.get("exit_code") != "0":
        errors.append(f"{prefix}: evidence exit_code is not zero")
    if status.get("quick_and_dirty") != "false":
        errors.append(f"{prefix}: evidence is not quick_and_dirty=false")
    if status.get("timed_out") != "false":
        errors.append(f"{prefix}: evidence timed out or omits timed_out=false")
    if evidence.get("run_id") != status.get("run_id"):
        errors.append(f"{prefix}: run_id disagrees with status file")
    if stage.get("session") != status.get("session"):
        errors.append(f"{prefix}: session disagrees with status file")


def _validate_theory_references(
    errors: list[str],
    project_root: Path,
    root_text: str,
    operation_name: str,
    stage_name: str,
    stage: dict[str, Any],
    needles: list[str],
) -> None:
    prefix = f"{operation_name}.{stage_name}"
    session = stage.get("session")
    if not isinstance(session, str) or f"session {session} " not in root_text:
        errors.append(f"{prefix}: session is absent from theories/ROOT")

    theory_names = stage.get("theories")
    if not isinstance(theory_names, list) or not theory_names:
        errors.append(f"{prefix}: no theory files are recorded")
        return
    contents: list[str] = []
    for theory_name in theory_names:
        theory_path = project_root / theory_name
        if not theory_path.is_file():
            errors.append(f"{prefix}: missing theory {theory_name}")
            continue
        contents.append(theory_path.read_text(encoding="utf-8"))
    combined = "\n".join(contents)
    for needle in needles:
        if needle not in combined:
            errors.append(f"{prefix}: {needle!r} is absent from recorded theories")


def _declares_isabelle_fact(theory_text: str, fact_name: str) -> bool:
    """Recognise a named Isabelle fact declaration, not a prose mention."""

    declaration = re.compile(
        rf"^\s*(?:lemma|theorem|corollary|proposition)\s+"
        rf"{re.escape(fact_name)}(?:\s*\[[^\n]*\])?\s*:",
        flags=re.MULTILINE,
    )
    return declaration.search(theory_text) is not None


def _isabelle_fact_statement(theory_text: str, fact_name: str) -> str | None:
    """Return the declaration statement before its proof, if it exists."""

    declaration = re.compile(
        rf"^\s*(?:lemma|theorem|corollary|proposition)\s+"
        rf"{re.escape(fact_name)}(?:\s*\[[^\n]*\])?\s*:",
        flags=re.MULTILINE,
    )
    match = declaration.search(theory_text)
    if match is None:
        return None
    tail = theory_text[match.start() :]
    proof = re.search(r"^\s*(?:proof|by|using)\b", tail, flags=re.MULTILINE)
    return tail if proof is None else tail[: proof.start()]


def _declares_isabelle_definition(theory_text: str, constant_name: str) -> bool:
    """Recognise a named Isabelle definition, not an incidental text mention."""

    declaration = re.compile(
        rf"^\s*(?:definition|abbreviation|fun|function|primrec)\s+"
        rf"{re.escape(constant_name)}(?:\s|$)",
        flags=re.MULTILINE,
    )
    return declaration.search(theory_text) is not None


def _validate_raw_operational_rungs(
    errors: list[str],
    project_root: Path,
    root_text: str,
    raw_rungs: Any,
) -> None:
    """Validate concrete raw-heap proof rungs without creating refinement claims."""

    if not isinstance(raw_rungs, list) or not raw_rungs:
        errors.append("raw_operational_rungs must be a non-empty list")
        return

    rung_ids: list[str] = []
    for index, rung in enumerate(raw_rungs):
        prefix = f"raw_operational_rungs[{index}]"
        if not isinstance(rung, dict):
            errors.append(f"{prefix}: rung must be an object")
            continue

        rung_id = rung.get("id")
        if not isinstance(rung_id, str) or not rung_id.strip():
            errors.append(f"{prefix}: id must be a non-empty string")
        else:
            rung_ids.append(rung_id)
            prefix = f"raw_operational_rungs[{rung_id}]"

        if rung.get("status") != "checker_green":
            errors.append(f"{prefix}: status must be 'checker_green'")
        if rung.get("is_source_to_abstract_refinement") is not False:
            errors.append(
                f"{prefix}: is_source_to_abstract_refinement must be exactly false"
            )
        if not isinstance(rung.get("claim"), str) or not rung["claim"].strip():
            errors.append(f"{prefix}: claim must be a non-empty string")

        session = rung.get("session")
        if not isinstance(session, str) or f"session {session} " not in root_text:
            errors.append(f"{prefix}: session is absent from theories/ROOT")

        has_theorem = "theorem" in rung
        has_theorems = "theorems" in rung
        theorem_names: list[str] = []
        if has_theorem == has_theorems:
            errors.append(f"{prefix}: record exactly one of theorem or theorems")
        elif has_theorem:
            theorem = rung.get("theorem")
            if isinstance(theorem, str) and theorem.strip():
                theorem_names = [theorem]
            else:
                errors.append(f"{prefix}: theorem must be a non-empty string")
        else:
            theorems = rung.get("theorems")
            if (
                isinstance(theorems, list)
                and theorems
                and all(isinstance(name, str) and name.strip() for name in theorems)
            ):
                theorem_names = list(theorems)
                if len(theorem_names) != len(set(theorem_names)):
                    errors.append(f"{prefix}: theorem names are not unique")
            else:
                errors.append(f"{prefix}: theorems must be a non-empty string list")

        theory_names = rung.get("theories")
        theory_contents: list[str] = []
        if (
            not isinstance(theory_names, list)
            or not theory_names
            or not all(isinstance(name, str) and name for name in theory_names)
        ):
            errors.append(f"{prefix}: theories must be a non-empty string list")
        else:
            if len(theory_names) != len(set(theory_names)):
                errors.append(f"{prefix}: theory paths are not unique")
            for theory_name in theory_names:
                theory_path = project_root / theory_name
                if not theory_path.is_file():
                    errors.append(f"{prefix}: missing theory {theory_name}")
                    continue
                theory_contents.append(theory_path.read_text(encoding="utf-8"))
        combined_theories = "\n".join(theory_contents)
        if "theory_sha256" in rung:
            if not isinstance(theory_names, list) or len(theory_names) != 1:
                errors.append(
                    f"{prefix}: theory_sha256 requires exactly one recorded theory"
                )
            else:
                theory_path = project_root / theory_names[0]
                if theory_path.is_file():
                    actual_digest = hashlib.sha256(theory_path.read_bytes()).hexdigest().upper()
                    if rung.get("theory_sha256") != actual_digest:
                        errors.append(f"{prefix}: theory_sha256 disagrees with theory")
        for theorem_name in theorem_names:
            if not _declares_isabelle_fact(combined_theories, theorem_name):
                errors.append(
                    f"{prefix}: theorem {theorem_name!r} is not declared "
                    "in the recorded theories"
                )

        run_id = rung.get("run_id")
        status_name = rung.get("status_file")
        if not isinstance(run_id, str) or not run_id.strip():
            errors.append(f"{prefix}: run_id must be a non-empty string")
            continue
        expected_status_name = f"runs/{run_id}/status.txt"
        if not isinstance(status_name, str):
            errors.append(f"{prefix}: status_file must be a string")
            continue
        if status_name.replace("\\", "/") != expected_status_name:
            errors.append(f"{prefix}: status_file path disagrees with run_id")
        status_path = project_root / status_name
        if not status_path.is_file():
            errors.append(f"{prefix}: missing status file {status_name}")
            continue
        status = _parse_status(status_path)
        if status.get("run_id") != run_id:
            errors.append(f"{prefix}: run_id disagrees with status file contents")
        if status.get("session") != session:
            errors.append(f"{prefix}: session disagrees with status file")
        if status.get("exit_code") != "0":
            errors.append(f"{prefix}: evidence exit_code is not zero")
        if status.get("quick_and_dirty") != "false":
            errors.append(f"{prefix}: evidence is not quick_and_dirty=false")
        if status.get("timed_out") != "false":
            errors.append(f"{prefix}: evidence timed out or omits timed_out=false")

    duplicates = sorted(
        rung_id for rung_id, count in Counter(rung_ids).items() if count > 1
    )
    for rung_id in duplicates:
        errors.append(f"raw_operational_rungs: duplicate id {rung_id!r}")


def _validate_non_refinement_proof_layers(
    errors: list[str],
    project_root: Path,
    root_text: str,
    layers: Any,
) -> None:
    """Validate green scaffolding that must not be counted as refinement."""

    if not isinstance(layers, list):
        errors.append("non_refinement_proof_layers must be a list")
        return

    layer_ids: list[str] = []
    for index, layer in enumerate(layers):
        prefix = f"non_refinement_proof_layers[{index}]"
        if not isinstance(layer, dict):
            errors.append(f"{prefix}: layer must be an object")
            continue

        layer_id = layer.get("id")
        if not isinstance(layer_id, str) or not layer_id.strip():
            errors.append(f"{prefix}: id must be a non-empty string")
        else:
            layer_ids.append(layer_id)
            prefix = f"non_refinement_proof_layers[{layer_id}]"
            expected_kind = NON_REFINEMENT_LAYER_KINDS.get(layer_id)
            if expected_kind is None:
                errors.append(f"{prefix}: id is not recognised by schema 1")
            elif layer.get("kind") != expected_kind:
                errors.append(f"{prefix}: kind must be {expected_kind!r}")

        if layer.get("status") != "checker_green":
            errors.append(f"{prefix}: status must be 'checker_green'")
        expected_opens_c = layer_id in NON_REFINEMENT_LAYERS_OPENING_GENERATED_C
        if layer.get("opens_generated_c_body") is not expected_opens_c:
            errors.append(
                f"{prefix}: opens_generated_c_body must be exactly "
                f"{str(expected_opens_c).lower()}"
            )
        if layer.get("is_source_to_abstract_refinement") is not False:
            errors.append(
                f"{prefix}: is_source_to_abstract_refinement must be exactly false"
            )
        if layer.get("source_to_abstract_refinement_theorem_count_delta") != 0:
            errors.append(
                f"{prefix}: source_to_abstract_refinement_theorem_count_delta "
                "must be exactly zero"
            )
        for label in ("scope", "claim"):
            value = layer.get(label)
            if not isinstance(value, str) or not value.strip():
                errors.append(f"{prefix}: {label} must be a non-empty string")
        expected_cost = EXPECTED_DEVELOPMENT_COSTS.get(layer_id)
        if expected_cost is not None and layer.get("development_cost") != expected_cost:
            errors.append(f"{prefix}: development_cost disagrees with recorded runs")

        definitions = layer.get("definitions")
        theorems = layer.get("theorems")
        if not isinstance(definitions, list) or not all(
            isinstance(name, str) and name.strip() for name in definitions
        ):
            errors.append(f"{prefix}: definitions must be a string list")
            definitions = []
        if not isinstance(theorems, list) or not all(
            isinstance(name, str) and name.strip() for name in theorems
        ):
            errors.append(f"{prefix}: theorems must be a string list")
            theorems = []
        if (
            not definitions
            and not theorems
            and layer_id != "Scheduler-P2-Generated-Layout"
        ):
            errors.append(f"{prefix}: record at least one definition or theorem")
        if len(definitions) != len(set(definitions)):
            errors.append(f"{prefix}: definition names are not unique")
        if len(theorems) != len(set(theorems)):
            errors.append(f"{prefix}: theorem names are not unique")
        if layer_id in {
            "Scheduler-Raw-List-Relabel",
            "Scheduler-P2-Generated-Layout",
            "Scheduler-List-ABI-Bridge",
            "Scheduler-List-ABI-Write-Bridge",
            "Scheduler-P2-Raw-Relation",
        } and layer.get("fact_count") != len(theorems):
            errors.append(f"{prefix}: fact_count disagrees with recorded theorems")

        theory_name = layer.get("theory")
        theory_text = ""
        if not isinstance(theory_name, str) or not theory_name:
            errors.append(f"{prefix}: theory must be a non-empty string")
        else:
            theory_path = project_root / theory_name
            if not theory_path.is_file():
                errors.append(f"{prefix}: missing theory {theory_name}")
            else:
                theory_text = theory_path.read_text(encoding="utf-8")
                actual_digest = hashlib.sha256(theory_path.read_bytes()).hexdigest().upper()
                if layer.get("theory_sha256") != actual_digest:
                    errors.append(f"{prefix}: theory_sha256 disagrees with theory")
        for definition in definitions:
            if not _declares_isabelle_definition(theory_text, definition):
                errors.append(
                    f"{prefix}: definition {definition!r} is not declared in the theory"
                )
        for theorem in theorems:
            if not _declares_isabelle_fact(theory_text, theorem):
                errors.append(
                    f"{prefix}: theorem {theorem!r} is not declared in the theory"
                )

        if layer_id == "Raw-R6-ordered-insert-empty-source":
            expected_definitions = (
                "raw_sentinel_max",
                "raw_ordered_insert_empty_heap",
                "raw_ordered_empty_effect",
            )
            expected_theorems = (
                "raw_ordered_insert_empty_transformer_effect",
                "raw_vListInsert_ordered_empty_max_heap_effect",
                "raw_vListInsert_ordered_empty_nonmax_heap_effect",
                "raw_vListInsert_ordered_empty_heap_effect",
            )
            if tuple(definitions) != expected_definitions:
                errors.append(
                    f"{prefix}: definitions must record the ordered-empty transformer"
                )
            if tuple(theorems) != expected_theorems:
                errors.append(
                    f"{prefix}: theorems must record both source branches and their unified effect"
                )
        if layer_id == "Scheduler-P2":
            expected_theorems = (
                "task_delay_abs_2_p2",
                "p2_pre_settled",
                "p2_post_core",
                "p2_post_phase_observations",
                "p2_post_not_settled",
            )
            if tuple(theorems) != expected_theorems:
                errors.append(
                    f"{prefix}: theorems must record the transition and both phase boundaries"
                )
            if any(needle in theory_text for needle in ("vTaskDelay'", "t_hrs_'")):
                errors.append(f"{prefix}: pure witness must not introduce source state")
        if layer_id == "Scheduler-Raw-List-Relabel":
            if tuple(definitions) != SCHEDULER_RELABEL_DEFINITIONS:
                errors.append(
                    f"{prefix}: definitions must record the explicit relabelling layer"
                )
            if tuple(theorems) != SCHEDULER_RELABEL_FACTS:
                errors.append(
                    f"{prefix}: theorems must record the checked relabelling facts"
                )
        if layer_id == "Scheduler-P2-Generated-Layout":
            if definitions or theorems:
                errors.append(
                    f"{prefix}: diagnostic probe must not claim definitions or theorems"
                )
            if tuple(layer.get("diagnostics", ())) != SCHEDULER_LAYOUT_DIAGNOSTICS:
                errors.append(
                    f"{prefix}: diagnostics must record the exact cross-parser boundary"
                )
            if layer.get("distinct_generated_struct_universes") is not True:
                errors.append(
                    f"{prefix}: generated struct universes must remain explicitly distinct"
                )
            if layer.get("common_heap_carrier") != "32 word -> 8 word":
                errors.append(f"{prefix}: common heap carrier is not recorded exactly")
            if layer.get("direct_scheduler_pointer_reuse") is not False:
                errors.append(
                    f"{prefix}: direct scheduler pointer reuse must be exactly false"
                )
            note = layer.get("evidence_note")
            expected_note = {
                "path": "notes/SCHEDULER_GENERATED_LAYOUT_PROBE.md",
                "sha256": "9FCC622B881F1FBAE91E10B0F86CFBEFA42CF8FBB6D644F3C464DC60A866CD49",
            }
            if note != expected_note:
                errors.append(f"{prefix}: evidence_note disagrees with the sealed probe")
            else:
                note_path = project_root / note["path"]
                if not note_path.is_file():
                    errors.append(f"{prefix}: missing evidence note {note['path']}")
                else:
                    actual_note_digest = hashlib.sha256(note_path.read_bytes()).hexdigest().upper()
                    if actual_note_digest != note["sha256"]:
                        errors.append(f"{prefix}: evidence note SHA-256 disagrees with file")
        if layer_id == "Scheduler-List-ABI-Bridge":
            if tuple(definitions) != SCHEDULER_ABI_DEFINITIONS:
                errors.append(
                    f"{prefix}: definitions must record the bounded ABI foundation"
                )
            if tuple(theorems) != SCHEDULER_ABI_FACTS:
                errors.append(f"{prefix}: theorems must record the 36 ABI facts")
            plan = layer.get("design_plan")
            if plan != SCHEDULER_ABI_DESIGN_PLAN:
                errors.append(
                    f"{prefix}: design plan must remain static non-checker evidence"
                )
            else:
                plan_path = project_root / plan["path"]
                if not plan_path.is_file():
                    errors.append(f"{prefix}: missing design plan {plan['path']}")
                else:
                    actual_plan_digest = hashlib.sha256(plan_path.read_bytes()).hexdigest().upper()
                    if actual_plan_digest != plan["sha256"]:
                        errors.append(f"{prefix}: design plan SHA-256 disagrees with file")
            if layer.get("design_plan_fully_implemented") is not False:
                errors.append(
                    f"{prefix}: bounded ABI facts must not claim the full plan is implemented"
                )
        if layer_id == "Scheduler-List-ABI-Write-Bridge":
            if tuple(definitions) != SCHEDULER_ABI_WRITE_DEFINITIONS:
                errors.append(
                    f"{prefix}: definitions must record the wake-key field pointers"
                )
            if tuple(theorems) != SCHEDULER_ABI_WRITE_FACTS:
                errors.append(
                    f"{prefix}: theorems must record the wake-key address and write facts"
                )
            if layer.get("arbitrary_intermediate_heap") is not True:
                errors.append(
                    f"{prefix}: arbitrary_intermediate_heap must be exactly true"
                )
        if layer_id == "Scheduler-P2-Raw-Relation":
            if tuple(definitions) != SCHEDULER_P2_RAW_RELATION_DEFINITIONS:
                errors.append(
                    f"{prefix}: definitions must record the layered scheduler relation"
                )
            if tuple(theorems) != SCHEDULER_P2_RAW_RELATION_FACTS:
                errors.append(
                    f"{prefix}: theorems must record the exact decoders and conditional endpoints"
                )
            if layer.get("records") != ["scheduler_decode", "scheduler_roots"]:
                errors.append(f"{prefix}: records disagree with the relation theory")
            if layer.get("datatypes") != ["scheduler_phase"]:
                errors.append(f"{prefix}: scheduler phase datatype is not recorded")
            if layer.get("functions") != ["scheduler_endpoint_rel"]:
                errors.append(f"{prefix}: endpoint relation function is not recorded")
            if layer.get("conditional_endpoint_only") is not True:
                errors.append(f"{prefix}: conditional_endpoint_only must be exactly true")
            for flag in (
                "concrete_preimage_complete",
                "source_execution_complete",
                "positive_delay_source_refinement_complete",
            ):
                if layer.get(flag) is not False:
                    errors.append(f"{prefix}: {flag} must be exactly false")

        session = layer.get("session")
        if not isinstance(session, str) or f"session {session} " not in root_text:
            errors.append(f"{prefix}: session is absent from theories/ROOT")
        run_id = layer.get("run_id")
        status_name = layer.get("status_file")
        if not isinstance(run_id, str) or not run_id.strip():
            errors.append(f"{prefix}: run_id must be a non-empty string")
            continue
        expected_status = f"runs/{run_id}/status.txt"
        if not isinstance(status_name, str):
            errors.append(f"{prefix}: status_file must be a string")
            continue
        if status_name.replace("\\", "/") != expected_status:
            errors.append(f"{prefix}: status_file path disagrees with run_id")
        status_path = project_root / status_name
        if not status_path.is_file():
            errors.append(f"{prefix}: missing status file {status_name}")
            continue
        status = _parse_status(status_path)
        if status.get("run_id") != run_id:
            errors.append(f"{prefix}: run_id disagrees with status file contents")
        if status.get("session") != session:
            errors.append(f"{prefix}: session disagrees with status file")
        if status.get("exit_code") != "0":
            errors.append(f"{prefix}: evidence exit_code is not zero")
        if status.get("quick_and_dirty") != "false":
            errors.append(f"{prefix}: evidence is not quick_and_dirty=false")
        if status.get("timed_out") != "false":
            errors.append(f"{prefix}: evidence timed out or omits timed_out=false")
        if layer_id in HASHED_RUN_EVIDENCE_IDS:
            _validate_run_artifact_hashes(errors, project_root, prefix, layer)

    duplicates = sorted(
        layer_id for layer_id, count in Counter(layer_ids).items() if count > 1
    )
    for layer_id in duplicates:
        errors.append(f"non_refinement_proof_layers: duplicate id {layer_id!r}")
    missing = sorted(set(NON_REFINEMENT_LAYER_KINDS) - set(layer_ids))
    for layer_id in missing:
        errors.append(f"non_refinement_proof_layers: missing id {layer_id!r}")


def _validate_non_refinement_translation_gates(
    errors: list[str],
    project_root: Path,
    root_text: str,
    gates: Any,
    operations: list[Any],
) -> None:
    """Validate parse/translation gates without promoting them to refinement."""

    if not isinstance(gates, list):
        errors.append("non_refinement_translation_gates must be a list")
        return
    operation_by_id = {
        entry.get("id"): entry
        for entry in operations
        if isinstance(entry, dict) and isinstance(entry.get("id"), str)
    }
    gate_ids: list[str] = []
    for index, gate in enumerate(gates):
        prefix = f"non_refinement_translation_gates[{index}]"
        if not isinstance(gate, dict):
            errors.append(f"{prefix}: gate must be an object")
            continue
        gate_id = gate.get("id")
        schema = None
        if not isinstance(gate_id, str) or not gate_id.strip():
            errors.append(f"{prefix}: id must be a non-empty string")
        else:
            gate_ids.append(gate_id)
            prefix = f"non_refinement_translation_gates[{gate_id}]"
            schema = NON_REFINEMENT_TRANSLATION_GATE_SCHEMAS.get(gate_id)
            if schema is None:
                errors.append(f"{prefix}: id is not recognised by schema 1")
            else:
                for field in ("kind", "translation_route", "covered_operation_ids"):
                    if gate.get(field) != schema[field]:
                        errors.append(
                            f"{prefix}: {field} disagrees with the schema 1 gate"
                        )

        if gate.get("status") != "checker_green":
            errors.append(f"{prefix}: status must be 'checker_green'")
        if gate.get("is_source_to_abstract_refinement") is not False:
            errors.append(
                f"{prefix}: is_source_to_abstract_refinement must be exactly false"
            )
        if gate.get("source_to_abstract_refinement_theorem_count_delta") != 0:
            errors.append(
                f"{prefix}: source_to_abstract_refinement_theorem_count_delta "
                "must be exactly zero"
            )
        claim = gate.get("claim")
        if not isinstance(claim, str) or not claim.strip():
            errors.append(f"{prefix}: claim must be a non-empty string")

        generated = gate.get("generated_definitions")
        artifacts = gate.get("artifacts")
        for label, values in (
            ("generated_definitions", generated),
            ("artifacts", artifacts),
        ):
            if not isinstance(values, list) or not all(
                isinstance(value, str) and value.strip() for value in values
            ):
                errors.append(f"{prefix}: {label} must be a string list")
        if not isinstance(generated, list):
            generated = []
        if not isinstance(artifacts, list):
            artifacts = []
        if not generated and not artifacts:
            errors.append(f"{prefix}: record a generated definition or parse artifact")
        if len(generated) != len(set(generated)):
            errors.append(f"{prefix}: generated definitions are not unique")
        if len(artifacts) != len(set(artifacts)):
            errors.append(f"{prefix}: artifacts are not unique")

        theory_name = gate.get("theory")
        theory_text = ""
        if not isinstance(theory_name, str) or not theory_name:
            errors.append(f"{prefix}: theory must be a non-empty string")
        else:
            theory_path = project_root / theory_name
            if not theory_path.is_file():
                errors.append(f"{prefix}: missing theory {theory_name}")
            else:
                theory_text = theory_path.read_text(encoding="utf-8")
                actual_digest = hashlib.sha256(theory_path.read_bytes()).hexdigest().upper()
                if gate.get("theory_sha256") != actual_digest:
                    errors.append(f"{prefix}: theory_sha256 disagrees with theory")
        for definition in generated:
            if f"print_statement {definition}" not in theory_text:
                errors.append(
                    f"{prefix}: generated definition {definition!r} is not printed"
                )
        for artifact in artifacts:
            if artifact not in theory_text:
                errors.append(f"{prefix}: parse artifact {artifact!r} is absent")
        if gate.get("translation_route") == "skip_heap_abs" and "skip_heap_abs" not in theory_text:
            errors.append(f"{prefix}: theory does not select skip_heap_abs")

        session = gate.get("session")
        if not isinstance(session, str) or f"session {session} " not in root_text:
            errors.append(f"{prefix}: session is absent from theories/ROOT")
        run_id = gate.get("run_id")
        status_name = gate.get("status_file")
        if not isinstance(run_id, str) or not run_id.strip():
            errors.append(f"{prefix}: run_id must be a non-empty string")
            continue
        expected_status = f"runs/{run_id}/status.txt"
        if not isinstance(status_name, str):
            errors.append(f"{prefix}: status_file must be a string")
            continue
        if status_name.replace("\\", "/") != expected_status:
            errors.append(f"{prefix}: status_file path disagrees with run_id")
        status_path = project_root / status_name
        if not status_path.is_file():
            errors.append(f"{prefix}: missing status file {status_name}")
            continue
        status = _parse_status(status_path)
        if status.get("run_id") != run_id:
            errors.append(f"{prefix}: run_id disagrees with status file contents")
        if status.get("session") != session:
            errors.append(f"{prefix}: session disagrees with status file")
        if status.get("exit_code") != "0":
            errors.append(f"{prefix}: evidence exit_code is not zero")
        if status.get("quick_and_dirty") != "false":
            errors.append(f"{prefix}: evidence is not quick_and_dirty=false")
        if status.get("timed_out") != "false":
            errors.append(f"{prefix}: evidence timed out or omits timed_out=false")

        covered_ids = gate.get("covered_operation_ids", [])
        if isinstance(covered_ids, list):
            for operation_id in covered_ids:
                operation = operation_by_id.get(operation_id)
                if operation is None:
                    errors.append(f"{prefix}: unknown covered operation {operation_id!r}")
                    continue
                translated = operation.get("stages", {}).get("translated", {})
                if translated.get("status") != "checker_green":
                    errors.append(f"{prefix}: covered operation is not translation-green")
                if translated.get("generated_definition") not in generated:
                    errors.append(
                        f"{prefix}: covered operation definition is absent from gate"
                    )
                evidence = translated.get("evidence", {})
                if (
                    translated.get("session") != session
                    or not isinstance(evidence, dict)
                    or evidence.get("run_id") != run_id
                    or evidence.get("status_file") != status_name
                ):
                    errors.append(
                        f"{prefix}: covered operation evidence disagrees with gate"
                    )

    duplicates = sorted(
        gate_id for gate_id, count in Counter(gate_ids).items() if count > 1
    )
    for gate_id in duplicates:
        errors.append(f"non_refinement_translation_gates: duplicate id {gate_id!r}")
    missing = sorted(set(NON_REFINEMENT_TRANSLATION_GATE_SCHEMAS) - set(gate_ids))
    for gate_id in missing:
        errors.append(f"non_refinement_translation_gates: missing id {gate_id!r}")


def _validate_source_to_abstract_refinement_rungs(
    errors: list[str],
    project_root: Path,
    root_text: str,
    manifest: dict[str, Any],
) -> tuple[int, set[str]]:
    """Validate genuine but explicitly scoped source-to-model proof rungs."""

    rungs = manifest.get("source_to_abstract_refinement_rungs")
    if not isinstance(rungs, list) or not rungs:
        errors.append(
            "source_to_abstract_refinement_rungs must be a non-empty list"
        )
        return 0, set()

    operations = manifest.get("operations", [])
    operation_by_id = {
        entry.get("id"): entry
        for entry in operations
        if isinstance(entry, dict) and isinstance(entry.get("id"), str)
    }
    proof_layers = manifest.get("non_refinement_proof_layers", [])
    proof_layer_by_id = {
        entry.get("id"): entry
        for entry in proof_layers
        if isinstance(entry, dict) and isinstance(entry.get("id"), str)
    }
    abstract_catalog = manifest.get("abstract_operation_catalog", {})
    if not isinstance(abstract_catalog, dict):
        abstract_catalog = {}
    rung_by_id = {
        entry.get("id"): entry
        for entry in rungs
        if isinstance(entry, dict) and isinstance(entry.get("id"), str)
    }

    rung_ids: list[str] = []
    valid_count = 0
    valid_operation_ids: set[str] = set()
    for index, rung in enumerate(rungs):
        prefix = f"source_to_abstract_refinement_rungs[{index}]"
        if not isinstance(rung, dict):
            errors.append(f"{prefix}: rung must be an object")
            continue
        error_count_before = len(errors)

        rung_id = rung.get("id")
        if not isinstance(rung_id, str) or not rung_id.strip():
            errors.append(f"{prefix}: id must be a non-empty string")
        else:
            rung_ids.append(rung_id)
            prefix = f"source_to_abstract_refinement_rungs[{rung_id}]"
            if rung_id not in REFINEMENT_RUNG_SCOPES:
                errors.append(
                    f"{prefix}: id is not recognised by schema 1"
                )

        if rung.get("status") != "checker_green":
            errors.append(f"{prefix}: status must be 'checker_green'")
        if rung.get("is_source_to_abstract_refinement") is not True:
            errors.append(
                f"{prefix}: is_source_to_abstract_refinement must be exactly true"
            )
        expected_scope = REFINEMENT_RUNG_SCOPES.get(rung_id)
        if expected_scope is not None and rung.get("scope") != expected_scope:
            errors.append(f"{prefix}: scope must be {expected_scope!r}")
        expected_generality = REFINEMENT_RUNG_GENERALITY.get(rung_id)
        if (
            expected_generality is not None
            and rung.get("general_operation_refinement") is not expected_generality
        ):
            errors.append(
                f"{prefix}: general_operation_refinement must be exactly "
                f"{str(expected_generality).lower()}"
            )
        if not isinstance(rung.get("claim"), str) or not rung["claim"].strip():
            errors.append(f"{prefix}: claim must be a non-empty string")
        expected_cost = EXPECTED_DEVELOPMENT_COSTS.get(rung_id)
        if expected_cost is not None and rung.get("development_cost") != expected_cost:
            errors.append(f"{prefix}: development_cost disagrees with recorded runs")

        operation_id = rung.get("operation_id")
        operation = operation_by_id.get(operation_id)
        if operation is None:
            errors.append(f"{prefix}: operation_id does not name a mapped operation")
        else:
            stages = operation.get("stages", {})
            translated = stages.get("translated", {})
            abstract = stages.get("abstract_model", {})
            refined = stages.get("refined", {})

            generated = translated.get("generated_definition")
            expected_source = (
                generated[:-4]
                if isinstance(generated, str) and generated.endswith("_def")
                else None
            )
            if rung.get("source_function") != expected_source:
                errors.append(
                    f"{prefix}: source_function disagrees with translated definition"
                )

            model_operation = rung.get("model_operation")
            if model_operation not in abstract.get("operation_ids", []):
                errors.append(
                    f"{prefix}: model_operation is absent from the operation's abstract stage"
                )
            model_entry = abstract_catalog.get(model_operation)
            if not isinstance(model_entry, dict):
                errors.append(f"{prefix}: model_operation is absent from the catalog")
            else:
                model_theory_name = model_entry.get("theory")
                model_theory = (
                    project_root / model_theory_name
                    if isinstance(model_theory_name, str)
                    else None
                )
                if model_theory is None or not model_theory.is_file():
                    errors.append(f"{prefix}: model operation theory is missing")
                elif not _declares_isabelle_definition(
                    model_theory.read_text(encoding="utf-8"), str(model_operation)
                ):
                    errors.append(
                        f"{prefix}: model operation is not defined in its catalog theory"
                    )

            relation = rung.get("relation")
            if relation not in refined.get("relation_ids", []):
                errors.append(
                    f"{prefix}: relation disagrees with the operation's refined stage"
                )
            theorem = rung.get("theorem")
            if theorem not in refined.get("theorems", []):
                errors.append(
                    f"{prefix}: theorem disagrees with the operation's refined stage"
                )
            if refined.get("status") != "checker_green":
                errors.append(f"{prefix}: mapped operation is not refinement-green")

            stage_view = refined
            refinement_cases = refined.get("refinement_cases")
            if refinement_cases is not None:
                if not isinstance(refinement_cases, list):
                    errors.append(f"{prefix}: refined stage cases must be a list")
                    stage_view = {}
                else:
                    matching_cases = [
                        case
                        for case in refinement_cases
                        if isinstance(case, dict) and case.get("rung_id") == rung_id
                    ]
                    if len(matching_cases) != 1:
                        errors.append(
                            f"{prefix}: refined stage must contain exactly one matching case"
                        )
                        stage_view = {}
                    else:
                        stage_view = matching_cases[0]

            if stage_view.get("scope") != rung.get("scope"):
                errors.append(f"{prefix}: scope disagrees with the refined stage")
            if stage_view.get("general_operation_refinement") is not rung.get(
                "general_operation_refinement"
            ):
                errors.append(
                    f"{prefix}: generality disagrees with the refined stage"
                )
            if stage_view.get("session") != rung.get("session"):
                errors.append(f"{prefix}: session disagrees with the refined stage")
            if stage_view.get("boundary_conditions") != rung.get("boundary_conditions"):
                errors.append(
                    f"{prefix}: boundary_conditions disagree with the refined stage"
                )
            evidence = stage_view.get("evidence", {})
            if not isinstance(evidence, dict) or evidence.get("kind") != "refinement_proof":
                errors.append(f"{prefix}: refined stage lacks refinement_proof evidence")
            elif (
                evidence.get("run_id") != rung.get("run_id")
                or evidence.get("status_file") != rung.get("status_file")
            ):
                errors.append(f"{prefix}: run evidence disagrees with the refined stage")

        source_function = rung.get("source_function")
        model_operation = rung.get("model_operation")
        relation = rung.get("relation")
        theorem = rung.get("theorem")
        prestate_theorem = rung.get("prestate_relation_theorem")
        for label, value in (
            ("source_function", source_function),
            ("model_operation", model_operation),
            ("relation", relation),
            ("theorem", theorem),
        ):
            if not isinstance(value, str) or not value.strip():
                errors.append(f"{prefix}: {label} must be a non-empty string")
        requires_prestate = rung_id in {
            "Raw-R5",
            "Raw-R5-remove",
            "Scheduler-Switch-Suspended",
            "Scheduler-Increment-Tick-Suspended",
            "Scheduler-Delay-Zero",
        }
        if requires_prestate and (
            not isinstance(prestate_theorem, str) or not prestate_theorem.strip()
        ):
            errors.append(
                f"{prefix}: prestate_relation_theorem must be a non-empty string"
            )
        if rung_id == "Scheduler-Tick-Read":
            if prestate_theorem is not None:
                errors.append(
                    f"{prefix}: boundary refinement must not invent a prestate theorem"
                )
            if rung.get("boundary_conditions") != SCHEDULER_TICK_BOUNDARY_CONDITIONS:
                errors.append(
                    f"{prefix}: boundary_conditions must record the exact quiescent tick boundary"
                )
        if rung_id == "Scheduler-Switch-Suspended" and rung.get(
            "boundary_conditions"
        ) != SCHEDULER_SWITCH_SUSPENDED_BOUNDARY_CONDITIONS:
            errors.append(
                f"{prefix}: boundary_conditions must record the exact suspended switch boundary"
            )
        if rung_id == "Scheduler-Increment-Tick-Suspended" and rung.get(
            "boundary_conditions"
        ) != SCHEDULER_INCREMENT_TICK_SUSPENDED_BOUNDARY_CONDITIONS:
            errors.append(
                f"{prefix}: boundary_conditions must record the exact suspended no-wrap increment-tick boundary"
            )
        if rung_id == "Scheduler-Delay-Zero" and rung.get(
            "boundary_conditions"
        ) != SCHEDULER_DELAY_ZERO_BOUNDARY_CONDITIONS:
            errors.append(
                f"{prefix}: boundary_conditions must record the exact zero-delay no-wrap boundary"
            )
        if rung_id == "Scheduler-Delay-Until-Suspended-No-Delay" and rung.get(
            "boundary_conditions"
        ) != SCHEDULER_DELAY_UNTIL_NO_DELAY_BOUNDARY_CONDITIONS:
            errors.append(
                f"{prefix}: boundary_conditions must record the exact suspended no-delay boundary"
            )

        theory_name = rung.get("theory")
        theory_text = ""
        if not isinstance(theory_name, str) or not theory_name:
            errors.append(f"{prefix}: theory must be a non-empty string")
        else:
            theory_path = project_root / theory_name
            if not theory_path.is_file():
                errors.append(f"{prefix}: missing theory {theory_name}")
            else:
                theory_text = theory_path.read_text(encoding="utf-8")
                recorded_digest = rung.get("theory_sha256")
                actual_digest = hashlib.sha256(theory_path.read_bytes()).hexdigest().upper()
                if recorded_digest != actual_digest:
                    errors.append(f"{prefix}: theory_sha256 disagrees with theory")

        relation_theory_text = theory_text
        relation_theory_name = rung.get("relation_theory")
        if relation_theory_name is not None:
            if not isinstance(relation_theory_name, str) or not relation_theory_name:
                errors.append(f"{prefix}: relation_theory must be a non-empty string")
                relation_theory_text = ""
            else:
                relation_theory_path = project_root / relation_theory_name
                if not relation_theory_path.is_file():
                    errors.append(
                        f"{prefix}: missing relation theory {relation_theory_name}"
                    )
                    relation_theory_text = ""
                else:
                    relation_theory_text = relation_theory_path.read_text(
                        encoding="utf-8"
                    )
                    actual_digest = hashlib.sha256(
                        relation_theory_path.read_bytes()
                    ).hexdigest().upper()
                    if rung.get("relation_theory_sha256") != actual_digest:
                        errors.append(
                            f"{prefix}: relation_theory_sha256 disagrees with theory"
                        )

        prestate_theory_text = theory_text
        prestate_theory_name = rung.get("prestate_theory")
        if prestate_theory_name is not None:
            if not isinstance(prestate_theory_name, str) or not prestate_theory_name:
                errors.append(f"{prefix}: prestate_theory must be a non-empty string")
                prestate_theory_text = ""
            else:
                prestate_theory_path = project_root / prestate_theory_name
                if not prestate_theory_path.is_file():
                    errors.append(
                        f"{prefix}: missing prestate theory {prestate_theory_name}"
                    )
                    prestate_theory_text = ""
                else:
                    prestate_theory_text = prestate_theory_path.read_text(
                        encoding="utf-8"
                    )
                    actual_digest = hashlib.sha256(
                        prestate_theory_path.read_bytes()
                    ).hexdigest().upper()
                    if rung.get("prestate_theory_sha256") != actual_digest:
                        errors.append(
                            f"{prefix}: prestate_theory_sha256 disagrees with theory"
                        )

        if isinstance(relation, str) and not _declares_isabelle_definition(
            relation_theory_text, relation
        ):
            errors.append(
                f"{prefix}: relation is not defined in the recorded relation theory"
            )
        theorem_statement = (
            _isabelle_fact_statement(theory_text, theorem)
            if isinstance(theorem, str)
            else None
        )
        if theorem_statement is None:
            errors.append(f"{prefix}: theorem is not declared in the recorded theory")
        else:
            for label, needle in (
                ("source function", source_function),
                ("model operation", model_operation),
                ("relation", relation),
            ):
                if (
                    rung_id == "Raw-R6-initialise-item-insert-remove-sequence"
                    and label == "source function"
                ):
                    continue
                if not isinstance(needle, str) or needle not in theorem_statement:
                    errors.append(f"{prefix}: theorem statement omits {label}")
            result_fragment = REFINEMENT_RUNG_RESULT_FRAGMENTS.get(rung_id)
            if not isinstance(result_fragment, str) or result_fragment not in theorem_statement:
                errors.append(f"{prefix}: theorem statement omits the positive Result")

        if requires_prestate:
            prestate_statement = (
                _isabelle_fact_statement(prestate_theory_text, prestate_theorem)
                if isinstance(prestate_theorem, str)
                else None
            )
            if prestate_statement is None:
                errors.append(
                    f"{prefix}: prestate relation theorem is not declared in the recorded theory"
                )
            elif isinstance(relation, str) and relation not in prestate_statement:
                errors.append(f"{prefix}: prestate theorem omits the relation")

        if rung_id == "Scheduler-Tick-Read":
            boundary_needles = (
                "xTickCount_' c = sa_tick a",
                "eal6_port_critical_depth_' c = 0",
                "eal6_port_interrupts_disabled_' c = 0",
            )
            for needle in boundary_needles:
                if needle not in relation_theory_text:
                    errors.append(f"{prefix}: relation omits boundary fact {needle!r}")
            if theorem_statement is not None and "sa_missed_ticks" in theorem_statement:
                errors.append(f"{prefix}: theorem returns missed ticks instead of committed tick")
        if rung_id in {
            "Scheduler-Switch-Suspended",
            "Scheduler-Increment-Tick-Suspended",
            "Scheduler-Delay-Zero",
            "Scheduler-Delay-Until-Suspended-No-Delay",
        }:
            relation_needles = (
                "xTickCount_' c = sa_tick a",
                "unat (uxSchedulerSuspended_' c) = sa_suspend_depth a",
                "unat (uxMissedTicks_' c) = sa_missed_ticks a",
                "xMissedYield_' c = (if sa_missed_yield a then 1 else 0)",
                "unat (eal6_port_yield_count_' c) = sa_yield_count a",
            )
            for needle in relation_needles:
                if needle not in relation_theory_text:
                    errors.append(f"{prefix}: relation omits control fact {needle!r}")
        if rung_id == "Scheduler-Switch-Suspended":
            if theorem_statement is not None and r"sa_suspend_depth a \<noteq> 0" not in theorem_statement:
                errors.append(f"{prefix}: theorem omits the suspended-branch premise")
            exact_statement = _isabelle_fact_statement(
                theory_text, "vTaskSwitchContext_suspended_result"
            )
            if (
                exact_statement is None
                or "t = xMissedYield_'_update" not in exact_statement
            ):
                errors.append(f"{prefix}: exact source result does not frame one update")
        if rung_id == "Scheduler-Increment-Tick-Suspended":
            if theorem_statement is not None:
                if r"sa_suspend_depth a \<noteq> 0" not in theorem_statement:
                    errors.append(f"{prefix}: theorem omits the suspended-branch premise")
                if "scheduler_missed_tick_no_wrap c" not in theorem_statement:
                    errors.append(f"{prefix}: theorem omits the no-wrap premise")
            exact_statement = _isabelle_fact_statement(
                theory_text, "vTaskIncrementTick_suspended_result"
            )
            if (
                exact_statement is None
                or "t = uxMissedTicks_'_update" not in exact_statement
            ):
                errors.append(f"{prefix}: exact source result does not frame one update")
        if rung_id == "Scheduler-Delay-Zero":
            if theorem_statement is not None:
                if "vTaskDelay' 0" not in theorem_statement:
                    errors.append(f"{prefix}: theorem is not restricted to delay argument zero")
                if "scheduler_yield_count_no_wrap c" not in theorem_statement:
                    errors.append(f"{prefix}: theorem omits the yield-count no-wrap premise")
            exact_statement = _isabelle_fact_statement(
                theory_text, "vTaskDelay_zero_result"
            )
            if (
                exact_statement is None
                or "t = eal6_port_yield_count_'_update" not in exact_statement
            ):
                errors.append(f"{prefix}: exact source result does not frame one update")
        if rung_id == "Scheduler-Delay-Until-Suspended-No-Delay":
            if theorem_statement is not None:
                premise_needles = (
                    "c_guard previous_ptr",
                    "uxSchedulerSuspended_' c = 1",
                    "eal6_port_critical_depth_' c = 0",
                    "eal6_port_interrupts_disabled_' c = 0",
                    r"\<not> should_delay_until",
                    "scheduler_yield_count_no_wrap c",
                )
                for needle in premise_needles:
                    if needle not in theorem_statement:
                        errors.append(f"{prefix}: theorem omits premise {needle!r}")
            exact_theorem = rung.get("exact_source_theorem")
            exact_statement = (
                _isabelle_fact_statement(theory_text, exact_theorem)
                if isinstance(exact_theorem, str)
                else None
            )
            if exact_statement is None:
                errors.append(f"{prefix}: exact source theorem is not declared")
            elif "t = scheduler_delay_until_no_delay_state" not in exact_statement:
                errors.append(f"{prefix}: exact source theorem omits the exact state")

            exact_run_id = rung.get("exact_source_first_green_run_id")
            exact_status_name = rung.get("exact_source_first_green_status_file")
            expected_exact_status = (
                f"runs/{exact_run_id}/status.txt"
                if isinstance(exact_run_id, str)
                else None
            )
            if (
                not isinstance(exact_status_name, str)
                or exact_status_name.replace("\\", "/") != expected_exact_status
            ):
                errors.append(f"{prefix}: exact-source status path disagrees with run")
            else:
                exact_status_path = project_root / exact_status_name
                if not exact_status_path.is_file():
                    errors.append(f"{prefix}: exact-source status file is missing")
                else:
                    exact_status = _parse_status(exact_status_path)
                    if exact_status.get("run_id") != exact_run_id:
                        errors.append(f"{prefix}: exact-source run_id disagrees with status")
                    if exact_status.get("session") != rung.get("session"):
                        errors.append(f"{prefix}: exact-source session disagrees with status")
                    if exact_status.get("exit_code") != "0":
                        errors.append(f"{prefix}: exact-source evidence is not green")
                    if exact_status.get("quick_and_dirty") != "false":
                        errors.append(f"{prefix}: exact-source evidence is quick_and_dirty")
                    if exact_status.get("timed_out") != "false":
                        errors.append(f"{prefix}: exact-source evidence timed out")
        if rung_id == "Raw-R6-remove-general":
            if rung.get("prestate_relation_theorem") is not None:
                errors.append(
                    f"{prefix}: general relation premise must not be replaced by a fixed prestate theorem"
                )
            if rung.get("preconditions") != GENERAL_REMOVE_PRECONDITIONS:
                errors.append(
                    f"{prefix}: preconditions must record exact member removal"
                )
            if tuple(rung.get("supporting_layer_ids", ())) != GENERAL_REMOVE_SUPPORTING_LAYERS:
                errors.append(
                    f"{prefix}: supporting_layer_ids must record the checked effect pipeline"
                )
            effect_theorem = rung.get("effect_theorem")
            effect_statement = (
                _isabelle_fact_statement(theory_text, effect_theorem)
                if isinstance(effect_theorem, str)
                else None
            )
            if effect_statement is None:
                errors.append(f"{prefix}: effect theorem is not declared in the theory")
            elif "raw_remove_effect" not in effect_statement:
                errors.append(f"{prefix}: effect theorem omits raw_remove_effect")
            if (
                theorem_statement is not None
                and r"p \<in> set (ring xs)" not in theorem_statement
            ):
                errors.append(f"{prefix}: theorem omits the member premise")
        if rung_id == "Raw-R6-insert-general":
            if rung.get("prestate_relation_theorem") is not None:
                errors.append(
                    f"{prefix}: general relation premise must not be replaced by a fixed prestate theorem"
                )
            if rung.get("preconditions") != GENERAL_INSERT_PRECONDITIONS:
                errors.append(
                    f"{prefix}: preconditions must record exact fresh insertion and count increment"
                )
            if tuple(rung.get("supporting_layer_ids", ())) != GENERAL_INSERT_SUPPORTING_LAYERS:
                errors.append(
                    f"{prefix}: supporting_layer_ids must record the checked insert pipeline"
                )

            transformer_layer_id = rung.get("exact_heap_transformer_layer_id")
            if transformer_layer_id != "Raw-R6-insert-source-effects":
                errors.append(
                    f"{prefix}: exact heap transformer must point to its supporting layer"
                )
            transformer_layer = proof_layer_by_id.get(transformer_layer_id)
            transformer_theorem = rung.get("exact_heap_transformer_theorem")
            transformer_statement = None
            if not isinstance(transformer_layer, dict):
                errors.append(f"{prefix}: exact heap transformer layer is missing")
            else:
                if transformer_layer.get("is_source_to_abstract_refinement") is not False:
                    errors.append(
                        f"{prefix}: exact heap transformer support must not be counted as refinement"
                    )
                if transformer_theorem not in transformer_layer.get("theorems", []):
                    errors.append(
                        f"{prefix}: exact heap transformer theorem is absent from its supporting layer"
                    )
                transformer_theory_name = transformer_layer.get("theory")
                if isinstance(transformer_theory_name, str):
                    transformer_theory_path = project_root / transformer_theory_name
                    if transformer_theory_path.is_file() and isinstance(
                        transformer_theorem, str
                    ):
                        transformer_statement = _isabelle_fact_statement(
                            transformer_theory_path.read_text(encoding="utf-8"),
                            transformer_theorem,
                        )
            if transformer_statement is None:
                errors.append(f"{prefix}: exact heap transformer theorem is not declared")
            else:
                for needle in (
                    "vListInsertEnd'",
                    "Result ()",
                    "raw_insert_concrete_heap",
                ):
                    if needle not in transformer_statement:
                        errors.append(
                            f"{prefix}: exact heap transformer theorem omits {needle!r}"
                        )

            effect_theorem = rung.get("effect_theorem")
            effect_statement = (
                _isabelle_fact_statement(theory_text, effect_theorem)
                if isinstance(effect_theorem, str)
                else None
            )
            if effect_statement is None:
                errors.append(f"{prefix}: effect theorem is not declared in the theory")
            else:
                for needle in ("raw_insert_concrete_heap", "list_insert_end_abs"):
                    if needle not in effect_statement:
                        errors.append(f"{prefix}: effect theorem omits {needle!r}")
            if theorem_statement is not None:
                for needle in (
                    "raw_fresh_for_insert lp (ring xs) p",
                    "raw_count_can_increment xs",
                ):
                    if needle not in theorem_statement:
                        errors.append(f"{prefix}: theorem omits premise {needle!r}")
        if rung_id == "Raw-R6-ordered-insert-empty":
            if rung.get("prestate_relation_theorem") is not None:
                errors.append(
                    f"{prefix}: empty-branch relation premise must not be replaced by a fixed prestate theorem"
                )
            if rung.get("preconditions") != ORDERED_INSERT_EMPTY_PRECONDITIONS:
                errors.append(
                    f"{prefix}: preconditions must record empty ring, freshness, and maximum-key sentinel"
                )
            if (
                tuple(rung.get("supporting_layer_ids", ()))
                != ORDERED_INSERT_EMPTY_SUPPORTING_LAYERS
            ):
                errors.append(
                    f"{prefix}: supporting_layer_ids must record the ordered-empty source-effect layer"
                )
            else:
                source_layer = proof_layer_by_id.get(
                    ORDERED_INSERT_EMPTY_SUPPORTING_LAYERS[0]
                )
                source_effect = rung.get("source_effect_theorem")
                if not isinstance(source_layer, dict):
                    errors.append(f"{prefix}: ordered-empty source-effect layer is missing")
                else:
                    if source_layer.get("is_source_to_abstract_refinement") is not False:
                        errors.append(
                            f"{prefix}: source-effect support must not be counted as refinement"
                        )
                    if source_effect not in source_layer.get("theorems", []):
                        errors.append(
                            f"{prefix}: source effect theorem is absent from its supporting layer"
                        )
                    source_theory_name = source_layer.get("theory")
                    if isinstance(source_theory_name, str):
                        source_theory_path = project_root / source_theory_name
                        source_statement = (
                            _isabelle_fact_statement(
                                source_theory_path.read_text(encoding="utf-8"),
                                source_effect,
                            )
                            if source_theory_path.is_file()
                            and isinstance(source_effect, str)
                            else None
                        )
                        if source_statement is None:
                            errors.append(
                                f"{prefix}: source effect theorem is not declared"
                            )
                        else:
                            for needle in (
                                "vListInsert'",
                                "Result ()",
                                "raw_ordered_insert_empty_heap",
                            ):
                                if needle not in source_statement:
                                    errors.append(
                                        f"{prefix}: source effect theorem omits {needle!r}"
                                    )

            corollaries = rung.get("corollaries")
            if tuple(corollaries or ()) != ORDERED_INSERT_EMPTY_COROLLARIES:
                errors.append(
                    f"{prefix}: corollaries must record the ordered and maximum-key views"
                )
            else:
                for corollary in corollaries:
                    statement = _isabelle_fact_statement(theory_text, corollary)
                    if statement is None:
                        errors.append(
                            f"{prefix}: corollary {corollary!r} is not declared"
                        )
                ordered_statement = _isabelle_fact_statement(
                    theory_text, ORDERED_INSERT_EMPTY_COROLLARIES[0]
                )
                if ordered_statement is not None and "raw_ordered_xlist_rel" not in ordered_statement:
                    errors.append(f"{prefix}: ordered corollary omits raw_ordered_xlist_rel")
                max_statement = _isabelle_fact_statement(
                    theory_text, ORDERED_INSERT_EMPTY_COROLLARIES[1]
                )
                if max_statement is not None and "max_word" not in max_statement:
                    errors.append(f"{prefix}: maximum-key corollary omits max_word")
            if tuple(refined.get("corollaries", ())) != tuple(corollaries or ()):
                errors.append(f"{prefix}: corollaries disagree with the refined stage")

            if theorem_statement is not None:
                for needle in (
                    "ring xs = []",
                    "raw_fresh_for_insert lp (ring xs) p",
                    "raw_sentinel_max (hrs_mem (t_hrs_' s)) lp",
                ):
                    if needle not in theorem_statement:
                        errors.append(f"{prefix}: theorem omits premise {needle!r}")
            if "vListInsert'_def" in theory_text:
                errors.append(f"{prefix}: refinement theory reopens the generated body")
        if rung_id == "Raw-R6-remove-insert-sequence":
            if rung.get("kind") != "sequential_composition_refinement":
                errors.append(
                    f"{prefix}: kind must be 'sequential_composition_refinement'"
                )
            if rung.get("sequential_composition_refinement") is not True:
                errors.append(
                    f"{prefix}: sequential_composition_refinement must be exactly true"
                )
            if rung.get("distinct_operation_count_delta") != 0:
                errors.append(
                    f"{prefix}: distinct_operation_count_delta must be exactly zero"
                )
            if tuple(rung.get("composed_operation_ids", ())) != (
                REMOVE_INSERT_SEQUENCE_OPERATION_IDS
            ):
                errors.append(
                    f"{prefix}: composed_operation_ids must record remove then insert-end"
                )
            if rung.get("composed_source_function") != "vListInsertEnd'":
                errors.append(
                    f"{prefix}: composed_source_function must be vListInsertEnd'"
                )
            if rung.get("composed_model_operation") != "list_insert_end_abs":
                errors.append(
                    f"{prefix}: composed_model_operation must be list_insert_end_abs"
                )
            if rung.get("preconditions") != GENERAL_REMOVE_PRECONDITIONS:
                errors.append(
                    f"{prefix}: preconditions must record exact member removal"
                )
            if tuple(rung.get("supporting_rung_ids", ())) != (
                REMOVE_INSERT_SEQUENCE_SUPPORTING_RUNGS
            ):
                errors.append(
                    f"{prefix}: supporting_rung_ids must record the two checked general refinements"
                )
            else:
                for supporting_id in REMOVE_INSERT_SEQUENCE_SUPPORTING_RUNGS:
                    supporting = rung_by_id.get(supporting_id)
                    if not isinstance(supporting, dict) or supporting.get(
                        "is_source_to_abstract_refinement"
                    ) is not True:
                        errors.append(
                            f"{prefix}: supporting rung {supporting_id!r} is not a checked refinement"
                        )
            if rung.get("bridge_obligations") != REMOVE_INSERT_SEQUENCE_BRIDGES:
                errors.append(
                    f"{prefix}: bridge_obligations must record freshness, count headroom, and key preservation"
                )
            if tuple(rung.get("intermediate_theorems", ())) != (
                REMOVE_INSERT_SEQUENCE_INTERMEDIATE_THEOREMS
            ):
                errors.append(
                    f"{prefix}: intermediate_theorems must record the checked composition adapters"
                )
            if rung.get("opens_generated_c_body") is not False:
                errors.append(
                    f"{prefix}: opens_generated_c_body must be exactly false"
                )

            insert_operation = operation_by_id.get("LIST-INSERT-END", {})
            insert_translated = insert_operation.get("stages", {}).get(
                "translated", {}
            )
            insert_abstract = insert_operation.get("stages", {}).get(
                "abstract_model", {}
            )
            insert_refined = insert_operation.get("stages", {}).get("refined", {})
            if insert_translated.get("generated_definition") != "vListInsertEnd'_def":
                errors.append(
                    f"{prefix}: composed source operation lacks its checked translation"
                )
            if "list_insert_end_abs" not in insert_abstract.get("operation_ids", []):
                errors.append(
                    f"{prefix}: composed model operation lacks its checked abstract stage"
                )
            if insert_refined.get("status") != "checker_green":
                errors.append(
                    f"{prefix}: composed insert-end operation is not refinement-green"
                )

            for fact_name in (
                *REMOVE_INSERT_SEQUENCE_BRIDGES.values(),
                *REMOVE_INSERT_SEQUENCE_INTERMEDIATE_THEOREMS,
            ):
                if not _declares_isabelle_fact(theory_text, fact_name):
                    errors.append(
                        f"{prefix}: composition fact {fact_name!r} is not declared"
                    )
            if theorem_statement is not None:
                for needle in (
                    "bind (vListRemove' p)",
                    "vListInsertEnd' lp p",
                    r"p \<in> set (ring xs)",
                    "list_remove_abs p xs",
                    "list_insert_end_abs p",
                    "raw_key_at (hrs_mem (t_hrs_' s)) p",
                ):
                    if needle not in theorem_statement:
                        errors.append(
                            f"{prefix}: sequential theorem omits {needle!r}"
                        )
            for generated_body in ("vListRemove'_def", "vListInsertEnd'_def"):
                if generated_body in theory_text:
                    errors.append(
                        f"{prefix}: sequential theory reopens generated body {generated_body!r}"
                    )

        if rung_id == "Raw-R6-initialise-item-insert-remove-sequence":
            if rung.get("kind") != "sequential_composition_refinement":
                errors.append(
                    f"{prefix}: kind must be 'sequential_composition_refinement'"
                )
            if rung.get("sequential_composition_refinement") is not True:
                errors.append(
                    f"{prefix}: sequential_composition_refinement must be exactly true"
                )
            if rung.get("distinct_operation_count_delta") != 0:
                errors.append(
                    f"{prefix}: distinct_operation_count_delta must be exactly zero"
                )
            if tuple(rung.get("composed_operation_ids", ())) != FOUR_CALL_SEQUENCE_OPERATION_IDS:
                errors.append(
                    f"{prefix}: composed_operation_ids must record the literal four-call order"
                )
            if tuple(rung.get("source_functions", ())) != FOUR_CALL_SEQUENCE_SOURCE_FUNCTIONS:
                errors.append(
                    f"{prefix}: source_functions must record the literal four-call order"
                )
            if rung.get("source_sequence_definition") != FOUR_CALL_SEQUENCE_DEFINITION:
                errors.append(f"{prefix}: source_sequence_definition is wrong")
            if tuple(rung.get("supporting_rung_ids", ())) != FOUR_CALL_SEQUENCE_SUPPORTING_RUNGS:
                errors.append(
                    f"{prefix}: supporting_rung_ids must record insert and remove refinements"
                )
            else:
                for supporting_id in FOUR_CALL_SEQUENCE_SUPPORTING_RUNGS:
                    supporting = rung_by_id.get(supporting_id)
                    if not isinstance(supporting, dict) or supporting.get(
                        "is_source_to_abstract_refinement"
                    ) is not True:
                        errors.append(
                            f"{prefix}: supporting rung {supporting_id!r} is not checked"
                        )
            if rung.get("corollary") != FOUR_CALL_SEQUENCE_COROLLARY:
                errors.append(f"{prefix}: empty-roundtrip corollary is wrong")
            elif not _declares_isabelle_fact(theory_text, FOUR_CALL_SEQUENCE_COROLLARY):
                errors.append(f"{prefix}: empty-roundtrip corollary is not declared")
            if rung.get("fixed_addresses") != {
                "list": "0x00001000",
                "item": "0x00002000",
                "sentinel": "0x00001008",
            }:
                errors.append(f"{prefix}: fixed addresses must record 0x1000/0x2000/0x1008")
            if rung.get("opens_generated_c_body") is not False:
                errors.append(f"{prefix}: opens_generated_c_body must be exactly false")

            definition_start = theory_text.find(
                f"definition {FOUR_CALL_SEQUENCE_DEFINITION}"
            )
            theorem_start = theory_text.find(
                "theorem raw_vListInitialise_insert_end_remove_refines",
                max(definition_start, 0),
            )
            if definition_start < 0 or theorem_start < 0:
                errors.append(f"{prefix}: literal source-monad definition is absent")
            else:
                definition_text = theory_text[definition_start:theorem_start]
                positions = [
                    definition_text.find(source_function)
                    for source_function in FOUR_CALL_SEQUENCE_SOURCE_FUNCTIONS
                ]
                if any(position < 0 for position in positions) or positions != sorted(positions):
                    errors.append(f"{prefix}: source calls are not in the literal required order")
                if definition_text.count("bind (") != 3:
                    errors.append(f"{prefix}: literal four-call chain must contain exactly three binds")
            if theorem_statement is not None:
                for needle in (
                    FOUR_CALL_SEQUENCE_DEFINITION,
                    "Result ()",
                    "raw_xlist_rel",
                    "list_insert_end_abs",
                    "list_remove_abs",
                ):
                    if needle not in theorem_statement:
                        errors.append(f"{prefix}: four-call theorem omits {needle!r}")
                if "assumes" in theorem_statement:
                    errors.append(f"{prefix}: literal four-call theorem must have no assumptions")
            for operation_name in FOUR_CALL_SEQUENCE_OPERATION_IDS:
                operation_entry = operation_by_id.get(operation_name, {})
                if operation_entry.get("stages", {}).get("translated", {}).get(
                    "status"
                ) != "checker_green":
                    errors.append(
                        f"{prefix}: source operation {operation_name!r} is not translation-green"
                    )
            for generated_body in (
                "vListInitialise'_def",
                "vListInitialiseItem'_def",
                "vListInsertEnd'_def",
                "vListRemove'_def",
            ):
                if generated_body in theory_text:
                    errors.append(
                        f"{prefix}: four-call theory reopens generated body {generated_body!r}"
                    )

        if rung_id == "Scheduler-P2-Frozen-Preimage":
            if rung.get("boundary_conditions") != SCHEDULER_P2_FROZEN_BOUNDARY_CONDITIONS:
                errors.append(
                    f"{prefix}: boundary_conditions must record the exact frozen P2 delay-2 boundary"
                )
            if rung.get("artifact_binding") != "frozen_artifact_binding":
                errors.append(f"{prefix}: artifact_binding is not the sealed frozen ledger")
            if rung.get("preimage_theorem") != "frozen_p2_preimage_nonempty":
                errors.append(f"{prefix}: preimage theorem is wrong")
            if rung.get("seal_theorem") != "frozen_p2_artifact_bound_seal":
                errors.append(f"{prefix}: seal theorem is wrong")
            if rung.get("supporting_refinement_theorem") != (
                "scheduler_vTaskDelay_2_p2_refines_task_delay_abs"
            ):
                errors.append(f"{prefix}: supporting delay-2 refinement theorem is wrong")
            for fact_name in (
                "frozen_p2_endpoint",
                "frozen_p2_preimage_nonempty",
                "frozen_p2_artifact_bound_vTaskDelay_2_refinement",
                "frozen_p2_artifact_bound_seal",
            ):
                if not _declares_isabelle_fact(theory_text, fact_name):
                    errors.append(f"{prefix}: frozen P2 fact {fact_name!r} is not declared")
            if theorem_statement is not None:
                for needle in (
                    "vTaskDelay' (2 :: 32 word)",
                    "frozen_p2_globals",
                    "Result ()",
                    "scheduler_endpoint_rel YieldPending",
                    "task_delay_abs 2 p2_pre",
                ):
                    if needle not in theorem_statement:
                        errors.append(f"{prefix}: artifact-bound theorem omits {needle!r}")
                if "assumes" in theorem_statement:
                    errors.append(f"{prefix}: artifact-bound theorem must have no assumptions")
            seal_statement = _isabelle_fact_statement(
                theory_text, "frozen_p2_artifact_bound_seal"
            )
            if seal_statement is not None:
                for needle in (
                    r"\<exists>D R c.",
                    "p2_source_footprint",
                    "vTaskDelay' (2 :: 32 word)",
                    "task_delay_abs 2 p2_pre",
                ):
                    if needle not in seal_statement:
                        errors.append(f"{prefix}: seal theorem omits {needle!r}")

        session = rung.get("session")
        if not isinstance(session, str) or f"session {session} " not in root_text:
            errors.append(f"{prefix}: session is absent from theories/ROOT")

        run_id = rung.get("run_id")
        status_name = rung.get("status_file")
        if not isinstance(run_id, str) or not run_id.strip():
            errors.append(f"{prefix}: run_id must be a non-empty string")
        if not isinstance(status_name, str):
            errors.append(f"{prefix}: status_file must be a string")
        elif isinstance(run_id, str):
            expected_status = f"runs/{run_id}/status.txt"
            if status_name.replace("\\", "/") != expected_status:
                errors.append(f"{prefix}: status_file path disagrees with run_id")
            status_path = project_root / status_name
            if not status_path.is_file():
                errors.append(f"{prefix}: missing status file {status_name}")
            else:
                status = _parse_status(status_path)
                if status.get("run_id") != run_id:
                    errors.append(f"{prefix}: run_id disagrees with status file contents")
                if status.get("session") != session:
                    errors.append(f"{prefix}: session disagrees with status file")
                if status.get("exit_code") != "0":
                    errors.append(f"{prefix}: evidence exit_code is not zero")
                if status.get("quick_and_dirty") != "false":
                    errors.append(f"{prefix}: evidence is not quick_and_dirty=false")
                if status.get("timed_out") != "false":
                    errors.append(
                        f"{prefix}: evidence timed out or omits timed_out=false"
                    )
                if rung_id in {
                    "Scheduler-P2-Frozen-Preimage",
                    "Raw-R6-initialise-item-insert-remove-sequence",
                }:
                    _validate_portable_artifact_identity(errors, prefix, status)
                if rung_id in HASHED_RUN_EVIDENCE_IDS:
                    _validate_run_artifact_hashes(errors, project_root, prefix, rung)

        if len(errors) == error_count_before:
            valid_count += 1
            if isinstance(operation_id, str):
                valid_operation_ids.add(operation_id)

    duplicates = sorted(
        rung_id for rung_id, count in Counter(rung_ids).items() if count > 1
    )
    for rung_id in duplicates:
        errors.append(
            f"source_to_abstract_refinement_rungs: duplicate id {rung_id!r}"
        )
    missing = sorted(set(REFINEMENT_RUNG_SCOPES) - set(rung_ids))
    for rung_id in missing:
        errors.append(
            f"source_to_abstract_refinement_rungs: missing id {rung_id!r}"
        )

    rung_ids_by_operation: dict[str, list[str]] = {}
    for rung in rungs:
        if isinstance(rung, dict):
            operation_id = rung.get("operation_id")
            rung_id = rung.get("id")
            if isinstance(operation_id, str) and isinstance(rung_id, str):
                rung_ids_by_operation.setdefault(operation_id, []).append(rung_id)
    for operation_id, expected_case_ids in rung_ids_by_operation.items():
        if len(expected_case_ids) < 2:
            continue
        operation = operation_by_id.get(operation_id, {})
        refined = operation.get("stages", {}).get("refined", {})
        cases = refined.get("refinement_cases")
        prefix = f"operations[{operation_id}].refined"
        if not isinstance(cases, list):
            errors.append(f"{prefix}: multiple rungs require refinement_cases")
            continue
        case_ids = [
            case.get("rung_id") for case in cases if isinstance(case, dict)
        ]
        if len(case_ids) != len(set(case_ids)):
            errors.append(f"{prefix}: refinement case IDs must be unique")
        if set(case_ids) != set(expected_case_ids):
            errors.append(f"{prefix}: refinement cases disagree with mapped rungs")
        top_level_matches = [
            case
            for case in cases
            if isinstance(case, dict)
            and case.get("scope") == refined.get("scope")
            and case.get("general_operation_refinement")
            is refined.get("general_operation_refinement")
            and case.get("session") == refined.get("session")
            and case.get("evidence") == refined.get("evidence")
        ]
        if len(top_level_matches) != 1:
            errors.append(
                f"{prefix}: top-level coverage must select exactly one recorded case"
            )
    return valid_count, valid_operation_ids


def validate_mapping(manifest: dict[str, Any], project_root: Path) -> list[str]:
    """Return all manifest errors without mutating the repository."""

    errors: list[str] = []
    project_root = project_root.resolve()

    if manifest.get("schema") != 1:
        errors.append("schema must be 1")
    claim_boundary = manifest.get("claim_boundary", {})
    if not isinstance(claim_boundary, dict):
        errors.append("claim_boundary must be an object")
        claim_boundary = {}
    if claim_boundary.get("non_refinement_green_layers_are_not_refinement") is not True:
        errors.append(
            "claim_boundary must exclude non-refinement green layers from refinement"
        )
    if claim_boundary.get("positive_delay_source_refinement_complete") is not True:
        errors.append(
            "claim_boundary must record the checked positive-delay source refinement"
        )
    if claim_boundary.get("concrete_p2_preimage_complete") is not True:
        errors.append("claim_boundary must record the checked concrete P2 preimage")

    _validate_frozen_artifact_binding(errors, project_root, manifest)

    semantic_name = manifest.get("semantic_slice_manifest")
    if not isinstance(semantic_name, str):
        return errors + ["semantic_slice_manifest is missing"]
    semantic_path = project_root / semantic_name
    if not semantic_path.is_file():
        return errors + [f"missing semantic slice {semantic_name}"]
    semantic = _read_json(semantic_path)

    source_root_name = manifest.get("source_root")
    if source_root_name != semantic.get("source_root"):
        errors.append("source_root disagrees with semantic slice")
    if not isinstance(source_root_name, str):
        return errors
    source_root = project_root / source_root_name

    active_configuration = manifest.get("active_configuration", {})
    if active_configuration.get("semantic_slice") != semantic.get("configuration"):
        errors.append("active_configuration.semantic_slice must exactly match the freeze")
    additions = active_configuration.get("proof_environment_additions", {})
    if not isinstance(additions, dict):
        errors.append("proof_environment_additions must be an object")
        additions = {}
    for name, entry in additions.items():
        if not isinstance(entry, dict):
            errors.append(f"configuration {name}: entry must be an object")
            continue
        evidence_name = entry.get("evidence_file")
        if not isinstance(evidence_name, str) or not (project_root / evidence_name).is_file():
            errors.append(f"configuration {name}: missing evidence_file")
            continue
        evidence_text = (project_root / evidence_name).read_text(encoding="utf-8")
        directive = re.search(
            rf"^\s*#define\s+{re.escape(name)}\s+([^\s/]+)",
            evidence_text,
            flags=re.MULTILINE,
        )
        if not directive or directive.group(1) != str(entry.get("value")):
            errors.append(f"configuration {name}: value is not witnessed by its header")

    hashes = manifest.get("official_source_hashes", {})
    expected_files = set(semantic.get("files", {}))
    if set(hashes) != expected_files:
        errors.append("official_source_hashes keys must equal semantic-slice files")
    sums_path = project_root / "upstream" / "SHA256SUMS"
    sums = _parse_sha256sums(sums_path) if sums_path.is_file() else {}
    archive_prefix = f"{Path(source_root_name).name}/"
    for relative_name in sorted(expected_files):
        digest = hashes.get(relative_name)
        if not isinstance(digest, str) or not HEX_SHA256.fullmatch(digest):
            errors.append(f"{relative_name}: invalid manifest SHA-256")
            continue
        official_name = archive_prefix + relative_name
        if sums.get(official_name) != digest:
            errors.append(f"{relative_name}: digest disagrees with upstream/SHA256SUMS")
        source_path = source_root / relative_name
        if not source_path.is_file():
            errors.append(f"{relative_name}: source file is missing")
            continue
        actual = hashlib.sha256(source_path.read_bytes()).hexdigest().upper()
        if actual != digest:
            errors.append(f"{relative_name}: source bytes disagree with manifest digest")

    required = manifest.get("required_operation_sets", {})
    expected_sets = {
        "frozen_roots": semantic.get("roots", []),
        "internal_helpers": semantic.get("internal_closure", []),
        "list_operations": list(LIST_OPERATIONS),
    }
    if required != expected_sets:
        errors.append("required_operation_sets disagrees with the frozen target")

    macro_catalog = manifest.get("macro_catalog", {})
    if not isinstance(macro_catalog, dict):
        errors.append("macro_catalog must be an object")
        macro_catalog = {}
    for macro_id, entry in macro_catalog.items():
        if not isinstance(entry, dict):
            errors.append(f"macro {macro_id}: entry must be an object")
            continue
        evidence = entry.get("evidence", {})
        evidence_file = evidence.get("file") if isinstance(evidence, dict) else None
        line_range = evidence.get("line_range") if isinstance(evidence, dict) else None
        if not isinstance(evidence_file, str) or not isinstance(line_range, str):
            errors.append(f"macro {macro_id}: incomplete evidence location")
            continue
        path = project_root / evidence_file
        if not path.is_file():
            errors.append(f"macro {macro_id}: missing evidence file {evidence_file}")
            continue
        try:
            first, last = _range_bounds(line_range)
        except ValueError as exc:
            errors.append(f"macro {macro_id}: {exc}")
            continue
        lines = path.read_text(encoding="latin-1").splitlines()
        if last > len(lines):
            errors.append(f"macro {macro_id}: evidence range exceeds file")
        elif str(entry.get("name")) not in "\n".join(lines[first - 1 : last]):
            errors.append(f"macro {macro_id}: macro name absent from evidence range")

    abstract_catalog = manifest.get("abstract_operation_catalog", {})
    invariant_catalog = manifest.get("invariant_catalog", {})
    if not isinstance(abstract_catalog, dict):
        errors.append("abstract_operation_catalog must be an object")
        abstract_catalog = {}
    if not isinstance(invariant_catalog, dict):
        errors.append("invariant_catalog must be an object")
        invariant_catalog = {}

    operations = manifest.get("operations")
    if not isinstance(operations, list):
        return errors + ["operations must be a list"]
    names = [entry.get("name") for entry in operations if isinstance(entry, dict)]
    expected_names = set().union(*map(set, expected_sets.values()))
    if len(names) != len(set(names)):
        errors.append("operation names are not unique")
    if set(names) != expected_names:
        errors.append("operations do not cover exactly the frozen roots/helpers/list API")

    known_configuration = set(semantic.get("configuration", {})) | set(additions)
    role_by_name = {
        **{name: "frozen_root" for name in expected_sets["frozen_roots"]},
        **{name: "internal_helper" for name in expected_sets["internal_helpers"]},
        **{name: "list_operation" for name in expected_sets["list_operations"]},
    }
    root_file = project_root / "theories" / "ROOT"
    root_text = root_file.read_text(encoding="utf-8") if root_file.is_file() else ""
    _validate_raw_operational_rungs(
        errors, project_root, root_text, manifest.get("raw_operational_rungs")
    )
    _validate_non_refinement_proof_layers(
        errors,
        project_root,
        root_text,
        manifest.get("non_refinement_proof_layers"),
    )
    _validate_non_refinement_translation_gates(
        errors,
        project_root,
        root_text,
        manifest.get("non_refinement_translation_gates"),
        operations,
    )
    summary: dict[str, Counter[str]] = {stage: Counter() for stage in STAGES}

    for operation in operations:
        if not isinstance(operation, dict):
            errors.append("operation entry must be an object")
            continue
        name = operation.get("name")
        if not isinstance(name, str):
            errors.append("operation lacks a name")
            continue
        if operation.get("role") != role_by_name.get(name):
            errors.append(f"{name}: role disagrees with frozen operation set")

        source = operation.get("source", {})
        relative_file = source.get("file") if isinstance(source, dict) else None
        definition_range = source.get("definition_range") if isinstance(source, dict) else None
        if relative_file not in semantic.get("files", {}):
            errors.append(f"{name}: source file is outside semantic slice")
        elif not isinstance(definition_range, str):
            errors.append(f"{name}: definition_range is missing")
        else:
            try:
                first, last = _range_bounds(definition_range)
                allowed = _expand_ranges(semantic["files"][relative_file])
                actual_range = set(range(first, last + 1))
                if not actual_range <= allowed:
                    errors.append(f"{name}: definition_range escapes semantic slice")
                source_lines = (source_root / relative_file).read_text(
                    encoding="latin-1"
                ).splitlines()
                if last > len(source_lines):
                    errors.append(f"{name}: definition_range exceeds source file")
                elif not re.search(
                    rf"\b{re.escape(name)}\b",
                    "\n".join(source_lines[first - 1 : last]),
                ):
                    errors.append(f"{name}: symbol absent from definition_range")
            except (OSError, ValueError) as exc:
                errors.append(f"{name}: invalid source range: {exc}")

        operation_configuration = operation.get("active_configuration", [])
        if not isinstance(operation_configuration, list):
            errors.append(f"{name}: active_configuration must be a list")
        else:
            unknown = set(operation_configuration) - known_configuration
            if unknown:
                errors.append(f"{name}: unknown configuration keys {sorted(unknown)}")
        operation_macros = operation.get("active_macros", [])
        if not isinstance(operation_macros, list):
            errors.append(f"{name}: active_macros must be a list")
        else:
            unknown = set(operation_macros) - set(macro_catalog)
            if unknown:
                errors.append(f"{name}: unknown macro IDs {sorted(unknown)}")

        stages = operation.get("stages", {})
        if set(stages) != set(STAGES):
            errors.append(f"{name}: stages must be exactly {list(STAGES)}")
            continue

        translated = stages["translated"]
        translated_status = translated.get("status")
        summary["translated"][str(translated_status)] += 1
        if translated_status not in {"checker_green", "prepared_unchecked", "not_started"}:
            errors.append(f"{name}.translated: invalid status {translated_status!r}")
        elif translated_status in {"checker_green", "prepared_unchecked"}:
            generated = translated.get("generated_definition")
            needles = [generated] if isinstance(generated, str) else []
            if not needles:
                errors.append(f"{name}.translated: generated_definition is missing")
            _validate_theory_references(
                errors, project_root, root_text, name, "translated", translated, needles
            )
            if translated_status == "checker_green":
                _validate_green_evidence(
                    errors,
                    project_root,
                    name,
                    "translated",
                    translated,
                    "translation_smoke",
                )
            elif translated.get("evidence") is not None:
                errors.append(f"{name}.translated: unchecked preparation cannot cite a run")

        abstract = stages["abstract_model"]
        abstract_status = abstract.get("status")
        summary["abstract_model"][str(abstract_status)] += 1
        operation_ids = abstract.get("operation_ids", [])
        invariant_ids = abstract.get("invariant_ids", [])
        theorems = abstract.get("theorems", [])
        if abstract_status == "checker_green":
            if not operation_ids:
                errors.append(f"{name}.abstract_model: operation_ids are required")
            if set(operation_ids) - set(abstract_catalog):
                errors.append(f"{name}.abstract_model: unknown abstract operation ID")
            if set(invariant_ids) - set(invariant_catalog):
                errors.append(f"{name}.abstract_model: unknown invariant ID")
            _validate_theory_references(
                errors,
                project_root,
                root_text,
                name,
                "abstract_model",
                abstract,
                list(operation_ids) + list(theorems),
            )
            _validate_green_evidence(
                errors,
                project_root,
                name,
                "abstract_model",
                abstract,
                "abstract_model_proof",
            )
            if name == "vTaskDelay" and abstract.get("supporting_layer_ids") != [
                "Scheduler-P2"
            ]:
                errors.append(
                    "vTaskDelay.abstract_model: supporting_layer_ids must record the pure P2 witness"
                )
        elif abstract_status == "not_modelled":
            if operation_ids or invariant_ids or theorems or abstract.get("evidence") is not None:
                errors.append(f"{name}.abstract_model: not_modelled must carry no proof claim")
        else:
            errors.append(f"{name}.abstract_model: invalid status {abstract_status!r}")

        refined = stages["refined"]
        refined_status = refined.get("status")
        summary["refined"][str(refined_status)] += 1
        relation_ids = refined.get("relation_ids", [])
        refinement_theorems = refined.get("theorems", [])
        refinement_evidence = refined.get("evidence")
        if isinstance(refinement_evidence, dict) and refinement_evidence.get("kind") == "translation_smoke":
            errors.append(f"{name}.refined: translation_smoke cannot establish refinement")
        if refined_status == "checker_green":
            if not relation_ids:
                errors.append(f"{name}.refined: relation_ids are required")
            if not refinement_theorems:
                errors.append(f"{name}.refined: refinement theorem is required")
            _validate_theory_references(
                errors,
                project_root,
                root_text,
                name,
                "refined",
                refined,
                list(refinement_theorems),
            )
            _validate_green_evidence(
                errors,
                project_root,
                name,
                "refined",
                refined,
                "refinement_proof",
            )
        elif refined_status == "blocked_by_encoding":
            if relation_ids:
                errors.append(f"{name}.refined: blocked stage cannot claim a relation")
            if not refinement_theorems:
                errors.append(f"{name}.refined: obstruction theorem is required")
            _validate_theory_references(
                errors,
                project_root,
                root_text,
                name,
                "refined",
                refined,
                list(refinement_theorems),
            )
            _validate_green_evidence(
                errors,
                project_root,
                name,
                "refined",
                refined,
                "refinement_obstruction",
            )
        elif refined_status == "not_started":
            if relation_ids or refinement_theorems or refinement_evidence is not None:
                errors.append(f"{name}.refined: not_started must carry no proof claim")
        else:
            errors.append(f"{name}.refined: invalid status {refined_status!r}")

    refinement_rung_count, refinement_operation_ids = (
        _validate_source_to_abstract_refinement_rungs(
            errors, project_root, root_text, manifest
        )
    )
    recorded_summary = manifest.get("status_summary")
    computed_summary = {
        stage: dict(sorted(counts.items())) for stage, counts in summary.items()
    }
    if recorded_summary != computed_summary:
        errors.append("status_summary disagrees with operation stages")
    checker_green_refinements = computed_summary["refined"].get(
        "checker_green", 0
    )
    if checker_green_refinements != len(refinement_operation_ids):
        errors.append(
            "status_summary refinement operation count disagrees with validated refinement rungs"
        )
    boundary_count = claim_boundary.get("source_to_abstract_refinement_theorems")
    if boundary_count != refinement_rung_count:
        errors.append(
            "claim_boundary refinement count disagrees with validated refinement rungs"
        )
    distinct_operation_count = claim_boundary.get(
        "distinct_source_operations_with_refinement"
    )
    if distinct_operation_count != len(refinement_operation_ids):
        errors.append(
            "claim_boundary distinct refined-operation count disagrees with validated refinement rungs"
        )
    sequence_count = sum(
        1
        for rung in manifest.get("source_to_abstract_refinement_rungs", [])
        if isinstance(rung, dict)
        and rung.get("sequential_composition_refinement") is True
    )
    if claim_boundary.get("sequential_composition_refinement_theorems") != sequence_count:
        errors.append(
            "claim_boundary sequential-composition count disagrees with validated refinement rungs"
        )

    return errors


def validate_manifest(manifest_path: Path, project_root: Path | None = None) -> list[str]:
    manifest_path = manifest_path.resolve()
    if project_root is None:
        project_root = manifest_path.parent.parent
    return validate_mapping(_read_json(manifest_path), project_root)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "manifest",
        nargs="?",
        type=Path,
        default=Path("scope/source_itp_mapping.json"),
    )
    args = parser.parse_args()
    errors = validate_manifest(args.manifest)
    report = {
        "manifest": args.manifest.resolve().as_posix(),
        "valid": not errors,
        "errors": errors,
    }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
