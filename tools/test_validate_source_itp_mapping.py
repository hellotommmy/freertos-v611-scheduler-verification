import copy
import json
import unittest
from pathlib import Path
from unittest import mock

import validate_source_itp_mapping


PROJECT_ROOT = Path(__file__).resolve().parent.parent
MANIFEST_PATH = PROJECT_ROOT / "scope" / "source_itp_mapping.json"


def load_manifest() -> dict:
    return json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))


def operation(manifest: dict, name: str) -> dict:
    return next(entry for entry in manifest["operations"] if entry["name"] == name)


def raw_rung(manifest: dict, rung_id: str) -> dict:
    return next(
        entry for entry in manifest["raw_operational_rungs"] if entry["id"] == rung_id
    )


def refinement_rung(manifest: dict, rung_id: str) -> dict:
    return next(
        entry
        for entry in manifest["source_to_abstract_refinement_rungs"]
        if entry["id"] == rung_id
    )


def non_refinement_layer(manifest: dict, layer_id: str) -> dict:
    return next(
        entry
        for entry in manifest["non_refinement_proof_layers"]
        if entry["id"] == layer_id
    )


def translation_gate(manifest: dict, gate_id: str) -> dict:
    return next(
        entry
        for entry in manifest["non_refinement_translation_gates"]
        if entry["id"] == gate_id
    )


class SourceItpMappingTests(unittest.TestCase):
    def test_repository_manifest_is_valid(self) -> None:
        errors = validate_source_itp_mapping.validate_mapping(
            load_manifest(), PROJECT_ROOT
        )
        self.assertEqual(errors, [])

    def test_translation_smoke_is_rejected_as_refinement(self) -> None:
        manifest = load_manifest()
        target = operation(manifest, "vListInitialise")
        smoke = copy.deepcopy(target["stages"]["translated"])
        target["stages"]["refined"] = {
            "status": "checker_green",
            "relation_ids": ["fake_relation"],
            "theorems": ["vListInitialise'_def"],
            "theories": smoke["theories"],
            "session": smoke["session"],
            "evidence": smoke["evidence"],
        }
        manifest["status_summary"]["refined"] = {
            "checker_green": 8,
            "not_started": 4,
        }
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertTrue(
            any("translation_smoke cannot establish refinement" in error for error in errors),
            errors,
        )

    def test_source_range_cannot_escape_frozen_slice(self) -> None:
        manifest = load_manifest()
        operation(manifest, "vTaskSuspendAll")["source"]["definition_range"] = (
            "1090-1103"
        )
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "vTaskSuspendAll: definition_range escapes semantic slice", errors
        )

    def test_hash_tampering_is_detected(self) -> None:
        manifest = load_manifest()
        manifest["official_source_hashes"]["Source/list.c"] = "0" * 64
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertTrue(
            any("Source/list.c" in error and "digest" in error for error in errors),
            errors,
        )

    def test_raw_rung_ids_must_be_unique(self) -> None:
        manifest = load_manifest()
        duplicate = copy.deepcopy(manifest["raw_operational_rungs"][0])
        manifest["raw_operational_rungs"].append(duplicate)
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "raw_operational_rungs: duplicate id 'Raw-R0'", errors
        )

    def test_raw_rung_must_be_green_and_explicitly_not_refinement(self) -> None:
        manifest = load_manifest()
        target = raw_rung(manifest, "Raw-R2")
        target["status"] = "prepared_unchecked"
        target["is_source_to_abstract_refinement"] = True
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "raw_operational_rungs[Raw-R2]: status must be 'checker_green'", errors
        )
        self.assertIn(
            "raw_operational_rungs[Raw-R2]: "
            "is_source_to_abstract_refinement must be exactly false",
            errors,
        )

    def test_raw_rung_status_path_and_run_id_must_agree(self) -> None:
        manifest = load_manifest()
        raw_rung(manifest, "Raw-R1")["run_id"] = "forged-run"
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "raw_operational_rungs[Raw-R1]: status_file path disagrees with run_id",
            errors,
        )
        self.assertIn(
            "raw_operational_rungs[Raw-R1]: "
            "run_id disagrees with status file contents",
            errors,
        )

    def test_raw_rung_status_must_be_successful_and_non_quick(self) -> None:
        manifest = load_manifest()
        target = raw_rung(manifest, "Raw-R2")
        target_path = (PROJECT_ROOT / target["status_file"]).resolve()
        original_parse = validate_source_itp_mapping._parse_status

        def forged_status(path: Path) -> dict[str, str]:
            status = original_parse(path)
            if path.resolve() == target_path:
                status["exit_code"] = "1"
                status["quick_and_dirty"] = "true"
            return status

        with mock.patch.object(
            validate_source_itp_mapping,
            "_parse_status",
            side_effect=forged_status,
        ):
            errors = validate_source_itp_mapping.validate_mapping(
                manifest, PROJECT_ROOT
            )
        self.assertIn(
            "raw_operational_rungs[Raw-R2]: evidence exit_code is not zero", errors
        )
        self.assertIn(
            "raw_operational_rungs[Raw-R2]: "
            "evidence is not quick_and_dirty=false",
            errors,
        )

    def test_raw_rung_theorem_and_session_are_checked(self) -> None:
        manifest = load_manifest()
        target = raw_rung(manifest, "Raw-R0")
        target["theorem"] = "invented_raw_theorem"
        target["session"] = "Invented_Session"
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "raw_operational_rungs[Raw-R0]: session is absent from theories/ROOT",
            errors,
        )
        self.assertIn(
            "raw_operational_rungs[Raw-R0]: theorem 'invented_raw_theorem' "
            "is not declared in the recorded theories",
            errors,
        )

    def test_raw_r3_rungs_are_recorded_as_concrete_evidence_only(self) -> None:
        manifest = load_manifest()
        expected_runs = {
            "Raw-R3a": "20260731Tlist-raw-r3a-01-prefix",
            "Raw-R3b": "20260731Tlist-raw-r3b-19-selector-frames",
            "Raw-R3c": "20260731Tlist-raw-r3c-06-prestate",
            "Raw-R3d": "20260731Tlist-raw-r3d-05-result",
        }
        for rung_id, run_id in expected_runs.items():
            rung = raw_rung(manifest, rung_id)
            self.assertEqual(rung["status"], "checker_green")
            self.assertEqual(rung["run_id"], run_id)
            self.assertIs(rung["is_source_to_abstract_refinement"], False)
            self.assertTrue(rung["theorems"])
        self.assertIn(
            "raw_insert_end_prestate_fields",
            raw_rung(manifest, "Raw-R3c")["theorems"],
        )
        self.assertIn(
            "raw_insert_end_prestate_htd_unchanged",
            raw_rung(manifest, "Raw-R3c")["theorems"],
        )
        self.assertIn(
            "raw_vListInsertEnd_empty_result",
            raw_rung(manifest, "Raw-R3d")["theorems"],
        )
        self.assertIn(
            "raw_sentinel_h_val_after_item_update_direct",
            raw_rung(manifest, "Raw-R3d")["theorems"],
        )
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )
        self.assertEqual(manifest["status_summary"]["refined"]["checker_green"], 8)
        self.assertTrue(
            all(
                rung["is_source_to_abstract_refinement"] is False
                for rung in manifest["raw_operational_rungs"]
            )
        )

    def test_raw_r4_master_is_concrete_fixed_remove_evidence(self) -> None:
        manifest = load_manifest()
        rung = raw_rung(manifest, "Raw-R4-master")
        self.assertEqual(rung["scope"], "fixed_singleton_to_empty")
        self.assertIs(rung["general_operation_refinement"], False)
        self.assertIs(rung["is_source_to_abstract_refinement"], False)
        self.assertEqual(rung["theorem"], "raw_vListRemove_singleton_master")
        self.assertEqual(rung["run_id"], "20260731Tlist-raw-r4-master-01")
        self.assertEqual(
            rung["theory_sha256"],
            "6F7F2107DD62B00D8541DA2E3C449452AD70A5E291DBC31D835B6819EE998E54",
        )

    def test_raw_r4_master_hash_tampering_is_rejected(self) -> None:
        manifest = load_manifest()
        raw_rung(manifest, "Raw-R4-master")["theory_sha256"] = "0" * 64
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "raw_operational_rungs[Raw-R4-master]: "
            "theory_sha256 disagrees with theory",
            errors,
        )

    def test_general_scaffolding_layers_are_green_but_not_refinement(self) -> None:
        manifest = load_manifest()
        expected = {
            "Raw-R5-cycle": (
                "20260731Tlist-raw-r5c-04-nth-append",
                "E4C7B971C69464B29C1ED2EE4B20D0E87B1A329F80E960AAE14A779F442E4F3E",
            ),
            "Raw-R6-generic-prefix": (
                "20260731Tlist-raw-r6gp-01-generic-prefix",
                "281703B2FDEDEC5756C5F01127F4DFE4FB367F9E9F7C72CFD7A56FCDE6A1CD85",
            ),
            "Raw-R6-dynamic-guards": (
                "20260731Tlist-raw-r6dg-06-imageI",
                "82D4F9E75A801E4D433346F85B5B32FE59BDE1992F70A2BE67283CC1A68A1758",
            ),
        }
        for layer_id, (run_id, digest) in expected.items():
            with self.subTest(layer_id=layer_id):
                layer = non_refinement_layer(manifest, layer_id)
                self.assertEqual(layer["status"], "checker_green")
                self.assertEqual(layer["run_id"], run_id)
                self.assertEqual(layer["theory_sha256"], digest)
                self.assertIs(layer["opens_generated_c_body"], False)
                self.assertIs(layer["is_source_to_abstract_refinement"], False)
                self.assertEqual(
                    layer["source_to_abstract_refinement_theorem_count_delta"], 0
                )
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )

    def test_r6_execution_and_relation_layers_do_not_inflate_refinement(self) -> None:
        manifest = load_manifest()
        expected = {
            "Raw-R6-unlink-locality": (
                "20260731Tlist-raw-r6ul-13-general-remove-direct-exact",
                "7EA7C1094272F35FF5D80A58D89D588F180617BF3ED679371CBCEE887A2D3BBF",
                True,
            ),
            "Raw-R6-remove-relation": (
                "20260731Tlist-raw-r6rr-07-count-transfer",
                "4CE9BE41FC318FCF2919BCAC2F72B7CED73833BA3DC37980D92B827A429687CF",
                False,
            ),
            "Raw-R6-insert-relation": (
                "20260731Tlist-raw-r6ir-03-live-cases",
                "9022271DAB3CE824CBE19C5D2DBB1EF2AC4295D6CFACD0BA6F6E6B3D061A204D",
                False,
            ),
            "Raw-R6-unlink-projection": (
                "20260731Tlist-raw-r6up-04-two-write-where",
                "8581095989FC3ED46DE8BA4E9A6FFEB12BE0A016E6076313E40699C8C2A62712",
                False,
            ),
        }
        for layer_id, (run_id, digest, opens_c) in expected.items():
            with self.subTest(layer=layer_id):
                layer = non_refinement_layer(manifest, layer_id)
                self.assertEqual(layer["run_id"], run_id)
                self.assertEqual(layer["theory_sha256"], digest)
                self.assertIs(layer["opens_generated_c_body"], opens_c)
                self.assertIs(layer["is_source_to_abstract_refinement"], False)
                self.assertEqual(
                    layer["source_to_abstract_refinement_theorem_count_delta"], 0
                )
        unlink = non_refinement_layer(manifest, "Raw-R6-unlink-locality")
        self.assertIn("raw_vListRemove_general_result", unlink["theorems"])
        self.assertNotIn("list_remove_abs", unlink["theorems"])
        projection = non_refinement_layer(manifest, "Raw-R6-unlink-projection")
        self.assertIn("raw_unlink_two_writes_ring_links", projection["theorems"])
        self.assertIs(projection["opens_generated_c_body"], False)
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )

    def test_general_remove_effect_pipeline_is_green_but_not_refinement(self) -> None:
        manifest = load_manifest()
        expected = {
            "Raw-R6-remove-metadata": (
                "20260731Tlist-raw-r6rm-18-branch-count",
                "AF30BE7A4A98C4F96D8B564D564B5929C80B926370766D393A06284CC979AEE5",
                False,
                "raw_remove_effect_refines",
            ),
            "Raw-R6-remove-source-effects": (
                "20260731Tlist-raw-r6rse-09-exact-heap-let",
                "E3B1DFB0FE53A6A549CFC74DD84D34B7018DAE3848FA9CCF9ABCB44FEECBEC26",
                True,
                "raw_vListRemove_general_heap_effect",
            ),
            "Raw-R6-remove-index-effect": (
                "20260731Tlist-raw-r6rie-06-taken-index-def",
                "1ABFC8C67E6B97A396C2318A1FDB3A79DAE01736158CBA0555E856AC2B4F70B4",
                False,
                "raw_vListRemove_general_index_effect",
            ),
            "Raw-R6-remove-payload-effect": (
                "20260731Tlist-raw-r6rpe-04-heap-projection",
                "4E299F699558DFB127FB1F14BC6639AF0DAF637786B50718C27F59F437C0F9F2",
                False,
                "raw_vListRemove_general_payload_effect",
            ),
            "Raw-R6-remove-topology-effect": (
                "20260731Tlist-raw-r6rte-06-heap-projection",
                "5B6FDCEAABDC0B042FB2B65462D98F89BD100C9605238793D81A952DD95999B3",
                False,
                "raw_vListRemove_general_topology_effect",
            ),
        }
        for layer_id, (run_id, digest, opens_c, theorem) in expected.items():
            with self.subTest(layer=layer_id):
                layer = non_refinement_layer(manifest, layer_id)
                self.assertEqual(layer["run_id"], run_id)
                self.assertEqual(layer["theory_sha256"], digest)
                self.assertIs(layer["opens_generated_c_body"], opens_c)
                self.assertIn(theorem, layer["theorems"])
                self.assertIs(layer["is_source_to_abstract_refinement"], False)
                self.assertEqual(
                    layer["source_to_abstract_refinement_theorem_count_delta"], 0
                )
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )

    def test_general_insert_exact_heap_transformer_is_support_not_refinement(
        self,
    ) -> None:
        manifest = load_manifest()
        layer = non_refinement_layer(manifest, "Raw-R6-insert-source-effects")
        self.assertEqual(layer["kind"], "raw_source_heap_effect_layer")
        self.assertEqual(layer["scope"], "general_N_insert_exact_heap_effect")
        self.assertEqual(layer["definitions"], ["raw_insert_concrete_heap"])
        self.assertEqual(
            layer["theorems"], ["raw_vListInsertEnd_general_heap_effect"]
        )
        self.assertEqual(layer["run_id"], "20260731Tlist-raw-r6ise-01-first")
        self.assertEqual(
            layer["theory_sha256"],
            "38D21F5E8D283FD8938912C23F3D271A8CEFB7FA3640D4EE7CA61A806149BC0D",
        )
        self.assertIs(layer["opens_generated_c_body"], True)
        self.assertIs(layer["is_source_to_abstract_refinement"], False)
        self.assertEqual(
            layer["source_to_abstract_refinement_theorem_count_delta"], 0
        )
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )

    def test_ordered_empty_source_effect_is_sealed_support_not_refinement(
        self,
    ) -> None:
        manifest = load_manifest()
        layer = non_refinement_layer(
            manifest, "Raw-R6-ordered-insert-empty-source"
        )
        self.assertEqual(layer["kind"], "raw_source_heap_effect_layer")
        self.assertEqual(
            layer["theorems"],
            [
                "raw_ordered_insert_empty_transformer_effect",
                "raw_vListInsert_ordered_empty_max_heap_effect",
                "raw_vListInsert_ordered_empty_nonmax_heap_effect",
                "raw_vListInsert_ordered_empty_heap_effect",
            ],
        )
        self.assertEqual(
            layer["development_cost"],
            {
                "checker_calls": 18,
                "checker_green": 5,
                "elapsed_seconds": 534.339,
                "final_elapsed_seconds": 39.848,
            },
        )
        self.assertEqual(
            layer["theory_sha256"],
            "238178DDF2C973ABF1D2B80B98EAA475D39C89B3DEED16F118480F3A82E681C9",
        )
        self.assertEqual(
            layer["status_sha256"],
            "ADE3AAC35F3DCD7FBEE30E12B64AE67009E9E0F7F307FE97AD7D3C708C4AD7FB",
        )
        self.assertEqual(
            layer["stdout_sha256"],
            "823A32FA6F3CC9A1A39B33724AD5AB77D0001A2B65EF1405453995B901480435",
        )
        self.assertIs(layer["opens_generated_c_body"], True)
        self.assertIs(layer["is_source_to_abstract_refinement"], False)
        self.assertEqual(layer["source_to_abstract_refinement_theorem_count_delta"], 0)

    def test_non_refinement_layer_cannot_claim_refinement(self) -> None:
        manifest = load_manifest()
        layer = non_refinement_layer(manifest, "Raw-R6-dynamic-guards")
        layer["is_source_to_abstract_refinement"] = True
        layer["source_to_abstract_refinement_theorem_count_delta"] = 1
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "non_refinement_proof_layers[Raw-R6-dynamic-guards]: "
            "is_source_to_abstract_refinement must be exactly false",
            errors,
        )
        self.assertIn(
            "non_refinement_proof_layers[Raw-R6-dynamic-guards]: "
            "source_to_abstract_refinement_theorem_count_delta must be exactly zero",
            errors,
        )

    def test_non_refinement_layer_hash_tampering_is_rejected(self) -> None:
        manifest = load_manifest()
        non_refinement_layer(manifest, "Scheduler-ABS")["theory_sha256"] = "0" * 64
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "non_refinement_proof_layers[Scheduler-ABS]: "
            "theory_sha256 disagrees with theory",
            errors,
        )

    def test_new_run_artifact_hash_tampering_is_rejected(self) -> None:
        cases = (
            ("layer", "Raw-R6-ordered-insert-empty-source"),
            ("layer", "Scheduler-P2"),
            ("layer", "Scheduler-Raw-List-Relabel"),
            ("layer", "Scheduler-P2-Generated-Layout"),
            ("layer", "Scheduler-List-ABI-Bridge"),
            ("layer", "Scheduler-List-ABI-Write-Bridge"),
            ("layer", "Scheduler-P2-Raw-Relation"),
            ("rung", "Raw-R6-ordered-insert-empty"),
        )
        for record_kind, record_id in cases:
            for field, message in (
                ("status_sha256", "status_sha256 disagrees with status file"),
                ("stdout_sha256", "stdout_sha256 disagrees with stdout file"),
            ):
                with self.subTest(record=record_id, field=field):
                    manifest = load_manifest()
                    record = (
                        non_refinement_layer(manifest, record_id)
                        if record_kind == "layer"
                        else refinement_rung(manifest, record_id)
                    )
                    record[field] = "0" * 64
                    errors = validate_source_itp_mapping.validate_mapping(
                        manifest, PROJECT_ROOT
                    )
                    self.assertTrue(any(message in error for error in errors), errors)

    def test_scheduler_relabel_is_green_support_not_refinement(self) -> None:
        manifest = load_manifest()
        layer = non_refinement_layer(manifest, "Scheduler-Raw-List-Relabel")
        self.assertEqual(layer["kind"], "pure_scheduler_list_relabel_layer")
        self.assertEqual(layer["fact_count"], 12)
        self.assertEqual(
            layer["development_cost"],
            {
                "checker_calls": 2,
                "checker_green": 1,
                "elapsed_seconds": 57.276,
                "final_elapsed_seconds": 29.046,
            },
        )
        self.assertEqual(
            layer["theory_sha256"],
            "3EED28E0FA3ADC44682E4ABE32569A4D2BDC1FA3392F693E7DA07578A2F129AA",
        )
        self.assertIs(layer["is_source_to_abstract_refinement"], False)
        self.assertEqual(layer["source_to_abstract_refinement_theorem_count_delta"], 0)

    def test_scheduler_layout_probe_records_distinct_struct_universes(self) -> None:
        manifest = load_manifest()
        layer = non_refinement_layer(manifest, "Scheduler-P2-Generated-Layout")
        self.assertEqual(layer["kind"], "generated_layout_diagnostic")
        self.assertEqual(layer["fact_count"], 0)
        self.assertEqual(layer["definitions"], [])
        self.assertEqual(layer["theorems"], [])
        self.assertIs(layer["distinct_generated_struct_universes"], True)
        self.assertEqual(layer["common_heap_carrier"], "32 word -> 8 word")
        self.assertIs(layer["direct_scheduler_pointer_reuse"], False)
        self.assertEqual(
            layer["development_cost"],
            {
                "checker_calls": 4,
                "checker_green": 1,
                "elapsed_seconds": 236.199,
                "final_elapsed_seconds": 58.491,
            },
        )
        self.assertEqual(
            layer["theory_sha256"],
            "604A4BCCE04F39AFC499A3F58BC9DD65F7E31A57CA8AB526467DB645FFA8F843",
        )
        self.assertIs(layer["is_source_to_abstract_refinement"], False)

    def test_scheduler_abi_bridge_has_36_facts_but_plan_stays_static(self) -> None:
        manifest = load_manifest()
        layer = non_refinement_layer(manifest, "Scheduler-List-ABI-Bridge")
        self.assertEqual(layer["kind"], "translation_unit_abi_bridge_layer")
        self.assertEqual(layer["fact_count"], 36)
        self.assertEqual(len(layer["theorems"]), 36)
        self.assertEqual(
            layer["development_cost"],
            {
                "checker_calls": 3,
                "checker_green": 3,
                "elapsed_seconds": 112.143,
                "final_elapsed_seconds": 23.281,
            },
        )
        self.assertEqual(
            layer["theory_sha256"],
            "2F9CB0E2D0CE2D99E40AF25C1CDAB75DD8C7FB68018BFBA8E8CD8671427F5434",
        )
        self.assertEqual(layer["design_plan"]["status"], "design_only_static")
        self.assertEqual(layer["design_plan"]["checker_calls"], 0)
        self.assertIs(layer["design_plan"]["is_checker_evidence"], False)
        self.assertIs(layer["design_plan_fully_implemented"], False)
        self.assertIs(layer["is_source_to_abstract_refinement"], False)
        self.assertEqual(layer["source_to_abstract_refinement_theorem_count_delta"], 0)
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )
        self.assertEqual(
            manifest["claim_boundary"]["distinct_source_operations_with_refinement"],
            8,
        )
        self.assertIs(
            manifest["claim_boundary"]["positive_delay_source_refinement_complete"],
            False,
        )
        self.assertIs(
            manifest["claim_boundary"]["concrete_p2_preimage_complete"],
            False,
        )

    def test_scheduler_abi_plan_cannot_be_promoted_by_metadata(self) -> None:
        manifest = load_manifest()
        layer = non_refinement_layer(manifest, "Scheduler-List-ABI-Bridge")
        layer["design_plan"]["is_checker_evidence"] = True
        layer["design_plan_fully_implemented"] = True
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "non_refinement_proof_layers[Scheduler-List-ABI-Bridge]: "
            "design plan must remain static non-checker evidence",
            errors,
        )
        self.assertIn(
            "non_refinement_proof_layers[Scheduler-List-ABI-Bridge]: "
            "bounded ABI facts must not claim the full plan is implemented",
            errors,
        )

    def test_scheduler_abi_write_key_brick_is_support_only(self) -> None:
        manifest = load_manifest()
        layer = non_refinement_layer(manifest, "Scheduler-List-ABI-Write-Bridge")
        self.assertEqual(layer["kind"], "translation_unit_abi_write_bridge_layer")
        self.assertEqual(layer["fact_count"], 13)
        self.assertEqual(
            layer["development_cost"],
            {
                "checker_calls": 2,
                "checker_green": 2,
                "elapsed_seconds": 42.023,
                "final_elapsed_seconds": 20.882,
            },
        )
        self.assertEqual(
            layer["theory_sha256"],
            "C972FA5B4CAFCC230056DBA267EC6581B144E93C4BDFCED7015CDB0399AED76A",
        )
        self.assertIs(layer["arbitrary_intermediate_heap"], True)
        self.assertIs(layer["opens_generated_c_body"], False)
        self.assertIs(layer["is_source_to_abstract_refinement"], False)
        self.assertEqual(layer["source_to_abstract_refinement_theorem_count_delta"], 0)

    def test_scheduler_p2_raw_relation_is_conditional_support_only(self) -> None:
        manifest = load_manifest()
        layer = non_refinement_layer(manifest, "Scheduler-P2-Raw-Relation")
        self.assertEqual(layer["kind"], "conditional_scheduler_raw_relation_layer")
        self.assertEqual(layer["fact_count"], 11)
        self.assertEqual(
            layer["development_cost"],
            {
                "checker_calls": 8,
                "checker_green": 4,
                "elapsed_seconds": 251.043,
                "final_elapsed_seconds": 28.897,
            },
        )
        self.assertEqual(
            layer["theory_sha256"],
            "9A153B79D0871D4D96A5DF82299EF0D40AC8F918692FE60934A8245E048510ED",
        )
        self.assertIs(layer["conditional_endpoint_only"], True)
        self.assertIs(layer["concrete_preimage_complete"], False)
        self.assertIs(layer["source_execution_complete"], False)
        self.assertIs(layer["positive_delay_source_refinement_complete"], False)
        self.assertIs(layer["opens_generated_c_body"], False)
        self.assertIs(layer["is_source_to_abstract_refinement"], False)
        self.assertEqual(layer["source_to_abstract_refinement_theorem_count_delta"], 0)
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )
        self.assertEqual(
            manifest["claim_boundary"]["distinct_source_operations_with_refinement"],
            8,
        )

    def test_scheduler_pure_model_is_mapped_without_c_refinement(self) -> None:
        manifest = load_manifest()
        expected_operations = {
            "vTaskDelayUntil": "task_delay_until_abs",
            "vTaskDelay": "task_delay_abs",
            "vTaskIncrementTick": "task_increment_tick_abs",
            "vTaskSwitchContext": "task_switch_context_abs",
            "xTaskGetTickCount": "task_get_tick_abs",
        }
        for operation_name, model_operation in expected_operations.items():
            with self.subTest(operation=operation_name):
                stages = operation(manifest, operation_name)["stages"]
                self.assertEqual(stages["abstract_model"]["status"], "checker_green")
                self.assertEqual(
                    stages["abstract_model"]["operation_ids"], [model_operation]
                )
                expected_refined = (
                    "checker_green"
                    if operation_name
                    in {
                        "vTaskDelayUntil",
                        "vTaskDelay",
                        "vTaskIncrementTick",
                        "vTaskSwitchContext",
                        "xTaskGetTickCount",
                    }
                    else "not_started"
                )
                self.assertEqual(stages["refined"]["status"], expected_refined)
        scheduler_layer = non_refinement_layer(manifest, "Scheduler-ABS")
        self.assertEqual(scheduler_layer["kind"], "pure_abstract_model")
        self.assertIs(scheduler_layer["is_source_to_abstract_refinement"], False)
        self.assertEqual(
            manifest["status_summary"]["abstract_model"],
            {"checker_green": 8, "not_modelled": 4},
        )

    def test_scheduler_p2_is_pure_phase_witness_not_source_refinement(self) -> None:
        manifest = load_manifest()
        layer = non_refinement_layer(manifest, "Scheduler-P2")
        self.assertEqual(layer["kind"], "pure_abstract_model_witness")
        self.assertEqual(
            layer["theorems"],
            [
                "task_delay_abs_2_p2",
                "p2_pre_settled",
                "p2_post_core",
                "p2_post_phase_observations",
                "p2_post_not_settled",
            ],
        )
        self.assertEqual(
            layer["development_cost"],
            {
                "checker_calls": 6,
                "checker_green": 2,
                "elapsed_seconds": 115.266,
                "final_elapsed_seconds": 12.597,
            },
        )
        self.assertEqual(
            layer["theory_sha256"],
            "FB03C1FDE6BEC66357F4E7185838423B8867D8999E2CD1422CF2064DC0C48236",
        )
        self.assertIs(layer["opens_generated_c_body"], False)
        self.assertIs(layer["is_source_to_abstract_refinement"], False)
        delay_abstract = operation(manifest, "vTaskDelay")["stages"][
            "abstract_model"
        ]
        self.assertEqual(delay_abstract["supporting_layer_ids"], ["Scheduler-P2"])
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )

    def test_scheduler_p2_support_link_tampering_is_rejected(self) -> None:
        manifest = load_manifest()
        operation(manifest, "vTaskDelay")["stages"]["abstract_model"][
            "supporting_layer_ids"
        ] = []
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "vTaskDelay.abstract_model: supporting_layer_ids must record the pure P2 witness",
            errors,
        )

    def test_scheduler_translation_gates_are_green_but_not_refinement(self) -> None:
        manifest = load_manifest()
        expected = {
            "Scheduler-Parse": (
                "20260801Tpublish-portable-scheduler-parse-01",
                "BA286C0091DF4BEE9D4DCB8013A5E3903DEE054357E6012968C459D1ED51BA68",
            ),
            "Scheduler-Tick-Raw": (
                "20260731Tscheduler-tick-02-raw-heap",
                "7299537CA9D94A6B292F308114250F99AF435F3E891CB62407411AE67071E291",
            ),
            "Scheduler-Delay-Raw": (
                "20260731Tscheduler-delay-01-raw-heap",
                "D34512E4642779C49BF412E7FF05E4FB622EF47E255F152AA1CB765E7EA89A68",
            ),
            "Scheduler-Roots-Raw": (
                "20260731Tscheduler-roots-01-raw-heap",
                "B560345AB2B38ADC871060A33E7A850E8603C8CC5DADFD6D1945A2FD2C3A3E7B",
            ),
        }
        for gate_id, (run_id, digest) in expected.items():
            with self.subTest(gate=gate_id):
                gate = translation_gate(manifest, gate_id)
                self.assertEqual(gate["status"], "checker_green")
                self.assertEqual(gate["run_id"], run_id)
                self.assertEqual(gate["theory_sha256"], digest)
                self.assertIs(gate["is_source_to_abstract_refinement"], False)
                self.assertEqual(
                    gate["source_to_abstract_refinement_theorem_count_delta"], 0
                )
        self.assertEqual(
            manifest["status_summary"]["translated"], {"checker_green": 12}
        )

    def test_scheduler_translation_gate_hash_tampering_is_rejected(self) -> None:
        manifest = load_manifest()
        translation_gate(manifest, "Scheduler-Tick-Raw")["theory_sha256"] = (
            "0" * 64
        )
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "non_refinement_translation_gates[Scheduler-Tick-Raw]: "
            "theory_sha256 disagrees with theory",
            errors,
        )

    def test_scheduler_tick_read_is_the_third_strictly_bounded_refinement(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Scheduler-Tick-Read")
        self.assertEqual(rung["scope"], "quiescent_tick_read_boundary")
        self.assertIs(rung["general_operation_refinement"], False)
        self.assertEqual(rung["operation_id"], "ROOT-GET-TICK")
        self.assertEqual(rung["source_function"], "xTaskGetTickCount'")
        self.assertEqual(rung["model_operation"], "task_get_tick_abs")
        self.assertEqual(rung["relation"], "scheduler_tick_boundary_rel")
        self.assertEqual(rung["theorem"], "xTaskGetTickCount_refines")
        self.assertEqual(
            rung["theory_sha256"],
            "99D46C2193DD213CF6D4645D48A4F93F18B50CA8887BA1ABC74255BF77094BCA",
        )
        self.assertEqual(
            rung["boundary_conditions"],
            {
                "eal6_port_critical_depth_'": 0,
                "eal6_port_interrupts_disabled_'": 0,
                "committed_tick_equality": "xTickCount_' = sa_tick",
                "returned_value": "committed_tick",
                "excluded_value": "sa_missed_ticks",
            },
        )
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )
        self.assertEqual(
            manifest["status_summary"]["refined"],
            {"checker_green": 8, "not_started": 4},
        )

    def test_scheduler_tick_boundary_tampering_is_rejected(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Scheduler-Tick-Read")
        rung["boundary_conditions"]["eal6_port_interrupts_disabled_'"] = 1
        operation(manifest, "xTaskGetTickCount")["stages"]["refined"][
            "boundary_conditions"
        ]["eal6_port_interrupts_disabled_'"] = 1
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "source_to_abstract_refinement_rungs[Scheduler-Tick-Read]: "
            "boundary_conditions must record the exact quiescent tick boundary",
            errors,
        )

    def test_scheduler_suspended_switch_is_the_fourth_bounded_refinement(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Scheduler-Switch-Suspended")
        self.assertEqual(rung["scope"], "suspended_scheduler_control_boundary")
        self.assertIs(rung["general_operation_refinement"], False)
        self.assertEqual(rung["operation_id"], "ROOT-SWITCH-CONTEXT")
        self.assertEqual(rung["source_function"], "vTaskSwitchContext'")
        self.assertEqual(rung["model_operation"], "task_switch_context_abs")
        self.assertEqual(rung["relation"], "scheduler_control_rel")
        self.assertEqual(
            rung["prestate_relation_theorem"],
            "scheduler_control_rel_suspended_witness",
        )
        self.assertEqual(rung["theorem"], "vTaskSwitchContext_suspended_refines")
        self.assertEqual(
            rung["theory_sha256"],
            "E6907500EEE776183F11178EEDDC095E6DE92E14CB7C23A8F382C2B16C685D4A",
        )
        self.assertEqual(
            rung["boundary_conditions"],
            {
                "sa_suspend_depth": "nonzero",
                "uxSchedulerSuspended_'": "nonzero",
                "source_effect": "xMissedYield_' := 1",
                "abstract_effect": "sa_missed_yield := True",
                "ready_list_access": False,
                "proof_port_yield": False,
            },
        )
        switch = operation(manifest, "vTaskSwitchContext")["stages"]["refined"]
        self.assertEqual(switch["status"], "checker_green")
        self.assertEqual(switch["theorems"], ["vTaskSwitchContext_suspended_refines"])
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )

    def test_scheduler_suspended_switch_boundary_tampering_is_rejected(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Scheduler-Switch-Suspended")
        rung["boundary_conditions"]["ready_list_access"] = True
        operation(manifest, "vTaskSwitchContext")["stages"]["refined"][
            "boundary_conditions"
        ]["ready_list_access"] = True
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "source_to_abstract_refinement_rungs[Scheduler-Switch-Suspended]: "
            "boundary_conditions must record the exact suspended switch boundary",
            errors,
        )

    def test_scheduler_suspended_increment_is_the_fifth_bounded_refinement(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Scheduler-Increment-Tick-Suspended")
        self.assertEqual(
            rung["scope"], "suspended_no_wrap_scheduler_control_boundary"
        )
        self.assertIs(rung["general_operation_refinement"], False)
        self.assertEqual(rung["operation_id"], "ROOT-INCREMENT-TICK")
        self.assertEqual(rung["source_function"], "vTaskIncrementTick'")
        self.assertEqual(rung["model_operation"], "task_increment_tick_abs")
        self.assertEqual(rung["relation"], "scheduler_control_rel")
        self.assertEqual(
            rung["prestate_relation_theorem"],
            "scheduler_increment_tick_suspended_pre_witness",
        )
        self.assertEqual(rung["theorem"], "vTaskIncrementTick_suspended_refines")
        self.assertEqual(
            rung["theory_sha256"],
            "06077C3FCD1F17C07694437957C7D4AA5CB94D68C056B3BC80B9E3B73F60F098",
        )
        self.assertEqual(
            rung["boundary_conditions"],
            {
                "sa_suspend_depth": "nonzero",
                "uxSchedulerSuspended_'": "nonzero",
                "scheduler_missed_tick_no_wrap": True,
                "source_effect": "uxMissedTicks_' := uxMissedTicks_' + 1",
                "abstract_effect": "sa_missed_ticks := Suc sa_missed_ticks",
                "committed_tick_changed": False,
                "delayed_list_access": False,
            },
        )
        increment = operation(manifest, "vTaskIncrementTick")["stages"]["refined"]
        self.assertEqual(increment["status"], "checker_green")
        self.assertEqual(
            increment["theorems"], ["vTaskIncrementTick_suspended_refines"]
        )
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )

    def test_scheduler_suspended_increment_boundary_tampering_is_rejected(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Scheduler-Increment-Tick-Suspended")
        rung["boundary_conditions"]["scheduler_missed_tick_no_wrap"] = False
        operation(manifest, "vTaskIncrementTick")["stages"]["refined"][
            "boundary_conditions"
        ]["scheduler_missed_tick_no_wrap"] = False
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "source_to_abstract_refinement_rungs[Scheduler-Increment-Tick-Suspended]: "
            "boundary_conditions must record the exact suspended no-wrap "
            "increment-tick boundary",
            errors,
        )

    def test_scheduler_zero_delay_is_the_sixth_bounded_refinement(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Scheduler-Delay-Zero")
        self.assertEqual(rung["scope"], "zero_delay_no_wrap_scheduler_control_boundary")
        self.assertIs(rung["general_operation_refinement"], False)
        self.assertEqual(rung["operation_id"], "ROOT-DELAY")
        self.assertEqual(rung["source_function"], "vTaskDelay'")
        self.assertEqual(rung["model_operation"], "task_delay_abs")
        self.assertEqual(rung["relation"], "scheduler_control_rel")
        self.assertEqual(
            rung["prestate_relation_theorem"], "scheduler_delay_zero_pre_witness"
        )
        self.assertEqual(rung["theorem"], "vTaskDelay_zero_refines")
        self.assertEqual(
            rung["theory_sha256"],
            "A77DE8F4215AF1EE592858B9232FD8F3EF068D5A2C12C4912C99028FE525D9E4",
        )
        self.assertEqual(
            rung["boundary_conditions"],
            {
                "delay_argument": 0,
                "scheduler_yield_count_no_wrap": True,
                "source_effect": (
                    "eal6_port_yield_count_' := eal6_port_yield_count_' + 1"
                ),
                "abstract_effect": "sa_yield_count := Suc sa_yield_count",
                "scheduler_suspend_protocol": False,
                "current_tcb_access": False,
                "list_access": False,
            },
        )
        delay = operation(manifest, "vTaskDelay")["stages"]["refined"]
        self.assertEqual(delay["status"], "checker_green")
        self.assertEqual(delay["theorems"], ["vTaskDelay_zero_refines"])
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )

    def test_scheduler_zero_delay_boundary_tampering_is_rejected(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Scheduler-Delay-Zero")
        rung["boundary_conditions"]["delay_argument"] = 1
        operation(manifest, "vTaskDelay")["stages"]["refined"][
            "boundary_conditions"
        ]["delay_argument"] = 1
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "source_to_abstract_refinement_rungs[Scheduler-Delay-Zero]: "
            "boundary_conditions must record the exact zero-delay no-wrap boundary",
            errors,
        )

    def test_scheduler_suspended_no_delay_until_is_eighth_bounded_refinement(
        self,
    ) -> None:
        manifest = load_manifest()
        rung = refinement_rung(
            manifest, "Scheduler-Delay-Until-Suspended-No-Delay"
        )
        self.assertEqual(rung["scope"], "suspended_no_delay_scheduler_boundary")
        self.assertIs(rung["general_operation_refinement"], False)
        self.assertEqual(rung["operation_id"], "ROOT-DELAY-UNTIL")
        self.assertEqual(rung["source_function"], "vTaskDelayUntil'")
        self.assertEqual(rung["model_operation"], "task_delay_until_abs")
        self.assertEqual(rung["relation"], "scheduler_control_rel")
        self.assertEqual(
            rung["boundary_conditions"],
            {
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
            },
        )
        self.assertEqual(
            rung["exact_source_theorem"],
            "vTaskDelayUntil_suspended_no_delay_result",
        )
        self.assertEqual(
            rung["exact_source_first_green_run_id"],
            "20260731Tscheduler-delay-until-nodelay-05-all-method",
        )
        self.assertEqual(
            rung["theorem"], "vTaskDelayUntil_suspended_no_delay_refines"
        )
        self.assertEqual(
            rung["run_id"], "20260731Tscheduler-delay-until-nodelay-08-readback"
        )
        self.assertEqual(
            rung["theory_sha256"],
            "44C6CF2B014D9BB9D2F47D4770246457DD0EFCB3850FB2D52B6301FAF19A51EB",
        )
        delay_until = operation(manifest, "vTaskDelayUntil")["stages"]["refined"]
        self.assertEqual(delay_until["status"], "checker_green")
        self.assertEqual(
            delay_until["theorems"],
            ["vTaskDelayUntil_suspended_no_delay_refines"],
        )
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )
        self.assertEqual(
            manifest["status_summary"]["refined"],
            {"checker_green": 8, "not_started": 4},
        )

    def test_scheduler_delay_until_boundary_tampering_is_rejected(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(
            manifest, "Scheduler-Delay-Until-Suspended-No-Delay"
        )
        rung["boundary_conditions"]["list_migration"] = True
        operation(manifest, "vTaskDelayUntil")["stages"]["refined"][
            "boundary_conditions"
        ]["list_migration"] = True
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "source_to_abstract_refinement_rungs"
            "[Scheduler-Delay-Until-Suspended-No-Delay]: "
            "boundary_conditions must record the exact suspended no-delay boundary",
            errors,
        )

    def test_raw_r5_insert_is_separate_and_strictly_scoped_refinement(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Raw-R5")
        self.assertIs(rung["is_source_to_abstract_refinement"], True)
        self.assertEqual(rung["scope"], "fixed_empty_to_singleton")
        self.assertIs(rung["general_operation_refinement"], False)
        self.assertEqual(rung["operation_id"], "LIST-INSERT-END")
        self.assertEqual(rung["source_function"], "vListInsertEnd'")
        self.assertEqual(rung["model_operation"], "list_insert_end_abs")
        self.assertEqual(rung["relation"], "raw_xlist_rel")
        self.assertEqual(rung["theorem"], "raw_vListInsertEnd_empty_refines")
        self.assertEqual(
            rung["prestate_relation_theorem"],
            "raw_insert_end_prestate_rep_empty",
        )

    def test_raw_r5_remove_is_separate_and_strictly_scoped_refinement(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Raw-R5-remove")
        self.assertIs(rung["is_source_to_abstract_refinement"], True)
        self.assertEqual(rung["scope"], "fixed_singleton_to_empty")
        self.assertIs(rung["general_operation_refinement"], False)
        self.assertEqual(rung["operation_id"], "LIST-REMOVE")
        self.assertEqual(rung["source_function"], "vListRemove'")
        self.assertEqual(rung["model_operation"], "list_remove_abs")
        self.assertEqual(rung["relation"], "raw_xlist_rel")
        self.assertEqual(rung["theorem"], "raw_vListRemove_singleton_refines")
        self.assertEqual(
            rung["prestate_relation_theorem"], "raw_singleton_prestate_rep"
        )
        self.assertEqual(
            rung["prestate_theory_sha256"],
            "FE1DF5B644267CD33E6C5E6962144684BDF3EC0A3E3E62DA3701D09AEAF49AF7",
        )
        self.assertEqual(
            rung["relation_theory_sha256"],
            "5CD5EF0B3850FEBD712664EA375ED04E3BDDD2C8B80B9AEA75EBDF006613A199",
        )
        self.assertEqual(
            rung["theory_sha256"],
            "4187C45D7E870E77A3EC009B0D1424597BFF9FEBB84A850D59FF4DB6C6FF653F",
        )

    def test_raw_r6_general_remove_is_the_seventh_general_refinement(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Raw-R6-remove-general")
        self.assertEqual(rung["scope"], "general_N_member_remove")
        self.assertIs(rung["general_operation_refinement"], True)
        self.assertEqual(rung["operation_id"], "LIST-REMOVE")
        self.assertEqual(rung["source_function"], "vListRemove'")
        self.assertEqual(rung["model_operation"], "list_remove_abs")
        self.assertEqual(rung["relation"], "raw_xlist_rel")
        self.assertEqual(
            rung["preconditions"], {"membership": "p is in set (ring xs)"}
        )
        self.assertEqual(rung["effect_theorem"], "raw_vListRemove_general_effect")
        self.assertEqual(rung["theorem"], "raw_vListRemove_general_refines")
        self.assertEqual(
            rung["supporting_layer_ids"],
            [
                "Raw-R6-remove-metadata",
                "Raw-R6-remove-source-effects",
                "Raw-R6-remove-index-effect",
                "Raw-R6-remove-payload-effect",
                "Raw-R6-remove-topology-effect",
            ],
        )
        self.assertEqual(
            rung["theory_sha256"],
            "A08443F3DC4B2CB828D8089AC41BC4F59C004C38E98257A07B9B607E2F039B6A",
        )
        self.assertEqual(rung["run_id"], "20260731Tlist-raw-r6rgr-01-assemble")

        refined = operation(manifest, "vListRemove")["stages"]["refined"]
        self.assertEqual(refined["scope"], "general_N_member_remove")
        self.assertIs(refined["general_operation_refinement"], True)
        self.assertEqual(
            refined["theorems"],
            [
                "raw_vListRemove_singleton_refines",
                "raw_vListRemove_general_refines",
                "raw_vListRemove_insert_end_general_refines",
            ],
        )
        self.assertEqual(
            {case["rung_id"] for case in refined["refinement_cases"]},
            {
                "Raw-R5-remove",
                "Raw-R6-remove-general",
                "Raw-R6-remove-insert-sequence",
            },
        )
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )
        self.assertEqual(
            manifest["status_summary"]["refined"],
            {"checker_green": 8, "not_started": 4},
        )

    def test_raw_r6_general_remove_scope_tampering_is_rejected(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Raw-R6-remove-general")
        rung["preconditions"]["membership"] = "p may be absent"
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "source_to_abstract_refinement_rungs[Raw-R6-remove-general]: "
            "preconditions must record exact member removal",
            errors,
        )

    def test_raw_r6_general_insert_is_the_ninth_general_refinement(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Raw-R6-insert-general")
        self.assertEqual(rung["scope"], "general_N_fresh_insert_end")
        self.assertIs(rung["general_operation_refinement"], True)
        self.assertEqual(rung["operation_id"], "LIST-INSERT-END")
        self.assertEqual(rung["source_function"], "vListInsertEnd'")
        self.assertEqual(rung["model_operation"], "list_insert_end_abs")
        self.assertEqual(rung["relation"], "raw_xlist_rel")
        self.assertEqual(
            rung["preconditions"],
            {
                "freshness": "raw_fresh_for_insert lp (ring xs) p",
                "count_increment": "raw_count_can_increment xs",
            },
        )
        self.assertEqual(
            rung["supporting_layer_ids"],
            ["Raw-R6-insert-relation", "Raw-R6-insert-source-effects"],
        )
        self.assertEqual(
            rung["exact_heap_transformer_theorem"],
            "raw_vListInsertEnd_general_heap_effect",
        )
        self.assertEqual(
            rung["effect_theorem"], "raw_insert_concrete_heap_refines"
        )
        self.assertEqual(
            rung["theorem"],
            "raw_vListInsertEnd_general_refines_via_transformer",
        )
        self.assertEqual(
            rung["theory_sha256"],
            "E83219F8F59CBF18A6BB4050A3E8F380F586BD5B237AD0EE2857D7635846959C",
        )
        self.assertEqual(
            rung["session"],
            "EAL6_FreeRTOS_V611_List_Raw_R6_Insert_Post_Transformer",
        )
        self.assertEqual(
            rung["run_id"], "20260731Tlist-raw-r6ipt-04-where-spacing"
        )

        refined = operation(manifest, "vListInsertEnd")["stages"]["refined"]
        self.assertEqual(refined["scope"], "general_N_fresh_insert_end")
        self.assertIs(refined["general_operation_refinement"], True)
        self.assertEqual(
            refined["theorems"],
            [
                "raw_vListInsertEnd_empty_refines",
                "raw_vListInsertEnd_general_refines_via_transformer",
            ],
        )
        self.assertEqual(
            {case["rung_id"] for case in refined["refinement_cases"]},
            {"Raw-R5", "Raw-R6-insert-general"},
        )
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )
        self.assertEqual(
            manifest["status_summary"]["refined"],
            {"checker_green": 8, "not_started": 4},
        )

    def test_raw_r6_general_insert_transformer_support_tampering_is_rejected(
        self,
    ) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Raw-R6-insert-general")
        rung["exact_heap_transformer_layer_id"] = "Raw-R6-insert-relation"
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "source_to_abstract_refinement_rungs[Raw-R6-insert-general]: "
            "exact heap transformer must point to its supporting layer",
            errors,
        )

    def test_ordered_empty_is_eleventh_restricted_refinement(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Raw-R6-ordered-insert-empty")
        self.assertEqual(rung["scope"], "restricted_empty_list_ordered_insert")
        self.assertIs(rung["general_operation_refinement"], False)
        self.assertEqual(rung["operation_id"], "LIST-INSERT-ORDERED")
        self.assertEqual(rung["source_function"], "vListInsert'")
        self.assertEqual(rung["model_operation"], "list_insert_ordered_abs")
        self.assertEqual(rung["relation"], "raw_xlist_rel")
        self.assertEqual(
            rung["preconditions"],
            {
                "empty_ring": "ring xs = []",
                "freshness": "raw_fresh_for_insert lp (ring xs) p",
                "sentinel_key": "raw_sentinel_max (hrs_mem (t_hrs_' s)) lp",
            },
        )
        self.assertEqual(
            rung["supporting_layer_ids"],
            ["Raw-R6-ordered-insert-empty-source"],
        )
        self.assertEqual(rung["theorem"], "raw_vListInsert_ordered_empty_refines")
        self.assertEqual(
            rung["corollaries"],
            [
                "raw_vListInsert_ordered_empty_refines_ordered",
                "raw_vListInsert_ordered_empty_max_refines",
            ],
        )
        self.assertEqual(
            rung["development_cost"],
            {
                "checker_calls": 3,
                "checker_green": 1,
                "elapsed_seconds": 167.993,
                "final_elapsed_seconds": 89.835,
            },
        )
        self.assertEqual(
            rung["theory_sha256"],
            "8319D39955FACD488B1409C1CFABBC021E8332A3A3F52645C4A88BDE50413806",
        )
        self.assertEqual(
            rung["status_sha256"],
            "69B11F9B55CF4518EC6B570D5F085C81AC7629E0CABB6118E935A9B3EBCBC265",
        )
        self.assertEqual(
            rung["stdout_sha256"],
            "91801D97F2C08C506E3BC75753C3AADE4846B5902DEB05D2DD77BCC497F8F0CB",
        )
        refined = operation(manifest, "vListInsert")["stages"]["refined"]
        self.assertEqual(refined["status"], "checker_green")
        self.assertEqual(refined["theorems"], [rung["theorem"]])
        self.assertEqual(refined["corollaries"], rung["corollaries"])
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )
        self.assertEqual(
            manifest["claim_boundary"]["distinct_source_operations_with_refinement"],
            8,
        )
        self.assertEqual(
            manifest["status_summary"]["refined"],
            {"checker_green": 8, "not_started": 4},
        )

    def test_ordered_empty_scope_tampering_is_rejected(self) -> None:
        manifest = load_manifest()
        refinement_rung(manifest, "Raw-R6-ordered-insert-empty")["preconditions"][
            "empty_ring"
        ] = "ring xs may be nonempty"
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "source_to_abstract_refinement_rungs[Raw-R6-ordered-insert-empty]: "
            "preconditions must record empty ring, freshness, and maximum-key sentinel",
            errors,
        )

    def test_raw_r6_remove_insert_sequence_is_the_tenth_refinement(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Raw-R6-remove-insert-sequence")
        self.assertEqual(rung["kind"], "sequential_composition_refinement")
        self.assertEqual(rung["scope"], "general_N_member_remove_then_insert_end")
        self.assertIs(rung["general_operation_refinement"], True)
        self.assertIs(rung["sequential_composition_refinement"], True)
        self.assertEqual(rung["distinct_operation_count_delta"], 0)
        self.assertEqual(
            rung["composed_operation_ids"], ["LIST-REMOVE", "LIST-INSERT-END"]
        )
        self.assertEqual(rung["source_function"], "vListRemove'")
        self.assertEqual(rung["composed_source_function"], "vListInsertEnd'")
        self.assertEqual(rung["model_operation"], "list_remove_abs")
        self.assertEqual(rung["composed_model_operation"], "list_insert_end_abs")
        self.assertEqual(rung["relation"], "raw_xlist_rel")
        self.assertEqual(
            rung["supporting_rung_ids"],
            ["Raw-R6-remove-general", "Raw-R6-insert-general"],
        )
        self.assertEqual(
            rung["bridge_obligations"],
            {
                "freshness": "raw_remove_post_fresh_for_insert",
                "count_headroom": "raw_remove_post_count_can_increment",
                "key_preservation": "raw_remove_concrete_heap_preserves_item_key",
            },
        )
        self.assertEqual(
            rung["theorem"], "raw_vListRemove_insert_end_general_refines"
        )
        self.assertEqual(
            rung["theory_sha256"],
            "E12FDC4BA9A08F62C2C8F0C8493657CECE41FEE88D8B14F11360738E65B85A9D",
        )
        self.assertEqual(
            rung["session"],
            "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Insert_Sequence",
        )
        self.assertEqual(
            rung["run_id"], "20260731Tlist-raw-r6ris-07-bind-weaken"
        )
        self.assertIs(rung["opens_generated_c_body"], False)
        self.assertEqual(
            manifest["claim_boundary"]["source_to_abstract_refinement_theorems"],
            11,
        )
        self.assertEqual(
            manifest["claim_boundary"]["distinct_source_operations_with_refinement"],
            8,
        )
        self.assertEqual(
            manifest["claim_boundary"]["sequential_composition_refinement_theorems"],
            1,
        )

    def test_remove_insert_sequence_bridge_tampering_is_rejected(self) -> None:
        manifest = load_manifest()
        rung = refinement_rung(manifest, "Raw-R6-remove-insert-sequence")
        rung["bridge_obligations"]["key_preservation"] = "invented_key_bridge"
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "source_to_abstract_refinement_rungs[Raw-R6-remove-insert-sequence]: "
            "bridge_obligations must record freshness, count headroom, and key preservation",
            errors,
        )

    def test_remove_insert_sequence_cannot_inflate_distinct_operation_count(
        self,
    ) -> None:
        manifest = load_manifest()
        refinement_rung(manifest, "Raw-R6-remove-insert-sequence")[
            "distinct_operation_count_delta"
        ] = 1
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "source_to_abstract_refinement_rungs[Raw-R6-remove-insert-sequence]: "
            "distinct_operation_count_delta must be exactly zero",
            errors,
        )

    def test_refinement_rung_must_be_explicitly_true(self) -> None:
        manifest = load_manifest()
        refinement_rung(manifest, "Raw-R5")[
            "is_source_to_abstract_refinement"
        ] = False
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "source_to_abstract_refinement_rungs[Raw-R5]: "
            "is_source_to_abstract_refinement must be exactly true",
            errors,
        )

    def test_refinement_rung_id_is_not_free_text(self) -> None:
        manifest = load_manifest()
        refinement_rung(manifest, "Raw-R5")["id"] = "invented-rung"
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "source_to_abstract_refinement_rungs[invented-rung]: "
            "id is not recognised by schema 1",
            errors,
        )

    def test_remove_refinement_theory_hash_tampering_is_rejected(self) -> None:
        cases = (
            ("relation_theory_sha256", "relation_theory_sha256"),
            ("prestate_theory_sha256", "prestate_theory_sha256"),
            ("theory_sha256", "theory_sha256"),
        )
        for field, error_label in cases:
            with self.subTest(field=field):
                manifest = load_manifest()
                refinement_rung(manifest, "Raw-R5-remove")[field] = "0" * 64
                errors = validate_source_itp_mapping.validate_mapping(
                    manifest, PROJECT_ROOT
                )
                self.assertIn(
                    "source_to_abstract_refinement_rungs[Raw-R5-remove]: "
                    f"{error_label} disagrees with theory",
                    errors,
                )

    def test_refinement_rung_forged_theorem_is_rejected(self) -> None:
        manifest = load_manifest()
        refinement_rung(manifest, "Raw-R5")["theorem"] = "invented_refinement"
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "source_to_abstract_refinement_rungs[Raw-R5]: "
            "theorem is not declared in the recorded theory",
            errors,
        )

    def test_refinement_rung_forged_run_is_rejected(self) -> None:
        manifest = load_manifest()
        refinement_rung(manifest, "Raw-R5")["run_id"] = "forged-run"
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "source_to_abstract_refinement_rungs[Raw-R5]: "
            "status_file path disagrees with run_id",
            errors,
        )

    def test_refinement_count_forgery_is_rejected(self) -> None:
        manifest = load_manifest()
        manifest["claim_boundary"]["source_to_abstract_refinement_theorems"] = 12
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn(
            "claim_boundary refinement count disagrees with validated refinement rungs",
            errors,
        )

    def test_raw_green_rungs_are_not_added_to_refined_count(self) -> None:
        manifest = load_manifest()
        manifest["status_summary"]["refined"]["checker_green"] = len(
            manifest["raw_operational_rungs"]
        )
        errors = validate_source_itp_mapping.validate_mapping(manifest, PROJECT_ROOT)
        self.assertIn("status_summary disagrees with operation stages", errors)


if __name__ == "__main__":
    unittest.main()
