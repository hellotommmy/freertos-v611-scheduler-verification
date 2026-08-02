theory Scheduler_Resume_Pending_Drain_Gate_Relation_Decoder
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Drain_Gate_Relation_Base.Scheduler_Resume_Pending_Drain_Gate_Relation_Base"
begin

lemma resume_pending_gate_decoderD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "scheduler_decode_rel D a"
proof -
  have generic:
    "scheduler_family_pre_rel
       (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))
       (rpc_generic_roots C) generic_raw (rpc_live C) D"
    by (rule resume_pending_gate_generic_familyD[OF rel])
  have geometry: "universal_tcb_geometry (rpc_live C) D"
    using generic by (simp add: scheduler_family_pre_rel_def)
  have laws: "universal_decoder_laws (rpc_live C) D"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  have live: "sa_live a = rpc_live C"
    using rel
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  have universal_pair:
    "universal_tcb_geometry (rpc_live C) D \<and>
     universal_decoder_laws (rpc_live C) D"
  proof (rule conjI)
    show "universal_tcb_geometry (rpc_live C) D"
      by (rule geometry)
    show "universal_decoder_laws (rpc_live C) D"
      by (rule laws)
  qed
  have universal: "universal_scheduler_geometry (rpc_live C) D"
    by (rule universal_scheduler_geometry_def[THEN iffD2, OF universal_pair])
  show ?thesis
    by (rule universal_geometry_scheduler_decode_rel[OF universal live])
qed

lemma resume_pending_gate_decoder_lawsD:
  assumes rel:
    "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
  shows "universal_decoder_laws (rpc_live C) D"
  using rel
  unfolding resume_pending_gate_entry_rel_def Let_def
  by blast

lemma resume_pending_gate_generic_event_ptr_distinct:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and generic_live: "u \<in> rpc_live C"
    and event_live: "t \<in> rpc_live C"
  shows
    "resume_pending_generic_raw_ptr D u \<noteq> event_item_raw_ptr D t"
proof
  assume equal:
    "resume_pending_generic_raw_ptr D u = event_item_raw_ptr D t"
  have laws: "universal_decoder_laws (rpc_live C) D"
    by (rule resume_pending_gate_decoder_lawsD[OF rel])
  have generic_decode:
    "sd_node_decode D (resume_pending_generic_raw_ptr D u) =
       Some (Generic u)"
    using universal_node_decode_Generic_iff[
      OF laws, where p="resume_pending_generic_raw_ptr D u" and t=u]
      generic_live
    by (simp add: resume_pending_generic_raw_ptr_def)
  have event_decode:
    "sd_node_decode D (event_item_raw_ptr D t) = Some (Event t)"
    using universal_node_decode_Event_iff[
      OF laws, where p="event_item_raw_ptr D t" and t=t]
      event_live
    by (simp add: event_item_raw_ptr_def)
  show False using generic_decode event_decode equal by simp
qed

lemma resume_pending_gate_event_notin_generic_rootD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and event_live: "t \<in> rpc_live C"
    and root: "g \<in> rpc_generic_roots C"
  shows
    "event_item_raw_ptr D t \<notin> set (ring (generic_raw g))"
proof
  assume member:
    "event_item_raw_ptr D t \<in> set (ring (generic_raw g))"
  have subset:
    "set (ring (generic_raw g)) \<subseteq>
       resume_pending_generic_raw_set (rpc_live C) D"
    using rel root
    unfolding resume_pending_gate_entry_rel_def Let_def
    by blast
  then obtain u where generic_live: "u \<in> rpc_live C"
      and equal:
        "event_item_raw_ptr D t = resume_pending_generic_raw_ptr D u"
    using member
    by (auto simp: resume_pending_generic_raw_set_def)
  have distinct:
    "resume_pending_generic_raw_ptr D u \<noteq> event_item_raw_ptr D t"
    by (rule resume_pending_gate_generic_event_ptr_distinct[
      OF rel generic_live event_live])
  show False using equal distinct by simp
qed

lemma resume_pending_gate_generic_notin_event_rootD:
  assumes rel:
      "resume_pending_gate_entry_rel D R c a C S generic_raw event_raw"
    and generic_live: "t \<in> rpc_live C"
    and root: "e \<in> rpc_event_roots C"
  shows
    "resume_pending_generic_raw_ptr D t \<notin>
       set (ring (event_raw e))"
proof
  assume member:
    "resume_pending_generic_raw_ptr D t \<in> set (ring (event_raw e))"
  have subset:
    "set (ring (event_raw e)) \<subseteq>
       event_item_raw_set (rpc_live C) D"
    by (rule scheduler_event_root_family_raw_nodesD[
      OF resume_pending_gate_event_familyD[OF rel] root])
  then obtain u where event_live: "u \<in> rpc_live C"
      and equal:
        "resume_pending_generic_raw_ptr D t = event_item_raw_ptr D u"
    using member
    by (auto simp: event_item_raw_set_def)
  show False
    using resume_pending_gate_generic_event_ptr_distinct[
      OF rel generic_live event_live] equal
    by simp
qed

end
