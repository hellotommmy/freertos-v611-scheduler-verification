theory List_V611_Raw_R6_Remove_General_Refinement
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Index_Effect.List_V611_Raw_R6_Remove_Index_Effect"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Payload_Effect.List_V611_Raw_R6_Remove_Payload_Effect"
    "EAL6_FreeRTOS_V611_List_Raw_R6_Remove_Topology_Effect.List_V611_Raw_R6_Remove_Topology_Effect"
begin

text \<open>
  General-N removal refinement.  The source body is symbolically executed once
  in the exact heap-effect parent.  This leaf only conjoins four checked
  projections and invokes the pure representation-relation assembler.
\<close>

theorem raw_vListRemove_general_effect:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_remove_effect
         (hrs_mem (t_hrs_' s)) (hrs_mem (t_hrs_' t)) lp xs p
     \<rbrace>"
proof -
  note count = raw_vListRemove_general_count_effect[OF rel member]
  note index = raw_vListRemove_general_index_effect[OF rel member]
  note topology = raw_vListRemove_general_topology_effect[OF rel member]
  note payload = raw_vListRemove_general_payload_effect[OF rel member]
  have grouped:
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       (r = Result () \<and>
        uxNumberOfItems_C (h_val (hrs_mem (t_hrs_' t)) lp) =
          uxNumberOfItems_C (h_val (hrs_mem (t_hrs_' s)) lp) - 1) \<and>
       (r = Result () \<and>
        pxIndex_C (h_val (hrs_mem (t_hrs_' t)) lp) =
          (if pxIndex_C (h_val (hrs_mem (t_hrs_' s)) lp) = p
           then raw_prev_at (hrs_mem (t_hrs_' s)) lp p
           else pxIndex_C (h_val (hrs_mem (t_hrs_' s)) lp))) \<and>
       (r = Result () \<and>
        raw_ring_links (hrs_mem (t_hrs_' t)) lp
          (remove1 p (ring xs))) \<and>
       (r = Result () \<and>
        (\<forall>q \<in> set (remove1 p (ring xs)).
          raw_key_at (hrs_mem (t_hrs_' t)) q =
            raw_key_at (hrs_mem (t_hrs_' s)) q \<and>
          pvContainer_C (h_val (hrs_mem (t_hrs_' t)) q) =
            pvContainer_C (h_val (hrs_mem (t_hrs_' s)) q)))
     \<rbrace>"
    using count index topology payload
    by (simp only: runs_to_conj)
  show ?thesis
    apply (rule runs_to_weaken[OF grouped])
    by (auto simp: raw_remove_effect_def)
qed

theorem raw_vListRemove_general_refines:
  assumes rel:
    "raw_xlist_rel (hrs_mem (t_hrs_' s)) lp xs"
    and member: "p \<in> set (ring xs)"
  shows
    "vListRemove' p \<bullet> s
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       raw_xlist_rel (hrs_mem (t_hrs_' t)) lp (list_remove_abs p xs)
     \<rbrace>"
proof -
  note effect = raw_vListRemove_general_effect[OF rel member]
  show ?thesis
    apply (rule runs_to_weaken[OF effect])
    using raw_remove_effect_refines[OF rel member]
    by auto
qed

end
