theory Scheduler_Raw_List_Relabel
  imports
    "EAL6_FreeRTOS_V611_List_Raw_R5_Relation.List_V611_Raw_R5_Relation"
    "EAL6_FreeRTOS_V611_Scheduler_Abstract_Model.Scheduler_Abstract_Model"
begin

text \<open>
  A thin relabelling layer between the pointer identities used by
  raw_xlist_rel and the Generic/Event node identities used by the scheduler
  model.  The decoder is supplied explicitly; no partial choice operator is
  hidden in the relation.
\<close>

type_synonym 'tid raw_node_decoder =
  "raw_node_id \<Rightarrow> 'tid node_kind option"

definition xlist_relabel ::
  "'tid raw_node_decoder \<Rightarrow>
   (raw_node_id, raw_key) xlist_abs \<Rightarrow>
   'tid node_ring \<Rightarrow> bool"
where
  "xlist_relabel D rx q \<longleftrightarrow>
     list_all2 (\<lambda>p n. D p = Some n) (ring rx) (ring q) \<and>
     rel_option (\<lambda>p n. D p = Some n) (cursor rx) (cursor q) \<and>
     (\<forall>p \<in> set (ring rx). \<forall>n.
        D p = Some n \<longrightarrow> item_key rx p = item_key q n)"

definition sched_xlist_rel ::
  "'tid raw_node_decoder \<Rightarrow> heap_mem \<Rightarrow>
   xLIST_C ptr \<Rightarrow> 'tid node_ring \<Rightarrow> bool"
where
  "sched_xlist_rel D h lp q \<longleftrightarrow>
     (\<exists>rx. raw_xlist_rel h lp rx \<and> xlist_relabel D rx q)"

lemma list_all2_decoder_left_closed:
  assumes pairs:
    "list_all2 (\<lambda>p n. D p = Some n) ps ns"
    and live: "p \<in> set ps"
  shows "\<exists>n \<in> set ns. D p = Some n"
  using pairs live
  by (induction rule: list_all2_induct) auto

lemma list_all2_decoder_right_closed:
  assumes pairs:
    "list_all2 (\<lambda>p n. D p = Some n) ps ns"
    and live: "n \<in> set ns"
  shows "\<exists>p \<in> set ps. D p = Some n"
  using pairs live
  by (induction rule: list_all2_induct) auto

lemma xlist_relabel_ring_length:
  assumes "xlist_relabel D rx q"
  shows "length (ring rx) = length (ring q)"
  using assms list_all2_lengthD
  by (auto simp: xlist_relabel_def)

lemma xlist_relabel_decoder_left_closed:
  assumes relabel: "xlist_relabel D rx q"
    and live: "p \<in> set (ring rx)"
  shows "\<exists>n \<in> set (ring q). D p = Some n"
  using relabel live
  by (auto simp: xlist_relabel_def
      dest: list_all2_decoder_left_closed)

lemma xlist_relabel_decoder_right_closed:
  assumes relabel: "xlist_relabel D rx q"
    and live: "n \<in> set (ring q)"
  shows "\<exists>p \<in> set (ring rx). D p = Some n"
  using relabel live
  by (auto simp: xlist_relabel_def
      dest: list_all2_decoder_right_closed)

lemma xlist_relabel_key_agreementD:
  assumes relabel: "xlist_relabel D rx q"
    and live: "p \<in> set (ring rx)"
    and decode: "D p = Some n"
  shows "item_key rx p = item_key q n"
  using assms by (auto simp: xlist_relabel_def)

lemma xlist_relabel_emptyI:
  assumes raw_ring: "ring rx = []"
    and raw_cursor: "cursor rx = None"
    and abs_ring: "ring q = []"
    and abs_cursor: "cursor q = None"
  shows "xlist_relabel D rx q"
  using assms by (simp add: xlist_relabel_def)

lemma xlist_relabel_ready_singletonI:
  assumes raw_ring: "ring rx = [p]"
    and raw_cursor: "cursor rx = Some p"
    and abs_ring: "ring q = [Generic t]"
    and abs_cursor: "cursor q = Some (Generic t)"
    and decode: "D p = Some (Generic t)"
    and key: "item_key rx p = item_key q (Generic t)"
  shows "xlist_relabel D rx q"
  using assms by (auto simp: xlist_relabel_def)

lemma xlist_relabel_ordered_singletonI:
  assumes raw_ring: "ring rx = [p]"
    and raw_cursor: "cursor rx = None"
    and abs_ring: "ring q = [Generic t]"
    and abs_cursor: "cursor q = None"
    and decode: "D p = Some (Generic t)"
    and key: "item_key rx p = item_key q (Generic t)"
  shows "xlist_relabel D rx q"
  using assms by (auto simp: xlist_relabel_def)

lemma sched_xlist_rel_emptyI:
  assumes raw: "raw_xlist_rel h lp rx"
    and raw_ring: "ring rx = []"
    and raw_cursor: "cursor rx = None"
    and abs_ring: "ring q = []"
    and abs_cursor: "cursor q = None"
  shows "sched_xlist_rel D h lp q"
proof -
  have relabel: "xlist_relabel D rx q"
    by (rule xlist_relabel_emptyI; fact)
  show ?thesis using raw relabel by (auto simp: sched_xlist_rel_def)
qed

lemma sched_xlist_rel_ready_singletonI:
  assumes raw: "raw_xlist_rel h lp rx"
    and raw_ring: "ring rx = [p]"
    and raw_cursor: "cursor rx = Some p"
    and abs_ring: "ring q = [Generic t]"
    and abs_cursor: "cursor q = Some (Generic t)"
    and decode: "D p = Some (Generic t)"
    and key: "item_key rx p = item_key q (Generic t)"
  shows "sched_xlist_rel D h lp q"
proof -
  have relabel: "xlist_relabel D rx q"
    by (rule xlist_relabel_ready_singletonI; fact)
  show ?thesis using raw relabel by (auto simp: sched_xlist_rel_def)
qed

lemma sched_xlist_rel_ordered_singletonI:
  assumes raw: "raw_xlist_rel h lp rx"
    and raw_ring: "ring rx = [p]"
    and raw_cursor: "cursor rx = None"
    and abs_ring: "ring q = [Generic t]"
    and abs_cursor: "cursor q = None"
    and decode: "D p = Some (Generic t)"
    and key: "item_key rx p = item_key q (Generic t)"
  shows "sched_xlist_rel D h lp q"
proof -
  have relabel: "xlist_relabel D rx q"
    by (rule xlist_relabel_ordered_singletonI; fact)
  show ?thesis using raw relabel by (auto simp: sched_xlist_rel_def)
qed

end
