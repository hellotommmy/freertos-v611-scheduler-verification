theory XList_Model
  imports XList_Model_Invariants
begin

text \<open>Executable witnesses guard against a vacuous invariant.\<close>

definition example_fifo :: "(nat, nat) xlist_abs" where
  "example_fifo =
     list_insert_end_abs 2 0 (list_insert_end_abs 1 0
       \<lparr>ring = [], cursor = None, item_key = (\<lambda>_. 0)\<rparr>)"

value "ring example_fifo"
value "cursor example_fifo"

lemma example_fifo_nonempty:
  "xlist_wf example_fifo \<and> ring example_fifo = [1, 2] \<and>
   cursor example_fifo = Some 2"
  by (simp add: example_fifo_def xlist_wf_def list_insert_end_abs_def)

definition example_ordered :: "(nat, nat) xlist_abs" where
  "example_ordered =
     list_insert_ordered_abs 3 5
       (list_insert_ordered_abs 2 3
         (list_insert_ordered_abs 1 3
            \<lparr>ring = [], cursor = None, item_key = (\<lambda>_. 0)\<rparr>))"

value "ring example_ordered"
value "map (item_key example_ordered) (ring example_ordered)"

lemma example_equal_keys_are_stable:
  "ring example_ordered = [1, 2, 3] \<and>
   map (item_key example_ordered) (ring example_ordered) = [3, 3, 5]"
  by (simp add: example_ordered_def list_insert_ordered_abs_def Let_def)

end
