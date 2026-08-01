theory XList_Model_Definitions
  imports Main
begin

text \<open>
  A source-derived, allocation-free view of one concrete xList ring.  The
  sentinel is represented by @{term None}; real nodes are the identifiers in
  the ring field.  Keeping the cursor separate is essential: a ready/FIFO view
  starts just after the cursor, whereas an ordered-delay view starts just after
  the sentinel.
\<close>

record ('id, 'key) xlist_abs =
  ring :: "'id list"
  cursor :: "'id option"
  item_key :: "'id \<Rightarrow> 'key"

definition xlist_wf :: "('id, 'key) xlist_abs \<Rightarrow> bool" where
  "xlist_wf xs \<longleftrightarrow>
     distinct (ring xs) \<and>
     (case cursor xs of None \<Rightarrow> True | Some c \<Rightarrow> c \<in> set (ring xs))"

fun insert_after :: "'id \<Rightarrow> 'id \<Rightarrow> 'id list \<Rightarrow> 'id list" where
  "insert_after c x [] = []"
| "insert_after c x (y # ys) =
     (if y = c then y # x # ys else y # insert_after c x ys)"

definition list_insert_end_abs ::
  "'id \<Rightarrow> 'key \<Rightarrow> ('id, 'key) xlist_abs \<Rightarrow> ('id, 'key) xlist_abs"
where
  "list_insert_end_abs x k xs =
     xs\<lparr>ring := (case cursor xs of
                     None \<Rightarrow> x # ring xs
                   | Some c \<Rightarrow> insert_after c x (ring xs)),
         cursor := Some x,
         item_key := (item_key xs)(x := k)\<rparr>"

fun stable_key_insert ::
  "('id \<Rightarrow> 'key::linorder) \<Rightarrow> 'id \<Rightarrow> 'id list \<Rightarrow> 'id list"
where
  "stable_key_insert key x [] = [x]"
| "stable_key_insert key x (y # ys) =
     (if key x < key y
      then x # y # ys
      else y # stable_key_insert key x ys)"

definition list_insert_ordered_abs ::
  "'id \<Rightarrow> 'key::linorder \<Rightarrow>
   ('id, 'key) xlist_abs \<Rightarrow> ('id, 'key) xlist_abs"
where
  "list_insert_ordered_abs x k xs =
     (let updated_key = (item_key xs)(x := k)
      in xs\<lparr>ring := stable_key_insert updated_key x (ring xs),
             item_key := updated_key\<rparr>)"

fun predecessor_aux :: "'id \<Rightarrow> 'id \<Rightarrow> 'id list \<Rightarrow> 'id option" where
  "predecessor_aux previous x [] = None"
| "predecessor_aux previous x (y # ys) =
     (if y = x then Some previous else predecessor_aux y x ys)"

fun predecessor :: "'id \<Rightarrow> 'id list \<Rightarrow> 'id option" where
  "predecessor x [] = None"
| "predecessor x (y # ys) =
     (if y = x then None else predecessor_aux y x ys)"

definition list_remove_abs ::
  "'id \<Rightarrow> ('id, 'key) xlist_abs \<Rightarrow> ('id, 'key) xlist_abs"
where
  "list_remove_abs x xs =
     xs\<lparr>ring := remove1 x (ring xs),
         cursor := (if cursor xs = Some x then predecessor x (ring xs)
                    else cursor xs)\<rparr>"

end
