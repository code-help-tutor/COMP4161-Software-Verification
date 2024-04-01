theory a2
  imports Main a2_fmap
begin

(* don't forget to work on Q1 questions in a2_fmap.thy! *)



(* Q2: Garbage collector specification *)

type_synonym 'data block = "nat list \<times> 'data"

type_synonym 'data heap = "(nat, 'data block) fmap"

inductive_set reach :: "'data heap \<Rightarrow> nat list \<Rightarrow> nat set" for h roots
  where
  reach_root[intro]: "a \<in> set roots \<Longrightarrow> a \<in> reach h roots"
| reach_step[intro]: "\<lbrakk>b \<in> reach h roots; lookup h b = Some(as,data); a \<in> set as\<rbrakk> \<Longrightarrow> a \<in> reach h roots"

(* 2-a *)
lemma reach_empty:
  assumes "a \<in> reach h []"
  shows "False"
  (* TODO *)
  sorry


lemma reach_empty_simp[simp]:
  shows "a \<in> reach h [] = False"
  by(metis reach_empty)

(* 2-b *)
lemma reach_roots_mono:
  assumes "a \<in> reach h roots"
  and "set roots \<subseteq> set roots'"
  shows   "a \<in> reach h roots'"
  (* TODO *)
  sorry


(* 2-c *)
lemma reach_compose:
  assumes "a \<in> reach h roots"
  and "b \<in> reach h [a]"
  shows   "b \<in> reach h roots"
  (* TODO *)
  sorry


(* 2-d *)
lemma reach_dangling1:
  assumes "lookup h x = None"
  and   "a \<in> reach h (x#roots)"
  shows "x = a \<or> a \<in> reach h roots"
  (* TODO *)
  sorry


lemma reach_dangling[simp]:
  assumes "lookup h x = None"
  shows   "(a \<in> reach h (x#roots)) = (x = a \<or> a \<in> reach h roots)"
  using assms
  by(auto dest: reach_dangling1 intro: reach_roots_mono)

(* 2-e *)
lemma reach_subset:
  "x \<in> reach heap roots \<Longrightarrow> (x \<in> set roots) \<or> (\<exists>block. block \<in> fran heap \<and> x \<in> set(fst block))"
  (* TODO *)
  sorry


fun collect :: "'data heap \<Rightarrow> nat list \<Rightarrow> 'data heap"
  where
  "collect h roots = frestrict_set (reach h roots) h"

definition ex1_heap :: "unit heap"
  where "ex1_heap = fmap_of [(0,([1,2],())),
                                  (1,([0],())),
                                  (2,([2],())),
                                  (3,([0],()))
                                 ]"

(* 2-f *)
definition ex1_reach :: "nat set"
  where "ex1_reach = undefined" \<comment> \<open> TODO \<close>

(* 2-g *)
lemma ex1:
  "ex1_reach \<subseteq> fdom(collect ex1_heap [0])"
  (* TODO *)
  sorry


(* 2-h *)
lemma collect_sound: \<comment> \<open>A sound garbage collector retains all non-garbage.\<close>
  "n \<in> reach h roots \<Longrightarrow> n \<in> reach (collect h roots) roots"
  (* TODO *)
  sorry


(* 2-i *)
lemma collect_complete: \<comment> \<open>A complete garbage collector removes all garbage.\<close>
  "\<lbrakk>n \<in> fdom h; n \<notin> reach h roots\<rbrakk> \<Longrightarrow> n \<notin> fdom (collect h roots)"
  (* TODO *)
  sorry


(* 2-j *)
lemma collect_idempotent: \<comment> \<open>Running a garbage collector a second time in a row does nothing.\<close>
  "collect (collect h roots) roots = collect h roots"
  (* TODO *)
  sorry



(* Q3: Garbage collector refinement *)

fun marked :: "(bool \<times> 'data) block \<Rightarrow> bool"
  where "marked(ptr,(tag,data)) = tag"

fun mark_block :: "(bool \<times> 'data) block \<Rightarrow> (bool \<times> 'data) block"
  where "mark_block(ptr,(tag,data)) = (ptr,(True,data))"

fun unmark_block :: "(bool \<times> 'data) block \<Rightarrow> (bool \<times> 'data) block"
  where "unmark_block(ptr,(tag,data)) = (ptr,(False,data))"

inductive mark where
  mark_done[intro!,simp]: "mark heap [] heap"
| mark_dangling[elim]: "
   \<lbrakk>lookup heap root = None;
    mark heap roots new_heap\<rbrakk>
   \<Longrightarrow> mark heap (root#roots) new_heap"
| mark_marked[intro]: "
   \<lbrakk>lookup heap root = Some block;
    marked block;
    mark heap roots new_heap\<rbrakk>
   \<Longrightarrow> mark heap (root#roots) new_heap"
| mark_unmarked[intro]: "
   \<lbrakk>lookup heap root = Some block;
    \<not>marked block;
    mark (fupd root (mark_block block) heap) (roots@fst block) new_heap\<rbrakk>
   \<Longrightarrow> mark heap (root#roots) new_heap"

abbreviation unmarked_root where
  "unmarked_root \<equiv> \<lambda>h root. case lookup h root of None ⇒ True | Some y ⇒ Not (marked y)"

inductive_set ureach:: "(bool \<times> 'data) heap \<Rightarrow> nat list \<Rightarrow> nat set" for h roots
  where
  ureach_root[intro]: "\<lbrakk>a \<in> set roots; unmarked_root h a\<rbrakk> \<Longrightarrow> a \<in> ureach h roots"
| ureach_step[intro]: "\<lbrakk>b \<in> ureach h roots; lookup h b = Some(as,(False,data)); a \<in> set as;
                        unmarked_root h a\<rbrakk>
                       \<Longrightarrow> a \<in> ureach h roots"

(* 3-a *)
lemma ureach_roots_mono:
  assumes "a \<in> ureach h roots"
  and "set roots \<subseteq> set roots'"
  shows   "a \<in> ureach h roots'"
  (* TODO *)
  sorry

(* 3-b *)
lemma ureach_dangling1:
  assumes "lookup h x = None"
  and   "a \<in> ureach h (x#roots)"
  shows "a = x \<or> a \<in> ureach h roots"
  (* TODO *)
  sorry

(* 3-c *)
lemma ureach_marked[intro]:
  assumes "lookup h x = Some(ptrs,(True,tags))"
  and   "a \<in> ureach h (x#roots)"
  shows "a \<in> ureach h roots"
  (* TODO *)
  sorry

lemma ureach_dangling[simp]:
  assumes "lookup h x = None"
  shows   "(a \<in> ureach h (x#roots)) = (a = x \<or> a \<in> ureach h roots)"
  using assms
  by(auto dest: ureach_dangling1 intro: ureach_roots_mono)

(* 3-d *)
lemma ureach_mark_step:
  assumes "lookup heap root = Some (a, (False, b))"
      and "x \<in> ureach (fupd root (a, True, b) heap) (roots @ a)"
    shows "x \<in> ureach heap (root # roots)"
  using assms(2) assms(1)
  (* TODO *)
  sorry

(* 3-e *)
lemma ureach_mark_step':
  assumes "lookup heap root = Some (a, (False, b))"
      and "x \<in> ureach heap (root # roots)"
    shows "x \<in> ureach (fupd root (a, True, b) heap) (roots @ a) \<or> x = root"
  using assms(2) assms(1)
  (* TODO *)
  sorry

(* 3-f *)
lemma mark_correct_aux:
  "mark heap roots newheap \<Longrightarrow>
   newheap =
   fmap_keys
     (\<lambda>ptr (ptrs,(tag,data)). (ptrs,(tag \<or> (ptr \<in> ureach heap roots),data)))
     heap"
  (* TODO *)
  sorry

(* 3-g *)
lemma ureach_reach[intro]:
  assumes "a \<in> ureach h roots"
  shows "a \<in> reach h roots"
  (* TODO *)
  sorry

(* 3-h *)
lemma reach_ureach[dest]:
  assumes "a \<in> reach h roots"
      and "fpred (\<lambda>ptr block. \<not>marked block) h"
  shows "a \<in> ureach h roots \<or> a \<in> set roots"
  (* TODO *)
  sorry

(* 3-i *)
lemma mark_correct:
  "mark heap roots newheap \<Longrightarrow>
   fpred (\<lambda>ptr block. \<not>marked block) heap \<Longrightarrow>
   newheap = fmap_keys (\<lambda>ptr (ptrs,(tag,data)). (ptrs,((ptr \<in> reach heap roots),data))) heap"
  (* TODO *)
  sorry

definition sweep :: "(bool \<times> 'data) heap \<Rightarrow> (bool \<times> 'data) heap" where
  "sweep h = fmmap unmark_block (fmap_filter (Not o unmarked_root h) h)"

declare sweep_def[simp]

(* 3-j *)
lemma gc_refinement:
  "mark h roots h' \<Longrightarrow>
   fpred (\<lambda>ptr block. \<not>marked block) h \<Longrightarrow>
   collect h roots = sweep h'"
  (* TODO *)
  sorry

end