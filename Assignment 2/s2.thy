theory s2
  imports Main s2_fmap
begin

type_synonym 'data block = "nat list \<times> 'data"

type_synonym 'data heap = "(nat, 'data block) fmap"

(* Q: start out with some fmap exercises? *)
inductive_set reach :: "'data heap \<Rightarrow> nat list \<Rightarrow> nat set" for h roots
  where
  reach_root[intro]: "a \<in> set roots \<Longrightarrow> a \<in> reach h roots"
| reach_step[intro]: "\<lbrakk>b \<in> reach h roots; lookup h b = Some(as,data); a \<in> set as\<rbrakk> \<Longrightarrow> a \<in> reach h roots"

lemma reach_empty:
  assumes "a \<in> reach h []"
  shows "False"
  using assms
  by induct auto

lemma reach_empty_simp[simp]:
  shows "a \<in> reach h [] = False"
  by(metis reach_empty)

lemma reach_roots_mono:
  assumes "a \<in> reach h roots"
  and "set roots \<subseteq> set roots'"
  shows   "a \<in> reach h roots'"
  using assms
  by induct auto
(*
lemma reach_heap_mono:
  assumes "a \<in> reach h roots"
  and "fmap_le h h'"
  shows "a \<in> reach h' roots"
  using assms
  by induct (auto simp add: fmap_le_def fdom_def dom_def split: option.split_asm)
*)
lemma reach_compose:
  assumes "a \<in> reach h roots"
  and "b \<in> reach h [a]"
  shows   "b \<in> reach h roots"
  using assms(2) assms(1)
  by(induct rule: reach.induct) auto

lemma reach_dangling1:
  assumes "lookup h x = None"
  and   "a \<in> reach h (x#roots)"
  shows "x = a \<or> a \<in> reach h roots"
  using assms(2) assms(1)
  by (induct rule: reach.induct) auto

lemma reach_dangling[simp]:
  assumes "lookup h x = None"
  shows   "(a \<in> reach h (x#roots)) = (x = a \<or> a \<in> reach h roots)"
  using assms
  by(auto dest: reach_dangling1 intro: reach_roots_mono)

fun collect :: "'data heap \<Rightarrow> nat list \<Rightarrow> 'data heap"
  where
  "collect h roots = frestrict_set (reach h roots) h"

definition ex1_heap :: "unit heap"
  where "ex1_heap = fmap_of [(0,([1,2],())),
                                  (1,([0],())),
                                  (2,([2],())),
                                  (3,([0],()))
                                 ]"

definition ex1_reach :: "nat set"
  where "ex1_reach = {0,1,2}"

lemma ex1:
  "ex1_reach \<subseteq> fdom(collect ex1_heap [0])"
  apply(rule subsetI)
  apply(force simp add: ex1_heap_def ex1_reach_def fdom_restrict_set_precise)
  done

lemma reach_restrict_reach:
  "n \<in> reach h roots \<Longrightarrow> n \<in> reach (frestrict_set (reach h roots) h) roots"
  by(induct rule: reach.induct) auto

lemma collect_sound: \<comment> \<open>A sound garbage collector retains all non-garbage.\<close>
  "n \<in> reach h roots \<Longrightarrow> n \<in> reach (collect h roots) roots"
  by(force intro: reach_restrict_reach)

lemma collect_complete: \<comment> \<open>A complete garbage collector removes all garbage.\<close>
  "\<lbrakk>n \<in> fdom h; n \<notin> reach h roots\<rbrakk> \<Longrightarrow> n \<notin> fdom (collect h roots)"
  by (auto simp: frestrict_set_def)

lemma collect_idempotent: \<comment> \<open>Running a garbage collector a second time in a row does nothing.\<close>
  "collect (collect h roots) roots = collect h roots"
  by (rule lookup_ext) (force intro: reach_restrict_reach)

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

lemma reach_subset:
  "x \<in> reach heap roots \<Longrightarrow> (x \<in> set roots) \<or> (\<exists>block. block \<in> fran heap \<and> x \<in> set(fst block))"
  by(induct rule: reach.induct) (auto simp add: lookup_ran_iff)

abbreviation unmarked_root where
  "unmarked_root \<equiv> \<lambda>h root. case lookup h root of None \<Rightarrow> True | Some y \<Rightarrow> Not (marked y)"

inductive_set ureach:: "(bool \<times> 'data) heap \<Rightarrow> nat list \<Rightarrow> nat set" for h roots
  where
  ureach_root[intro]: "\<lbrakk>a \<in> set roots; unmarked_root h a\<rbrakk> \<Longrightarrow> a \<in> ureach h roots"
| ureach_step[intro]: "\<lbrakk>b \<in> ureach h roots; lookup h b = Some(as,(False,data)); a \<in> set as;
                        unmarked_root h a\<rbrakk>
                       \<Longrightarrow> a \<in> ureach h roots"

lemma ureach_empty:
  assumes "a \<in> ureach h []"
  shows "False"
  using assms
  by induct auto

lemma ureach_empty_simp[simp]:
  shows "a \<in> ureach h [] = False"
  by(metis ureach_empty)

lemma ureach_roots_mono:
  assumes "a \<in> ureach h roots"
  and "set roots \<subseteq> set roots'"
  shows   "a \<in> ureach h roots'"
  using assms
  by induct auto

lemma ureach_dangling1:
  assumes "lookup h x = None"
  and   "a \<in> ureach h (x#roots)"
  shows "a = x \<or> a \<in> ureach h roots"
  using assms(2) assms(1)
  by (induct rule: ureach.induct) auto

lemma ureach_marked[intro]:
  assumes "lookup h x = Some(ptrs,(True,tags))"
  and   "a \<in> ureach h (x#roots)"
  shows "a \<in> ureach h roots"
  using assms(2) assms(1)
  by (induct rule: ureach.induct) auto

lemma ureach_dangling[simp]:
  assumes "lookup h x = None"
  shows   "(a \<in> ureach h (x#roots)) = (a = x \<or> a \<in> ureach h roots)"
  using assms
  by(auto dest: ureach_dangling1 intro: ureach_roots_mono)

lemma ureach_mark_step:
  assumes "lookup heap root = Some (a, (False, b))"
      and "x \<in> ureach (fupd root (a, True, b) heap) (roots @ a)"
    shows "x \<in> ureach heap (root # roots)"
  using assms(2) assms(1)
  by(induct rule: ureach.induct) (force split: option.split_asm if_split_asm)+

lemma ureach_mark_step':
  assumes "lookup heap root = Some (a, (False, b))"
      and "x \<in> ureach heap (root # roots)"
    shows "x \<in> ureach (fupd root (a, True, b) heap) (roots @ a) \<or> x = root"
  using assms(2) assms(1)
  apply(induct rule: ureach.induct)
   apply force
  apply(clarsimp split: option.split_asm if_split_asm)
   apply(case_tac "ba=root";force)+
  done

lemma mark_correct_aux:
  "mark heap roots newheap \<Longrightarrow>
   newheap =
   fmap_keys
     (\<lambda>ptr (ptrs,(tag,data)). (ptrs,(tag \<or> (ptr \<in> ureach heap roots),data)))
     heap"
  supply lookup_fmap_keys[simp]
  apply(induct rule: mark.induct; rule lookup_ext)
     apply(force simp add: map_option.identity)
   apply(auto split: option.split prod.split simp add: map_option.identity
              intro!: map_option_cong
              intro: ureach_roots_mono[rotated,OF set_subset_Cons]
        )
    apply(rule ureach_root; clarsimp)
   apply(drule ureach_mark_step,assumption,simp)
  apply(drule ureach_mark_step',assumption,simp)
  done

lemma ureach_reach[intro]:
  assumes "a \<in> ureach h roots"
  shows "a \<in> reach h roots"
  using assms
  by induct auto

lemma reach_ureach[dest]:
  assumes "a \<in> reach h roots"
      and "fpred (\<lambda>ptr block. \<not>marked block) h"
  shows "a \<in> ureach h roots \<or> a \<in> set roots"
  using assms
  apply(induct rule: reach.induct)
   apply force
  apply(case_tac "b \<in> set roots")
   apply(rule disjI1)
   apply clarsimp
   apply(rule ureach_step[OF ureach_root],assumption,force,force,force)
   apply(rename_tac r)
   apply(case_tac "lookup h r";force)
  apply(case_tac "a \<in> set roots"; clarsimp)
  apply(erule ureach_step)
    apply force
   apply assumption
  apply(rename_tac r)
  apply(case_tac "lookup h r";force)
  done

lemma mark_correct:
  "mark heap roots newheap \<Longrightarrow>
   fpred (\<lambda>ptr block. \<not>marked block) heap \<Longrightarrow>
   newheap = fmap_keys (\<lambda>ptr (ptrs,(tag,data)). (ptrs,((ptr \<in> reach heap roots),data))) heap"
  apply(drule mark_correct_aux)
  apply(force intro: map_option_cong lookup_ext simp: lookup_fmap_keys)
  done

definition sweep :: "(bool \<times> 'data) heap \<Rightarrow> (bool \<times> 'data) heap" where
  "sweep h = fmmap unmark_block (fmap_filter (Not o unmarked_root h) h)"

declare sweep_def[simp]

lemma gc_refinement:
  "mark h roots h' \<Longrightarrow>
   fpred (\<lambda>ptr block. \<not>marked block) h \<Longrightarrow>
   collect h roots = sweep h'"
  apply(rule lookup_ext)
  by(force split: option.split dest: mark_correct simp: lookup_map lookup_fmap_keys)

end