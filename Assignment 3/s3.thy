theory s3
  imports a3_fmap AutoCorres.AutoCorres
begin

(****************)

type_synonym 'data block = "nat list \<times> 'data"

type_synonym 'data heap = "(nat, 'data block) fmap"

fun marked :: "(bool \<times> 'data) block \<Rightarrow> bool"
  where "marked(ptr,(tag,data)) = tag"

fun mark_block :: "(bool \<times> 'data) block \<Rightarrow> (bool \<times> 'data) block"
  where "mark_block(ptr,(tag,data)) = (ptr,(True,data))"

fun unmark_block :: "(bool \<times> 'data) block \<Rightarrow> (bool \<times> 'data) block"
  where "unmark_block(ptr,(tag,data)) = (ptr,(False,data))"

function markF
  where
  "markF heap [] = heap"
| "markF heap (root#roots) =
    (case fmap.lookup heap root of
       None \<Rightarrow> markF heap roots
     | Some blk \<Rightarrow>
       if marked blk then
         markF heap roots
       else
         markF (fupd root (mark_block blk) heap) (roots@fst blk))"
  by pat_completeness auto

termination
(*
  apply(relation "measures [(\<lambda>(h, r). size_fmap(fmap_filter (\<lambda>i. case_option False (Not o marked) (fmap.lookup h i)) h))
                  , (\<lambda>(h, r). length r)]")
  apply (rule wf_measures)
*)
(*
      apply(relation "measures [(\<lambda>(h, r). card (fdom (fmap_filter (\<lambda>a. \<exists>b c. (fmap.lookup h a) = Some(b, False, c)) h)))
                  , (\<lambda>(h, r). length r)]")
  apply (rule wf_measures)
*)
  apply(relation "measure (\<lambda>h. size_fmap(fmap_filter (\<lambda>i. case_option False (Not o marked) (fmap.lookup h i)) h))
                  <*lex*>
                  measure length")
  apply(rule wf_lex_prod;simp)
    apply clarsimp+
  apply(rule Finite_Set.psubset_card_mono,simp)
  apply(rule psubsetI)
   apply(simp add: subset_eq Ball_def)
   apply clarify
  apply clarify
  apply(drule Set.equalityD2)
  apply(clarsimp simp add: subset_eq Ball_def split: if_split_asm)
  by (metis comp_apply fdomI lookup_fdom_iff marked.simps option.case_eq_if option.sel)

abbreviation unmarked_root where
  "unmarked_root \<equiv> \<lambda>h root. case fmap.lookup h root of None \<Rightarrow> True | Some y \<Rightarrow> Not (marked y)"

inductive_set ureach:: "(bool \<times> 'data) heap \<Rightarrow> nat list \<Rightarrow> nat set" for h roots
  where
  ureach_root[intro]: "\<lbrakk>a \<in> set roots; unmarked_root h a\<rbrakk> \<Longrightarrow> a \<in> ureach h roots"
| ureach_step[intro]: "\<lbrakk>b \<in> ureach h roots; fmap.lookup h b = Some(as,(False,data)); a \<in> set as;
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
  assumes "fmap.lookup h x = None"
  and   "a \<in> ureach h (x#roots)"
  shows "a = x \<or> a \<in> ureach h roots"
  using assms(2) assms(1)
  by (induct rule: ureach.induct) auto

lemma ureach_marked[intro]:
  assumes "fmap.lookup h x = Some(ptrs,(True,tags))"
  and   "a \<in> ureach h (x#roots)"
  shows "a \<in> ureach h roots"
  using assms(2) assms(1)
  by (induct rule: ureach.induct) auto

lemma ureach_mark_step:
  assumes "fmap.lookup heap root = Some (a, (False, b))"
      and "x \<in> ureach (fupd root (a, True, b) heap) (roots @ a)"
    shows "x \<in> ureach heap (root # roots)"
  using assms(2) assms(1)
  by(induct rule: ureach.induct) (force split: option.split_asm if_split_asm)+

lemma ureach_mark_step':
  assumes "fmap.lookup heap root = Some (a, (False, b))"
      and "x \<in> ureach heap (root # roots)"
    shows "x \<in> ureach (fupd root (a, True, b) heap) (roots @ a) \<or> x = root"
  using assms(2) assms(1)
  apply(induct rule: ureach.induct)
   apply force
  apply(clarsimp split: option.split_asm if_split_asm)
   apply(case_tac "ba=root";force)+
  done

lemma ureach_dangling[simp]:
  assumes "fmap.lookup h x = None"
  shows   "(a \<in> ureach h (x#roots)) = (a = x \<or> a \<in> ureach h roots)"
  using assms
  by(auto dest: ureach_dangling1 intro: ureach_roots_mono)

lemma mark_correct_aux:
  "markF heap roots =
   fmap_keys
     (\<lambda>ptr (ptrs,(tag,data)). (ptrs,(tag \<or> (ptr \<in> ureach heap roots),data)))
     heap"
  apply(induct heap roots rule: markF.induct; rule lookup_ext)
   apply (fastforce simp: lookup_fmap_keys option.map_ident)
  apply (case_tac "fmap.lookup heap root"; simp split del: if_split)
   apply (case_tac "fmap.lookup heap x"; clarsimp)
   apply fastforce
  apply (case_tac "marked a"; simp)
  apply (clarsimp simp: lookup_fmap_keys)
   apply (case_tac "fmap.lookup heap x"; clarsimp)
  apply (metis (no_types, lifting) insert_iff list.set(2) subsetI ureach_marked ureach_roots_mono)
  apply (clarsimp simp: lookup_fmap_keys)
   apply (case_tac "fmap.lookup heap x"; clarsimp)
  apply safe
  apply force
  apply force
  apply force
   apply(drule ureach_mark_step,assumption,simp)
  apply(drule ureach_mark_step',assumption,simp)
  done

inductive_set reach :: "'data heap \<Rightarrow> nat list \<Rightarrow> nat set" for h roots
  where
  reach_root[intro]: "a \<in> set roots \<Longrightarrow> a \<in> reach h roots"
| reach_step[intro]: "\<lbrakk>b \<in> reach h roots; fmap.lookup h b = Some(as,data); a \<in> set as\<rbrakk> \<Longrightarrow> a \<in> reach h roots"

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
   apply(case_tac "fmap.lookup h r";force)
  apply(case_tac "a \<in> set roots"; clarsimp)
  apply(erule ureach_step)
    apply force
   apply assumption
  apply(rename_tac r)
  apply(case_tac "fmap.lookup h r";force)
  done

term markF
lemma mark_correct:
  "fpred (\<lambda>ptr block. \<not>marked block) heap \<Longrightarrow>
   markF heap roots = fmap_keys (\<lambda>ptr (ptrs,(tag,data)). (ptrs,((ptr \<in> reach heap roots),data))) heap"
  apply(subst mark_correct_aux)
  apply(rule lookup_ext)
  apply (clarsimp simp: lookup_fmap_keys)
  apply (case_tac "fmap.lookup heap x"; simp)
  apply force
  done

(*******************************************************)


external_file "gc.c"
install_C_file "gc.c"
autocorres "gc.c"

primrec
  list :: "lifted_globals \<Rightarrow> blist_C ptr \<Rightarrow> blist_C ptr list \<Rightarrow> bool"
where
  "list s p [] = (p = NULL)"
| "list s p (x#xs) = (
       p = x \<and> p \<noteq> NULL \<and> is_valid_blist_C s p \<and> list s (next_C (heap_blist_C s p)) xs)"

lemma list_empty[simp]:
  "list s NULL xs = (xs = [])"
  by (induct xs) auto

lemma list_in[simp]:
  "\<lbrakk> list s p xs; p \<noteq> NULL \<rbrakk> \<Longrightarrow> p \<in> set xs"
  by (induct xs) auto

lemma list_hd_tl:
  "\<lbrakk> p \<noteq> NULL \<rbrakk> \<Longrightarrow>
    list s p xs = (\<exists>ys. xs = p # ys \<and> is_valid_blist_C s p \<and> list s (next_C (heap_blist_C s p)) ys)"
  by (cases xs) auto

lemma list_unique:
  "list s p xs \<Longrightarrow> list s p ys \<Longrightarrow> xs = ys"
  by (induct xs arbitrary: p ys) (auto simp add: list_hd_tl)

lemma list_append_Ex:
  "list s p (xs @ ys) \<Longrightarrow> (\<exists>q. list s q ys)"
  by (induct xs arbitrary: p) auto

lemma list_distinct[simp]:
  "list s p xs \<Longrightarrow> distinct xs"
  apply (induct xs arbitrary: p)
   apply simp
  apply (clarsimp dest!: split_list)
  apply (frule list_append_Ex)
  apply (auto dest: list_unique)
  done

lemma list_notin_update_eq[simp]:
  "q \<notin> set xs \<Longrightarrow> list (heap_blist_C_update (\<lambda>h. h (q := next_C_update (\<lambda>_. v) (h q))) s) p xs = list s p xs"
  by (induct xs arbitrary: p) auto

definition
  the_list :: "lifted_globals \<Rightarrow> blist_C ptr \<Rightarrow> blist_C ptr list"
where
  "the_list s p = (THE xs. list s p xs)"

lemma the_list_val [simp]: "list s p xs \<Longrightarrow> the_list s p = xs"
  apply (clarsimp simp: the_list_def)
  apply (metis (lifting) list_unique the_equality)
  done

lemma the_list_notin_update_eq[simp]:
   "\<lbrakk> q \<notin> set xs; list s p xs \<rbrakk> \<Longrightarrow>
     the_list (heap_blist_C_update (\<lambda>h. h (q := next_C_update (\<lambda>_. v) (h q))) s) p = the_list s p"
  apply clarsimp
  done

context gc begin

thm append'_def
thm append_step'_def
thm mark'_def

term append'
term mark'

lemma append_step_correct:
"\<lbrace> \<lambda>s. p \<noteq> NULL \<and> list s p Ps \<and> list s q Qs \<and> set Ps \<inter> set Qs = {} \<rbrace>
   append_step' p q
 \<lbrace> \<lambda>r s. list s r (tl Ps) \<and> list s p (p#Qs)\<rbrace>!"
  unfolding append_step'_def
  apply wp
  apply clarsimp
  apply (frule list_distinct)
  apply (clarsimp simp: list_hd_tl)
  apply (fold fun_upd_def)
  apply simp
  done

lemma append_correct:
"\<lbrace> \<lambda>s. list s p Ps \<and> list s q Qs \<and> set Ps \<inter> set Qs = {} \<rbrace>
   append' p q
 \<lbrace> \<lambda>r s. list s r (rev Ps @ Qs) \<rbrace>!"
  unfolding append'_def append_step'_def bind_assoc K_bind_def

  txt \<open>Add the loop invariant and measure.\<close>
  apply (subst whileLoop_add_inv
    [where I = "\<lambda>(dest', list') s.
                 \<exists>ps qs. list s dest' ps \<and> list s list' qs \<and> set ps \<inter> set qs = {} \<and>
                         rev ps @ qs = rev Ps @ Qs"
       and M = " (\<lambda>((dest', _), s). length (the_list s dest'))"])
  apply (wp validNF_whileLoop_inv_measure_twosteps)
     apply (case_tac r; clarsimp)
  apply (frule list_distinct)
     apply (case_tac ps; clarsimp)
     apply (fold fun_upd_def)

     apply (rule_tac x=lista in exI)
  apply (subgoal_tac "aa \<notin> set lista")
  apply simp
  apply (rule_tac x="aa#qs" in exI, clarsimp)
     apply clarsimp
  txt \<open>Loop invariant done.\<close>


  txt \<open>Loop measure.\<close>
    apply wp
    apply (case_tac r; simp)
    apply clarsimp
    apply (fold fun_upd_def)
    apply (frule list_distinct)
  apply (case_tac ps; simp)

  txt \<open>Loop entrance and exit.\<close>
   apply fastforce+
  done
end

(**)

primrec
  mkd_list :: "lifted_globals \<Rightarrow> block_C ptr \<Rightarrow> block_C ptr list \<Rightarrow> bool"
where
  "mkd_list s p [] = (p = NULL)"
| "mkd_list s p (x#xs) = (
       p = x \<and> p \<noteq> NULL \<and> is_valid_block_C s p \<and> mkd_list s (m_nxt_C (heap_block_C s p)) xs)"

definition
  the_mkd_list :: "lifted_globals \<Rightarrow> block_C ptr \<Rightarrow> block_C ptr list"
where
  "the_mkd_list s p = (THE xs. mkd_list s p xs)"

lemma mkd_list_empty [simp]:
  "mkd_list s NULL xs = (xs = [])"
  by (induct xs) auto

lemma mkd_list_in [simp]:
  "\<lbrakk> mkd_list s p xs; p \<noteq> NULL \<rbrakk> \<Longrightarrow> p \<in> set xs"
  by (induct xs) auto

lemma mkd_list_hd_tl:
  "\<lbrakk> p \<noteq> NULL \<rbrakk> \<Longrightarrow>
    mkd_list s p xs = (\<exists>ys. xs = p # ys \<and> is_valid_block_C s p
                            \<and> mkd_list s (m_nxt_C (heap_block_C s p)) ys)"
  by (cases xs) auto

lemma mkd_list_unique:
  "mkd_list s p xs \<Longrightarrow> mkd_list s p ys \<Longrightarrow> xs = ys"
  by (induct xs arbitrary: p ys) (auto simp add: mkd_list_hd_tl)

lemma the_mkd_list_val [simp]: "mkd_list s p xs \<Longrightarrow> the_mkd_list s p = xs"
  apply (clarsimp simp: the_mkd_list_def)
  by (simp add: mkd_list_unique the_equality)

(**)

definition
  "block_in_list s p b \<equiv> (\<exists>xs q. list s p xs \<and> q \<in> set xs \<and> b = this_C (heap_blist_C s q))"

inductive_set b_reach :: "lifted_globals \<Rightarrow> blist_C ptr \<Rightarrow> (block_C ptr) set" for s r where
 b_reach_root[intro]:
     "block_in_list s r b \<Longrightarrow> b \<in> b_reach s r"
| b_reach_step[intro]:
    "\<lbrakk>q \<in> b_reach s r; block_in_list s (nexts_C (heap_block_C s q)) b\<rbrakk> \<Longrightarrow> b \<in> b_reach s r"

lemma b_reach_subset:
  "x \<in> b_reach s rts \<Longrightarrow>
         (block_in_list s rts x) \<or>
                (\<exists>block. block_in_list s (nexts_C (heap_block_C s block)) x)"
  by (induct rule: b_reach.induct) auto

context gc begin

thm mark'_def

lemma mark_correct:
"\<lbrace> \<lambda>s. list s rts roots \<and> R = b_reach s rts \<and>
   (\<forall>p. is_valid_block_C s p \<longrightarrow> flag_C (heap_block_C s p) = 0)\<rbrace>
   mark' rts
 \<lbrace> \<lambda>r s. \<exists>ls. mkd_list s r ls \<and> set ls = R\<rbrace>!"
  unfolding mark'_def
  oops

end

end