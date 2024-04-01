theory a3
  imports a3_fmap AutoCorres.AutoCorres
begin


(* To run this file you need the AutoCorres tool used
   in the lecture.

  1. Download AutoCorres from
       https://github.com/seL4/l4v/releases/download/autocorres-1.9/autocorres-1.9.tar.gz

  2. Unpack the .tar.gz file, which will create the directory autocorres-1.9
       tar -xzf autocorres-1.9.tar.gz

  3. Load this file using the AutoCorres base image
     L4V_ARCH=X64 isabelle jedit -d autocorres-1.9 -l AutoCorres a3.thy

  The first time you load AutoCorres, Isabelle will build an image file
  for the proofs in the AutoCorres session. This takes a while. The next
  time Isabelle loads the saved proof state from that image file directly
  and there should be no long wait any more.
*)


(*

   The questions for a3 are marked with "TODO" labels.

   We use some lemmas from a2 in this file. Those are sorried but
   you don't need to prove them.

 *)


(*---------------------------------------------------------*)
(*-------- Question 1: General recursive funciton ---------*)
(*---------------------------------------------------------*)


type_synonym 'data block = "nat list \<times> 'data"

type_synonym 'data heap = "(nat, 'data block) fmap"

fun marked :: "(bool \<times> 'data) block \<Rightarrow> bool" where
  "marked (ptr, (tag,data)) = tag"

fun mark_block :: "(bool \<times> 'data) block \<Rightarrow> (bool \<times> 'data) block" where
  "mark_block (ptr, (tag,data)) = (ptr, (True,data))"

fun unmark_block :: "(bool \<times> 'data) block \<Rightarrow> (bool \<times> 'data) block" where
  "unmark_block (ptr, (tag,data)) = (ptr, (False,data))"

(* 1-a *)
function markF where
  "markF heap [] = heap"
| "markF heap (root#roots) =
    (case fmap.lookup heap root of
       None \<Rightarrow> markF heap roots
     | Some blk \<Rightarrow> if marked blk then markF heap roots
                   else markF (fupd root (mark_block blk) heap) (roots@fst blk))"
  sorry (* TODO *)

termination
  sorry (* TODO *)


abbreviation unmarked_root where
  "unmarked_root \<equiv> \<lambda>h root. case fmap.lookup h root of None \<Rightarrow> True | Some y \<Rightarrow> Not (marked y)"

inductive_set ureach:: "(bool \<times> 'data) heap \<Rightarrow> nat list \<Rightarrow> nat set" for h roots where
  ureach_root[intro]: "\<lbrakk>a \<in> set roots; unmarked_root h a\<rbrakk> \<Longrightarrow> a \<in> ureach h roots"
| ureach_step[intro]: "\<lbrakk>b \<in> ureach h roots; fmap.lookup h b = Some(as,(False,data)); a \<in> set as;
                        unmarked_root h a\<rbrakk>
                       \<Longrightarrow> a \<in> ureach h roots"

lemma ureach_roots_mono:
  assumes "a \<in> ureach h roots"
  and "set roots \<subseteq> set roots'"
  shows   "a \<in> ureach h roots'"
  sorry (* a2 question : no need to prove *)

lemma ureach_dangling1:
  assumes "fmap.lookup h x = None"
  and   "a \<in> ureach h (x#roots)"
  shows "a = x \<or> a \<in> ureach h roots"
  sorry (* a2 question : no need to prove *)

lemma ureach_marked[intro]:
  assumes "fmap.lookup h x = Some(ptrs,(True,tags))"
  and   "a \<in> ureach h (x#roots)"
  shows "a \<in> ureach h roots"
  sorry (* a2 question : no need to prove *)

lemma ureach_mark_step:
  assumes "fmap.lookup heap root = Some (a, (False, b))"
      and "x \<in> ureach (fupd root (a, True, b) heap) (roots @ a)"
    shows "x \<in> ureach heap (root # roots)"
  using assms(2) assms(1)
  sorry (* a2 question : no need to prove *)

lemma ureach_mark_step':
  assumes "fmap.lookup heap root = Some (a, (False, b))"
      and "x \<in> ureach heap (root # roots)"
    shows "x \<in> ureach (fupd root (a, True, b) heap) (roots @ a) \<or> x = root"
  using assms(2) assms(1)
  sorry (* a2 question : no need to prove *)

lemma ureach_dangling[simp]:
  assumes "fmap.lookup h x = None"
  shows   "(a \<in> ureach h (x#roots)) = (a = x \<or> a \<in> ureach h roots)"
  using assms
  by(auto dest: ureach_dangling1 intro: ureach_roots_mono)

(* 1-b *)
lemma mark_correct_aux: (* for markF *)
  "markF heap roots =
     fmap_keys (\<lambda>ptr (ptrs, (tag,data)). (ptrs, (tag \<or> ptr \<in> ureach heap roots, data))) heap"
  oops (* TODO *)

inductive_set reach :: "'data heap \<Rightarrow> nat list \<Rightarrow> nat set" for h roots where
  reach_root[intro]: "a \<in> set roots \<Longrightarrow> a \<in> reach h roots"
| reach_step[intro]: "\<lbrakk>b \<in> reach h roots; fmap.lookup h b = Some(as, data); a \<in> set as\<rbrakk> \<Longrightarrow>
                       a \<in> reach h roots"

lemma ureach_reach[intro]:
  assumes "a \<in> ureach h roots"
  shows "a \<in> reach h roots"
  using assms
  sorry (* a2 question : no need to prove *)

lemma reach_ureach[dest]:
  assumes "a \<in> reach h roots"
      and "fpred (\<lambda>ptr block. \<not>marked block) h"
  shows "a \<in> ureach h roots \<or> a \<in> set roots"
  using assms
  sorry (* a2 question : no need to prove *)


(* 1-c *)
lemma mark_correct: (* for markF *)
  "fpred (\<lambda>ptr block. \<not>marked block) heap \<Longrightarrow>
     markF heap roots =
     fmap_keys (\<lambda>ptr (ptrs, (tag,data)). (ptrs, (ptr \<in> reach heap roots, data))) heap"
  oops (* TODO *)


(*---------------------------------------------------------*)
(*------------- Question 2: C verification ----------------*)
(*---------------------------------------------------------*)


external_file "gc.c"
install_C_file "gc.c"
autocorres "gc.c"

primrec list :: "lifted_globals \<Rightarrow> blist_C ptr \<Rightarrow> blist_C ptr list \<Rightarrow> bool" where
  "list s p [] = (p = NULL)"
| "list s p (x#xs) =
     (p = x \<and> p \<noteq> NULL \<and> is_valid_blist_C s p \<and> list s (next_C (heap_blist_C s p)) xs)"

(* 2-a *)
lemma list_empty[simp]:
  "list s NULL xs = (xs = [])"
  oops (* TODO *)

(* 2-b *)
lemma list_in[simp]:
  "\<lbrakk> list s p xs; p \<noteq> NULL \<rbrakk> \<Longrightarrow> p \<in> set xs"
  oops (* TODO *)

(* 2-c *)
lemma list_hd_tl:
  "\<lbrakk> p \<noteq> NULL \<rbrakk> \<Longrightarrow>
    list s p xs = (\<exists>ys. xs = p # ys \<and> is_valid_blist_C s p \<and> list s (next_C (heap_blist_C s p)) ys)"
  oops (* TODO *)

(* 2-d *)
lemma list_unique:
  "list s p xs \<Longrightarrow> list s p ys \<Longrightarrow> xs = ys"
  sorry (* TODO *)

(* 2-e *)
lemma list_distinct[simp]:
  "list s p xs \<Longrightarrow> distinct xs"
  oops (* TODO *)

(* 2-f *)
lemma list_notin_update_eq[simp]:
  "q \<notin> set xs \<Longrightarrow>
   list (heap_blist_C_update (\<lambda>h. h (q := next_C_update (\<lambda>_. v) (h q))) s) p xs = list s p xs"
  oops (* TODO *)

definition the_list :: "lifted_globals \<Rightarrow> blist_C ptr \<Rightarrow> blist_C ptr list" where
  "the_list s p = (THE xs. list s p xs)"

lemma the_list_val [simp]: "list s p xs \<Longrightarrow> the_list s p = xs"
  apply (clarsimp simp: the_list_def)
  apply (metis (lifting) list_unique the_equality)
  done

(* 2-g *)
lemma the_list_notin_update_eq[simp]:
   "\<lbrakk> q \<notin> set xs; list s p xs \<rbrakk> \<Longrightarrow>
     the_list (heap_blist_C_update (\<lambda>h. h (q := next_C_update (\<lambda>_. v) (h q))) s) p = the_list s p"
  oops (* TODO *)

context gc begin

thm append'_def
thm append_step'_def
thm mark'_def

term append'
term mark'

(* 2-h *)
lemma append_step_correct:
"\<lbrace> \<lambda>s. p \<noteq> NULL \<and> list s p Ps \<and> list s q Qs \<and> set Ps \<inter> set Qs = {} \<rbrace>
   append_step' p q
 \<lbrace> \<lambda>r s. list s r (tl Ps) \<and> list s p (p#Qs)\<rbrace>!"
  unfolding append_step'_def
  oops (* TODO *)

(* 2-i & 2-j *)
lemma append_correct:
"\<lbrace> \<lambda>s. TODO \<rbrace>
   append' p q
 \<lbrace> \<lambda>r s. list s r (rev Ps @ Qs) \<rbrace>!"
  unfolding append'_def append_step'_def bind_assoc K_bind_def
  apply (subst whileLoop_add_inv
    [where I = TODO
       and M = TODO])
  apply (wp validNF_whileLoop_inv_measure_twosteps)
  oops (* TODO *)

end

(* ------------------- *)

(* 2-k *)
primrec mkd_list :: "lifted_globals \<Rightarrow> block_C ptr \<Rightarrow> block_C ptr list \<Rightarrow> bool" where
  undefined (* TODO *)


definition the_mkd_list :: "lifted_globals \<Rightarrow> block_C ptr \<Rightarrow> block_C ptr list" where
  "the_mkd_list s p = (THE xs. mkd_list s p xs)"

(* 2-l *)
lemma mkd_list_unique:
  "mkd_list s p xs \<Longrightarrow> mkd_list s p ys \<Longrightarrow> xs = ys"
  oops (* TODO *)

(* ------------------- *)

definition block_in_list :: "lifted_globals \<Rightarrow> blist_C ptr \<Rightarrow> block_C ptr \<Rightarrow> bool" where
  "block_in_list s p b \<equiv> (\<exists>xs q. list s p xs \<and> q \<in> set xs \<and> b = this_C (heap_blist_C s q))"

(* 2-m *)
inductive_set b_reach :: "lifted_globals \<Rightarrow> blist_C ptr \<Rightarrow> (block_C ptr) set" for s r where
  undefined (* TODO *)


(* 2-n *)
lemma b_reach_subset:
  "x \<in> b_reach s rts \<Longrightarrow>
     block_in_list s rts x \<or> (\<exists>block. block_in_list s (nexts_C (heap_block_C s block)) x)"
  oops (* TODO *)



context gc begin

thm mark'_def

(* 2-o *)
lemma mark_correct:
"\<lbrace> \<lambda>s. list s rts roots \<and> R = b_reach s rts \<and>
   (\<forall>p. is_valid_block_C s p \<longrightarrow> flag_C (heap_block_C s p) = 0) \<rbrace>
   mark' rts
 \<lbrace> \<lambda>r s. TODO \<rbrace>!" (* TODO *)
  unfolding mark'_def
  oops (* state the post-condition, but no need to prove the lemma for the assignment *)

end

end