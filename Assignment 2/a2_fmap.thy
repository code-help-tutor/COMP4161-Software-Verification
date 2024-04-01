theory a2_fmap
  imports Main
begin


(* Q1: Finite map library *)

typedef ('a, 'b) fmap = "{m. finite (dom m)} :: ('a \<rightharpoonup> 'b) set"
  morphisms lookup Abs_fmap
proof
  show "Map.empty \<in> {m. finite (dom m)}"
    by auto
qed
print_theorems

(* 1-a *)

text \<open>
Explain how the type @{term fmap} is defined as an example of what you learned in
 the lecture.
Also give a brief description of the lemmas Isabelle generates.
What exactly is @{term lookup}?
\<close>

(* TODO : write the answer in the below as text *)

text \<open>


\<close>



declare Abs_fmap_inverse[simp]
declare lookup_inverse[simp]

lemma dom_lookup_finite[intro, simp]: "finite (dom (lookup m))"
  using lookup by auto

(* 1-b *)
lemma lookup_ext: 
  "(\<And>x. lookup f x = lookup g x) \<Longrightarrow> f = g"
  (* TODO *)
  sorry



(* fdom *)

definition fdom :: "('a, 'b) fmap \<Rightarrow> 'a set" where
  "fdom f \<equiv> dom (lookup f)"

lemma fdom_finite: "finite (fdom f)"
  by (simp add: fdom_def)

lemma lookup_fdom_iff: "lookup f x \<noteq> None \<longleftrightarrow> x \<in> fdom f"
  by (rule iffI; simp add: fdom_def dom_def)

lemma fdomI: "lookup f x = Some y \<Longrightarrow> x \<in> fdom f"
  by (simp add: lookup_fdom_iff[symmetric])

lemma fdom_notI: "lookup m x = None \<Longrightarrow> x \<notin> fdom m" by (simp add: lookup_fdom_iff[symmetric])
lemma fdom_notD[dest]: "x \<notin> fdom m \<Longrightarrow> lookup m x = None" by (simp add: lookup_fdom_iff[symmetric])

lemma fdomE[elim]: "x \<in> fdom f \<Longrightarrow> (\<And>x y. lookup f x = Some y \<Longrightarrow> R) \<Longrightarrow> R"
  by (auto simp: lookup_fdom_iff[symmetric])

lemma finite_fdom[simp]: "finite (fdom m)"
  by (auto simp: fdom_def lookup[simplified])

(* fran *)

definition fran :: "('a, 'b) fmap \<Rightarrow> 'b set" where
  "fran f \<equiv> ran (lookup f)"

lemma lookup_ran_iff: "y \<in> fran m \<longleftrightarrow> (\<exists>x. lookup m x = Some y)"
  by (auto simp: ran_def fran_def)

lemma franI: "lookup m x = Some y \<Longrightarrow> y \<in> fran m"
   by (auto simp: lookup_ran_iff)

lemma franE[elim]:
  assumes "y \<in> fran m"
  obtains x where "lookup m x = Some y"
using assms by (auto simp: lookup_ran_iff)

(* fempty *)

definition fempty :: "('a, 'b) fmap" where
  "fempty \<equiv> Abs_fmap Map.empty"

lemma fempty_lookup[simp]: "lookup fempty x = None"
  by (simp add: fempty_def)

lemma fdom_empty[simp]: "fdom fempty = {}" by (simp add: fempty_def fdom_def)
lemma fran_empty[simp]: "fran fempty = {}" by (auto simp: fran_def fempty_def)

(* fupd *)

definition fupd :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" where
  "fupd k v f \<equiv> Abs_fmap ((lookup f)(k \<mapsto> v))"

lemma fupd_lookup[simp]:
  "lookup (fupd a b f) x = (if a = x then Some b else lookup f x)"
  apply (simp add: fupd_def)
  done

lemma fmdom_fmupd[simp]: "fdom (fupd a b m) = insert a (fdom m)"
  by (auto simp: fdom_def dom_def)

lemma fmupd_idem[simp]: "fupd a x (fupd a y m) = fupd a x m"
  by (simp add: fupd_def)

(* fmap_filter *)

definition fmap_filter :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" where
"fmap_filter P m = Abs_fmap (\<lambda>x. if P x then (lookup m x) else None)"

lemma if_lookup[simp]: "finite (dom (\<lambda>x. if P x then lookup f x else None))"
  apply (simp add: dom_def imp_conj_iff split: if_splits)
  apply (rule_tac B="{a. \<exists>y. lookup f a = Some y}" in finite_subset)
   apply (simp add: Collect_mono_iff)
  apply (insert dom_lookup_finite[of f])
  by (simp add: dom_def)

(* 1-c *)
lemma fdom_filter[simp]: "fdom (fmap_filter P m) = Set.filter P (fdom m)"
  (* TODO *)
  sorry

lemma lookup_filter[simp]:
  "lookup (fmap_filter P m) x = (if P x then lookup m x else None)"
  by (auto simp: fmap_filter_def)

lemma fmap_filter_empty[simp]: "fmap_filter P fempty = fempty"
  apply (rule lookup_ext)
  by (auto simp: fmap_filter_def fempty_def split:if_splits)

lemma fmap_filter_true[simp]:
  assumes "\<And>x y. lookup m x = Some y \<Longrightarrow> P x"
  shows "fmap_filter P m = m"
  using assms apply -
  apply (rule lookup_ext)
  apply clarsimp
  apply (drule_tac x=x in meta_spec)
  apply (case_tac "lookup m x"; simp)
  done

lemma fmap_filter_false[simp]:
  assumes "\<And>x y. lookup m x = Some y \<Longrightarrow> \<not> P x"
  shows "fmap_filter P m = fempty"
  using assms
  apply (simp add: fmap_filter_def fempty_def)
  apply (rule arg_cong[where f=Abs_fmap])
  apply (rule ext; simp)
  apply (drule_tac x=x in meta_spec)
  apply (case_tac "lookup m x"; simp)
  done

lemma fmap_filter_comp[simp]: "fmap_filter P (fmap_filter Q m) = fmap_filter (\<lambda>x. P x \<and> Q x) m"
  apply (simp add: fmap_filter_def)
  apply (rule arg_cong[where f=Abs_fmap])
  apply (rule ext; simp)
  done

lemma fmap_filter_cong[cong]:
  assumes "\<And>x y. lookup m x = Some y \<Longrightarrow> P x = Q x"
  shows "fmap_filter P m = fmap_filter Q m"
proof (rule lookup_ext)
  fix x
  have "lookup m x = None" if "P x \<noteq> Q x"
    using that assms by fastforce
  then show "lookup (fmap_filter P m) x = lookup (fmap_filter Q m) x"
    by auto
qed

lemma fmap_filter_comm: "fmap_filter P (fmap_filter Q m) = fmap_filter Q (fmap_filter P m)"
  unfolding fmap_filter_comp
  apply (rule fmap_filter_cong)
  by auto

lemma fmap_filter_upd[simp]:
  "fmap_filter P (fupd x y m) = (if P x then fupd x y (fmap_filter P m) else fmap_filter P m)"
  apply (clarsimp simp: fupd_def fmap_filter_def)
  apply safe
  apply (rule lookup_ext, simp)
  apply (rule lookup_ext, simp)
  apply auto
  done

(* frestrict_set *)

definition frestrict_set :: "'a set \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" where
  "frestrict_set A \<equiv> fmap_filter (\<lambda>a. a \<in> A)"

lemma fdom_restrict_set_precise: "fdom (frestrict_set A m) = fdom m \<inter> A"
  apply (simp add: fdom_def frestrict_set_def)
  by (auto split: if_splits)

lemma fdom_restrict_set: "fdom (frestrict_set A m) \<subseteq> A"
  by (simp add: fdom_restrict_set_precise)

lemma lookup_frestrict_set[simp]:
  "lookup (frestrict_set A m) x = (if x \<in> A then lookup m x else None)"
  by (simp add: frestrict_set_def)

lemma frestrict_set_dom[simp]: "frestrict_set (fdom m) m = m"
by (rule lookup_ext) auto

lemma frestrict_set_empty[simp]: "frestrict_set A fempty = fempty"
  unfolding fempty_def frestrict_set_def fmap_filter_def map_filter_def
  by (rule lookup_ext, auto)

lemma frestrict_set_null[simp]: "frestrict_set {} m = fempty"
  unfolding fempty_def frestrict_set_def fmap_filter_def map_filter_def
  by (rule lookup_ext, auto)

lemma frestrict_set_twice[simp]: "frestrict_set S (frestrict_set T m) = frestrict_set (S \<inter> T) m"
unfolding frestrict_set_def map_filter_def o_def by (rule lookup_ext; auto split: if_splits)

(* fmap_add *)

definition
  fmap_add :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"  (infixl "+++" 100) where
  "m1 +++ m2 = Abs_fmap (\<lambda>x. case lookup m2 x of None \<Rightarrow> lookup m1 x | Some y \<Rightarrow> Some y)"

lemma case_lookup'[simp]:
  "finite (dom (\<lambda>x. case lookup f x of None \<Rightarrow> lookup g x | Some y \<Rightarrow> Some y))"
  apply (simp add: dom_def imp_conv_disj split: option.splits)
  apply (fold dom_def[simplified], simp)
  done
lemma lookup_add[simp]:
  "lookup (m +++ n) x = (if x \<in> fdom n then lookup n x else lookup m x)"
  apply (auto simp: fmap_add_def fdom_def
              split: option.splits)
  done

lemma fdom_add[simp]: "fdom (m +++ n) = fdom m \<union> fdom n"
  apply (simp add: fmap_add_def fdom_def dom_def)
  apply (simp add: imp_conv_disj split: option.splits)
  apply auto
  done

lemma fmadd_restrict_right_dom: "frestrict_set (fdom n) (m +++ n) = n"
by (rule lookup_ext) auto

lemma fmap_filter_add_distrib[simp]:
  "fmap_filter P (m +++ n) = fmap_filter P m +++ fmap_filter P n"
  apply (rule lookup_ext)
  apply simp
  done
 
lemma frestrict_set_add_distrib[simp]:
  "frestrict_set A (m +++ n) = frestrict_set A m +++ frestrict_set A n"
  apply (simp add: frestrict_set_def)
  done

lemma fadd_empty[simp]: "fempty +++ m = m" "m +++ fempty = m"
  by (rule lookup_ext, auto)+

lemma fadd_idempotent[simp]: "m +++ m = m"
  by (rule lookup_ext) simp

lemma fadd_assoc[simp]: "m +++ (n +++ p) = m +++ n +++ p"
  by (rule lookup_ext) simp

lemma fadd_fupd[simp]: "m +++ fupd a b n = fupd a b (m +++ n)"
  by (rule lookup_ext) simp

lemma fmap_distinct[simp]:
  "fempty \<noteq> fupd k v m"
  "fupd k v m \<noteq> fempty"
   apply (simp_all add: fupd_def Abs_fmap_inject fempty_def)
  apply clarsimp
  apply (drule sym)
 apply (simp_all add: fupd_def Abs_fmap_inject fempty_def)
  done

(* fpred *)

definition fpred :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> bool" where
  "fpred P m \<equiv> (\<forall>x. case lookup m x of None \<Rightarrow> True | Some y \<Rightarrow> P x y)"

lemma fpredI[intro]:
  assumes "\<And>x y. lookup m x = Some y \<Longrightarrow> P x y"
  shows "fpred P m"
using assms
  by (auto simp: fpred_def split: option.splits)

lemma fpredD[dest]: "fpred P m \<Longrightarrow> lookup m x = Some y \<Longrightarrow> P x y"
  by (auto simp: fpred_def split: option.split_asm)

lemma fpred_iff: "fpred P m \<longleftrightarrow> (\<forall>x y. lookup m x = Some y \<longrightarrow> P x y)"
by auto

lemma fpred_mono_strong:
  assumes "\<And>x y. lookup m x = Some y \<Longrightarrow> P x y \<Longrightarrow> Q x y"
  shows "fpred P m \<Longrightarrow> fpred Q m"
using assms unfolding fpred_iff by auto

lemma fpred_mono[mono]: "P \<le> Q \<Longrightarrow> fpred P \<le> fpred Q"
apply rule
apply (rule fpred_mono_strong[where P = P and Q = Q])
apply auto
done

lemma fpred_empty[intro!, simp]: "fpred P fempty"
by auto

lemma fpred_upd[intro]: "fpred P m \<Longrightarrow> P x y \<Longrightarrow> fpred P (fupd x y m)"
by (auto simp: fpred_def fupd_def)

lemma fpred_updD[dest]: "fpred P (fupd x y m) \<Longrightarrow> P x y"
by auto

lemma fpred_add[intro]: "fpred P m \<Longrightarrow> fpred P n \<Longrightarrow> fpred P (m +++ n)"
  by (auto simp: fpred_def map_add_def split: option.splits)

lemma fpred_filter[intro]: "fpred P m \<Longrightarrow> fpred P (fmap_filter Q m)"
  by (auto simp: fpred_def map_filter_def)

lemma fpred_restrict_set[intro]: "fpred P m \<Longrightarrow> fpred P (frestrict_set A m)"
by (auto simp: frestrict_set_def)

(* fmap_of *)

definition fmap_of :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) fmap" where
  "fmap_of ls \<equiv> Abs_fmap (map_of ls)"

(* 1-d *)
lemma fmap_of_simps[simp]:
  "fmap_of [] = fempty"
  "fmap_of ((k, v) # kvs) = fupd k v (fmap_of kvs)"
  (* TODO *)
  sorry




(* fmap_keys *)

definition fmap_keys :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'c) fmap" where
  "fmap_keys f m \<equiv> Abs_fmap (\<lambda>a. map_option (f a) (lookup m a))"

lemma map_option_fmap_finite: "finite (dom (\<lambda>a. map_option (f a) (lookup m a)))"
  apply (rule_tac B="dom (lookup m)" in finite_subset)
    apply (simp add: dom_def)
   apply simp
  done    

lemma fdom_fmap_keys[simp]: "fdom (fmap_keys f m) = fdom m"
  by (auto simp: fmap_keys_def fdom_def map_option_fmap_finite)

lemma lookup_fmap_keys[simp]: "lookup (fmap_keys f m) x = map_option (f x) (lookup m x)"
  by (simp add: fmap_keys_def map_option_fmap_finite)

(* 1-e *)
lemma fpred_fmap_keys[simp]: "fpred P (fmap_keys f m) = fpred (\<lambda>a b. P a (f a b)) m"
  (* TODO *)
  sorry



(* fmmap *)

definition fmmap :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'c) fmap" where
  "fmmap f \<equiv> Abs_fmap o (o) (map_option f) o lookup"

(* 1-f *)
lemma lookup_map[simp]: "lookup (fmmap f m) x = map_option f (lookup m x)"
  (* TODO *)
  sorry




end