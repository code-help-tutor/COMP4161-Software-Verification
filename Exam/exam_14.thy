theory exam_14
imports AutoCorres.AutoCorres
begin

text \<open> 
  This theory is designed to be loaded with the AutoCorres logic/image via e.g.
  
  L4V_ARCH=X64 isabelle jedit -d autocorres-1.9 -l AutoCorres exam_14.thy
OR:
  L4V_ARCH=ARM isabelle jedit -d autocorres-1.9 -l AutoCorres exam_14.thy

\<close>

section "Question 1: Lambda Calculus"

text \<open>
  (a) -- (c): Write your answers as Isabelle comments or include them in a separate .pdf 
              or .txt file.
\<close>

section "Question 2: Induction"

text \<open>
  (a-i)
\<close>

inductive_set pal_lists where
  pal_nil: "\<dots>"

text \<open>
  (a-ii)
\<close>

lemma pal_lists_Cons:
  "xs \<in> pal_lists ==> x # xs \<in> pal_lists"
  sorry

text \<open>
  (a-iii)
\<close>
lemma pal_univ: "xs \<in> pal_lists"
  sorry


text \<open>
  (a-iv)
\<close>

lemma pal_induct:
  assumes nil: "P []"
  assumes one: "\<And>x. P [x]"
  assumes two: "\<And>a xs b. P xs \<Longrightarrow> P (a # xs @ [b])"
  shows "P list"
  sorry

text \<open>
  (b)
\<close>

(* define palindrome *)


text \<open>
  (c)
\<close>

lemma pal_eq:
  "palindrome (a # xs @ [b]) \<Longrightarrow> a = b"
  sorry


text \<open>
  (d)
\<close>

text \<open>
  (e)
\<close>

lemma "palindrome xs = (xs \<in> palindromes)"
  sorry

section "C Verification"

external_file "divmod.c"
install_C_file "divmod.c"

autocorres [unsigned_word_abs = divmod even] "divmod.c"

context divmod begin

text \<open>
  (a) -- (b): Write your answers as Isabelle comments or include them in a separate .pdf 
              or .txt file.
\<close>

text \<open>
  (c)
\<close>
definition
  divmod_spec :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "divmod_spec n m domod \<equiv> if domod \<noteq> 0 then n mod m else n div m"

lemma divmod'_correct:
  "ovalid (\<lambda>_. True) (divmod' n m domod) (\<lambda>r s. r = divmod_spec n m domod)"
  sorry

text \<open>
  (d): replace PRE below with a suitable weakest precondition and prove it correct
\<close>

lemma divmod'_wp:
  "ovalid PRE (divmod' n m domod) Q"
  sorry

text \<open>
  (e)
\<close>
lemma even'_correct:
  "ovalid (\<lambda>_. True) (even' n) (\<lambda>r s. r = (if even n then 1 else 0))"
  sorry

text \<open>
  (f): Write your answer as an Isabelle comment or in a separate .pdf or .txt file
\<close>

end

text \<open> Bonus question: Recursive functions \<close>

datatype regexp =
   Atom char
 | Alt regexp regexp
 | Conc regexp regexp (infixl "\<cdot>"  60)
 | Star regexp
 | Neg regexp

(* Match everything: *)
definition
  "Univ = Alt (Neg (Atom (CHR ''x''))) (Atom (CHR ''x''))"

(* Match nothing: *)
definition
  "null = Neg Univ"

(* Match only the empty string: *)
definition
  "epsilon = Star null"

(* For examples/testing. *)
primrec string :: "char list \<Rightarrow> regexp"
  where
  "string []     = epsilon"
| "string (x#xs) = Atom x \<cdot> string xs"

(* Automatically coerce type "char list" into "regexp" using the function "string" *)
declare [[coercion string, coercion_enabled]]
term "Star ''abc''"

(* A set of strings repeated 0 or more times *)
inductive_set star :: "string set \<Rightarrow> string set" for L
  where
  star_empty[simp,intro!]: "[] \<in> star L"
| star_app[elim]: "\<lbrakk> u \<in> L; v \<in> star L \<rbrakk> \<Longrightarrow> u@v \<in> star L"

(* The concatenation of two sets of strings *)
definition conc :: "string set \<Rightarrow> string set \<Rightarrow> string set"
  where
  "conc A B \<equiv> { xs@ys |xs ys. xs \<in> A \<and> ys \<in> B}"

(* The sets of strings matched by an expression *)
primrec
  lang :: "regexp \<Rightarrow> string set"
  where
  "lang (Atom c) = {[c]}"
| "lang (Alt e1 e2) = lang e1 \<union> lang e2"
| "lang (Conc e1 e2) = conc (lang e1) (lang e2)"
| "lang (Star e) = star (lang e)"
| "lang (Neg e) = -lang e"

(* ------------------------------------------------------------ *)
(* New for the exam: *)

primrec split :: "('a list \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
  "split P Q xs [] = (P xs \<and> Q [])"
| "split P Q xs (y#ys) = (P xs \<and> Q (y#ys) \<or> split P Q (xs@[y]) ys)"

(* --------- 1a ------------ *)
lemma split_eq[simp]:
  "split P Q xs ys = (\<exists>as bs. ys = as @ bs \<and> P (xs@as) \<and> Q bs)"
  sorry (* TODO *)


lemma split_cong[fundef_cong,cong]:
  "\<lbrakk> xs = xs'; ys = ys'; P = P'; \<And>bs. length bs \<le> length ys' \<Longrightarrow> Q bs = Q' bs \<rbrakk> 
  \<Longrightarrow> split P Q xs ys = split P' Q' xs' ys'"
  by force

declare nat_le_Suc_less[simp]

(* Executable version of determining a regular expression match with negation. *)
fun matches :: "regexp \<Rightarrow> string \<Rightarrow> bool"
  where
  "matches (Atom c) cs     = (cs = [c])"
| "matches (Alt r1 r2) cs  = (matches r1 cs \<or> matches r2 cs)"
| "matches (Conc r1 r2) cs = split (matches r1) (matches r2) [] cs"
| "matches (Neg r) cs      = (\<not> matches r cs)"
| "matches (Star r) cs     = (cs \<noteq> [] \<longrightarrow> split (matches r) (matches (Star r)) [hd cs] (tl cs))"

(* Unfold matches_Star manually with "subst" *)
lemmas matches_Star[simp del] = matches.simps(5)

(* Examples *)
value "matches (Star (Alt ''ab'' ''a'')) ''''"
value "matches (Star (Alt ''ab'' ''a'')) ''ababa''"
value "matches (Star (Alt ''ab'' ''a'')) ''abba''"
value "matches (Neg (Star (Alt ''ab'' ''a''))) ''abba''"


(* --------- 1b ------------ *)

lemma matches_string:
  "matches (string xs) cs = (cs = xs)"
  sorry (* TODO: prove; find suitable helper lemmas *)


(* --------- 1c ------------ *)

lemma star_cons_append[elim]:
  "\<lbrakk> a # as \<in> L; bs \<in> star L\<rbrakk> \<Longrightarrow> a # as @ bs \<in> star L"
  sorry (* TODO *)

lemma star_cases:
  "xs \<in> star A \<Longrightarrow> xs = [] \<or> (\<exists>u v. xs = u@v \<and> u \<in> A \<and> v \<in> star A \<and> u \<noteq> [])"
  by (induct rule: star.induct) auto

lemma star_cons_case[dest!]:
  "x#xs \<in> star L \<Longrightarrow> (\<exists>u v. xs = u@v \<and> x#u \<in> L \<and> v \<in> star L)"
  sorry (* TODO *)

lemma matches_correct:
  "matches r cs = (cs \<in> lang r)"
  sorry (* TODO *)


end
