theory a1
imports Main
begin

section "Q1: Types"

(* TODO: provide your answers here or in an separate PDF file *)


section "Q2: @text \<lambda>-Calculus"

text \<open> Question 2 (a) \<close>

definition "true \<equiv> \<lambda>x y. x"
definition "false \<equiv> \<lambda>x y. y"
definition "ifthen \<equiv> \<lambda>z x y. z x y"
definition "mynot \<equiv> \<lambda>x. ifthen x false true"

definition "myxor \<equiv> TODO"


text \<open> Question 2 (b) \<close>

(* TODO: provide your answers here or in an separate PDF file *)


text \<open> Question 2 (c) \<close>

thm refl

lemma "myxor = (\<lambda>x y.  x (y false true) y)"
  oops

lemma "myxor false y = y"
  oops

lemma "myxor true y = mynot y"
  oops

section "Q3: Propositional Logic"

(*
You must use only these proof methods:
  - rule, erule, assumption, cases, frule, drule,
    rule_tac, erule_tac, frule_tac, drule_tac, rename_tac, case_tac

You must use only these proof rules:
   - impI, impE, conjI, conjE, disjI1, disjI2, disjE, notI, notE
     iffI, iffE, iffD1, iffD2, ccontr, classical, FalseE,
     TrueI, conjunct1, conjunct2, mp
*)

lemma prop_a:
  "A \<or> B \<or> A \<longrightarrow> B \<or> A"
  oops


lemma prop_b:
  "(\<not>a \<longrightarrow> b) \<longrightarrow> \<not> b \<longrightarrow> a"
  oops


text\<open>Saying that if Alice is here then Bob is definitely not here is the same 
as saying that they can't both be here"\<close>
lemma prop_c:
  "TODO"
  oops


lemma prop_d:
  "(A \<and> B \<or> C) = ((A \<or> C) \<and> (B \<or> C))"
  oops


lemma prop_e:
  "(\<not>P \<and> Q) \<longrightarrow> (\<not>(R\<and>P)) \<and> (R\<longrightarrow>Q)"
  oops


text \<open>If either it is not raining or you have an umbrella then it is not possible 
     that you do not have an umbrella at a time where it is also raining."\<close>
lemma prop_f:
  "TODO"
  oops


lemma prop_g:
  "(((f\<longrightarrow>g)\<and>h\<longrightarrow>f)\<longrightarrow>g)=((f\<longrightarrow>g)\<and>(g\<or>h))"
  oops


section "Q4: Higher-Order Logic"

(*
You must use only these proof methods:
  - rule, erule, assumption, frule, drule,
    rule_tac, erule_tac, frule_tac, drule_tac, rename_tac, case_tac
You must use only these proof rules:
   - impI, impE, conjI, conjE, disjI1, disjI2, disjE, notI, notE
     iffI, iffE, iffD1, iffD2, ccontr, classical, FalseE,
     TrueI, conjunct1, conjunct2, mp;
   - allI, allE, exI, and exE
*)


lemma hol_a:
  " (\<forall>x. \<not> P x) = (\<not>(\<exists>x. P x))"
  oops


lemma hol_b:
  "(\<forall>x. B x) \<or> (\<forall>y. A y) \<longrightarrow>(\<forall>x y. A y \<or> B x) " 
  oops

lemma hol_c:
  "(\<forall>x y. A y \<or> B x) \<longrightarrow> (\<forall>x. B x) \<or> (\<forall>y. A y)" 
  oops

text\<open>If any proposition is true then the value True is 
the same as the value False"\<close>
lemma hol_d:
  "TODO"
  oops

lemma hol_e:
  "((\<exists>x. A x)\<longrightarrow>\<not>C) \<longrightarrow> (\<forall>x. B x \<longrightarrow> A x) \<longrightarrow> (\<exists>x. B x) \<longrightarrow> \<not>C"
  oops

lemma hol_f:
  "(\<forall>x. \<not> R x x) \<longrightarrow> \<not>(\<forall>x y. \<not> R x y \<longrightarrow> R y x)"
  oops

end
