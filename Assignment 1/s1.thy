theory s1
imports Main
begin


text \<open> Question 1 (a) \<close>

text \<open>

Let \<Gamma>' = \<Gamma>, [x::\<tau>1, y:\<tau>2, z:\<tau>3] 

[1] assuming \<tau>3 = \<tau>6\<Rightarrow>\<tau>5\<Rightarrow>\<tau>4
[2] assuming \<tau>6 = \<tau>1
[3] assuming \<tau>8 = \<tau>2
[4] assuming \<tau>7 = \<tau>2
[*] assuming \<Gamma>(a) =  \<tau>8\<Rightarrow>\<tau>7\<Rightarrow>\<tau>5


   [1]                      [2]
----------------- Var  -------------Var
\<Gamma>' \<turnstile> z::\<tau>6\<Rightarrow>\<tau>5\<Rightarrow>\<tau>4       \<Gamma>' \<turnstile> x :: \<tau>6                     \<Theta>
-------------------------------------- App         ---------------
\<Gamma>' \<turnstile> z x :: \<tau>5\<Rightarrow>\<tau>4                                  \<Gamma>' \<turnstile> a y y: \<tau>5
---------------------------------------------------------------------- App
\<Gamma>, [x::\<tau>1, y:\<tau>2, z:\<tau>3] \<turnstile>  z x (a y y) :: \<tau>4
-------------------------------------------------------- Abs
\<Gamma>, [x::\<tau>1, y:\<tau>2] \<turnstile>  \<lambda>z. z x (a y y) :: \<tau>3 \<Rightarrow> \<tau>4
-------------------------------------------------------- Abs
\<Gamma>, [x::\<tau>1] \<turnstile> \<lambda>y z. z x (a y y) :: \<tau>2 \<Rightarrow> \<tau>3 \<Rightarrow> \<tau>4
-------------------------------------------------------- Abs
\<Gamma> \<turnstile> \<lambda>x y z. z x (a y y) :: \<tau>1 \<Rightarrow> \<tau>2 \<Rightarrow> \<tau>3 \<Rightarrow> \<tau>4

where \<Theta> is the following subtree:

    [*]                     [3]
-------------------Var  ------------Var
\<Gamma>' \<turnstile> a :: \<tau>8\<Rightarrow>\<tau>7\<Rightarrow>\<tau>5      \<Gamma>' \<turnstile> y :: \<tau>8         [3]
----------------------------------App    --------------Var
\<Gamma>' \<turnstile> a y :: \<tau>7 \<Rightarrow> \<tau>5                       \<Gamma>' \<turnstile> y :: \<tau>7
--------------------------------------------------------App
\<Gamma>' \<turnstile> a y y :: \<tau>5

Putting everything together, the term  \<lambda>x y z. z x (a y y)
is type correct with type 
  \<tau>1 \<Rightarrow> \<tau>2 \<Rightarrow> (\<tau>1\<Rightarrow>\<tau>5\<Rightarrow>\<tau>4) \<Rightarrow> \<tau>4

in contexts where a has type \<tau>2\<Rightarrow>\<tau>2\<Rightarrow>\<tau>5. 

This is also a most general type for this term.



Or: Direct tree: 

                             -----------Var  ------Var
                             \<Gamma>'\<turnstile>a::\<beta>\<Rightarrow>\<beta>\<Rightarrow>\<delta>   \<Gamma>'\<turnstile>y::\<beta>
----------- Var -------Var   ------------------------    ------Var
\<Gamma>'\<turnstile>z::\<alpha>\<Rightarrow>\<delta>\<Rightarrow>\<gamma>    \<Gamma>'\<turnstile>x::\<alpha>      \<Gamma>' \<turnstile> a y :: \<beta>\<Rightarrow>\<delta>           \<Gamma>'\<turnstile>y::\<beta>  
----------------------- App   ----------------------
\<Gamma>' \<turnstile> z x :: \<delta>\<Rightarrow>\<gamma>                   \<Gamma>' \<turnstile> a y y: \<delta>
---------------------------------------------------------------------- App
\<Gamma>, [x::\<alpha>,y:\<beta>,z:\<alpha>\<Rightarrow>\<delta>\<Rightarrow>\<gamma>] \<turnstile> z x (a y y)::\<gamma>
-------------------------------------------------------- Abs
\<Gamma>, [x::\<alpha>,y:\<beta>] \<turnstile>  \<lambda>z. z x (a y y) :: (\<alpha>\<Rightarrow>\<delta>\<Rightarrow>\<gamma>)\<Rightarrow>\<gamma>
-------------------------------------------------------- Abs
\<Gamma>, [x::\<alpha>] \<turnstile> \<lambda>y z. z x (a y y) :: \<beta>\<Rightarrow>(\<alpha>\<Rightarrow>\<delta>\<Rightarrow>\<gamma>)\<Rightarrow>\<gamma>
-------------------------------------------------------- Abs
\<Gamma> \<turnstile> \<lambda>x y z. z x (a y y) :: \<alpha>\<Rightarrow>\<beta>\<Rightarrow>(\<alpha>\<Rightarrow>\<delta>\<Rightarrow>\<gamma>)\<Rightarrow>\<gamma>

\<close>
context
notes [[show_types]]
begin
term "\<lambda>x y z. z x (a y y)"
end


text \<open> Question 1 (b) \<close>


text \<open>
The following term has type @{typ "('a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c"}
\<close>
term "\<lambda>x y z. x y y z"




text \<open> Question 2 (a) \<close>

text \<open> 
true = \<lambda>x y. x
false = \<lambda>x y. y
ifthen = \<lambda> z x y. z x y
not = \<lambda>x. if x false  true
\<close>

definition "true \<equiv> \<lambda>x y. x"
definition "false \<equiv> \<lambda>x y. y"
definition "ifthen \<equiv> \<lambda>z x y. z x y"
definition "mynot \<equiv> \<lambda>x. ifthen x false true"

definition "myxor \<equiv> \<lambda>x y. ifthen x (mynot y) y"


text \<open> Question 2 (b) \<close>

text \<open>

xor =
\<lambda>x y. ifthen x (not y) y  
=   \<lambda>x y. (\<lambda>z x y. z x y) x (not y) y  
=\<beta>  \<lambda>x y.  x (not y) y 
=   \<lambda>x y.  x ((\<lambda>x. ifthen x false true) y) y 
=\<beta>  \<lambda>x y.  x (ifthen y false true) y 
=   \<lambda>x y.  x ((\<lambda>z x y. z x y) y false true) y 
=\<beta>  \<lambda>x y.  x (y false true) y 
 

xor false y 
=   (\<lambda>x y.  x (y false true) y) false y  
=\<beta>  false (y false true) y 
=   (\<lambda>x y. y) (y false true) y 
=\<beta>  y

xor true y 
=   (\<lambda>x y.  x (y false true) y) true y  
=\<beta>  true (y false true) y 
=   (\<lambda>x y. x) (y false true) y 
=\<beta>  y false true
 
and 

not y 
=   (\<lambda>x. ifthen x false true) y
=\<beta>  ifthen y false true 
=   (\<lambda>z x y. z x y) y false true 
=\<beta>  y false true

\<close>

text \<open> Question 2 (c) \<close>

thm refl

text \<open>The theorem \texttt{refl} states that equality is reflexive, i.e. 
   that every term is equal to itself. The theorem can be used to prove the lemmas because
   equality in Isabelle is modulo \<beta> conversion and the lemmas are equalities between
   terms that are \<beta>-equivalent as we have shown.\<close>

lemma "myxor = (\<lambda>x y.  x (y false true) y)"
  apply (unfold myxor_def ifthen_def mynot_def)
  apply (rule refl)
  done
  
lemma "myxor false y = y"
  apply (unfold myxor_def ifthen_def false_def)
  apply (rule refl)
  done

lemma "myxor true y = mynot y"
  apply (unfold myxor_def ifthen_def true_def)
  apply (rule refl)
  done




text \<open> Question 3 \<close>

lemma prop_a:
  "A \<or> B \<or> A \<longrightarrow> B \<or> A"
  apply (rule impI)
  apply (erule disjE)
   apply (rule disjI2, assumption)
  apply assumption
  done

lemma prop_b:
  "(\<not>a \<longrightarrow> b) \<longrightarrow> \<not> b \<longrightarrow> a"
  apply (rule impI)
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE, assumption)
  apply (erule notE)
  apply assumption
  done

text\<open>Saying that if Alice is here then Bob is definitely not here is the same 
as saying that they can't both be here"\<close>
 
lemma prop_c:
  "(A\<longrightarrow>\<not>B) = (\<not>(A\<and>B))"
  apply (rule iffI)
   apply (rule notI)
   apply (erule conjE)
   apply (erule impE, assumption)
  apply (erule notE, assumption)
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply (rule conjI, assumption)
  apply assumption
  done


lemma prop_d:
  "(A \<and> B \<or> C) = ((A \<or> C) \<and> (B \<or> C))"
  apply (rule iffI)
   apply (rule conjI)
    apply (erule disjE)
     apply (erule conjE)
     apply (rule disjI1, assumption)
    apply (rule disjI2, assumption)
   apply (erule disjE)
    apply (erule conjE)
    apply (rule disjI1, assumption)
   apply (rule disjI2, assumption)
  apply (erule conjE) 
  apply (erule disjE) 
   apply (erule disjE) 
  apply (rule disjI1, rule conjI, assumption, assumption)
   apply (rule disjI2, assumption)
  apply (rule disjI2, assumption)
  done

lemma prop_e:
  "(\<not>P \<and> Q) \<longrightarrow> (\<not>(R\<and>P)) \<and> (R\<longrightarrow>Q)"
  apply (rule impI)
  apply (erule conjE)
  apply (case_tac R) 
   apply (rule conjI)
    apply (rule notI)
    apply (erule conjE)
    apply (erule notE, assumption)
   apply (rule impI, assumption)
  apply (rule conjI)
  apply (rule notI, erule conjE, erule notE, assumption)
  apply (rule impI, erule notE, assumption)
  done


text \<open>If either it is not raining or you have an umbrella then it is not possible 
     that you do not have an umbrella at a time where it is also raining."\<close>

lemma prop_f:
  " \<not>raining \<or> umbrella \<longrightarrow> \<not>(\<not>umbrella \<and> raining) "
  apply (rule impI)
  apply (rule notI, erule conjE)
  apply (erule disjE)
   apply (erule notE, assumption)
  apply (erule notE, assumption)
  done


lemma prop_g:
  "(((f\<longrightarrow>g)\<and>h\<longrightarrow>f)\<longrightarrow>g)=((f\<longrightarrow>g)\<and>(g\<or>h))"
  apply (rule iffI)
    apply (rule conjI)
    apply (rule impI)
    apply (erule impE)
     apply (rule impI)
     apply assumption
    apply assumption
   apply (case_tac h)
    apply (rule disjI2, assumption)
  apply (rule disjI1)
   apply (erule impE)
    apply (rule impI)
    apply (erule conjE)
    apply (erule notE, assumption)
   apply assumption
  apply (rule impI)
  apply (erule conjE)
  apply (erule disjE)
   apply assumption
  apply (erule impE, rule conjI, assumption, assumption)
  apply (erule impE, assumption)
  apply assumption
  done



text \<open> Question 4 \<close>


lemma hol_a:
  " (\<forall>x. \<not> P x) = (\<not>(\<exists>x. P x))"
  apply (rule iffI)
   apply (rule notI)
   apply (erule exE)
   apply (erule_tac x=x in allE)
   apply (erule notE, assumption)
  apply (rule allI)
  apply (rule notI)
  apply (erule notE)
  apply (rule exI, assumption)
  done


lemma hol_b:
  "(\<forall>x. B x) \<or> (\<forall>y. A y) \<longrightarrow>(\<forall>x y. A y \<or> B x) " 
  apply (rule impI)
  apply (rule allI)+
  apply (erule disjE)
   apply (erule allE, rule disjI2, assumption)
  apply (erule allE, rule disjI1, assumption)
  done

lemma hol_c:
  "(\<forall>x y. A y \<or> B x) \<longrightarrow> (\<forall>x. B x) \<or> (\<forall>y. A y)" 
  apply (rule impI)
  apply (case_tac "(\<forall>x. B x)") 
   apply (rule disjI1, assumption) 
  apply (rule disjI2) 
  apply (rule allI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule allI)
  apply (erule_tac x=x in allE)
  apply (erule_tac x=y in allE)
  apply (erule disjE)
  apply (erule notE, assumption)
  apply assumption
  done

text\<open>If any proposition is true then the value True is 
the same as the value False"\<close>
lemma hol_d:
  "(\<forall>P. P) \<longrightarrow> (True = False)"
  apply (rule impI)
  apply (rule iffI)
   apply (erule_tac x=False in allE)
   apply assumption
  apply (rule TrueI)
  done

lemma hol_e:
  "((\<exists>x. A x)\<longrightarrow>\<not>C) \<longrightarrow> (\<forall>x. B x \<longrightarrow> A x) \<longrightarrow> (\<exists>x. B x) \<longrightarrow> \<not>C"
  apply (rule impI)+
  apply (erule impE)
   apply (erule exE)
   apply (erule allE, erule impE, assumption)
   apply (rule exI, assumption)
  apply assumption
  done


lemma hol_f:
  "(\<forall>x. \<not> R x x) \<longrightarrow> \<not>(\<forall>x y. \<not> R x y \<longrightarrow> R y x)"
  apply (rule impI)
  apply (rule notI)
  apply (erule allE)
  apply (erule allE)
  apply (erule allE)
  apply (erule impE)
   apply assumption
  apply (erule notE, assumption)
  done
  
end