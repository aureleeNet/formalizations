theory extensions
  imports base 
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=2] (*default settings*)

(************** Extension-based semantics for argumentation frameworks******************)
named_theorems Defs

(* An argumentation frame(work) AF is completely characterized in HOL by its underlying relation "att",
   since the set of arguments (the carrier of att) is given implicitly as type domain. *)
type_synonym 'a \<A>\<F> = \<open>'a Rel\<close>

(* page 3 of [BCG2011] *)
definition plusset :: \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("[_|_]\<^sup>+") where \<open>[AF|Arg]\<^sup>+ \<equiv> \<lambda>b. \<exists>a. Arg a \<and> AF a b\<close>
definition minusset:: \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("[_|_]\<^sup>-") where \<open>[AF|Arg]\<^sup>- \<equiv> \<lambda>b. \<exists>a. Arg a \<and> AF b a\<close>
declare plusset_def[Defs] minusset_def[Defs]

(* Definition 6 (1). (Dung 1995)
A set S of arguments defends an argument A iff each argument B attacking A is itself attacked by
(at least one argument in) S.*)
definition defends :: \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> 'a \<Rightarrow> bool\<close> 
  where \<open>defends AF S a \<equiv> \<forall>b. AF b a \<longrightarrow> (\<exists>z. S z \<and> AF z b)\<close>
declare defends_def[Defs]

lemma defends_def2: "defends AF S a = [AF|\<lbrace>a\<rbrace>]\<^sup>- \<subseteq> [AF|S]\<^sup>+"
  by (simp add: defends_def minusset_def plusset_def)

(*Definition 16 [Dung1995]. The characteristic function, denoted by \<F>, of an argumentation
framework AF = (AR, attacks) is defined as follows: \<F>(S) = {A | A is defended by S}*)
abbreviation \<F>::"'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> 'a Set" where "\<F> \<equiv> defends"

(*\<F> is monotonic (i.e. order preserving wrt. set inclusion)*)
lemma \<F>_mono: "MONO (\<F> AF)" unfolding MONO_def by (metis defends_def)

(*We can in fact verify that \<F> has both a least and a greatest fixed point*)
lemma \<F>_leastFP_ex: \<open>\<exists>S. least (fixpoint (\<F> AF)) S id\<close> by (simp add: \<F>_mono wKTl)
lemma \<F>_greatestFP_ex: \<open>\<exists>S. greatest (fixpoint (\<F> AF)) S id\<close> by (simp add: \<F>_mono wKTg)

(*Recalling that least/greatest elements are unique we can define
  "the least/greatest fixed point of (the characteristic function of) AF"*)
definition "tlfp AF \<equiv> THE S. least (fixpoint (\<F> AF)) S id"
definition "tgfp AF \<equiv> THE S. greatest (fixpoint (\<F> AF)) S id"

(*Conflict-freeness*)

(* Def 12 of [BCG2011] A set S of arguments is said to be conflict-free if there are no
arguments A and B in S such that A attacks B.*)
definition conflictfree_ext :: \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>conflictfree_ext AF S \<equiv> \<forall>a b. (S a \<and> S b) \<longrightarrow> \<not>(AF a b)\<close>
declare conflictfree_ext_def[Defs]

(*the greatest fixed point is not conflict-free. What about the least? *)
lemma "conflictfree_ext AF (tgfp AF)" nitpick oops
lemma "conflictfree_ext AF (tlfp AF)" (*nitpick*) oops

(* Definition 6 (2). (Dung 1995)
A conflict-free set of arguments S is admissible if each argument in S is
defended by S. *)

definition admissible_ext :: \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> bool\<close> 
  where \<open>admissible_ext AF S \<equiv> conflictfree_ext AF S \<and> (\<forall>a. S a \<longrightarrow> defends AF S a)\<close>
declare admissible_ext_def[Defs]

(*Definition 23 (Dung 1995). An admissible set S of arguments is called a complete extension iff
each argument, which is defended by S, belongs to S.*)
definition complete_ext :: \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> bool\<close> 
  where \<open>complete_ext AF S \<equiv> admissible_ext AF S \<and> (\<forall>a. defends AF S a \<longrightarrow> S a)\<close>
declare complete_ext_def[Defs]

(*complete extensions are precisely the conflict-free fixed points of \<F>*)
lemma complete_ext_def2: "complete_ext AF S = (conflictfree_ext AF S \<and> fixpoint (\<F> AF) S)" 
  by (metis admissible_ext_def complete_ext_def fixpoint_def)

(*Definition 7 (Dung 1995). A preferred extension of an argumentation framework AF is a maximal
(with respect to set inclusion) admissible set of AF.*)
definition preferred_ext ::  \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where "preferred_ext AF S \<equiv> maximal (admissible_ext AF) S id"
declare preferred_ext_def[Defs]

(*just to check*)
lemma "preferred_ext AF S = (admissible_ext AF S \<and> (\<forall>Q. admissible_ext AF Q \<and> S \<subseteq> Q  \<longrightarrow> Q \<approx> S))"
  by (simp add: preferred_ext_def maximal_def)

(*preferred extensions are complete*)
lemma "preferred_ext AF S \<longrightarrow> complete_ext AF S"
  unfolding preferred_ext_def complete_ext_def maximal_def id_def
  by (smt (z3) defends_def admissible_ext_def conflictfree_ext_def)

(*Definition 20 (Dung 1995) The grounded extension of an argumentation framework AF
 is the least fixed point of \<F> *)
definition grounded_ext ::  \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where "grounded_ext AF S \<equiv> least (fixpoint (\<F> AF)) S id"
declare grounded_ext_def[Defs]

lemma grounded_ext_def2: "grounded_ext AF S = minimal (fixpoint (\<F> AF)) S id" 
  unfolding grounded_ext_def tlfp_def by (metis leastMin minLeastCollapse \<F>_leastFP_ex)

lemma "grounded_ext AF S \<longrightarrow> (S \<approx> tlfp AF)" unfolding grounded_ext_def oops (*TODO just a nice-to-have*)

(*grounded extensions are conflict-free*)
lemma groundedConflictfree: "grounded_ext AF S \<longrightarrow> conflictfree_ext AF S"
  unfolding grounded_ext_def2 minimal_def conflictfree_ext_def fixpoint_def sorry (*TODO prove*)

(*grounded extensions are complete*)
lemma groundedComplete: "grounded_ext AF S \<longrightarrow> complete_ext AF S" 
  using groundedConflictfree by (metis complete_ext_def2 grounded_ext_def least_def) 


(**TODO: to be continued...**)
end