theory extensions
  imports base 
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=2] (*default settings*)

(************** Extension-based semantics for argumentation frameworks ******************)

(* Sources: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
  Knowledge Engineering Review. (2011)
 [Dung 1995] Dung, P.M., On the acceptability of arguments and its fundamental role in nonmonotonic reasoning,
  logic programming and n-person games, Artificial Intelligence. (1995)
*)

(* A set S of arguments defends an argument A iff each argument B attacking A is itself attacked by
at least one argument in S ([Dung 1995] Def. 6(1) and  [BCG 2011] Def. 11). *)
definition defends :: \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> 'a \<Rightarrow> bool\<close> 
  where \<open>defends AF S a \<equiv> \<forall>b. AF b a \<longrightarrow> (\<exists>z. S z \<and> AF z b)\<close>
declare defends_def[Defs]

lemma defends_def2: "defends AF S a = [AF|\<lbrace>a\<rbrace>]\<^sup>- \<subseteq> [AF|S]\<^sup>+"
  by (simp add: defends_def minusset_def plusset_def)

(* The characteristic function, denoted by \<F>, of an argumentation framework AF = (AR, attacks) is
 defined as \<F>(S) = {A | A is defended by S} ([BCG 2011] Def. 11). In fact, this corresponds to 'defends'.*)
abbreviation \<F> :: "'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> 'a Set" where "\<F> \<equiv> defends"

(* \<F> is monotone (i.e. order preserving wrt. set inclusion). *)
lemma \<F>_mono: "MONO (\<F> AF)" unfolding MONO_def by (metis defends_def)

(* We can in fact verify that \<F> has both a least and a greatest fixed point. *)
lemma \<F>_leastFP_ex: \<open>\<exists>S. least (fixpoint (\<F> AF)) S id\<close> by (simp add: \<F>_mono wKTl)
lemma \<F>_greatestFP_ex: \<open>\<exists>S. greatest (fixpoint (\<F> AF)) S id\<close> by (simp add: \<F>_mono wKTg)

(* Recalling that least/greatest elements are unique we can indeed define:
  "the least/greatest fixed point of \<F>".*)
definition "tlfp AF \<equiv> THE S. least (fixpoint (\<F> AF)) S id"
definition "tgfp AF \<equiv> THE S. greatest (fixpoint (\<F> AF)) S id"

(* A set S of arguments is said to be conflict-free if there are no arguments A and B in S 
  such that A attacks B ([Dung 1995] Def. 5 and [BCG 2011] Def. 12). *)
definition conflictfree_ext :: \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where \<open>conflictfree_ext AF S \<equiv> \<forall>a b. (S a \<and> S b) \<longrightarrow> \<not>(AF a b)\<close>
declare conflictfree_ext_def[Defs]

(* The greatest fixed point is not conflict-free. What about the least? *)
lemma "conflictfree_ext AF (tgfp AF)" nitpick oops (*countermodel found*)
lemma "conflictfree_ext AF (tlfp AF)" (*nitpick*) oops (*neither proven nor disproven*)


(* A set of arguments S is admissible if it is conflict-free and each argument in S is
  defended by S ([Dung 1995] Def. 6(2) and [BCG 2011] Def. 13). *)
definition admissible_ext :: \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> bool\<close> 
  where \<open>admissible_ext AF S \<equiv> conflictfree_ext AF S \<and> (\<forall>a. S a \<longrightarrow> defends AF S a)\<close>
declare admissible_ext_def[Defs]

(* An admissible set S of arguments is called a complete extension if each argument,
  which is defended by S, belongs to S ([Dung 1995] Def. 23). *)
definition complete_ext :: \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> bool\<close> 
  where \<open>complete_ext AF S \<equiv> admissible_ext AF S \<and> (\<forall>a. defends AF S a \<longrightarrow> S a)\<close>
declare complete_ext_def[Defs]

(* Complete extensions are precisely the conflict-free fixed points of \<F> ([Dung 1995] Lemma 24). *)
lemma complete_ext_def2: "complete_ext AF S = (conflictfree_ext AF S \<and> fixpoint (\<F> AF) S)" 
  by (metis admissible_ext_def complete_ext_def fixpoint_def)

(* every complete extension is admissible but not the other way round *)
lemma completeAdmissible: \<open>complete_ext AF S \<longrightarrow> admissible_ext AF S\<close> by (simp add: complete_ext_def)
lemma \<open>admissible_ext AF S \<Longrightarrow> complete_ext AF S\<close> nitpick oops


(* A preferred extension of an argumentation framework AF is a maximal (with respect to set inclusion)
  admissible set of AF ([Dung 1995] Def. 7). *)
definition preferred_ext ::  \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where "preferred_ext AF S \<equiv> maximal (admissible_ext AF) S id"
declare preferred_ext_def[Defs]

(* (just to check) *)
lemma "preferred_ext AF S = (admissible_ext AF S \<and> (\<forall>Q. admissible_ext AF Q \<and> S \<subseteq> Q  \<longrightarrow> Q \<approx> S))"
  by (simp add: preferred_ext_def maximal_def)

(* We can verify that preferred extensions are maximally complete extensions; *)
lemma preferredMaxComplete: "preferred_ext AF S \<longrightarrow> maximal (complete_ext AF) S id" 
  unfolding preferred_ext_def maximal_def complete_ext_def by (smt (z3) admissible_ext_def conflictfree_ext_def defends_def id_apply)
(* however, the converse direction cannot be proven automatically.. yet.*)
lemma "maximal (complete_ext AF) S id \<longrightarrow> preferred_ext AF S" oops (* TODO prove*)


(* The grounded extension of an argumentation framework AF is a minimal complete extension ([BCG 2011] Def. 21). *)
definition grounded_ext ::  \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where "grounded_ext AF S \<equiv> minimal (complete_ext AF) S id"
declare grounded_ext_def[Defs]

(* This is equivalent to the least complete extension: *)
lemma grounded_ext_def2: "grounded_ext AF S = least (complete_ext AF) S id" 
  unfolding grounded_ext_def using \<F>_leastFP_ex  by (smt (z3) complete_ext_def2 conflictfree_ext_def id_def least_def minimal_def)


(* Alternatively, according to Dung, the grounded extension of an argumentation framework AF is
   the least fixed point of \<F> ([Dung 1995] Def. 20). *)
definition grounded_ext_Dung ::  \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where "grounded_ext_Dung AF S \<equiv> least (fixpoint (\<F> AF)) S id"
declare grounded_ext_Dung_def[Defs]

(* This is equivalent to the minimal (conflict free?) fixed point of \<F>. *)
lemma grounded_ext_Dung_def2: "grounded_ext_Dung AF S = minimal (fixpoint (\<F> AF)) S id" 
  unfolding grounded_ext_Dung_def tlfp_def by (metis leastMin minLeastCollapse \<F>_leastFP_ex)

(* The given [BCG 2011] definition indeed implies Dung's definition. *)
lemma groundedDungDefEq1: "grounded_ext AF S \<longrightarrow> grounded_ext_Dung AF S" 
  unfolding grounded_ext_def grounded_ext_Dung_def2 by (smt (verit, best) complete_ext_def2 conflictfree_ext_def id_apply minimal_def)

(* The key to proving the converse implication lies on proving that minimal/least fixed points of \<F>
 are conflict-free. However, provers still cannot prove this automatically. *)
lemma "grounded_ext_Dung AF S \<longrightarrow> conflictfree_ext AF S" oops (*TODO: reconstruct proof 'manually'*)

(* Assuming the result above, we can prove that Dung's definition implies the given [BCG 2011] definition. *)
lemma groundedDungDefEq2: assumes "grounded_ext_Dung AF S \<longrightarrow> conflictfree_ext AF S"
  shows "grounded_ext_Dung AF S \<longrightarrow> grounded_ext AF S" unfolding grounded_ext_def
  by (simp add: assms complete_ext_def2 grounded_ext_Dung_def2 minimal_def)

end

