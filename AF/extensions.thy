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
named_theorems Defs

(* An argumentation frame(work) AF is completely characterized in HOL by its underlying "attack" relation,
   since the set of arguments (the carrier of "attack") is given implicitly as the domain set for type 'a. *)
type_synonym 'a \<A>\<F> = \<open>'a Rel\<close>

(* Given a set of arguments S, we define its set of attacked (+) and attacking (-) arguments ([BCG 2011] p. 3). *)
definition plusset :: \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("[_|_]\<^sup>+") where \<open>[AF|S]\<^sup>+ \<equiv> \<lambda>b. \<exists>a. S a \<and> AF a b\<close>
definition minusset:: \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("[_|_]\<^sup>-") where \<open>[AF|S]\<^sup>- \<equiv> \<lambda>b. \<exists>a. S a \<and> AF b a\<close>
declare plusset_def[Defs] minusset_def[Defs]

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

(* A preferred extension of an argumentation framework AF is a maximal (with respect to set inclusion)
  admissible set of AF ([Dung 1995] Def. 7). *)
definition preferred_ext ::  \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where "preferred_ext AF S \<equiv> maximal (admissible_ext AF) S id"
declare preferred_ext_def[Defs]

(* (just to check) *)
lemma "preferred_ext AF S = (admissible_ext AF S \<and> (\<forall>Q. admissible_ext AF Q \<and> S \<subseteq> Q  \<longrightarrow> Q \<approx> S))"
  by (simp add: preferred_ext_def maximal_def)

(* Preferred extensions are complete. *)
lemma preferredComplete: "preferred_ext AF S \<longrightarrow> complete_ext AF S"
  unfolding preferred_ext_def complete_ext_def maximal_def id_def
  by (smt (z3) defends_def admissible_ext_def conflictfree_ext_def)

(* The grounded extension of an argumentation framework AF is the least fixed point of \<F> ([Dung 1995] Def. 20). *)
definition grounded_ext ::  \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> bool\<close>
  where "grounded_ext AF S \<equiv> least (fixpoint (\<F> AF)) S id"
declare grounded_ext_def[Defs]

(* The grounded extension also corresponds to the minimal (conflict free) fixed point of \<F> ([BCG 2011] Def. 21). *)
lemma grounded_ext_def2: "grounded_ext AF S = minimal (fixpoint (\<F> AF)) S id" 
  unfolding grounded_ext_def tlfp_def by (metis leastMin minLeastCollapse \<F>_leastFP_ex)

(* Grounded extensions are conflict-free (but provers cannot prove this automatically: we need a 'manual' proof). *)
lemma groundedConflictfree: "grounded_ext AF S \<longrightarrow> conflictfree_ext AF S"
  unfolding grounded_ext_def2 minimal_def conflictfree_ext_def fixpoint_def sorry (*TODO: reconstruct proof*)

(* Assuming the result above, grounded extensions are complete. *)
lemma groundedComplete: "grounded_ext AF S \<longrightarrow> complete_ext AF S" 
  using groundedConflictfree by (metis complete_ext_def2 grounded_ext_def least_def) 

end