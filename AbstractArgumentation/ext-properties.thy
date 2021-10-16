theory "ext-properties"
  imports extensions "Zorn-lemma"
begin

(*** Properties as used in JLC article section 4.2 ****)
(* except for those about correspondence, they are in correspondence-rel.thy *)

(* 1.  no self-attacks in conflictfree extension  [BCG textual on p.8] *)
(*lemma \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> \<not> (\<exists>A. (\<A> A) \<and> (S A) \<and> (att A A)) \<close> 
  by (simp add: conflictfreeExt_def)*)

lemma section42_prop1: \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> \<not> (\<exists>\<^sup>\<A> (\<lambda>a. (S a) \<and> (att a a))) \<close> 
  by (simp add: conflictfreeExt_def)


(* Prop 2. [BCG]
Lab complete iff for each A in Arg it holds that:
-- A is labelled in iff all its attackers are labelled out
-- A is labelled out iff it has at least one attacker labelled in ... todo in labellings *)


lemma \<open>stableExt\<^sup>\<A> att S \<Longrightarrow> S \<approx>\<^sup>\<A> (\<lambda>x. \<not>(\<exists>b. (S b) \<and> (att b x)))\<close> oops

(**** Testing definitions for extension-based semantics for argumentation frameworks ***)

section \<open>Admissible and complete extensions - Tests\<close>


(* The greatest fixed point is not conflict-free. What about the least? *)
lemma "gfp\<^sup>\<A> att S \<Longrightarrow> conflictfreeExt\<^sup>\<A> att S" nitpick oops (*countermodel found*)
lemma "lfp\<^sup>\<A> att S \<Longrightarrow> conflictfreeExt\<^sup>\<A> att S" (*nitpick*) oops (*neither proven nor disproven*)

(* Emptyset is admissible*)
lemma emptyAdmissible: \<open>admissibleExt\<^sup>\<A> att \<lbrace>-\<rbrace>\<close> by (simp add: admissibleExt_def conflictfreeExt_def)

(* every complete extension is admissible but not the other way round *)
lemma completeAdmissible: \<open>completeExt\<^sup>\<A> att S \<longrightarrow> admissibleExt\<^sup>\<A> att S\<close> by (simp add: completeExt_def)
lemma \<open>admissibleExt\<^sup>\<A> att S \<Longrightarrow> completeExt\<^sup>\<A> att S\<close> nitpick oops

(* Both definitions for complete extensions coincide *)
lemma completeExt_defEq: "completeExt\<^sup>\<A> att S \<longleftrightarrow> completeExt2\<^sup>\<A> att S" 
  by (smt (verit, del_insts) admissibleExt_def completeExt_def completeExt2_def fixpoint_rel_def)

section \<open>Preferred extensions - Tests\<close>

(* Dung's "Fundamental lemma" ([Dung 1995] Lemma 10) *)
lemma DungFundLemma1: "admissibleExt\<^sup>\<A> att S \<Longrightarrow> \<forall>a. defends\<^sup>\<A> att S a \<longrightarrow> admissibleExt\<^sup>\<A> att  (S \<union> \<lbrace>a\<rbrace>)"
  by (smt (z3) admissibleExt_def conflictfreeExt_def defends_rel_def)
lemma DungFundLemma2: "admissibleExt\<^sup>\<A> att S \<Longrightarrow> \<forall>a b. defends\<^sup>\<A> att S a \<and> defends\<^sup>\<A> att S b \<longrightarrow> defends\<^sup>\<A> att (S \<union> \<lbrace>a\<rbrace>) b"
  by (smt (verit) defends_rel_def)

(* The following lemma is also quite similar in spirit and might be useful to prove subsequent results *)
lemma aux: "admissibleExt\<^sup>\<A> att S \<Longrightarrow> admissibleExt\<^sup>\<A> att  (S \<union> (\<F>\<^sup>\<A> att S))" 
  by (smt (z3) admissibleExt_def conflictfreeExt_def defends_rel_def)

(********* [Dung 1995] Theorem 11: *************)
(*(1) Admissible sets form an \<omega>-complete poset.*)
(* We can, in fact, prove a stronger statement: admissible extensions form a dcpo*)
lemma admissibleDirectedComplete: "dcpo\<^sup>\<A> (admissibleExt\<^sup>\<A> att)" 
  unfolding admissibleExt_def conflictfreeExt_def defends_rel_def directedcomplete_rel_def directed_rel_def supremum_def by meson
lemma admissibleOmegaComplete: "\<omega>-cpo\<^sup>\<A> (admissibleExt\<^sup>\<A> att)" by (simp add: admissibleDirectedComplete dcpo_\<omega>_rel)

(*(2) For each admissible set S there exists a preferred extension E, such that S \<subseteq> E. *)
lemma DungTh11: "admissibleExt\<^sup>\<A> att S \<longrightarrow> (\<exists>E. S \<subseteq>\<^sup>\<A> E \<and> maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) E id)" 
  by (metis ZornLemma2_\<omega>_rel admissibleOmegaComplete)
lemma \<open>(\<exists>S. maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) S id) \<longrightarrow> (\<exists>S. maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) S id)\<close>
  by (metis ZornLemma2_\<omega>_rel admissibleOmegaComplete)

(* We can also prove that maximal admissible sets always exist*)
lemma preferredExist: "\<exists>S. maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) S id" 
  by (simp add: ZornLemma_\<omega>_rel admissibleOmegaComplete)

(* We can verify that maximally admissible extensions are maximally complete extensions; *)
lemma maxAdmissibleComplete: "maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) S id \<longrightarrow> maximal\<^sup>\<A> (completeExt\<^sup>\<A> att) S id"
  unfolding maximal_rel_def completeExt_def admissibleExt_def by (smt (z3) conflictfreeExt_def defends_rel_def id_apply)

(* The converse direction can proven by making use of the previous results*)
lemma maxCompleteAdmissible: "maximal\<^sup>\<A> (completeExt\<^sup>\<A> att) S id \<longrightarrow> maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) S id"
  by (smt (verit) DungTh11 completeAdmissible id_def maxAdmissibleComplete maximal_rel_def)

(* Finally, we can show that both definitions for preferred extensions coincide *)
lemma preferredExt_defEq: "preferredExt\<^sup>\<A> att S \<longleftrightarrow> preferredExt2\<^sup>\<A> att S"
  unfolding preferredExt2_def preferredExt_def using maxAdmissibleComplete maxCompleteAdmissible by blast

(* Useful lemma: subsets of preferred extensions are conflict-free*)
lemma preferredConflictfree: "A \<subseteq>\<^sup>\<A> B \<Longrightarrow> preferredExt\<^sup>\<A> att B \<Longrightarrow> conflictfreeExt\<^sup>\<A> att A"
  by (smt (verit, best) completeExt2_def completeExt_defEq conflictfreeExt_def maximal_rel_def preferredExt_def)


section \<open>Grounded extensions - Tests\<close>

(* The first two definitions of grounded extensions are shown equivalent 
(since \<F> has a least fixed point by the Knaster-Tarski theorem) *)
lemma groundedExt_defEq1: "groundedExt\<^sup>\<A> att S \<longleftrightarrow> groundedExt2\<^sup>\<A> att S" 
  unfolding groundedExt_def groundedExt2_def using \<F>_leastFP_ex by (smt (z3) completeExt2_def completeExt_defEq conflictfreeExt_def id_def least_rel_def minimal_rel_def)

(* A key lemma says that minimal/least fixed points of \<F> are conflict-free. This is not at all trivial! 
 Quite interestingly, SMT solver can prove this by somehow using the existence of preferred extensions.*)
lemma groundedConflictFree: "least\<^sup>\<A> (fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att)) S id \<longrightarrow> conflictfreeExt\<^sup>\<A> att S" 
  by (smt (verit, ccfv_threshold) completeExt2_def completeExt_defEq conflictfreeExt_def id_apply least_rel_def maxAdmissibleComplete maximal_rel_def preferredExist)

(* We can show automatically that Dung's definition is equivalent to the other ones*)
lemma groundedExt_defEq2: "groundedExt2\<^sup>\<A> att S \<longleftrightarrow> groundedExt3\<^sup>\<A> att S"
  by (smt (verit, best) \<F>_mono completeExt2_def completeExt_defEq groundedConflictFree groundedExt2_def groundedExt3_def least_rel_def wKTl_relw)

section \<open>Ideal extensions - Tests\<close>

(* Ideal sets are closed under union *)
lemma idealSetUnion: "idealSet\<^sup>\<A> att A \<Longrightarrow> idealSet\<^sup>\<A> att B \<Longrightarrow> idealSet\<^sup>\<A> att (A\<union>B)" proof -
  assume 1: "idealSet\<^sup>\<A> att A" and 2: "idealSet\<^sup>\<A> att B"
  hence 3: "conflictfreeExt\<^sup>\<A> att (A\<union>B)" unfolding idealSet_def   
    by (smt (z3) preferredConflictfree preferredExist maxAdmissibleComplete preferredExt_def)
  from 1 2 3 show "idealSet\<^sup>\<A> att (A\<union>B)" unfolding idealSet_def preferredExt_def admissibleExt_def by (smt (z3) MONO_def \<F>_mono')
qed

(* both definitions of ideal extensions (i.e. maximal ideal sets) are equivalent *)
lemma idealExt_defEq: "idealExt2\<^sup>\<A> att S \<longleftrightarrow> idealExt\<^sup>\<A> att S" 
  unfolding idealExt_def idealExt2_def maximal_rel_def greatest_rel_def
  using idealSetUnion id_def by (smt (verit, del_insts)) 

section \<open>Stable extensions - Tests\<close>

lemma stableExt_defEq: "stableExt\<^sup>\<A> att S \<longleftrightarrow> stableExt2\<^sup>\<A> att S"
  by (smt (verit) range_def conflictfreeExt_def plusset_rel_def stableExt2_def stableExt_def)

section \<open>Semistable extensions - Tests\<close>
(*TODO*)

section \<open>Stage extensions - Tests\<close>
(*TODO*)

end
