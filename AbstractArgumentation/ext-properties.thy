(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains experiments with and verification of properties of extension-based semantics
   for argumentation frameworks. *)
(* Auxiliary references:
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011)
 [Dung 1995] Dung, P.M., On the acceptability of arguments and its fundamental role in nonmonotonic reasoning,
            logic programming and n-person games, Artificial Intelligence. (1995)
*)
theory "ext-properties"
  imports extensions "Zorn-lemma"
begin

section \<open>Properties of Extension Semantics\<close>

text \<open>We prove structural properties of extension semantics and investigate their limits through
counterexamples.\<close>


subsection \<open>Admissible and complete extensions\<close>


text \<open>The greatest fixed point is not conflict-free.\<close>
lemma "gfp\<^sup>\<A> att S \<Longrightarrow> conflictfreeExt\<^sup>\<A> att S" nitpick oops (*countermodel found*)

text \<open>The least fixed point is conflict-free.\<close>
lemma "lfp\<^sup>\<A> att S \<Longrightarrow> conflictfreeExt\<^sup>\<A> att S"
proof -
  assume lfp: "lfp\<^sup>\<A> att S"
  have least_fp: "least\<^sup>\<A> (fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att)) S id"
    using lfp unfolding lfpR_def .
  have fp_S: "fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att) S"
    by (rule conjunct1[OF least_fp[unfolded least_rel_def]])
  have least_bound: "\<forall>X. fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att) X \<longrightarrow> S \<subseteq>\<^sup>\<A> X"
    by (rule conjunct2[OF least_fp[unfolded least_rel_def id_apply]])
  (* N collects the arguments not attacked by its input; the characteristic
     function is N composed with itself. *)
  let ?N = "\<lambda>X a. \<not> (\<exists>b. \<A> b \<and> X b \<and> att b a)"
  have square: "\<F>\<^sup>\<A> att X = ?N (?N X)" for X
    unfolding defends_rel_def by auto
  have respects_domain: "X \<approx>\<^sup>\<A> Y \<Longrightarrow> ?N X = ?N Y" for X Y
    by auto
  have square_S: "?N (?N S) \<approx>\<^sup>\<A> S"
    using fp_S unfolding fixpoint_rel_def square .
  have cube_S: "?N (?N (?N S)) = ?N S"
    by (rule respects_domain[OF square_S])
  have fp_N: "fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att) (?N S)"
    unfolding fixpoint_rel_def
  proof (intro allI impI)
    fix a assume "\<A> a"
    show "\<F>\<^sup>\<A> att (?N S) a \<longleftrightarrow> ?N S a"
      unfolding square by (rule fun_cong[OF cube_S])
  qed
  have "S \<subseteq>\<^sup>\<A> (?N S)"
    using least_bound[THEN spec, of "?N S"] fp_N by blast
  thus ?thesis unfolding conflictfreeExt_def by blast
qed

text \<open>The empty set is admissible.\<close>
lemma emptyAdmissible: \<open>admissibleExt\<^sup>\<A> att \<lbrace>-\<rbrace>\<close> by (simp add: admissibleExt_def conflictfreeExt_def)

text \<open>Every complete extension is admissible, but the converse does not hold.\<close>
lemma completeAdmissible: \<open>completeExt\<^sup>\<A> att S \<longrightarrow> admissibleExt\<^sup>\<A> att S\<close> by (simp add: completeExt_def)
lemma \<open>admissibleExt\<^sup>\<A> att S \<Longrightarrow> completeExt\<^sup>\<A> att S\<close> nitpick oops

(* Both definitions for complete extensions coincide *)
lemma completeExt_defEq: "completeExt\<^sup>\<A> att S \<longleftrightarrow> completeExt2\<^sup>\<A> att S" 
  by (smt (verit, del_insts) admissibleExt_def completeExt_def completeExt2_def fixpoint_rel_def)

subsection \<open>Preferred extensions\<close>

text \<open>Dung's fundamental lemma [Dung 1995, Lemma 10].\<close>
lemma DungFundLemma1: "admissibleExt\<^sup>\<A> att S \<Longrightarrow> \<forall>a. defends\<^sup>\<A> att S a \<longrightarrow> admissibleExt\<^sup>\<A> att  (S \<union> \<lbrace>a\<rbrace>)"
  by (smt (z3) admissibleExt_def conflictfreeExt_def defends_rel_def)
lemma DungFundLemma2: "admissibleExt\<^sup>\<A> att S \<Longrightarrow> \<forall>a b. defends\<^sup>\<A> att S a \<and> defends\<^sup>\<A> att S b \<longrightarrow> defends\<^sup>\<A> att (S \<union> \<lbrace>a\<rbrace>) b"
  by (smt (verit) defends_rel_def)

text \<open>The following related lemma is useful for subsequent proofs.\<close>
lemma aux: "admissibleExt\<^sup>\<A> att S \<Longrightarrow> admissibleExt\<^sup>\<A> att  (S \<union> (\<F>\<^sup>\<A> att S))" 
  by (smt (z3) admissibleExt_def conflictfreeExt_def defends_rel_def)

text \<open>Dung's Theorem 11(1) states that admissible sets form an @{text "\<omega>"}-complete partial
order [Dung 1995]. We prove the stronger result that admissible extensions form a dcpo.\<close>
lemma admissibleDirectedComplete: "dcpo\<^sup>\<A> (admissibleExt\<^sup>\<A> att)" 
  unfolding admissibleExt_def conflictfreeExt_def defends_rel_def directedcomplete_rel_def directed_rel_def supremum_def by meson
lemma admissibleOmegaComplete: "\<omega>-cpo\<^sup>\<A> (admissibleExt\<^sup>\<A> att)" by (simp add: admissibleDirectedComplete dcpo_\<omega>_rel)

text \<open>Dung's Theorem 11(2) states that every admissible set S is contained in a preferred extension
E, so S @{text "\<subseteq>"} E.\<close>
lemma DungTh11: "admissibleExt\<^sup>\<A> att S \<longrightarrow> (\<exists>E. S \<subseteq>\<^sup>\<A> E \<and> maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) E id)" 
  by (metis ZornLemma2_\<omega>_rel admissibleOmegaComplete)
lemma \<open>(\<exists>S. maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) S id) \<longrightarrow> (\<exists>S. maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) S id)\<close>
  by (metis ZornLemma2_\<omega>_rel admissibleOmegaComplete)

text \<open>Maximal admissible sets always exist.\<close>
lemma preferredExist: "\<exists>S. maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) S id" 
  by (simp add: ZornLemma_\<omega>_rel admissibleOmegaComplete)

text \<open>Maximal admissible extensions are maximal complete extensions.\<close>
lemma maxAdmissibleComplete: "maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) S id \<longrightarrow> maximal\<^sup>\<A> (completeExt\<^sup>\<A> att) S id"
  unfolding maximal_rel_def completeExt_def admissibleExt_def by (smt (z3) conflictfreeExt_def defends_rel_def id_apply)

text \<open>The previous results also establish the converse.\<close>
lemma maxCompleteAdmissible: "maximal\<^sup>\<A> (completeExt\<^sup>\<A> att) S id \<longrightarrow> maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) S id"
  by (smt (verit) DungTh11 completeAdmissible id_def maxAdmissibleComplete maximal_rel_def)

text \<open>The two definitions of preferred extensions therefore coincide.\<close>
lemma preferredExt_defEq: "preferredExt\<^sup>\<A> att S \<longleftrightarrow> preferredExt2\<^sup>\<A> att S"
  unfolding preferredExt2_def preferredExt_def using maxAdmissibleComplete maxCompleteAdmissible by blast

text \<open>Subsets of preferred extensions are conflict-free.\<close>
lemma preferredConflictfree: "A \<subseteq>\<^sup>\<A> B \<Longrightarrow> preferredExt\<^sup>\<A> att B \<Longrightarrow> conflictfreeExt\<^sup>\<A> att A"
  by (smt (verit, best) completeExt2_def completeExt_defEq conflictfreeExt_def maximal_rel_def preferredExt_def)


subsection \<open>Grounded extensions\<close>

(* The first two definitions of grounded extensions are shown equivalent
(since \<F> has a least fixed point by the Knaster-Tarski theorem) *)
lemma groundedExt_defEq1: "groundedExt\<^sup>\<A> att S \<longleftrightarrow> groundedExt2\<^sup>\<A> att S"
proof
  assume grounded: "groundedExt\<^sup>\<A> att S"
  have minimal_S: "minimal\<^sup>\<A> (completeExt\<^sup>\<A> att) S id"
    using grounded unfolding groundedExt_def .
  have complete_S: "completeExt\<^sup>\<A> att S"
    by (rule conjunct1[OF minimal_S[unfolded minimal_rel_def]])
  obtain L where least_L: "least\<^sup>\<A> (fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att)) L id"
    using \<F>_leastFP_ex by blast
  have fixed_L: "fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att) L"
    by (rule conjunct1[OF least_L[unfolded least_rel_def]])
  have bounds: "\<forall>X. fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att) X \<longrightarrow> L \<subseteq>\<^sup>\<A> X"
    by (rule conjunct2[OF least_L[unfolded least_rel_def id_apply]])
  have fixed_S: "fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att) S"
    using complete_S unfolding completeExt_defEq completeExt2_def by blast
  have sub: "L \<subseteq>\<^sup>\<A> S"
    using bounds[THEN spec, of S] fixed_S by blast
  have cf_S: "conflictfreeExt\<^sup>\<A> att S"
    using complete_S unfolding completeExt_defEq completeExt2_def by blast
  have cf_L: "conflictfreeExt\<^sup>\<A> att L"
    using cf_S sub unfolding conflictfreeExt_def by blast
  have complete_L: "completeExt\<^sup>\<A> att L"
    using cf_L fixed_L unfolding completeExt_defEq completeExt2_def by blast
  have equal: "L \<approx>\<^sup>\<A> S"
    using minimal_S complete_L sub unfolding minimal_rel_def id_apply by blast
  have below: "S \<subseteq>\<^sup>\<A> X" if complete_X: "completeExt\<^sup>\<A> att X" for X
  proof -
    have fixed_X: "fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att) X"
      using complete_X unfolding completeExt_defEq completeExt2_def by blast
    have "L \<subseteq>\<^sup>\<A> X" using bounds[THEN spec, of X] fixed_X by blast
    thus ?thesis using equal by blast
  qed
  show "groundedExt2\<^sup>\<A> att S"
    using complete_S below unfolding groundedExt2_def least_rel_def id_apply by blast
next
  assume grounded: "groundedExt2\<^sup>\<A> att S"
  show "groundedExt\<^sup>\<A> att S"
    unfolding groundedExt_def
    by (rule leastMin_rel[THEN mp, OF grounded[unfolded groundedExt2_def]])
qed

text \<open>A key lemma establishes that least fixed points of @{text "\<F>"} are conflict-free.\<close>
lemma groundedConflictFree: "least\<^sup>\<A> (fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att)) S id \<longrightarrow> conflictfreeExt\<^sup>\<A> att S" 
  by (smt (verit, ccfv_threshold) completeExt2_def completeExt_defEq conflictfreeExt_def id_apply least_rel_def maxAdmissibleComplete maximal_rel_def preferredExist)

text \<open>Dung's definition is equivalent to the other definitions of grounded extensions.\<close>
lemma groundedExt_defEq2: "groundedExt2\<^sup>\<A> att S \<longleftrightarrow> groundedExt3\<^sup>\<A> att S"
  by (smt (verit, best) \<F>_mono completeExt2_def completeExt_defEq groundedConflictFree groundedExt2_def groundedExt3_def least_rel_def wKTl_relw)

subsection \<open>Stable extensions\<close>

lemma stableExt_defEq: "stableExt\<^sup>\<A> att S \<longleftrightarrow> stableExt2\<^sup>\<A> att S"
  by (smt (verit) range_def conflictfreeExt_def plusset_rel_def stableExt2_def stableExt_def)

text \<open>Proposition 11 from [BCG 2011].\<close>
lemma bcgProp11_1: \<open>conflictfreeExt\<^sup>\<A> att S \<and> (S \<union> [\<A>|att|S]\<^sup>+) \<approx>\<^sup>\<A> \<A> \<Longrightarrow> admissibleExt\<^sup>\<A> att S \<and> (S \<union> [\<A>|att|S]\<^sup>+) \<approx>\<^sup>\<A> \<A>\<close>
  by (smt (verit) admissibleExt_def conflictfreeExt_def defends_rel_defEq minusset_rel_def)

lemma bcgProp11_2: \<open>admissibleExt\<^sup>\<A> att S \<and> (S \<union> [\<A>|att|S]\<^sup>+) \<approx>\<^sup>\<A> \<A> \<Longrightarrow> completeExt\<^sup>\<A> att S \<and> (S \<union> [\<A>|att|S]\<^sup>+) \<approx>\<^sup>\<A> \<A>\<close>
  by (smt (verit, del_insts) admissibleExt_def completeExt_def conflictfreeExt_def defends_rel_def plusset_rel_def)

lemma bcgProp11_3: \<open>completeExt\<^sup>\<A> att S \<and> (S \<union> [\<A>|att|S]\<^sup>+) \<approx>\<^sup>\<A> \<A> \<Longrightarrow> preferredExt\<^sup>\<A> att S \<and> (S \<union> [\<A>|att|S]\<^sup>+) \<approx>\<^sup>\<A> \<A>\<close>
proof -
  assume *: \<open>completeExt\<^sup>\<A> att S \<and> (S \<union> [\<A>|att|S]\<^sup>+) \<approx>\<^sup>\<A> \<A>\<close>
  have \<open>preferredExt\<^sup>\<A> att S\<close> unfolding stableExt_def 
    by (smt (verit) "*" admissibleExt_def completeAdmissible conflictfreeExt_def id_apply maximal_rel_def plusset_rel_def preferredExt_def)
  then show \<open>preferredExt\<^sup>\<A> att S \<and> (S \<union> [\<A>|att|S]\<^sup>+) \<approx>\<^sup>\<A> \<A>\<close> 
    by (simp add: "*")
qed

lemma bcgProp11_4: \<open>preferredExt\<^sup>\<A> att S \<and> (S \<union> [\<A>|att|S]\<^sup>+) \<approx>\<^sup>\<A> \<A> \<Longrightarrow> [\<A>|att|S]\<^sup>+ \<approx>\<^sup>\<A> (\<lambda>x. \<A> x \<and> \<not>(S x))\<close>
  by (metis preferredConflictfree range_def stableExt2_def stableExt_def stableExt_defEq)

lemma bcgProp11_5: \<open>[\<A>|att|S]\<^sup>+ \<approx>\<^sup>\<A> (\<lambda>x. \<A> x \<and> \<not>(S x)) \<Longrightarrow> conflictfreeExt\<^sup>\<A> att S \<and> (S \<union> [\<A>|att|S]\<^sup>+) \<approx>\<^sup>\<A> \<A>\<close>
  by (metis stableExt2_def stableExt_def stableExt_defEq)


subsection \<open>Ideal extensions\<close>

text \<open>Ideal sets are closed under union.\<close>
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


lemma ideal_closed_characteristic:
  assumes ideal: "idealSet\<^sup>\<A> att S"
  shows "idealSet\<^sup>\<A> att (S \<union> \<F>\<^sup>\<A> att S)"
proof -
  have adm: "admissibleExt\<^sup>\<A> att S" using ideal unfolding idealSet_def by blast
  have below: "(S \<union> \<F>\<^sup>\<A> att S) \<subseteq>\<^sup>\<A> P"
    if pref: "preferredExt\<^sup>\<A> att P" for P
  proof -
    have sub: "S \<subseteq>\<^sup>\<A> P" using ideal pref unfolding idealSet_def by blast
    have mono: "\<F>\<^sup>\<A> att S \<subseteq>\<^sup>\<A> \<F>\<^sup>\<A> att P"
      using \<F>_mono sub unfolding MONO_rel_def by blast
    have "\<F>\<^sup>\<A> att P \<subseteq>\<^sup>\<A> P"
      using pref unfolding preferredExt_def maximal_rel_def completeExt_def by auto
    thus ?thesis using sub mono by blast
  qed
  show ?thesis using aux[OF adm] below unfolding idealSet_def by blast
qed

subsection \<open>Stage extensions\<close>

text \<open>Theorem 4 from [BCG 2011].\<close>
lemma \<open>\<exists>Lab. stableExt\<^sup>\<A> att Lab \<Longrightarrow> \<forall>L. (stageExt\<^sup>\<A> att L \<longrightarrow> stableExt\<^sup>\<A> att L)\<close> 
proof -
  assume "\<exists>S. stableExt\<^sup>\<A> att S"
  then obtain S where stable: "stableExt\<^sup>\<A> att S" by blast
  have cf_S: "conflictfreeExt\<^sup>\<A> att S"
    and covers: "\<A> \<subseteq> range\<^sup>\<A> att S"
    using stable unfolding stableExt_def by auto
  show ?thesis
  proof (intro allI impI)
    fix L assume stage: "stageExt\<^sup>\<A> att L"
    have cf_L: "conflictfreeExt\<^sup>\<A> att L"
      using stage unfolding stageExt_def maximal_rel_def by blast
    have "range\<^sup>\<A> att L \<subseteq>\<^sup>\<A> range\<^sup>\<A> att S"
      using covers by blast
    hence "range\<^sup>\<A> att S \<approx>\<^sup>\<A> range\<^sup>\<A> att L"
      using stage cf_S unfolding stageExt_def maximal_rel_def by blast
    thus "stableExt\<^sup>\<A> att L"
      using cf_L covers unfolding stableExt_def by blast
  qed
qed

end
