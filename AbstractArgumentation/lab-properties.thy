(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains experiments with and verification of properties of labelling-based semantics
   for argumentation frameworks. *)
(* Auxiliary references: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011) 
 [Dung 1995] Dung, P.M., On the acceptability of arguments and its fundamental role in nonmonotonic reasoning,
            logic programming and n-person games, Artificial Intelligence. (1995)
*)
theory "lab-properties"
  imports labellings "Zorn-lemma" "lab-order"
begin

section \<open>Properties of Labelling Semantics\<close>

text \<open>We prove existence, uniqueness, and structural results for labelling semantics, independently of extension semantics.\<close>

subsection \<open>Admissible and conflict-free labellings\<close>

text \<open>There always exists an admissible Labelling (label, e.g., all arguments as Undec).\<close>
lemma exAdmissible: \<open>\<exists>Lab. admissibleLab\<^sup>\<A> att Lab\<close> unfolding Defs by auto
(* See here: *)
lemma fixes att :: \<open>'a Rel\<close> and Lab :: \<open>'a Labelling\<close>
      assumes \<open>\<forall>x. \<A> x \<longrightarrow> undec Lab x\<close> (* give every argument the label Undec *)
      shows \<open>admissibleLab\<^sup>\<A> att Lab\<close> using assms unfolding Defs by simp

text \<open>every admissible labelling is conflict-free but not the other way round.\<close>
lemma admissibleLabConflictfree: \<open>admissibleLab\<^sup>\<A> att Lab \<Longrightarrow> conflictfreeLab\<^sup>\<A> att Lab\<close> 
  by (simp add: admissibleLab_def conflictfreeLab_def inset_def legallyIn_def legallyOut_def outset_def)
lemma \<open>conflictfreeLab\<^sup>\<A> att Lab \<Longrightarrow> admissibleLab\<^sup>\<A> att Lab\<close> nitpick oops

text \<open>For admissible labellings, legally-undecided implies undecided but not the other way round.\<close>
lemma admissibleLabLegUndec: \<open>admissibleLab\<^sup>\<A> att Lab \<Longrightarrow> \<forall>x. \<A> x \<longrightarrow> legallyUndec\<^sup>\<A> att Lab x \<longrightarrow> undec Lab x\<close>
  unfolding admissibleLab_def by (meson Label.exhaust inset_def legallyUndec_def outset_def undecset_def)

lemma \<open>admissibleLab\<^sup>\<A> att Lab \<Longrightarrow> \<forall>x. \<A> x \<longrightarrow> undec Lab x \<longrightarrow> legallyUndec\<^sup>\<A> att Lab x\<close> nitpick oops

text \<open>OTOH, for admissible labellings, legally-in/out still do not imply in/out.\<close>
lemma \<open>admissibleLab\<^sup>\<A> att Lab \<Longrightarrow> \<forall>x. \<A> x \<longrightarrow> legallyIn\<^sup>\<A> att Lab x \<longrightarrow> in Lab x\<close> nitpick oops
lemma \<open>admissibleLab\<^sup>\<A> att Lab \<Longrightarrow> \<forall>x. \<A> x \<longrightarrow> legallyOut\<^sup>\<A> att Lab x \<longrightarrow> out Lab x\<close> nitpick oops

lemma DungFundLemma1Lab: \<open>admissibleLab\<^sup>\<A> att Lab \<and> defends\<^sup>\<A> att (in Lab) a \<longrightarrow>
                                admissibleLab\<^sup>\<A> att ( \<lambda>x. if (x = a) then In else
                                                     (if (att x a) then Out else (Lab x)) )\<close> 
  unfolding defends_rel_def admissibleLab_def
  by (smt (z3) Label.distinct(1) inset_def legallyIn_def legallyOut_def outset_def)
  
subsection \<open>Complete labellings\<close>

text \<open>For complete labellings, legally-in/out does indeed imply in/out-labelled.\<close>
lemma completeLabLegIn:  \<open>completeLab\<^sup>\<A> att Lab \<Longrightarrow> \<forall>x. \<A> x \<longrightarrow> legallyIn\<^sup>\<A> att Lab x \<longrightarrow> in Lab x\<close>
  unfolding Defs using Label.exhaust by metis
lemma completeLabLegOut: \<open>completeLab\<^sup>\<A> att Lab \<Longrightarrow> \<forall>x. \<A> x \<longrightarrow> legallyOut\<^sup>\<A> att Lab x \<longrightarrow> out Lab x\<close>
  unfolding Defs using Label.exhaust by metis

text \<open>in-sets of complete labellings are fixed points of the characteristic function.\<close>
lemma completeLabInFP: "completeLab\<^sup>\<A> att Lab \<Longrightarrow> fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att) (in Lab)"
  unfolding fixpoint_rel_def using completeLab2_def complete_defEq
  by (smt (verit, ccfv_threshold) defends_rel_def legallyIn_def legallyOut_def)

lemma completeLabInFP': "completeLab\<^sup>\<A> att Lab \<Longrightarrow> fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att) (\<A> \<inter> (in Lab))"
unfolding fixpoint_rel_def using completeLab2_def complete_defEq
  by (smt (verit, ccfv_threshold) defends_rel_def legallyIn_def legallyOut_def)


text \<open>complete labellings always exist.\<close>
lemma complete_exists: \<open>\<exists>Lab. completeLab\<^sup>\<A> att Lab\<close>
proof -
  obtain S where max: "maximal (admissible_decisions \<A> att) S id"
    using maximal_admissible_decisions_exists[of \<A> att] by blast
  have "completeLab\<^sup>\<A> att (decisions_lab S)"
    by (rule maximal_admissible_decisions_complete[OF max])
  thus ?thesis by blast
qed

lemma complete_fixed_point_exists:
  "\<exists>L. fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att) (in L)"
  by (meson complete_exists completeLabInFP)

text \<open>every complete labelling is admissible but not the other way round.\<close>
lemma completeLabAdmissible: \<open>completeLab\<^sup>\<A> att Lab \<Longrightarrow> admissibleLab\<^sup>\<A> att Lab\<close> by (simp add: completeLab_def)
lemma \<open>admissibleLab\<^sup>\<A> att Lab \<Longrightarrow> completeLab\<^sup>\<A> att Lab\<close> nitpick oops

text \<open>For complete labellings we have that in/out-sets completely determine the labelling.\<close>
lemma completeLabInLab: \<open>completeLab\<^sup>\<A> att L1 \<Longrightarrow> completeLab\<^sup>\<A> att L2 \<Longrightarrow> in(L1) \<approx>\<^sup>\<A> in(L2) \<longrightarrow> (\<forall>x. \<A> x \<longrightarrow> L1(x) = L2(x))\<close>
  unfolding completeLab2_def complete_defEq by (smt (verit, best) Label.exhaust inset_def legallyOut_def outset_def)

lemma completeLabOutLab: \<open>completeLab\<^sup>\<A> att L1 \<Longrightarrow> completeLab\<^sup>\<A> att L2 \<Longrightarrow> out(L1) \<approx>\<^sup>\<A> out(L2) \<longrightarrow> (\<forall>x. \<A> x \<longrightarrow> L1(x) = L2(x))\<close>
  unfolding completeLab2_def complete_defEq by (smt (verit, best) Label.exhaust inset_def legallyIn_def outset_def)

lemma \<open>completeLab\<^sup>\<A> att L1 \<Longrightarrow> completeLab\<^sup>\<A> att L2 \<Longrightarrow> undec(L1) \<approx>\<^sup>\<A> undec(L2) \<longrightarrow> (\<forall>x. \<A> x \<longrightarrow> L1(x) = L2(x))\<close> nitpick oops

lemma complete_least_in_exists: "\<exists>L. least\<^sup>\<A> (completeLab\<^sup>\<A> att) L in"
proof -
  obtain S where least_fp: "least (fixpoint (lab_update \<A> att)) S id"
    using wKTl[OF lab_update_mono[of \<A> att]] by blast
  have least_bound: "\<forall>X. fixpoint (lab_update \<A> att) X \<longrightarrow> S \<subseteq> X"
    by (rule conjunct2[OF least_fp[unfolded least_def id_apply]])
  obtain L where comp_L: "completeLab\<^sup>\<A> att L" using complete_exists by blast
  have fp_L: "fixpoint (lab_update \<A> att) (lab_decisions \<A> L)"
    using complete_lab_decisions[of \<A> att L] comp_L by blast
  have sub_L: "S \<subseteq> lab_decisions \<A> L"
    using least_bound[THEN spec, of "lab_decisions \<A> L"] fp_L by blast
  have cs: "consistent_decisions \<A> S"
    by (rule consistent_decisions_subset[OF lab_decisions_consistent sub_L])
  have rep: "lab_decisions \<A> (decisions_lab S) = S"
    by (rule decisions_lab_inverse[OF cs])
  have fp_S: "fixpoint (lab_update \<A> att) S"
    using least_fp unfolding least_def by blast
  have comp: "completeLab\<^sup>\<A> att (decisions_lab S)"
    by (rule decisions_fixpoint_complete[OF cs fp_S])
  have below: "(in (decisions_lab S)) \<subseteq>\<^sup>\<A> (in M)"
    if comp_M: "completeLab\<^sup>\<A> att M" for M
  proof -
    have fp_M: "fixpoint (lab_update \<A> att) (lab_decisions \<A> M)"
      using complete_lab_decisions[of \<A> att M] comp_M by blast
    have "S \<subseteq> lab_decisions \<A> M"
      using least_bound[THEN spec, of "lab_decisions \<A> M"] fp_M by blast
    hence "decisions_lab S \<sqsubseteq>\<^sup>\<A> M"
      using rep lab_decisions_order[of \<A> "decisions_lab S" M] by simp
    thus ?thesis unfolding lessOrEquallyCommittedLab_def by blast
  qed
  have "least\<^sup>\<A> (completeLab\<^sup>\<A> att) (decisions_lab S) in"
    using comp below unfolding least_rel_def by blast
  thus ?thesis by blast
qed

text \<open>Lemma 1 from [BCG2011].\<close>
lemma complete_in_out_mono:
  "completeLab\<^sup>\<A> att L \<Longrightarrow> completeLab\<^sup>\<A> att M \<Longrightarrow>
   (in L) \<subseteq>\<^sup>\<A> (in M) \<longleftrightarrow> (out L) \<subseteq>\<^sup>\<A> (out M)"
  unfolding complete_defEq completeLab2_def
  by (smt (verit) legallyIn_def legallyOut_def)

lemma complete_least_out_exists: "\<exists>L. least\<^sup>\<A> (completeLab\<^sup>\<A> att) L out"
proof -
  obtain L where least_in: "least\<^sup>\<A> (completeLab\<^sup>\<A> att) L in"
    using complete_least_in_exists by blast
  have comp: "completeLab\<^sup>\<A> att L" using least_in unfolding least_rel_def by blast
  have below: "(out L) \<subseteq>\<^sup>\<A> (out M)" if m: "completeLab\<^sup>\<A> att M" for M
  proof -
    have "(in L) \<subseteq>\<^sup>\<A> (in M)" using least_in m unfolding least_rel_def by blast
    thus ?thesis using complete_in_out_mono[OF comp m] by blast
  qed
  have "least\<^sup>\<A> (completeLab\<^sup>\<A> att) L out"
    using comp below unfolding least_rel_def by blast
  thus ?thesis by blast
qed

lemma complete_greatest_undec_exists: "\<exists>L. greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) L undec"
proof -
  obtain L where least_out: "least\<^sup>\<A> (completeLab\<^sup>\<A> att) L out"
    using complete_least_out_exists by blast
  have comp: "completeLab\<^sup>\<A> att L" using least_out unfolding least_rel_def by blast
  have below: "(undec M) \<subseteq>\<^sup>\<A> (undec L)" if m: "completeLab\<^sup>\<A> att M" for M
  proof -
    have outs: "(out L) \<subseteq>\<^sup>\<A> (out M)"
      using least_out m unfolding least_rel_def by blast
    have ins: "(in L) \<subseteq>\<^sup>\<A> (in M)"
      using complete_in_out_mono[OF comp m] outs by blast
    show ?thesis using ins outs
      by (smt (verit) Label.distinct Label.exhaust inset_def outset_def undecset_def)
  qed
  have "greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) L undec"
    using comp below unfolding greatest_rel_def by blast
  thus ?thesis by blast
qed

text \<open>For complete labellings, every in-set which is minimal is the least in-set.
(this result is key and has somehow to do with the fact that complete extensions are fixed points of a monotonic function).\<close>
lemma completeLabMinLeastIn: \<open>minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in \<longrightarrow> least\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in\<close>
  using minLeastCollapse_rel[where U="\<A>" and Prop="completeLab\<^sup>\<A> att" and E="in", OF complete_least_in_exists] by blast

lemma completeMinLeastOut: \<open>minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out \<longrightarrow> least\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out\<close>
  using minLeastCollapse_rel[where U="\<A>" and Prop="completeLab\<^sup>\<A> att" and E="out", OF complete_least_out_exists] by blast
lemma completeMaxGreatestUndec: \<open>maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec \<longrightarrow> greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec\<close>
  using maxGreatestCollapse_rel[where U="\<A>" and Prop="completeLab\<^sup>\<A> att" and E="undec", OF complete_greatest_undec_exists] by blast


(* Prop. 5 from [BCG2011]. *)
lemma prop5_1iff2: \<open>minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out = minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in\<close>
  unfolding minimal_rel_def using complete_defEq completeLab2_def by (smt (z3) Label.exhaust legallyIn_def legallyOut_def)

lemma prop5_2to3_weak: \<open>least\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out \<longrightarrow> greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec\<close> 
  unfolding least_rel_def greatest_rel_def by (smt (verit, ccfv_SIG) Label.exhaust completeLab2_def complete_defEq inset_def legallyIn_def outset_def undecset_def)

lemma prop5_3to2_weak: \<open>greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec \<longrightarrow> minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out\<close>
  unfolding minimal_rel_def greatest_rel_def 
  by (smt (verit, best) admissibleLabConflictfree Label.exhaust conflictfreeLab_def inset_def legallyOut_def outset_def undecset_def completeLabAdmissible)

lemma prop5_1to3: \<open>minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in \<longrightarrow> maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec\<close>
  using prop5_1iff2 completeMinLeastOut prop5_2to3_weak greatestMax_rel[where U="\<A>" and Prop="completeLab\<^sup>\<A> att" and E="undec"] by blast
lemma prop5_2to3: \<open>minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out \<longrightarrow> maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec\<close>
  using prop5_1iff2 prop5_1to3 by blast
lemma prop5_3to1: \<open>maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec \<longrightarrow> minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in\<close>
  using completeMaxGreatestUndec prop5_3to2_weak prop5_1iff2 by blast
lemma prop5_3to2: \<open>maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec \<longrightarrow> minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out\<close>
  using prop5_3to1 prop5_1iff2 by blast

(* Prop 2 BCG*)
lemma complete_iff_inoutlegal: \<open>completeLab\<^sup>\<A> att Lab \<longleftrightarrow> (\<forall>\<^sup>\<A> (\<lambda> a. ((Lab a) = In) \<longleftrightarrow> \<forall>\<^sup>\<A> (\<lambda>b. att b a \<longrightarrow> (Lab b) = Out)) ) \<and> (\<forall>\<^sup>\<A> (\<lambda> a. ((Lab a) = Out) \<longleftrightarrow> \<exists>\<^sup>\<A> (\<lambda>b. att b a \<and> (Lab b) = In)) )\<close>
proof
  show \<open>completeLab\<^sup>\<A> att Lab \<Longrightarrow> (\<forall>\<^sup>\<A> (\<lambda> a. ((Lab a) = In) \<longleftrightarrow> \<forall>\<^sup>\<A> (\<lambda>b. att b a \<longrightarrow> (Lab b) = Out)) ) \<and> (\<forall>\<^sup>\<A> (\<lambda> a. ((Lab a) = Out) \<longleftrightarrow> \<exists>\<^sup>\<A> (\<lambda>b. att b a \<and> (Lab b) = In)) )\<close>
  unfolding completeLab_def  admissibleLab_def
  by (smt (z3) Label.exhaust inset_def legallyIn_def legallyOut_def legallyUndec_def outset_def undecset_def) 
next
  show \<open> (\<forall>\<^sup>\<A> (\<lambda> a. ((Lab a) = In) \<longleftrightarrow> \<forall>\<^sup>\<A> (\<lambda>b. att b a \<longrightarrow> (Lab b) = Out)) ) \<and> (\<forall>\<^sup>\<A> (\<lambda> a. ((Lab a) = Out) \<longleftrightarrow> \<exists>\<^sup>\<A> (\<lambda>b. att b a \<and> (Lab b) = In)) ) \<Longrightarrow> completeLab\<^sup>\<A> att Lab\<close>
    by (smt (verit, del_insts) Label.distinct(3) Label.distinct(5) admissibleLab_def completeLab_def inset_def legallyIn_def legallyOut_def legallyUndec_def outset_def undecset_def)
qed

subsection \<open>Grounded and preferred labellings\<close>

(* the two provided definitions of grounded labellings are equivalent *)
lemma grounded_defEq: \<open>groundedLab\<^sup>\<A> att Lab \<longleftrightarrow> groundedLab2\<^sup>\<A> att Lab\<close>
  unfolding groundedLab_def groundedLab2_def
  using completeLabMinLeastIn leastMin_rel[where U="\<A>"
    and Prop="completeLab\<^sup>\<A> att" and E="in"] by blast

text \<open>grounded labellings always exist.\<close>
lemma grounded_exists: "\<exists>Lab. groundedLab\<^sup>\<A> att Lab"
proof -
  obtain L where least_in: "least\<^sup>\<A> (completeLab\<^sup>\<A> att) L in"
    using complete_least_in_exists by blast
  have "minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) L in"
    by (rule leastMin_rel[THEN mp, OF least_in])
  thus ?thesis unfolding groundedLab_def by blast
qed

text \<open>Side comment from [BCG2011] that grounded labellings are unique.\<close>
lemma grounded_unique: \<open>groundedLab\<^sup>\<A> att Lab1 \<Longrightarrow> groundedLab\<^sup>\<A> att Lab2 \<Longrightarrow> \<forall>x. \<A> x \<longrightarrow> Lab1(x) = Lab2(x)\<close>
  unfolding grounded_defEq least_rel_def
  by (smt (verit, del_insts) completeLabInLab groundedLab2_def least_rel_def) 

text \<open>preferred labellings always exist.\<close>
lemma preferred_exists: \<open>\<exists>Lab. preferredLab\<^sup>\<A> att Lab\<close>
proof -
  obtain S where max: "maximal (admissible_decisions \<A> att) S id"
    using maximal_admissible_decisions_exists[of \<A> att] by blast
  let ?L = "decisions_lab S"
  have comp: "completeLab\<^sup>\<A> att ?L"
    by (rule maximal_admissible_decisions_complete[OF max])
  have cs: "consistent_decisions \<A> S"
    using max unfolding maximal_def admissible_decisions_def by blast
  have rep: "lab_decisions \<A> ?L = S" by (rule decisions_lab_inverse[OF cs])
  have reverse_in: "(in M) \<subseteq>\<^sup>\<A> (in ?L)"
    if comp_M: "completeLab\<^sup>\<A> att M" and sub: "(in ?L) \<subseteq>\<^sup>\<A> (in M)" for M
  proof -
    have outs: "(out ?L) \<subseteq>\<^sup>\<A> (out M)"
      using complete_in_out_mono[OF comp comp_M] sub by blast
    have "?L \<sqsubseteq>\<^sup>\<A> M" using sub outs
      unfolding lessOrEquallyCommittedLab_def by blast
    hence sub_facts: "S \<subseteq> lab_decisions \<A> M"
      using rep lab_decisions_order[of \<A> ?L M] by simp
    have adm_M: "admissible_decisions \<A> att (lab_decisions \<A> M)"
      using admissible_lab_decisions[of \<A> att M] completeLabAdmissible[OF comp_M] by blast
    have "lab_decisions \<A> M \<approx> S"
      by (rule maximal_admissible_decisions_bound[OF max adm_M sub_facts])
    hence "lab_decisions \<A> M \<subseteq> lab_decisions \<A> ?L" using rep by simp
    hence "M \<sqsubseteq>\<^sup>\<A> ?L" by (simp only: lab_decisions_order)
    thus ?thesis unfolding lessOrEquallyCommittedLab_def by blast
  qed
  have "preferredLab\<^sup>\<A> att ?L"
    using comp reverse_in unfolding preferredLab_def maximal_rel_def by blast
  thus ?thesis by blast
qed

(*Prop 8 from [BCG2011] 
 For complete labellings, being maximal/greatest wrt In is equivalent to being maximal/greatest wrt Out*)
lemma prop8: \<open>maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in \<longleftrightarrow> maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out\<close> unfolding maximal_rel_def
  by (smt (z3) complete_defEq completeLab2_def legallyIn_def legallyOut_def)

lemma prop8': \<open>greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in \<longleftrightarrow> greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out\<close> unfolding greatest_rel_def
  by (smt (z3) complete_defEq completeLab2_def legallyIn_def legallyOut_def)

text \<open>In fact, being greatest wrt In implies being least wrt Undec, but not the other way round.\<close>
lemma \<open>greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in \<longrightarrow> least\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec\<close> unfolding greatest_rel_def least_rel_def
  by (smt (z3) admissibleLabLegUndec completeLab_def completeLab2_def complete_defEq legallyOut_def legallyUndec_def)

lemma \<open>least\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec \<longrightarrow> greatest\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in\<close> nitpick oops (* counterexample *)

text \<open>Moreover, being minimal wrt Undec implies being maximal wrt In, but not the other way round (cf. semi-stable labellings).\<close>
lemma \<open>minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec \<longrightarrow> maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in\<close> unfolding minimal_rel_def maximal_rel_def
  by (smt (verit, ccfv_SIG) Label.exhaust complete_defEq completeLab2_def inset_def legallyOut_def outset_def undecset_def)

lemma \<open>maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in \<longrightarrow> minimal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab undec\<close> nitpick oops (* counterexample *)

text \<open>Prop. 10 from [BCG2011] 
 If no argument is labelled Undec then the notions of conflict-free, admissible, complete and preferred collapse.\<close>
lemma prop10_1to2: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> conflictfreeLab\<^sup>\<A> att Lab \<longrightarrow> admissibleLab\<^sup>\<A> att Lab\<close>
  by (smt (verit, ccfv_threshold) Label.exhaust inset_def admissibleLab_def conflictfreeLab_def legallyIn_def legallyOut_def outset_def)
lemma prop10_2to3: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> admissibleLab\<^sup>\<A> att Lab \<longrightarrow> completeLab\<^sup>\<A> att Lab\<close> 
  by (simp add: completeLab_def undecset_def)
lemma prop10_3to4: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> completeLab\<^sup>\<A> att Lab \<longrightarrow>  preferredLab\<^sup>\<A> att Lab\<close> unfolding preferredLab_def maximal_rel_def
  by (smt (verit, ccfv_SIG) Label.exhaust completeLab2_def complete_defEq inset_def legallyOut_def outset_def)
lemma prop10_4to1: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> preferredLab\<^sup>\<A> att Lab \<longrightarrow> conflictfreeLab\<^sup>\<A> att Lab\<close>
  by (simp add: preferredLab_def admissibleLabConflictfree completeLab_def maximal_rel_def)



subsection \<open>Ideal labellings\<close>

text \<open>Quasi-ideal labellings have common upper bounds in the commitment order.\<close>
lemma qideal_directed:
  assumes qL: "qidealLab\<^sup>\<A> att L" and qM: "qidealLab\<^sup>\<A> att M"
  shows "\<exists>N. qidealLab\<^sup>\<A> att N \<and> L \<sqsubseteq>\<^sup>\<A> N \<and> M \<sqsubseteq>\<^sup>\<A> N"
proof -
  let ?S = "lab_decisions \<A> L \<union> lab_decisions \<A> M"
  let ?N = "decisions_lab ?S"
  obtain P where pref: "preferredLab\<^sup>\<A> att P" using preferred_exists by blast
  have bound_L: "L \<sqsubseteq>\<^sup>\<A> P" and bound_M: "M \<sqsubseteq>\<^sup>\<A> P"
    using qL qM pref unfolding qidealLab_def by auto
  have sub_P: "?S \<subseteq> lab_decisions \<A> P"
    using bound_L bound_M unfolding lab_decisions_order[symmetric] by blast
  have cs: "consistent_decisions \<A> ?S"
    by (rule consistent_decisions_subset[OF lab_decisions_consistent sub_P])
  have adm_L: "admissible_decisions \<A> att (lab_decisions \<A> L)"
    using qL admissible_lab_decisions[of \<A> att L] unfolding qidealLab_def by blast
  have adm_M: "admissible_decisions \<A> att (lab_decisions \<A> M)"
    using qM admissible_lab_decisions[of \<A> att M] unfolding qidealLab_def by blast
  have adm_S: "admissible_decisions \<A> att ?S"
    by (rule admissible_decisions_union[OF adm_L adm_M cs])
  have rep: "lab_decisions \<A> ?N = ?S" by (rule decisions_lab_inverse[OF cs])
  have adm_N: "admissibleLab\<^sup>\<A> att ?N"
    using admissible_lab_decisions[of \<A> att ?N] adm_S rep by simp
  have below: "?N \<sqsubseteq>\<^sup>\<A> Q" if pref_Q: "preferredLab\<^sup>\<A> att Q" for Q
  proof -
    have "L \<sqsubseteq>\<^sup>\<A> Q" "M \<sqsubseteq>\<^sup>\<A> Q"
      using qL qM pref_Q unfolding qidealLab_def by auto
    hence "?S \<subseteq> lab_decisions \<A> Q"
      unfolding lab_decisions_order[symmetric] by blast
    thus ?thesis using rep lab_decisions_order[of \<A> ?N Q] by simp
  qed
  have qN: "qidealLab\<^sup>\<A> att ?N"
    using adm_N below unfolding qidealLab_def by blast
  have "L \<sqsubseteq>\<^sup>\<A> ?N" "M \<sqsubseteq>\<^sup>\<A> ?N"
    using rep lab_decisions_order[of \<A> L ?N] lab_decisions_order[of \<A> M ?N] by auto
  thus ?thesis using qN by blast
qed

(* the two provided definitions of ideal labellings are equivalent *)
lemma ideal_defEq: \<open>idealLab\<^sup>\<A> att Lab \<longleftrightarrow> idealLab2\<^sup>\<A> att Lab\<close>
proof
  assume ideal: "idealLab\<^sup>\<A> att Lab"
  show "idealLab2\<^sup>\<A> att Lab"
    using ideal unfolding idealLab_def idealLab2_def
      equivalentLab_rel_def lessOrEquallyCommittedLab_def by blast
next
  assume max: "idealLab2\<^sup>\<A> att Lab"
  have q: "qidealLab\<^sup>\<A> att Lab" using max unfolding idealLab2_def by blast
  have below: "L \<sqsubseteq>\<^sup>\<A> Lab" if l: "qidealLab\<^sup>\<A> att L" for L
  proof -
    obtain N where qN: "qidealLab\<^sup>\<A> att N"
      and up: "Lab \<sqsubseteq>\<^sup>\<A> N" "L \<sqsubseteq>\<^sup>\<A> N"
      using qideal_directed[OF q l] by blast
    have "N \<cong>\<^sup>\<A> Lab" using max qN up(1) unfolding idealLab2_def by blast
    thus ?thesis using up(2) unfolding equivalentLab_rel_def lessOrEquallyCommittedLab_def by blast
  qed
  show "idealLab\<^sup>\<A> att Lab" using q below unfolding idealLab_def by blast
qed


(* Prop 14 from BCG *)
lemma grounded_below_ideal: \<open>groundedLab\<^sup>\<A> att Lab1 \<Longrightarrow> idealLab\<^sup>\<A> att Lab2 \<Longrightarrow> Lab1 \<sqsubseteq>\<^sup>\<A> Lab2\<close>
proof -
  assume g: "groundedLab\<^sup>\<A> att Lab1" and i: "idealLab\<^sup>\<A> att Lab2"
  have least_in: "least\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab1 in"
    using g unfolding grounded_defEq groundedLab2_def .
  have comp1: "completeLab\<^sup>\<A> att Lab1" using least_in unfolding least_rel_def by blast
  have below: "Lab1 \<sqsubseteq>\<^sup>\<A> P" if pref: "preferredLab\<^sup>\<A> att P" for P
  proof -
    have comp_P: "completeLab\<^sup>\<A> att P"
      using pref unfolding preferredLab_def maximal_rel_def by blast
    have ins: "(in Lab1) \<subseteq>\<^sup>\<A> (in P)"
      using least_in comp_P unfolding least_rel_def by blast
    have "(out Lab1) \<subseteq>\<^sup>\<A> (out P)"
      using complete_in_out_mono[OF comp1 comp_P] ins by blast
    thus ?thesis using ins unfolding lessOrEquallyCommittedLab_def by blast
  qed
  have "qidealLab\<^sup>\<A> att Lab1"
    using comp1 below unfolding qidealLab_def completeLab_def by blast
  thus ?thesis using i unfolding idealLab_def by blast
qed


text \<open>ideal labelling are unique.\<close>
lemma ideal_unique: \<open>idealLab\<^sup>\<A> att Lab1 \<Longrightarrow> idealLab\<^sup>\<A> att Lab2 \<Longrightarrow> \<forall>a. \<A> a \<longrightarrow> Lab1 a = Lab2 a\<close>
proof -
  assume i1: "idealLab\<^sup>\<A> att Lab1" and i2: "idealLab\<^sup>\<A> att Lab2"
  have "Lab1 \<sqsubseteq>\<^sup>\<A> Lab2" "Lab2 \<sqsubseteq>\<^sup>\<A> Lab1"
    using i1 i2 unfolding idealLab_def by auto
  thus ?thesis unfolding lessOrEquallyCommittedLab_def
    by (smt (verit) Label.exhaust inset_def outset_def)
qed

subsection \<open>Stable, semi-stable and stage labellings\<close>

text \<open>the (nonempty) AF in which every arguments attacks itself does not have a stable labelling.\<close>
lemma stableLem01: \<open>\<exists>x. \<A> x \<longrightarrow> (\<forall>Lab. \<not>stableLab\<^sup>\<A> (\<lambda>x y. x = y) Lab)\<close>
  unfolding stableLab_def completeLab_def by (metis (full_types) Label.exhaust admissibleLabConflictfree completeLab2_def completeLab_def complete_defEq conflictfreeLab_def inset_def legallyIn_def outset_def)

text \<open>stable labellings do not exist necessarily.\<close>
corollary \<open>\<exists>x. \<A> x \<longrightarrow> (\<exists>att. \<forall>Lab. \<not>stableLab\<^sup>\<A> att Lab)\<close> using stableLem01 by auto

text \<open>Lemma 14 from Dung. S is a stable extension iff S = {A | A is not attacked by S}.
Adapted to Labelings: It's weaker as we have to deal with Undec as well.\<close>
lemma lem14Dung: "stableLab\<^sup>\<A> att Lab \<longrightarrow> (\<forall>a. \<A> a \<longrightarrow> (in(Lab) a \<longleftrightarrow> \<not>(\<exists>b. \<A> b \<and> in(Lab) b \<and> att b a)))" unfolding stableLab_def complete_defEq
  by (metis (full_types) Label.distinct(1) Label.exhaust completeLab2_def inset_def legallyOut_def outset_def)

text \<open>Lemma 15 from Dung. Every stable extension is a preferred extension, but not vice versa.
Adapted to Labellings.\<close>
lemma lem15Dung: \<open>stableLab\<^sup>\<A> att Lab \<Longrightarrow> preferredLab\<^sup>\<A> att Lab\<close>
proof -
  assume stable: "stableLab\<^sup>\<A> att Lab"
  have comp: "completeLab\<^sup>\<A> att Lab" using stable unfolding stableLab_def by blast
  have reverse_in: "(in M) \<subseteq>\<^sup>\<A> (in Lab)"
    if comp_M: "completeLab\<^sup>\<A> att M" and sub: "(in Lab) \<subseteq>\<^sup>\<A> (in M)" for M
  proof -
    have outs: "(out Lab) \<subseteq>\<^sup>\<A> (out M)"
      using complete_in_out_mono[OF comp comp_M] sub by blast
    show ?thesis using stable outs unfolding stableLab_def
      by (smt (verit) Label.exhaust Label.distinct inset_def outset_def)
  qed
  show ?thesis using comp reverse_in unfolding preferredLab_def maximal_rel_def by blast
qed

lemma \<open>preferredLab\<^sup>\<A> att Lab \<Longrightarrow> stableLab\<^sup>\<A> att Lab\<close> nitpick oops (* counterexample *)

text \<open>infinite frameworks need not have semi-stable labellings.\<close>
lemma semistable_exists:
  assumes fin: "finite {x. \<A> x}"
  shows "\<exists>Lab. semistableLab\<^sup>\<A> att Lab"
proof -
  have nonempty: "\<exists>Lab. completeLab\<^sup>\<A> att Lab"
    using complete_least_in_exists unfolding least_rel_def by blast
  show ?thesis unfolding semistableLab_def
    by (rule finite_minimal_rel[OF fin nonempty])
qed

(* Theorem 3 of BCG *)
lemma \<open>\<exists>Lab. stableLab\<^sup>\<A> att Lab \<Longrightarrow> \<forall>L. (stageLab\<^sup>\<A> att L \<longrightarrow> stableLab\<^sup>\<A> att L)\<close> 
proof -
  assume "\<exists>Lab. stableLab\<^sup>\<A> att Lab"
  then obtain S where stable: "stableLab\<^sup>\<A> att S" by blast
  have cf_S: "conflictfreeLab\<^sup>\<A> att S"
    using stable admissibleLabConflictfree unfolding stableLab_def completeLab_def by blast
  show ?thesis
  proof (intro allI impI)
    fix L assume stage: "stageLab\<^sup>\<A> att L"
    have cf_L: "conflictfreeLab\<^sup>\<A> att L"
      using stage unfolding stageLab_def minimal_rel_def by blast
    have empty_S: "\<forall>x. \<A> x \<longrightarrow> \<not> undec S x"
      using stable unfolding stableLab_def undecset_def by blast
    have "(undec S) \<approx>\<^sup>\<A> (undec L)"
      using stage cf_S empty_S unfolding stageLab_def minimal_rel_def by blast
    hence total: "\<forall>x. \<A> x \<longrightarrow> L x \<noteq> Undec"
      using empty_S unfolding undecset_def by blast
    have adm: "admissibleLab\<^sup>\<A> att L"
      using cf_L total unfolding admissibleLab_def conflictfreeLab_def
        legallyIn_def legallyOut_def inset_def outset_def
      by (metis Label.exhaust)
    show "stableLab\<^sup>\<A> att L"
      using adm total unfolding stableLab_def completeLab_def undecset_def by blast
  qed
qed

end

