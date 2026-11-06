(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains the verification of meta-theoretical connections of labelling-based semanticss. 
   Auxiliary references: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011) 
*)
theory "lab-relationships"
  imports "labellings"  "lab-properties"
begin


(************************************************************************)
(* Inclusion relations as summary: Figure 12 of [BCG2011]
   All inclusions verified. The non-inclusion of the inverse directions has been checked
   with Nitpick in every case.  *)
(************************************************************************)

lemma stage_implies_cf: \<open>stageLab\<^sup>\<A> AF Lab \<Longrightarrow> conflictfreeLab\<^sup>\<A> AF Lab\<close> 
  by (simp add: minimal_rel_def stageLab_def)
 
lemma admissible_implies_cf: \<open>admissibleLab\<^sup>\<A> AF Lab \<Longrightarrow> conflictfreeLab\<^sup>\<A> AF Lab\<close>
  by (simp add: admissibleLab_def conflictfreeLab_def inset_def legallyIn_def legallyOut_def outset_def)

lemma complete_implies_admissible: \<open>completeLab\<^sup>\<A> AF Lab \<Longrightarrow> admissibleLab\<^sup>\<A> AF Lab\<close> 
  by (simp add: admissibleLab_def completeLab_def)

lemma grounded_implies_complete: \<open>groundedLab\<^sup>\<A> AF Lab \<Longrightarrow> completeLab\<^sup>\<A> AF Lab\<close>
  by (simp add: groundedLab_def minimal_rel_def)

lemma preferred_implies_complete: \<open>preferredLab\<^sup>\<A> AF Lab \<Longrightarrow> completeLab\<^sup>\<A> AF Lab\<close> 
  by (simp add: maximal_rel_def preferredLab_def)

lemma ideal_implies_complete: "idealLab\<^sup>\<A> AF Lab \<Longrightarrow> completeLab\<^sup>\<A> AF Lab"
proof -
  assume ideal: "idealLab\<^sup>\<A> AF Lab"
  let ?S = "lab_decisions \<A> Lab"
  let ?T = "lab_update \<A> AF ?S"
  let ?N = "decisions_lab ?T"
  have qL: "qidealLab\<^sup>\<A> AF Lab" using ideal unfolding idealLab_def by blast
  have adm_S: "admissible_decisions \<A> AF ?S"
    using qL admissible_lab_decisions[of \<A> AF Lab] unfolding qidealLab_def by blast
  have adm_T: "admissible_decisions \<A> AF ?T"
    by (rule admissible_decisions_update[OF adm_S])
  have cs: "consistent_decisions \<A> ?T"
    using adm_T unfolding admissible_decisions_def by blast
  have rep: "lab_decisions \<A> ?N = ?T" by (rule decisions_lab_inverse[OF cs])
  have adm_N: "admissibleLab\<^sup>\<A> AF ?N"
    using admissible_lab_decisions[of \<A> AF ?N] rep adm_T by simp
  have below: "?N \<sqsubseteq>\<^sup>\<A> P" if pref: "preferredLab\<^sup>\<A> AF P" for P
  proof -
    have sub: "?S \<subseteq> lab_decisions \<A> P"
      using qL pref unfolding qidealLab_def lab_decisions_order by blast
    have comp_P: "completeLab\<^sup>\<A> AF P"
      using pref unfolding preferredLab_def maximal_rel_def by blast
    have fp_P: "fixpoint (lab_update \<A> AF) (lab_decisions \<A> P)"
      using complete_lab_decisions[of \<A> AF P] comp_P by blast
    have mono: "?T \<subseteq> lab_update \<A> AF (lab_decisions \<A> P)"
      by (rule lab_update_monoD[OF sub])
    have "?T \<subseteq> lab_decisions \<A> P"
      using mono fp_P unfolding fixpoint_def by blast
    thus ?thesis using rep lab_decisions_order[of \<A> ?N P] by simp
  qed
  have qN: "qidealLab\<^sup>\<A> AF ?N" using adm_N below unfolding qidealLab_def by blast
  have "?N \<sqsubseteq>\<^sup>\<A> Lab" using ideal qN unfolding idealLab_def by blast
  hence reverse_sub: "?T \<subseteq> ?S" using rep lab_decisions_order[of \<A> ?N Lab] by simp
  have "?S \<subseteq> ?T" using adm_S unfolding admissible_decisions_def by blast
  hence "fixpoint (lab_update \<A> AF) ?S" using reverse_sub unfolding fixpoint_def by blast
  thus ?thesis by (simp only: complete_lab_decisions)
qed
  
lemma \<open>stableLab\<^sup>\<A> AF Lab \<Longrightarrow> stageLab\<^sup>\<A> AF Lab\<close>
  by (simp add: admissible_implies_cf leastMin_rel least_rel_def stableLab_def stageLab_def complete_implies_admissible undecset_def) 

lemma \<open>semistableLab\<^sup>\<A> AF Lab \<Longrightarrow> preferredLab\<^sup>\<A> AF Lab \<close> unfolding semistableLab_def preferredLab_def minimal_rel_def maximal_rel_def
  by (smt (verit, ccfv_SIG) Label.exhaust completeLab2_def complete_defEq inset_def legallyOut_def outset_def undecset_def)

lemma \<open>stableLab\<^sup>\<A> AF Lab \<Longrightarrow> semistableLab\<^sup>\<A> AF Lab\<close> 
  by (simp add: semistableLab_def stableLab_def undecset_def minimal_rel_def)

end
