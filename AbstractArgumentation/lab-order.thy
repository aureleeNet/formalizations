theory "lab-order"
  imports labellings "Zorn-lemma"
begin

(* A decision is an argument together with its In/Out label (True/False).
   Undec is represented by absence of both decisions.  This is an order
   representation of labellings for the generic powerset lemmas in misc. *)
definition lab_decisions :: "'a Set \<Rightarrow> 'a Labelling \<Rightarrow> ('a \<times> bool) Set"
  where "lab_decisions A L p \<equiv> A (fst p) \<and>
    (if snd p then in L (fst p) else out L (fst p))"

definition decisions_lab :: "('a \<times> bool) Set \<Rightarrow> 'a Labelling"
  where "decisions_lab S a \<equiv> if S (a, True) then In else
    if S (a, False) then Out else Undec"

definition consistent_decisions :: "'a Set \<Rightarrow> ('a \<times> bool) Set \<Rightarrow> bool"
  where "consistent_decisions A S \<equiv> \<forall>a.
    ((S (a, True) \<or> S (a, False)) \<longrightarrow> A a) \<and>
    \<not> (S (a, True) \<and> S (a, False))"

definition lab_update :: "'a Set \<Rightarrow> 'a Rel \<Rightarrow>
    ('a \<times> bool) Set \<Rightarrow> ('a \<times> bool) Set"
  where "lab_update A att S p \<equiv> A (fst p) \<and>
    (if snd p then (\<forall>b. A b \<longrightarrow> att b (fst p) \<longrightarrow> S (b, False))
     else (\<exists>b. A b \<and> att b (fst p) \<and> S (b, True)))"

definition admissible_decisions :: "'a Set \<Rightarrow> 'a Rel \<Rightarrow>
    ('a \<times> bool) Set \<Rightarrow> bool"
  where "admissible_decisions A att S \<equiv>
    consistent_decisions A S \<and> S \<subseteq> lab_update A att S"

lemma lab_decisions_consistent: "consistent_decisions A (lab_decisions A L)"
  unfolding consistent_decisions_def lab_decisions_def inset_def outset_def by auto

lemma decisions_lab_inverse:
  assumes cs: "consistent_decisions A S"
  shows "lab_decisions A (decisions_lab S) = S"
proof (rule ext)
  fix p :: "'a \<times> bool"
  obtain a b where p: "p = (a, b)" by (cases p) auto
  show "lab_decisions A (decisions_lab S) p = S p"
    using cs unfolding p consistent_decisions_def lab_decisions_def
      decisions_lab_def inset_def outset_def
    by (cases b) auto
qed

lemma consistent_decisions_subset:
  "consistent_decisions A T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> consistent_decisions A S"
  unfolding consistent_decisions_def by blast

lemma lab_decisions_order:
  "lab_decisions A L \<subseteq> lab_decisions A M \<longleftrightarrow> L \<sqsubseteq>\<^sup>A M"
  unfolding lab_decisions_def lessOrEquallyCommittedLab_def
  by (auto split: if_splits)

lemma lab_decisions_equiv:
  "lab_decisions A L = lab_decisions A M \<longleftrightarrow> L \<cong>\<^sup>A M"
proof -
  have "(lab_decisions A L = lab_decisions A M) \<longleftrightarrow>
    (lab_decisions A L \<subseteq> lab_decisions A M \<and>
     lab_decisions A M \<subseteq> lab_decisions A L)" 
    by auto
  also have "... \<longleftrightarrow> L \<cong>\<^sup>A M"
    unfolding lab_decisions_order lessOrEquallyCommittedLab_def equivalentLab_rel_def by blast
  finally show ?thesis .
qed

lemma lab_update_mono: "MONO (lab_update A att)"
  unfolding MONO_def lab_update_def by auto

lemma lab_update_monoD:
  "S \<subseteq> T \<Longrightarrow> lab_update A att S \<subseteq> lab_update A att T"
  unfolding lab_update_def by auto

lemma lab_update_consistent:
  "consistent_decisions A S \<Longrightarrow> consistent_decisions A (lab_update A att S)"
  unfolding consistent_decisions_def lab_update_def by auto

lemma all_decision_tags: "(\<forall>b :: bool. P b) \<longleftrightarrow> (P True \<and> P False)"
  by (metis (full_types))

lemma admissible_lab_decisions:
  "admissible_decisions A att (lab_decisions A L) \<longleftrightarrow> admissibleLab\<^sup>A att L"
  unfolding admissible_decisions_def
  by (simp add: lab_decisions_consistent lab_decisions_def lab_update_def
      admissibleLab_def legallyIn_def legallyOut_def all_decision_tags; blast)

lemma complete_lab_decisions:
  "fixpoint (lab_update A att) (lab_decisions A L) \<longleftrightarrow> completeLab\<^sup>A att L"
  by (simp add: fixpoint_def lab_update_def lab_decisions_def complete_defEq
      completeLab2_def legallyIn_def legallyOut_def all_decision_tags; blast)

lemma decisions_fixpoint_complete:
  assumes cs: "consistent_decisions A S" and fp: "fixpoint (lab_update A att) S"
  shows "completeLab\<^sup>A att (decisions_lab S)"
proof -
  have represented: "fixpoint (lab_update A att) (lab_decisions A (decisions_lab S))"
    unfolding decisions_lab_inverse[OF cs] by (rule fp)
  show ?thesis by (rule complete_lab_decisions[THEN iffD1, OF represented])
qed

lemma admissible_decisions_update:
  assumes adm: "admissible_decisions A att S"
  shows "admissible_decisions A att (lab_update A att S)"
proof -
  have cs: "consistent_decisions A S" and sub: "S \<subseteq> lab_update A att S"
    using adm unfolding admissible_decisions_def by auto
  have "lab_update A att S \<subseteq> lab_update A att (lab_update A att S)"
    by (rule lab_update_monoD[OF sub])
  thus ?thesis using lab_update_consistent[OF cs]
    unfolding admissible_decisions_def by blast
qed

lemma admissible_decisions_union:
  assumes s: "admissible_decisions A att S" and t: "admissible_decisions A att T"
    and cs: "consistent_decisions A (S \<union> T)"
  shows "admissible_decisions A att (S \<union> T)"
proof -
  have sub_S: "S \<subseteq> lab_update A att S" and sub_T: "T \<subseteq> lab_update A att T"
    using s t unfolding admissible_decisions_def by auto
  have mono_S: "lab_update A att S \<subseteq> lab_update A att (S \<union> T)"
    by (rule lab_update_monoD) auto
  have mono_T: "lab_update A att T \<subseteq> lab_update A att (S \<union> T)"
    by (rule lab_update_monoD) auto
  show ?thesis using cs sub_S sub_T mono_S mono_T unfolding admissible_decisions_def by blast
qed

lemma admissible_decisions_chain_complete: "\<omega>-cpo (admissible_decisions A att)"
proof (unfold omegacomplete_def, intro allI impI)
  fix C
  assume c: "C \<subseteq> admissible_decisions A att \<and> chain C"
  have member_cs: "consistent_decisions A X" if "C X" for X
    using c that unfolding admissible_decisions_def by blast
  have cs: "consistent_decisions A (\<^bold>\<Or>C)"
    unfolding consistent_decisions_def
  proof (intro allI conjI impI)
    fix a
    assume "(\<^bold>\<Or>C) (a, True) \<or> (\<^bold>\<Or>C) (a, False)"
    then obtain X where "C X" "X (a, True) \<or> X (a, False)"
      unfolding supremum_def by blast
    thus "A a" using member_cs[of X] unfolding consistent_decisions_def by blast
  next
    fix a
    show "\<not> ((\<^bold>\<Or>C) (a, True) \<and> (\<^bold>\<Or>C) (a, False))"
    proof
      assume "(\<^bold>\<Or>C) (a, True) \<and> (\<^bold>\<Or>C) (a, False)"
      then obtain X Y where x: "C X" "X (a, True)" and y: "C Y" "Y (a, False)"
        unfolding supremum_def by blast
      have "X \<subseteq> Y \<or> Y \<subseteq> X" using c x(1) y(1) unfolding chain_def by blast
      thus False using member_cs[OF x(1)] member_cs[OF y(1)] x(2) y(2)
        unfolding consistent_decisions_def by blast
    qed
  qed
  have sub: "\<^bold>\<Or>C \<subseteq> lab_update A att (\<^bold>\<Or>C)"
  proof (intro allI impI)
    fix p assume "(\<^bold>\<Or>C) p"
    then obtain X where cx: "C X" and xp: "X p" unfolding supremum_def by blast
    have sub_X: "X \<subseteq> lab_update A att X"
      using c cx unfolding admissible_decisions_def by blast
    have "X \<subseteq> \<^bold>\<Or>C" using cx unfolding supremum_def by blast
    hence "lab_update A att X \<subseteq> lab_update A att (\<^bold>\<Or>C)"
      by (rule lab_update_monoD)
    thus "lab_update A att (\<^bold>\<Or>C) p" using sub_X xp by blast
  qed
  show "admissible_decisions A att (\<^bold>\<Or>C)"
    using cs sub unfolding admissible_decisions_def by blast
qed

lemma maximal_admissible_decisions_exists:
  "\<exists>S. maximal (admissible_decisions A att) S id"
  by (rule ZornLemma_\<omega>[OF admissible_decisions_chain_complete])

lemma maximal_admissible_decisions_bound:
  assumes max: "maximal (admissible_decisions A att) S id"
    and member: "admissible_decisions A att T" and sub: "S \<subseteq> T"
  shows "T \<approx> S"
proof -
  have bound: "\<forall>X. admissible_decisions A att X \<and> S \<subseteq> X \<longrightarrow> X \<approx> S"
    by (rule conjunct2[OF max[unfolded maximal_def id_apply]])
  show ?thesis using bound[THEN spec, of T] member sub by blast
qed

lemma maximal_admissible_decisions_fixpoint:
  assumes max: "maximal (admissible_decisions A att) S id"
  shows "fixpoint (lab_update A att) S"
proof -
  have adm: "admissible_decisions A att S" using max unfolding maximal_def by blast
  have step: "admissible_decisions A att (lab_update A att S)"
    by (rule admissible_decisions_update[OF adm])
  have sub: "S \<subseteq> lab_update A att S" using adm unfolding admissible_decisions_def by blast
  show ?thesis unfolding fixpoint_def
    by (rule maximal_admissible_decisions_bound[OF max step sub])
qed

lemma maximal_admissible_decisions_complete:
  assumes max: "maximal (admissible_decisions A att) S id"
  shows "completeLab\<^sup>A att (decisions_lab S)"
proof -
  have cs: "consistent_decisions A S"
    using max unfolding maximal_def admissible_decisions_def by blast
  have fp: "fixpoint (lab_update A att) S"
    by (rule maximal_admissible_decisions_fixpoint[OF max])
  show ?thesis by (rule decisions_fixpoint_complete[OF cs fp])
qed

end
