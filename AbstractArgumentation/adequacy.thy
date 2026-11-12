(* D. Fuenmayor and A. Steen, August 2021 *)
(* This file contains various meta-theoretical properties of different argumentation semantics. *)
(* Auxiliary references:
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
            Knowledge Engineering Review (2011)
 [Dung 1995] Dung, P.M., On the acceptability of arguments and its fundamental role in nonmonotonic reasoning,
             logic programming and n-person games, Artificial Intelligence. (1995)
*)
theory "adequacy"
  imports "extensions" "labellings" "Zorn-lemma" "ext-properties" "lab-properties"
begin

section \<open>Adequacy of the Argumentation Encoding\<close>

text \<open>We verify central results from the literature to demonstrate the adequacy of the higher-order
encoding.\<close>

text \<open>We follow the results and lemma numbering in Section 4.2 of the article by Steen and
Fuenmayor. Correspondence results appear in correspondence.thy; relationships between
semantics appear in ext-relationships.thy and lab-relationships.thy.\<close>

text \<open>Lemma 4.3: A conflict-free extension contains no self-attacking arguments [BCG 2011, p. 8].\<close>
lemma cf_noselfattacks: \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> \<not> (\<exists>\<^sup>\<A> (\<lambda>a. (S a) \<and> (att a a))) \<close> 
  by (simp add: conflictfreeExt_def)

text \<open>Lemma 4.4: The characteristic function preserves conflict-freeness.\<close>
lemma cf_preserveChar: \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> conflictfreeExt\<^sup>\<A> att (\<F>\<^sup>\<A> att S)\<close>
  by (smt (verit) conflictfreeExt_def defends_rel_def)

text \<open>Lemma 4.5: A conflict-free set S is admissible if and only if it is a subset of
@{text "\<F>"}(S) [Dung 1995, Lemma 18].\<close>
lemma cf_admissibleChar: \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> admissibleExt\<^sup>\<A> att S \<longleftrightarrow> S \<subseteq>\<^sup>\<A> \<F>\<^sup>\<A> att S\<close> 
  by (simp add: admissibleExt_def)

text \<open>Lemma 4.6: Admissible sets can be extended with defended arguments (Dung's fundamental lemma)
[Dung 1995, Lemma 10].\<close>
lemma dung_fundlemma_1: \<open>(admissibleExt\<^sup>\<A> att S) \<and> (defends\<^sup>\<A> att S a) \<Longrightarrow> admissibleExt\<^sup>\<A> att (S \<union> \<lbrace>a\<rbrace>)\<close>
  by (smt (z3) admissibleExt_def conflictfreeExt_def defends_rel_def)

lemma dung_fundlemma_2: \<open>(admissibleExt\<^sup>\<A> att S) \<and> (defends\<^sup>\<A> att S a) \<and> (defends\<^sup>\<A> att S a') \<Longrightarrow> defends\<^sup>\<A> att (S \<union> \<lbrace>a\<rbrace>) a'\<close> 
  by (metis (full_types, lifting) MONO_def \<F>_mono')

text \<open>Lemma 4.7: Admissible sets form an @{text "\<omega>"}-complete partial order under set
inclusion [Dung 1995, Theorem 11(1)].\<close>
(* We can, in fact, prove a stronger statement: admissible extensions form a dcpo*)
lemma admissibleDirectedComplete: "dcpo\<^sup>\<A> (admissibleExt\<^sup>\<A> AF)" 
  unfolding admissibleExt_def conflictfreeExt_def defends_rel_def directedcomplete_rel_def directed_rel_def
    supremum_def by meson
lemma admissibleOmegaComplete: "\<omega>-cpo\<^sup>\<A> (admissibleExt\<^sup>\<A> AF)" by (simp add: admissibleDirectedComplete dcpo_\<omega>_rel)

text \<open>Lemma 4.8: Every admissible set is contained in a preferred extension [Dung 1995, Theorem
11(2)].\<close>
lemma DungTh11: "admissibleExt\<^sup>\<A> att S \<longrightarrow> (\<exists>E. S \<subseteq>\<^sup>\<A> E \<and> preferredExt\<^sup>\<A> att E)" 
  using ZornLemma2_\<omega>_rel admissibleOmegaComplete  
  by (metis preferredExt2_def preferredExt_defEq)

text \<open>Lemma 4.9: A conflict-free set is complete if and only if it is a fixed point of
@{text "\<F>"}.\<close>
lemma complete_fix: \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> completeExt\<^sup>\<A> att S \<longleftrightarrow> S \<approx>\<^sup>\<A> \<F>\<^sup>\<A> att S\<close> 
  by (metis admissibleExt_def completeExt_def)

text \<open>Lemma 4.10: Complete, preferred, and grounded extensions always exist.\<close>
lemma completeExtExists: \<open>\<exists>E. completeExt\<^sup>\<A> att E\<close> 
  by (metis DungTh11 emptyAdmissible maximal_rel_def preferredExt_def)
lemma preferredExtExists: \<open>\<exists>E. preferredExt\<^sup>\<A> att E\<close> 
  by (meson DungTh11 emptyAdmissible maximal_rel_def preferredExt_def)
lemma groundedExtExists: \<open>\<exists>E. groundedExt\<^sup>\<A> att E\<close> 
  by (meson \<F>_leastFP_ex groundedExt3_def groundedExt_defEq1 groundedExt_defEq2 DungTh11 emptyAdmissible minimal_rel_def groundedExt_def)

text \<open>Lemma 4.11: Grounded labellings can equivalently be characterised by minimal in-sets or
minimal out-sets [BCG 2011, Proposition 5].\<close>
lemma complete_sets_mono: \<open>completeLab\<^sup>\<A> att Lab1 \<and> completeLab\<^sup>\<A> att Lab2 \<Longrightarrow> in(Lab1) \<subseteq>\<^sup>\<A> in(Lab2) \<longleftrightarrow> out(Lab1) \<subseteq>\<^sup>\<A> out(Lab2)\<close>
  unfolding completeLab_def inset_def outset_def
  by (smt (z3) Label.exhaust admissibleLab_def inset_def legallyIn_def legallyOut_def legallyUndec_def outset_def undecset_def)

lemma complete_min_inout: \<open>minimal\<^sup>\<A>  (completeLab\<^sup>\<A> att) Lab in \<longleftrightarrow> minimal\<^sup>\<A>  (completeLab\<^sup>\<A> att) Lab out \<close>
  by (smt (verit) complete_sets_mono minimal_rel_def)

text \<open>Lemma 4.12: Grounded extensions and grounded labellings are unique [BCG 2011, Proposition 4].\<close>
lemma \<open>groundedExt\<^sup>\<A> att E \<longleftrightarrow> least\<^sup>\<A> (completeExt\<^sup>\<A> att) E id\<close>
  by (simp add: groundedExt2_def groundedExt_defEq1)
lemma \<open>groundedLab\<^sup>\<A> att Lab \<longleftrightarrow> least\<^sup>\<A> (groundedLab\<^sup>\<A> att) Lab in\<close>
  by (metis (full_types) grounded_unique inset_def least_rel_def)

text \<open>Lemma 4.13: Preferred labellings can equivalently be characterised by maximal in-sets or
maximal out-sets [BCG 2011, Proposition 8].\<close>
lemma preferred_max_inout: \<open>maximal\<^sup>\<A>  (completeLab\<^sup>\<A> att) Lab in \<longleftrightarrow> maximal\<^sup>\<A>  (completeLab\<^sup>\<A> att) Lab out \<close>
  using prop8 by auto

text \<open>For relationships between semantics, see ext-relationships.thy and lab-relationships.thy.\<close>
text \<open>For correspondence results, see correspondence.thy.\<close>

text \<open>The following properties supplement the results presented in the article.\<close>
lemma \<open>conflictfreeExt\<^sup>\<A> att S \<and>  minimal\<^sup>\<A> (fixpoint\<^sup>\<A> (\<F>\<^sup>\<A> att)) S id \<Longrightarrow> lfp\<^sup>\<A> att S  \<close>  
  by (meson \<F>_leastFP_ex lfpR_def minLeastCollapse_rel)

lemma emptyset_is_cf: \<open>conflictfreeExt\<^sup>\<A> att (\<lambda>x. False)\<close> 
  by (simp add: conflictfreeExt_def)

lemma char_is_cf: \<open>conflictfreeExt\<^sup>\<A> att (\<F>\<^sup>\<A> att (\<lambda>x. False))\<close> 
  by (simp add: cf_preserveChar emptyset_is_cf)

lemma \<open> maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab in \<longleftrightarrow>  maximal\<^sup>\<A> (completeLab\<^sup>\<A> att) Lab out\<close>
  by (smt (verit) complete_sets_mono maximal_rel_def)

lemma \<open> maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) S id \<Longrightarrow>  maximal\<^sup>\<A> (completeExt\<^sup>\<A> att) S id\<close>
  unfolding maximal_rel_def completeExt_def admissibleExt_def by (smt (z3) conflictfreeExt_def defends_rel_def id_apply)

end
