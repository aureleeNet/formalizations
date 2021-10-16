theory "adequacy"
  imports "extensions" "labellings" "Zorn-lemma" "ext-properties"
begin

(*** Properties as used in JLC article section 4.2 ****)
(* except for those about correspondence, they are in correspondence-rel.thy *)

(* 1.  no self-attacks in conflictfree extension  [BCG textual on p.8] *)
(*lemma \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> \<not> (\<exists>A. (\<A> A) \<and> (S A) \<and> (att A A)) \<close> 
  by (simp add: conflictfreeExt_def)*)

lemma cf_noselfattacks: \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> \<not> (\<exists>\<^sup>\<A> (\<lambda>a. (S a) \<and> (att a a))) \<close> 
  by (simp add: conflictfreeExt_def)

(********* [Dung 1995] Theorem 11: *************)
(*(1) Admissible sets form an \<omega>-complete poset.*)
(* We can, in fact, prove a stronger statement: admissible extensions form a dcpo*)
lemma admissibleDirectedComplete: "dcpo\<^sup>\<A> (admissibleExt\<^sup>\<A> AF)" 
  unfolding admissibleExt_def conflictfreeExt_def defends_rel_def directedcomplete_rel_def directed_rel_def supremum_def by meson
lemma admissibleOmegaComplete: "\<omega>-cpo\<^sup>\<A> (admissibleExt\<^sup>\<A> AF)" by (simp add: admissibleDirectedComplete dcpo_\<omega>_rel)
lemma cf_admissibleChar: \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> admissibleExt\<^sup>\<A> att S \<longleftrightarrow> S \<subseteq>\<^sup>\<A> \<F>\<^sup>\<A> att S\<close> 
  by (simp add: admissibleExt_def)

lemma cf_preserveChar: \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> conflictfreeExt\<^sup>\<A> att (\<F>\<^sup>\<A> att S)\<close>
  by (smt (verit) conflictfreeExt_def defends_rel_def)


lemma dung_fundlemma_1: \<open>(admissibleExt\<^sup>\<A> att S) \<and> (defends\<^sup>\<A> att S a) \<Longrightarrow> admissibleExt\<^sup>\<A> att (S \<union> \<lbrace>a\<rbrace>)\<close>
  by (smt (z3) admissibleExt_def conflictfreeExt_def defends_rel_def)

lemma dung_fundlemma_2: \<open>(admissibleExt\<^sup>\<A> att S) \<and> (defends\<^sup>\<A> att S a) \<and> (defends\<^sup>\<A> att S a') \<Longrightarrow> defends\<^sup>\<A> att (S \<union> \<lbrace>a\<rbrace>) a'\<close> 
  by (metis (full_types, lifting) MONO_def \<F>_mono')

(* admissible sets are CPO: todo *)
(*(2) For each admissible set S there exists a preferred extension E, such that S \<subseteq> E. *)
lemma DungTh11: "admissibleExt\<^sup>\<A> att S \<longrightarrow> (\<exists>E. S \<subseteq>\<^sup>\<A> E \<and> preferredExt\<^sup>\<A> att E)" 
  using ZornLemma2_\<omega>_rel admissibleOmegaComplete  
  by (metis preferredExt2_def preferredExt_defEq)

lemma \<open>\<exists>E. completeExt\<^sup>\<A> att E\<close> 
  by (metis DungTh11 emptyAdmissible maximal_rel_def preferredExt_def)

lemma \<open>\<exists>E. preferredExt\<^sup>\<A> att E\<close> 
  by (meson DungTh11 emptyAdmissible maximal_rel_def preferredExt_def)

lemma \<open>\<exists>E. groundedExt\<^sup>\<A> att E\<close> 
  by (meson \<F>_leastFP_ex groundedExt3_def groundedExt_defEq1 groundedExt_defEq2 DungTh11 emptyAdmissible minimal_rel_def groundedExt_def)

(* complete stuff *)
lemma complete_fix: \<open>conflictfreeExt\<^sup>\<A> att S \<Longrightarrow> completeExt\<^sup>\<A> att S \<longleftrightarrow> S \<approx>\<^sup>\<A> \<F>\<^sup>\<A> att S\<close> 
  by (metis admissibleExt_def completeExt_def)


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
  
lemma complete_sets_mono: \<open>completeLab\<^sup>\<A> att Lab1 \<and> completeLab\<^sup>\<A> att Lab2 \<Longrightarrow> in(Lab1) \<subseteq>\<^sup>\<A> in(Lab2) \<longleftrightarrow> out(Lab1) \<subseteq>\<^sup>\<A> out(Lab2)\<close>
  unfolding completeLab_def inset_def outset_def
  by (smt (z3) Label.exhaust admissibleLab_def inset_def legallyIn_def legallyOut_def legallyUndec_def outset_def undecset_def)

lemma complete_min_inout: \<open>minimal\<^sup>\<A>  (completeLab\<^sup>\<A> att) Lab in \<longleftrightarrow> minimal\<^sup>\<A>  (completeLab\<^sup>\<A> att) Lab out \<close>
  by (smt (verit) complete_sets_mono minimal_rel_def)

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

lemma \<open> maximal\<^sup>\<A> (completeExt\<^sup>\<A> att) S id \<Longrightarrow>  maximal\<^sup>\<A> (admissibleExt\<^sup>\<A> att) S id\<close>
  oops



(* todo from here *)

lemma \<open> lfp\<^sup>\<A> att S  \<Longrightarrow>  conflictfreeExt\<^sup>\<A> att S \<close> 
proof -
  assume *: \<open>lfp\<^sup>\<A> att S\<close> 
  from * have \<open>S \<approx>\<^sup>\<A> \<F>\<^sup>\<A> att S\<close> 
    by (metis (mono_tags, hide_lams) fixpoint_rel_def least_rel_def lfpR_def)
  assume **:  \<open>\<not>conflictfreeExt\<^sup>\<A> att S \<close> 
  from ** have \<open>\<exists>\<^sup>S (\<lambda>x. \<exists>\<^sup>S (\<lambda>y. att x y))\<close> 
    by (meson conflictfreeExt_def)
    
  oops

function chainOfFs:: \<open>'a Set => 'a Rel => 'a Set \<Rightarrow> 'a Set Set\<close> where
  \<open>chainOfFs \<A> att S = (\<lambda>x. x = S \<or> (chainOfFs \<A> att (\<F>\<^sup>\<A> att S)) x)\<close>
  apply auto[1] 
  by simp

lemma \<open>chain (chainOfFs \<A> att (\<lambda>x. False))\<close> unfolding chain_def 
  oops


lemma \<open>\<exists>S. completeExt2\<^sup>\<A> att S\<close> using ZornLemma oops

(* stable stuff *)
lemma \<open>stableExt\<^sup>\<A> att S \<Longrightarrow> S \<approx>\<^sup>\<A> \<lambda>x. \<not>\<exists>\<^sup>S (\<lambda>y. att y x) \<close> oops (* some encoding error here *)


end
