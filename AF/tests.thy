theory tests
  imports labellings correspondance
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=2] (*default settings*)


(******************** Admissible and conflict-free **********************)

(* There always exists an admissible Labelling (label, e.g., all arguments as Undec). *)
lemma exAdmissible: \<open>\<exists>Lab. admissible AF Lab\<close> unfolding Defs by auto
(* See here: *)
lemma fixes AF :: \<open>'a \<A>\<F>\<close> and Lab :: \<open>'a Labelling\<close>
      assumes \<open>\<forall>x. undec Lab x\<close> (* give every argument the label Undec *)
      shows \<open>admissible AF Lab\<close> using assms unfolding Defs by simp

(* every admissible labelling is conflict-free but not the other way round*)
lemma admissibleConflictfree: \<open>admissible AF Lab \<Longrightarrow> conflictfree AF Lab\<close>
  by (simp add: admissible_def conflictfree_def inset_def legallyIn_def legallyOut_def outset_def)
lemma \<open>conflictfree AF Lab \<Longrightarrow> admissible AF Lab\<close> nitpick oops

(*For admissible labellings, legally-undecided implies undecided but not the other way round*)
lemma admissibleLegUndec: \<open>admissible AF Lab \<Longrightarrow> legallyUndec AF Lab x \<longrightarrow> undec Lab x\<close>
  by (meson Label.exhaust admissible_def inset_def legallyUndec_def outset_def undecset_def)
lemma \<open>admissible AF Lab \<Longrightarrow> undec Lab x \<longrightarrow> legallyUndec AF Lab x\<close> nitpick oops

(*OTOH, for admissible labellings, legally-in/out still do not imply in/out*)
lemma \<open>admissible AF Lab \<Longrightarrow> legallyIn AF Lab x \<longrightarrow> in Lab x\<close> nitpick oops
lemma \<open>admissible AF Lab \<Longrightarrow> legallyOut AF Lab x \<longrightarrow> out Lab x\<close> nitpick oops


(********************************** Complete **************************************)

(*in-sets of complete labellings are fixed points of the characteristic function*)
lemma completeInFP: "complete AF Lab \<Longrightarrow> fixpoint (\<F> AF) (in Lab)" unfolding fixpoint_def
  by (metis complete_def2 defends_def legallyIn_def legallyOut_def)

lemma \<open>\<exists>Lab. fixpoint (\<F> AF) (in Lab)\<close> unfolding fixpoint_def using complete_def2 exAdmissible oops (*TODO*)

(* complete labellings always exist *)
lemma \<open>\<exists>Lab. complete AF Lab\<close>  using complete_def2 exAdmissible oops (*TODO*) 

(* every complete labelling is admissible but not the other way round *)
lemma completeAdmissible: \<open>complete AF Lab \<Longrightarrow> admissible AF Lab\<close> by (simp add: complete_def)
lemma \<open>admissible AF Lab \<Longrightarrow> complete AF Lab\<close> nitpick oops

(* For complete labellings we have that in/out-sets completely determine the labelling*)
lemma completeInLab: \<open>complete AF L1 \<Longrightarrow> complete AF L2 \<Longrightarrow> in(L1) \<approx> in(L2) \<longrightarrow> (\<forall>x. L1(x) = L2(x))\<close>
  by (smt (verit) Label.exhaust admissibleConflictfree complete_def conflictfree_def inset_def legallyOut_def legallyUndec_def outset_def undecset_def)
lemma completeOutLab: \<open>complete AF L1 \<Longrightarrow> complete AF L2 \<Longrightarrow> out(L1) \<approx> out(L2) \<longrightarrow> (\<forall>x. L1(x) = L2(x))\<close>
  by (metis (full_types) Label.exhaust complete_def2 inset_def legallyIn_def outset_def)
lemma \<open>complete AF L1 \<Longrightarrow> complete AF L2 \<Longrightarrow> undec(L1) \<approx> undec(L2) \<longrightarrow> (\<forall>x. L1(x) = L2(x))\<close> nitpick oops

(* For complete labellings, every in-set which is minimal is the least in-set.
(this result is key and has somehow to do with the fact that complete extensions are fixed points of a monotonic function)*)
lemma completeMinLeastIn: \<open>minimal (complete AF) Lab in \<longrightarrow> least (complete AF) Lab in\<close> oops (*TODO*)
(*(these two below may hold too, but are less important)*)
lemma \<open>minimal (complete AF) Lab out \<longrightarrow> least (complete AF) Lab out\<close> oops
lemma \<open>maximal (complete AF) Lab undec \<longrightarrow> greatest (complete AF) Lab undec\<close> oops

(*Lemma 1 from [BCG2011] *)
lemma \<open>complete AF Lab1 \<Longrightarrow> complete AF Lab2 \<Longrightarrow> (in(Lab1) \<subseteq> in(Lab2) \<longleftrightarrow> out(Lab1) \<subseteq> out(Lab2))\<close> unfolding Defs
  by (metis (full_types) Label.exhaust)

(*Prop 5 from [BCG2011], only partially proven so far *)
lemma prop5_1iff2: \<open>minimal (complete AF) Lab out = minimal (complete AF) Lab in\<close>
  unfolding minimal_def using complete_def2 by (smt (z3) Label.exhaust legallyIn_def legallyOut_def)
(* some of the following still required *)
lemma prop5_1to3: \<open>minimal (complete AF) Lab in \<longrightarrow> maximal (complete AF) Lab undec\<close> oops (*TODO*)
lemma prop5_2to3: \<open>minimal (complete AF) Lab out \<longrightarrow> maximal (complete AF) Lab undec\<close> oops (*TODO*)
lemma prop5_3to1: \<open>maximal (complete AF) Lab undec \<longrightarrow> minimal (complete AF) Lab in\<close> oops (*TODO*)
lemma prop5_3to2: \<open>maximal (complete AF) Lab undec \<longrightarrow> minimal (complete AF) Lab out\<close> oops (*TODO*)

(*However, we can prove weaker variants of some of the above*)
lemma prop5_2to3_weak: \<open>least (complete AF) Lab out \<longrightarrow> greatest (complete AF) Lab undec\<close> unfolding least_def greatest_def
  by (smt (verit, best) Label.exhaust outset_def complete_def2 undecset_def legallyIn_def inset_def)
lemma prop5_3to2_weak: \<open>greatest (complete AF) Lab undec \<longrightarrow> minimal (complete AF) Lab out\<close> unfolding minimal_def greatest_def
  by (metis admissibleConflictfree admissibleLegUndec complete_def complete_def2 conflictfree_def legallyUndec_def legallyOut_def )


(*********************************** Grounded and Preferred ********************************)

(* grounded labellings always exist *)
lemma \<open>\<exists>Lab. grounded AF Lab\<close> oops (*TODO*)

(* Side comment from [BCG2011] that grounded labellings are unique *)
lemma grounded_unique: \<open>grounded AF Lab1 \<Longrightarrow> grounded AF Lab2 \<Longrightarrow> \<forall>x. Lab1(x) = Lab2(x)\<close>
  unfolding grounded_def least_def by (metis (full_types) Label.exhaust complete_def2 inset_def legallyOut_def outset_def)

(* side-comment: it can be proven that the definition below is equivalent *)
lemma preferred_def2: \<open>preferred AF Lab = (complete AF Lab \<and> (\<forall>L. (complete AF L \<and> in(Lab) \<subseteq> in(L)) \<longrightarrow> (\<forall>x. L(x) = Lab(x))))\<close>
   by (smt (z3) completeInLab inset_def maximal_def preferred_def)  

(* preferred labellings always exist *)
lemma \<open>\<exists>Lab. preferred AF Lab\<close> oops (*TODO*)

(*Prop 8 from [BCG2011] 
 For complete labellings, being maximal/greatest wrt In is equivalent to being maximal/greatest wrt Out*)
lemma prop8: \<open>maximal (complete AF) Lab in \<longleftrightarrow> maximal (complete AF) Lab out\<close> unfolding maximal_def
  by (smt (z3) complete_def2 legallyIn_def legallyOut_def)

lemma prop8': \<open>greatest (complete AF) Lab in \<longleftrightarrow> greatest (complete AF) Lab out\<close> unfolding greatest_def
  by (metis complete_def2 legallyIn_def legallyOut_def)

(* In fact, being greatest wrt In implies being least wrt Undec, but not the other way round*)
lemma \<open>greatest (complete AF) Lab in \<longrightarrow> least (complete AF) Lab undec\<close> unfolding greatest_def least_def
  by (metis admissibleLegUndec complete_def complete_def2 legallyOut_def legallyUndec_def)
lemma \<open>least (complete AF) Lab undec \<longrightarrow> greatest (complete AF) Lab in\<close> nitpick oops
(* Moreover, being minimal wrt Undec implies being maximal wrt In, but not the other way round (cf. semi-stable labellings)*)
lemma \<open>minimal (complete AF) Lab undec \<longrightarrow> maximal (complete AF) Lab in\<close> unfolding minimal_def maximal_def
  by (smt (verit, ccfv_SIG) Label.exhaust complete_def2 inset_def legallyOut_def outset_def undecset_def)
lemma \<open>maximal (complete AF) Lab in \<longrightarrow> minimal (complete AF) Lab undec\<close> nitpick oops


(* Prop. 10 from [BCG2011] 
 If no argument is labelled Undec then the notions of conflict-free, admissible, complete and preferred collapse *)
lemma prop10_1to2: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> conflictfree AF Lab \<longrightarrow> admissible AF Lab\<close>
  unfolding Defs by (meson Label.exhaust)
lemma prop10_2to3: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> admissible AF Lab \<longrightarrow> complete AF Lab\<close> 
  by (simp add: complete_def undecset_def)
lemma prop10_3to4: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> complete AF Lab \<longrightarrow>  preferred AF Lab\<close> unfolding preferred_def maximal_def
  by (metis admissibleConflictfree admissibleLegUndec completeLegIn complete_def conflictfree_def legallyOut_def legallyUndec_def undecset_def)
lemma prop10_4to1: \<open>\<forall>x. Lab(x) \<noteq> Undec \<Longrightarrow> preferred AF Lab \<longrightarrow> conflictfree AF Lab\<close>
  by (simp add: preferred_def admissibleConflictfree complete_def maximal_def)


(************************************* Stable and semi-stable ************************)

(* the AF in which every arguments attacks itself does not have a stable labelling *)
lemma stableLem01: \<open>\<forall>Lab. \<not>stable (\<lambda>x y. x = y) Lab\<close>
  unfolding stable_def complete_def by (metis (mono_tags, hide_lams) Label.exhaust admissibleConflictfree conflictfree_def legallyOut_def inset_def outset_def)

(* stable labellings do not exist necessarily *)
corollary \<open>\<exists>AF. \<forall>Lab. \<not>stable AF Lab\<close> using stableLem01 by auto

(*Lemma 14 from Dung. S is a stable extension iff S = {A | A is not attacked by S}.
Adapted to Labelings: It's weaker as we have to deal with Undec as well. *)
lemma lem14Dung: "stable AF Lab \<longrightarrow> (\<forall>a. in(Lab) a \<longleftrightarrow> \<not>(\<exists>b. in(Lab) b \<and> AF b a))" unfolding stable_def complete_def2
  by (metis (full_types) Label.distinct(1) Label.exhaust inset_def legallyOut_def outset_def)

(*Lemma 15 from Dung. Every stable extension is a preferred extension, but not vice versa.
Adapted to Labellings *)
lemma lem15Dung: \<open>stable AF Lab \<Longrightarrow> preferred AF Lab\<close> 
  by (simp add: prop10_3to4 stable_def)
lemma \<open>preferred AF Lab \<Longrightarrow> stable AF Lab\<close> nitpick oops

(* semistable labellings always exist *)
lemma \<open>\<exists>Lab. semistable AF Lab\<close> oops (*TODO*)

(***************************** Ideal ************************)


(***************************** Stage ************************)


(************************************************************************)
(* Inclusion relations as summary: Figure 12 of [BCG2011]
   All but ONE verified.
   The non-inclusion of the inverse directions has been checked with Nitpick in every case. 
 Also, the CF2 stuff is missing, I haven't looked at it so far.
 *)

lemma \<open>stable AF Lab \<Longrightarrow> semistable AF Lab\<close> 
  by (simp add: semistable_def stable_def undecset_def minimal_def)

lemma \<open>semistable AF Lab \<Longrightarrow> preferred AF Lab \<close> unfolding semistable_def preferred_def minimal_def maximal_def
  by (smt (verit, ccfv_SIG) Label.exhaust complete_def2 inset_def legallyOut_def outset_def undecset_def)

lemma \<open>stable AF Lab \<Longrightarrow> stage AF Lab\<close> 
  by (metis lem15Dung prop10_4to1 stable_def stage_def undecset_def minimal_def)

lemma \<open>preferred AF Lab \<Longrightarrow> complete AF Lab\<close>
  by (simp add: preferred_def maximal_def)

lemma \<open>ideal AF Lab \<Longrightarrow> complete AF Lab\<close> 
  oops (*TODO*)

lemma \<open>grounded AF Lab \<Longrightarrow> complete AF Lab\<close>
  by (simp add: grounded_def least_def)

lemma \<open>complete AF Lab \<Longrightarrow> admissible AF Lab\<close> 
  by (simp add: admissible_def complete_def)

lemma \<open>admissible AF Lab \<Longrightarrow> conflictfree AF Lab\<close> 
  by (simp add: admissibleConflictfree) 

lemma \<open>stage AF Lab \<Longrightarrow> conflictfree AF Lab\<close> 
  by (simp add: stage_def minimal_def)



end