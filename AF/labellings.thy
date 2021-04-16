theory labellings
  imports extensions 
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=2] (*default settings*)

(*
Labelling-based argumentation framework semantics based on
 [BCG2011] Baroni, Caminada and Giacomin, An Introduction to argumentation semantics, 
           The Knowledge Engineering Review, 2011.
*)

(* Generalising sets as "labellings", i.e. functions into some finite codomain (of "labels") *)
datatype Label = In | Out | Undec (*introduces a 3-element set of labels*)
type_synonym 'a Labelling = \<open>'a \<Rightarrow> Label\<close> (*labellings as functions into "labels" *)

(* page 4 of [BCG2011] *)
definition inset :: \<open>'a Labelling \<Rightarrow> 'a Set\<close> ("in") where \<open>in(Lab) \<equiv> \<lambda>x. Lab(x) = In\<close>
definition outset :: \<open>'a Labelling \<Rightarrow> 'a Set\<close> ("out") where \<open>out(Lab) \<equiv> \<lambda>x. Lab(x) = Out\<close>
definition undecset :: \<open>'a Labelling \<Rightarrow> 'a Set\<close> ("undec") where \<open>undec(Lab) \<equiv> \<lambda>x. Lab(x) = Undec\<close>

(*Extension-Labelling mappings*)
abbreviation Lab2Ext::\<open>'a Labelling \<Rightarrow> 'a Set\<close>
  where \<open>Lab2Ext Lab \<equiv> in(Lab)\<close>
abbreviation Ext2Lab::\<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> 'a Labelling\<close> (*Warning: works only for conflict-free sets!*)
  where \<open>Ext2Lab AF E \<equiv> \<lambda>a. if (E a) then In else (if ([AF|E]\<^sup>+ a) then Out else Undec)\<close>
declare inset_def[Defs] outset_def[Defs] undecset_def[Defs]

(* Def 9 of [BCG2011] unrestricted for any argument independent of its labelling*)
(*An argument is legally-in iff all of its attackers are labelled out*)
definition legallyIn :: \<open>'a \<A>\<F> \<Rightarrow> 'a Labelling \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>legallyIn AF Lab \<equiv> \<lambda>x.  (\<forall>y. (AF y x) \<longrightarrow> out Lab y)\<close>
(*An argument is legally-out iff it has an in-labelled attacker*)
definition legallyOut :: \<open>'a \<A>\<F> \<Rightarrow> 'a Labelling \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>legallyOut AF Lab \<equiv>  \<lambda>x.  (\<exists>y. (AF y x) \<and> in Lab y)\<close>
(*An argument is legally-undec if it is neither legally-in nor legally-out; cf. Def 17 of [BCG2011] *)
definition legallyUndec :: \<open>'a \<A>\<F> \<Rightarrow> 'a Labelling \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>legallyUndec AF Lab \<equiv> \<lambda>x. \<not>legallyIn AF Lab x \<and> \<not>legallyOut AF Lab x\<close>

declare legallyIn_def[Defs] legallyOut_def[Defs] legallyUndec_def[Defs]

(* Def 16 of [BCG2011] *)  
definition conflictfree :: \<open>'a \<A>\<F> \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>conflictfree AF Lab \<equiv> \<forall>x. (in Lab x  \<longrightarrow> \<not>legallyOut AF Lab x) \<and> (out Lab x \<longrightarrow> legallyOut AF Lab x)\<close>
declare conflictfree_def[Defs]

(* Def 10 of [BCG2011] *)
definition admissible :: \<open>'a \<A>\<F> \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>admissible AF Lab \<equiv> \<forall>x. (in Lab x \<longrightarrow> legallyIn AF Lab x) \<and> (out Lab x \<longrightarrow> legallyOut AF Lab x)\<close>
declare admissible_def[Defs]


(* Def 18 of [BCG2011] *)
definition complete :: \<open>'a \<A>\<F> \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>complete AF Lab \<equiv> admissible AF Lab \<and> (\<forall>x. undec Lab x \<longrightarrow> legallyUndec AF Lab x)\<close>
declare complete_def[Defs] 

(*For complete labellings, legally-in/out does indeed imply in/out*)
lemma completeLegIn:  \<open>complete AF Lab \<Longrightarrow> legallyIn AF Lab x \<longrightarrow> in Lab x\<close> unfolding Defs by (metis Label.exhaust)  
lemma completeLegOut: \<open>complete AF Lab \<Longrightarrow> legallyOut AF Lab x \<longrightarrow> out Lab x\<close> unfolding Defs by (metis Label.exhaust)  

(* Prop. 2 from [BCG2011] *)
lemma complete_def2: \<open>complete AF Lab = (\<forall>x. (in Lab x \<longleftrightarrow> legallyIn AF Lab x) \<and> (out Lab x \<longleftrightarrow> legallyOut AF Lab x))\<close>
 using completeLegIn completeLegOut by (metis Label.distinct(3) Label.distinct(5) admissible_def complete_def legallyUndec_def inset_def outset_def undecset_def)


(* Def. 20 from [BCG2011] *)
definition grounded :: \<open>'a \<A>\<F> \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
   where \<open>grounded AF Lab \<equiv> least (complete AF) Lab in\<close>    (* we work meanwhile with this definition until we prove the lemma above*)
   (* where \<open>grounded AF Lab \<equiv> minimal (complete AF) Lab in\<close>  (*as it actually appears in [BCG2011]*) *)
declare grounded_def[Defs] 

(*just to check:*)
lemma \<open>grounded AF Lab = (complete AF Lab \<and> (\<forall>L. complete AF L \<longrightarrow> in(Lab) \<subseteq> in(L)))\<close> by (simp add: grounded_def least_def)

(* Def. 22 from [BCG2011] *)
definition preferred :: \<open>'a \<A>\<F> \<Rightarrow> 'a Labelling => bool\<close>
  where \<open>preferred AF Lab \<equiv> maximal (complete AF) Lab in\<close>
declare preferred_def[Defs]

(* Def 24 from [BCG2011] *)
definition stable :: \<open>'a \<A>\<F> \<Rightarrow> 'a Labelling => bool\<close>
  where \<open>stable AF Lab \<equiv> complete AF Lab \<and> (\<forall>x. Lab(x) \<noteq> Undec)\<close>
declare stable_def[Defs]

(* Def. 26 from [BCG2011] *) 
definition semistable :: \<open>'a \<A>\<F> \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>semistable AF Lab \<equiv> minimal (complete AF) Lab undec\<close>  
declare semistable_def[Defs]

(* Def. 28 from [BCG2011] *)
definition lessOrEquallyCommitted :: \<open>'a Labelling \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close> (infix "\<sqsubseteq>" 52) 
  where "L1 \<sqsubseteq> L2 \<equiv> (in(L1) \<subseteq> in(L2)) \<and> (out(L1) \<subseteq> out(L2))"
declare lessOrEquallyCommitted_def[Defs]

(* Def. 29 from [BCG2011], Check if this is really correct. *)
definition ideal :: \<open>'a \<A>\<F> \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  (* where \<open>ideal AF Lab \<equiv> admissible AF Lab \<and> (\<forall>L. ((admissible AF L) \<and> Lab \<sqsubseteq> L) \<longrightarrow> (\<forall>x. Lab(x) = L(x))) \<and> (\<forall>L. ((preferred AF L)) \<longrightarrow> (Lab \<sqsubseteq> L)) \<close>   *)
  where \<open>ideal AF Lab \<equiv> admissible AF Lab \<and> (\<forall>L. admissible AF L \<longrightarrow> L \<sqsubseteq> Lab) \<and> (\<forall>L. preferred AF L \<longrightarrow> Lab \<sqsubseteq> L)\<close>  
declare ideal_def[Defs] 

(* Def. 31 from [BCG2011] *)
definition stage :: \<open>'a \<A>\<F> \<Rightarrow> 'a Labelling \<Rightarrow> bool\<close>
  where \<open>stage AF Lab \<equiv> minimal (conflictfree AF) Lab undec\<close>  
declare stage_def[Defs] 


(************************************************************************)
(* Argument justification, \<section>4 of [BCG2011]. *)
type_synonym 'a Semantics = \<open>'a \<A>\<F> \<Rightarrow> 'a Labelling => bool\<close>

definition skepticallyJustified :: \<open>'a Semantics \<Rightarrow> 'a \<A>\<F> \<Rightarrow> 'a \<Rightarrow> bool\<close> ("sJ")
  where \<open>sJ S AF \<equiv> \<lambda>arg. \<forall>Lab. (S AF Lab) \<longrightarrow> Lab(arg) = In\<close>
definition credulouslyJustified :: \<open>'a Semantics \<Rightarrow> 'a \<A>\<F> \<Rightarrow> 'a \<Rightarrow> bool\<close> ("cJ")
  where \<open>cJ S AF \<equiv> \<lambda>arg. \<exists>Lab. (S AF Lab) \<longrightarrow> Lab(arg) = In\<close>

lemma \<open>sJ S AF a \<Longrightarrow> cJ S AF a\<close> 
  by (simp add: credulouslyJustified_def skepticallyJustified_def)
lemma \<open>cJ S AF a \<Longrightarrow> sJ S AF a\<close> nitpick oops


(************************************************************************)
(* Utility for EXAMPLES *)

(* this is adapted for label functions *)
abbreviation "findFor AF Prop Ext \<equiv> \<forall>Lab. Ext Lab \<longleftrightarrow> (Prop(AF) Lab)"
(* when using sets instead of predicates, we get nitpick to output only those which are contained *)
abbreviation "findFor2 AF Prop Ext \<equiv> \<forall>Lab. Lab \<in> Ext \<longleftrightarrow> (Prop(AF) Lab)"

end