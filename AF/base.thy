theory base
  imports Main 
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=2] (*default settings*)

(************** Basic set- and order-theoretical notions ******************)

(* hide set notation for Isabelle's built-in sets: *)
no_notation
  subset  ("'(\<subset>')") and
  subset  ("(_/ \<subset> _)" [51, 51] 50) and
  subset_eq  ("'(\<subseteq>')") and
  subset_eq  ("(_/ \<subseteq> _)" [51, 51] 50) and
  union (infixl "\<union>" 65) and
  inter (infixl "\<inter>" 70)

(* Sets and relations are vanilla type-polymorphic predicates ('a is a type variable representing an arbitrary type). *)
type_synonym 'a Set = \<open>'a \<Rightarrow> bool\<close> (*sets as functions into a 2-element codomain. *)
type_synonym 'a Rel = \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>

(* Introduce useful set operations and shorthand: *)
abbreviation union::\<open>'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> (infixl "\<union>" 53) where \<open>A \<union> B \<equiv> \<lambda>x. (A x \<or> B x)\<close>
abbreviation inter::\<open>'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> (infixl "\<inter>" 54) where \<open>A \<inter> B \<equiv> \<lambda>x. (A x \<and> B x)\<close>
abbreviation compl::\<open>'a Set \<Rightarrow> 'a Set\<close> ("\<midarrow>_") where \<open>\<midarrow>A \<equiv> \<lambda>x. \<not>A x\<close>
abbreviation inclusion::\<open>'a Set \<Rightarrow> 'a Set \<Rightarrow> bool\<close> (infix "\<subseteq>" 52) where \<open>A \<subseteq> B \<equiv> \<forall>x. (A x \<longrightarrow> B x)\<close>
abbreviation equ::\<open>'a Set \<Rightarrow> 'a Set \<Rightarrow> bool\<close> (infix "\<approx>" 55) where \<open>A \<approx> B \<equiv> \<forall>x. (A x \<longleftrightarrow> B x)\<close>
abbreviation proper_inclusion::\<open>'a Set \<Rightarrow> 'a Set \<Rightarrow>bool\<close> (infix "\<subset>" 52) where \<open>A \<subset> B \<equiv> (A \<subseteq> B) \<and> \<not>(A\<approx>B)\<close>
abbreviation set_cnstr0::\<open>'a Set\<close> ("\<lbrace>-\<rbrace>") where \<open>\<lbrace>-\<rbrace> \<equiv> \<lambda>x. False\<close>
abbreviation set_cnstr1::\<open>'a\<Rightarrow>'a Set\<close> ("\<lbrace>_\<rbrace>") where \<open>\<lbrace>a\<rbrace> \<equiv> \<lambda>x. x = a\<close>
abbreviation set_cnstr2::\<open>'a\<Rightarrow>'a\<Rightarrow>'a Set\<close> ("\<lbrace>_,_\<rbrace>") where \<open>\<lbrace>a,b\<rbrace> \<equiv> \<lambda>x. x = a \<or> x = b\<close>
abbreviation set_cnstr3::\<open>'a\<Rightarrow>'a\<Rightarrow>'a\<Rightarrow>'a Set\<close> ("\<lbrace>_,_,_\<rbrace>") where \<open>\<lbrace>a,b,c\<rbrace> \<equiv> \<lambda>x. x = a \<or> x = b \<or> x = c\<close>

(* and some generic notions for representing minimal and maximal (resp.least and greatest) sets wrt. set inclusion: *)
definition  \<open>minimal Prop Obj E \<equiv> Prop Obj \<and> (\<forall>X. Prop X \<and> E(X) \<subseteq> E(Obj) \<longrightarrow> E(X) \<approx> E(Obj))\<close>
definition  \<open>maximal Prop Obj E \<equiv> Prop Obj \<and> (\<forall>X. Prop X \<and> E(Obj) \<subseteq> E(X) \<longrightarrow> E(X) \<approx> E(Obj))\<close>
definition    \<open>least Prop Obj E \<equiv> Prop Obj \<and> (\<forall>X. Prop X \<longrightarrow> E(Obj) \<subseteq> E(X))\<close>
definition \<open>greatest Prop Obj E \<equiv> Prop Obj \<and> (\<forall>X. Prop X \<longrightarrow> E(X) \<subseteq> E(Obj))\<close>

(* Least (resp. greatest) sets are minimal (resp. maximal) but not the other way round. *)
lemma leastMin: \<open>least Prop Obj E \<longrightarrow>  minimal Prop Obj E\<close> unfolding least_def minimal_def by blast
lemma greatestMax: \<open>greatest Prop Obj E \<longrightarrow>  maximal Prop Obj E\<close> unfolding greatest_def maximal_def by blast
lemma  \<open>minimal Prop Obj E \<longrightarrow>    least Prop Obj E\<close> nitpick oops (* countermodel found *)
lemma  \<open>maximal Prop Obj E \<longrightarrow> greatest Prop Obj E\<close> nitpick oops (* countermodel found *)

(* Least and greatest elements are unique (wrt. their extensions by E). *)
lemma leastUnique: "least Prop A E \<and> least Prop B E \<longrightarrow> E(A) \<approx> E(B)" by (metis least_def)
lemma greatestUnique: "greatest Prop A E \<and> greatest Prop B E \<longrightarrow> E(A) \<approx> E(B)" by (metis greatest_def)

(* If there exists a least/greatest element then minimal/maximal collapse to least/greatest. *)
lemma minLeastCollapse: \<open>\<exists>A. least Prop A E \<Longrightarrow> \<forall>B. minimal Prop B E \<longrightarrow>  least Prop B E\<close> 
  by (smt (verit, best) least_def minimal_def)
lemma maxGreatestCollapse: \<open>\<exists>A. greatest Prop A E \<Longrightarrow> \<forall>B. maximal Prop B E \<longrightarrow>  greatest Prop B E\<close> 
  by (smt (verit, best) greatest_def maximal_def)


(* In what follows we verify some useful results concerning the existence of least/greatest fixed points of monotone functions. *)

(* We start by defining infinite meet (infimum) and infinite join (supremum) operations,*)
definition infimum:: "('a Set\<Rightarrow>bool)\<Rightarrow>'a Set" ("\<^bold>\<And>_") where "\<^bold>\<And>S \<equiv> \<lambda>w. \<forall>X. S X \<longrightarrow> X w"
definition supremum::"('a Set\<Rightarrow>bool)\<Rightarrow>'a Set" ("\<^bold>\<Or>_") where "\<^bold>\<Or>S \<equiv> \<lambda>w. \<exists>X. S X  \<and>  X w"

(* and show that the corresponding lattice is complete. *)
definition "upper_bound U S \<equiv> \<forall>X. (S X) \<longrightarrow> X \<subseteq> U"
definition "lower_bound L S \<equiv> \<forall>X. (S X) \<longrightarrow> L \<subseteq> X"
abbreviation "is_supremum U S \<equiv> upper_bound U S \<and> (\<forall>X. upper_bound X S \<longrightarrow> U \<subseteq> X)"
abbreviation "is_infimum  L S \<equiv> lower_bound L S \<and> (\<forall>X. lower_bound X S \<longrightarrow> X \<subseteq> L)"

lemma sup_char: "is_supremum \<^bold>\<Or>S S" unfolding supremum_def upper_bound_def by auto
lemma inf_char: "is_infimum \<^bold>\<And>S S" unfolding infimum_def lower_bound_def by auto

(* Definition of a monotone function.*)
definition "MONO F \<equiv> \<forall>A B. A \<subseteq> B \<longrightarrow> F A \<subseteq> F B"

(* We speak of argument-sets being fixed points of functions (mapping argument-sets to argument-sets).
For a given function we define in the usual way a fixed-point predicate for argument-sets.*)
definition fixpoint::"('a Set \<Rightarrow> 'a Set) \<Rightarrow> 'a Set \<Rightarrow> bool" where "fixpoint \<phi> S \<equiv> \<phi>(S) \<approx> S"

(* A weak formulation of the Knaster-Tarski Theorem:
 Any monotone function on a powerset lattice has a least/greatest fixed-point.*)
lemma wKTl': "MONO F \<Longrightarrow> let S = \<^bold>\<And>(\<lambda>x. F x \<subseteq> x) in (least (fixpoint F) S id)" 
  unfolding least_def fixpoint_def by (smt (verit, ccfv_threshold) inf_char lower_bound_def MONO_def id_def)
lemma wKTg': "MONO F \<Longrightarrow> let S = \<^bold>\<Or>(\<lambda>x. x \<subseteq> F x) in (greatest (fixpoint F) S id)" 
  unfolding greatest_def fixpoint_def by (smt (z3) MONO_def eq_id_iff supremum_def)
lemma wKTl:  "MONO F \<Longrightarrow> \<exists>S. least (fixpoint F) S id" using wKTl' by auto
lemma wKTg:  "MONO F \<Longrightarrow> \<exists>S. greatest (fixpoint F) S id" using wKTg' by auto

(* (just to check) *)
lemma    "(least (fixpoint F) S id) = (fixpoint F S \<and> (\<forall>X. fixpoint F X \<longrightarrow> S \<subseteq> X))" by (simp add: least_def)
lemma "(greatest (fixpoint F) S id) = (fixpoint F S \<and> (\<forall>X. fixpoint F X \<longrightarrow> X \<subseteq> S))" by (simp add: greatest_def)


(************** Representation basics of argumentation frameworks and related basic notions ******************)


(* Source: 
 [BCG 2011] Baroni, P., M. Caminada and M. Giacomin, An introduction to argumentation semantics,
  Knowledge Engineering Review. (2011)
*)

(* A collection of definitions related to AFs  *)
named_theorems Defs

(* An argumentation frame(work) AF is completely characterized in HOL by its underlying "attack" relation,
   since the set of arguments (the carrier of "attack") is given implicitly as the domain set for type 'a. *)
type_synonym 'a \<A>\<F> = \<open>'a Rel\<close>

(* Given a set of arguments S, we define its set of attacked (+) and attacking (-) arguments ([BCG 2011] p. 3). *)
definition plusset :: \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("[_|_]\<^sup>+") where \<open>[AF|S]\<^sup>+ \<equiv> \<lambda>b. \<exists>a. S a \<and> AF a b\<close>
definition minusset:: \<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> 'a Set\<close> ("[_|_]\<^sup>-") where \<open>[AF|S]\<^sup>- \<equiv> \<lambda>b. \<exists>a. S a \<and> AF b a\<close>
declare plusset_def[Defs] minusset_def[Defs]

end

