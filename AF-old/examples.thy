theory examples
  imports labellings (* extensions*)
begin

nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=2] (*default settings*)

(************************************************************************)
(************************************************************************)
(* EXAMPLES *)
(************************************************************************)
(************************************************************************)

(* Example set-up from [BG2011], Figure 4 *)
locale ExFig4 begin
datatype Arg = A | B | C | D
  fun att :: \<open>Arg Rel\<close> where
    "att A B = True" |
    "att B C = True" |
    "att C D = True" |
    "att D C = True" |
    "att _ _ = False"

(* admissible labellings *)
lemma \<open>admissible att Lab\<close> nitpick[satisfy] oops
(* ask nitpick for all admissible labellings *) 
lemma \<open>findFor2 att admissible Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* this gives us: {(\<lambda>x. _)(A := In, B := Out, C := In, D := Out), (\<lambda>x. _)(A := In, B := Out, C := Out, D := In), (\<lambda>x. _)
       (A := In, B := Out, C := Undec, D := Undec), (\<lambda>x. _)(A := In, B := Undec, C := Out, D := In), (\<lambda>x. _)
       (A := In, B := Undec, C := Undec, D := Undec), (\<lambda>x. _)(A := Undec, B := Undec, C := Out, D := In), (\<lambda>x. _)
       (A := Undec, B := Undec, C := Undec, D := Undec)} *)
(* checked: these are exactly the 7 labellings given in [BG2011] *) 
(* we can even ask nitpick to give us that number explicitly using eval *)

(* complete labellings *)
lemma \<open>complete att Lab\<close> nitpick[satisfy] oops
lemma \<open>findFor2 att complete Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* checked: these are exactly the 3 labellings given in [BG2011] *) 

(* grounded labellings *)
lemma \<open>grounded att Lab\<close> nitpick[satisfy] oops
lemma \<open>findFor2 att grounded Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
(* checked: these is exactly the one labelling given in [BG2011] *)   
(* comment: we have to disable boxing for nitpick to find the model *)

(* preferred labellings *)
lemma \<open>preferred att Lab\<close> nitpick[satisfy] oops
lemma \<open>findFor2 att preferred Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
(* checked: these are exactly the two labellings given in [BG2011] *)   
(* comment: we have to disable boxing for nitpick to find the model *)

(* stable labellings *)
lemma \<open>stable att Lab\<close> nitpick[satisfy] oops
lemma \<open>findFor2 att stable Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
(* checked: these are exactly the two labellings given in [BG2011] *)   
(* comment: we have to disable boxing for nitpick to find the model *)

(* semi-stable labellings *)
lemma \<open>semistable att Lab\<close> nitpick[satisfy] oops
lemma \<open>findFor2 att semistable Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
(* checked: these are exactly the two labellings given in [BG2011] *)   
(* comment: we have to disable boxing for nitpick to find the model *)


(* ideal labellings: Check this out in detail, the results are weird. But I did not spend time on
ideal labellings sofar. *)
lemma \<open>ideal att Lab\<close> oops
lemma \<open>findFor2 att ideal Labs\<close> oops
(*expected: same as grounded *)
end 


(* Example set-up from [BG2011], Figure 5 *)
locale ExFig5 begin
datatype Arg = A | B | C | D
  fun att :: \<open>Arg Rel\<close> where
    "att A B = True" |
    "att B A = True" |
    "att A C = True" |
    "att B C = True" |
    "att C D = True" |
    "att _ _ = False"

(* admissible labellings *)
lemma \<open>admissible att Lab\<close> nitpick[satisfy] oops
(* ask nitpick for all  z admissible labellings *) 
lemma \<open>findFor2 att admissible Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* this gives us: Labs =
      {(\<lambda>x. _)(A := In, B := Out, C := Out, D := In), (\<lambda>x. _)(A := In, B := Out, C := Out, D := Undec), (\<lambda>x. _)
       (A := In, B := Out, C := Undec, D := Undec), (\<lambda>x. _)(A := Out, B := In, C := Out, D := In), (\<lambda>x. _)
       (A := Out, B := In, C := Out, D := Undec), (\<lambda>x. _)(A := Out, B := In, C := Undec, D := Undec), (\<lambda>x. _)
       (A := Undec, B := Undec, C := Undec, D := Undec)} *)
(* these are 7 labellings, as mentioned in [BG2011]; I havent checked them all. *) 

(* complete labellings *)
lemma \<open>complete att Lab\<close> nitpick[satisfy] oops
lemma \<open>findFor2 att complete Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* checked: these are exactly the 3 labellings given in [BG2011] *) 

(* grounded labellings *)
lemma \<open>grounded2 att Lab\<close> nitpick[satisfy] oops
lemma \<open>findFor2 att grounded Labs\<close> nitpick[satisfy, box=false, eval = "card Labs"] oops
(* (comment: using the the definition above requires disabling boxing for nitpick to find a model)*)
lemma \<open>findFor2 att grounded2 Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* checked: these is exactly the one labelling given in [BG2011] *)   

(* preferred labellings *)
lemma \<open>preferred att Lab\<close> nitpick[satisfy] oops
lemma \<open>findFor2 att preferred Labs\<close> nitpick[satisfy, box=false, eval = "card Labs"] oops
(* checked: these are exactly the two labellings given in [BG2011] *)   
(* (comment: we have to disable boxing for nitpick to find the model) *)

(* stable labellings *)
lemma \<open>stable att Lab\<close> nitpick[satisfy] oops
lemma \<open>findFor2 att stable Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
(* checked: these are exactly the two labellings given in [BG2011] *)   
(* comment: we have to disable boxing for nitpick to find the model *)

(* semi-stable labellings *)
lemma \<open>semistable att Lab\<close> nitpick[satisfy] oops
lemma \<open>findFor2 att semistable Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
(* checked: these are exactly the two labellings given in [BG2011] *)   
(* comment: we have to disable boxing for nitpick to find the model *)
end

(* Example set-up from [BG2011], Figure 6 *)
locale ExFig6 begin
datatype Arg = A | B | C  
  fun att :: \<open>Arg Rel\<close> where
    "att A B = True" |
    "att B C = True" |
    "att C A = True" |
    "att _ _ = False"

(* admissible labellings *)
lemma \<open>admissible att Lab\<close> nitpick[satisfy] oops
(* ask nitpick for all admissible labellings *) 
lemma \<open>findFor2 att admissible Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* this gives us: Labs = {(\<lambda>x. _)(A := Undec, B := Undec, C := Undec)} *)
(* this is the one trivial labelling, as mentioned in [BG2011]. *) 

(* complete labellings *)
lemma \<open>complete att Lab\<close> nitpick[satisfy] oops
lemma \<open>findFor2 att complete Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* checked: this is the one trivial labelling, as mentioned in [BG2011].*) 

(* grounded labellings *)
lemma \<open>grounded att Lab\<close> nitpick[satisfy] oops
lemma \<open>findFor2 att grounded2 Labs\<close> nitpick[satisfy, eval = "card Labs"] oops
(* checked: this is the one trivial labelling, as mentioned in [BG2011].*) 

(* preferred labellings *)
lemma \<open>preferred att Lab\<close> nitpick[satisfy] oops
lemma \<open>findFor2 att preferred Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
(* checked: this is the one trivial labelling, as mentioned in [BG2011].*) 
(* comment: we have to disable boxing for nitpick to find the model *)

(* stable labellings *)
lemma \<open>findFor2 att stable Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
(* checked: these are no stable labellings, see [BG2011] *)   
(* comment: we have to disable boxing for nitpick to find the model *)

(* semi-stable labellings *)
lemma \<open>semistable att Lab\<close> nitpick[satisfy] oops
lemma \<open>findFor2 att semistable Labs\<close> nitpick[satisfy,box=false, eval = "card Labs"] oops
(* checked: this is the one trivial labelling, as mentioned in [BG2011].*) 
(* comment: we have to disable boxing for nitpick to find the model *)
end


(******************************)
(* further tests with locales *)

(* Lab is an admissible labelling *)
locale ExFig4Admissible = ExFig4 +
  fixes Lab :: \<open>Arg Labelling\<close>
  assumes \<open>admissible att Lab\<close>
begin

(* Confirms what [BG2011] says: A can only be labelled legally In or Undec *)
(* lemma \<open>Lab(A) = In \<or> Lab(A) = Undec\<close> unfolding Defs *)
lemma \<open>in Lab A \<or> undec Lab A\<close> unfolding Defs
  using ExFig4Admissible_axioms ExFig4Admissible_def ExFig4.att.simps(14) Label.exhaust admissible_def legallyOut_def by (metis outset_def)
  (* by (metis ExFig4Admissible_axioms ExFig4Admissible_def ExFig4.att.simps(14) Label.exhaust admissible_def legallyOut_def) *)

(* Confirms what [BG2011] says: If A is labelled Undec, then B has to be labelled Undec as well *)
(* lemma \<open>Lab(A) = Undec \<Longrightarrow> Lab(B) = Undec\<close> unfolding Defs *)
lemma \<open>undec Lab A \<Longrightarrow> undec Lab B\<close> unfolding Defs 
  using ExFig4Admissible_axioms ExFig4Admissible_def ExFig4.Arg.distinct(7) ExFig4.Arg.distinct(9) ExFig4.att.elims(2) ExFig4.att.simps(1) Label.distinct(3) Label.distinct(5) Label.exhaust admissible_def legallyIn_def legallyOut_def
  by (smt (z3) inset_def outset_def)
  (* by (metis (full_types) ExFig4Admissible_axioms ExFig4Admissible_def ExFig4.Arg.distinct(7) ExFig4.Arg.distinct(9) ExFig4.att.elims(2) ExFig4.att.simps(1) Label.distinct(3) Label.distinct(5) Label.exhaust admissible_def legallyIn_def legallyOut_def) *)
end


(* Small test: Test-setup as locale merging of admissible labelling with Figure locale. *)
locale AdmissibleLab =
  fixes Lab :: \<open>'a Labelling\<close>
  assumes \<open>admissible att Lab\<close>
(* saves a bit of writing work, but makes the tools slower, it seems (see below) *)
locale ExFig4Admissible2 = ExFig4 + AdmissibleLab Lab
  for Lab :: \<open>ExFig4.Arg Labelling\<close> 
begin

(* A can only be labelled legally In or Undec *)
(* lemma \<open>Lab(A) = In \<or> Lab(A) = Undec\<close> unfolding Defs  *)
lemma \<open>in Lab A \<or> undec Lab A\<close> unfolding Defs
  using AdmissibleLab_axioms AdmissibleLab_def ExFig4.att.simps(14) Label.exhaust admissible_def legallyOut_def
  by (metis outset_def)
  (* by (metis AdmissibleLab_axioms AdmissibleLab_def ExFig4.att.simps(14) Label.exhaust admissible_def legallyOut_def) *)





(* If A is labelled Undec, then B has to be labelled Undec as well *)
(* lemma \<open>Lab(A) = Undec \<Longrightarrow> Lab(B) = Undec\<close> unfolding Defs  *)
lemma \<open>undec Lab A \<Longrightarrow> undec Lab B\<close> unfolding Defs
  using AdmissibleLab_axioms AdmissibleLab_def ExFig4.Arg.distinct(7) ExFig4.Arg.distinct(9) ExFig4.att.elims(2) ExFig4.att.simps(1) Label.distinct(3) Label.distinct(5) Label.exhaust admissible_def legallyIn_def legallyOut_def
  by (smt (z3) inset_def outset_def)
  (* by (metis (full_types) AdmissibleLab_axioms AdmissibleLab_def ExFig4.Arg.distinct(7) ExFig4.Arg.distinct(9) ExFig4.att.elims(2) ExFig4.att.simps(1) Label.distinct(3) Label.distinct(5) Label.exhaust admissible_def legallyIn_def legallyOut_def) *)

(* ask nitpick for all admissible labellings: MUCH slower, so I commented it out. Works though *) 
lemma \<open>findFor2 att admissible Labs\<close> (* nitpick[satisfy]*) oops
(* this gives us: {(\<lambda>x. _)(A := In, B := Out, C := In, D := Out), (\<lambda>x. _)(A := In, B := Out, C := Out, D := In), (\<lambda>x. _)
       (A := In, B := Out, C := Undec, D := Undec), (\<lambda>x. _)(A := In, B := Undec, C := Out, D := In), (\<lambda>x. _)
       (A := In, B := Undec, C := Undec, D := Undec), (\<lambda>x. _)(A := Undec, B := Undec, C := Out, D := In), (\<lambda>x. _)
       (A := Undec, B := Undec, C := Undec, D := Undec)} *)
(* these are exactly the labellings given in [BG2011] *) 
end
(* I will not be using sublocales for now, seems of little use *)

(******************************)
(* further tests with locales END *)
(******************************)


(*example set-ups copied from David Fuenmayor's extension-based version *)
(*Example 1/3/8
A mock argument between two persons I and A, whose countries are at
war, about who is responsible for blocking negotiation in their region.
I: My government cannot negotiate with your government because your
government doesn't even recognize my government.
A: Your government doesn't recognize my government either.
I: But your government is a terrorist government.

The exchange between I and A can be
represented by an argumentation framework (AR, attacks) as follows: AR =
{i\<^sub>1, i\<^sub>2, a} and attacks = {(i\<^sub>1, a), (a, i\<^sub>1), (i\<^sub>2, a)} with i\<^sub>1, and i\<^sub>2, denoting the first and
the second argument of I, respectively, and a denoting the argument of A.
It is not difficult to see that AF has exactly one preferred extension E = {i1, i2}*)
locale War_Example begin
  datatype \<alpha> = i\<^sub>1 | i\<^sub>2 | a
  fun attacks ::"\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" where
    "attacks i\<^sub>1 a = True" |
    "attacks i\<^sub>2 a = True" |
    "attacks a i\<^sub>1 = True" |
    "attacks _ _ = False"
  
  (*Uses nitpick to find a preferred extension to the argument graph defined above*)
  lemma "preferred(attacks) Lab" nitpick[satisfy] oops
  (* Read-off labeling: Lab(i1) = Lab(i2) = In, Lab(a) = Out *)

  (*We can in fact get from nitpick all extensions in one shot*)
  lemma "findFor2 attacks preferred Labs" nitpick[satisfy,timeout=70,box=false] oops
end

(*Example 9 (Nixon diamond). The well-known Nixon diamond example can be
represented as an argumentation framework AF = (AR, attacks) with AR =
{A, B}, and attacks = {(A, B), (B, A)} where A represents the argument "Nixon
is anti-pacifist since he is a republican", and B represents the argument "Nixon is
a pacifist since he is a quaker". This argumentation framework has two preferred
extensions, one in which Nixon is a pacifist and one in which Nixon is a quaker.*)
locale Nixon_Example begin
datatype \<alpha> = A | B
fun attacks ::"\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" where
  "attacks A B = True" |
  "attacks B A = True" |
  "attacks _ _ = False"

(* gives the expected results *)
lemma "preferred(attacks) Lab" nitpick[satisfy,timeout=90] oops
lemma "findFor2 attacks preferred Labs" nitpick[satisfy] oops
end

abbreviation "isTotal R \<equiv> \<forall>x y. x \<noteq> y \<longrightarrow> R x y \<or> R y x"
abbreviation "isAsymm R \<equiv> \<forall>x y. R x y \<longrightarrow> \<not>R y x"
abbreviation "isTrans R \<equiv> \<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z"

(*Section 3.2
Example: Stable Marriage Problem (infinitistic version)*)
locale SMP = 
  fixes prefM::"'m\<Rightarrow>'w\<Rightarrow>'w\<Rightarrow>bool"
    and prefW::"'w\<Rightarrow>'m\<Rightarrow>'m\<Rightarrow>bool"
assumes same_card:  "\<exists>g::'m\<Rightarrow>'w. bij g"
    and prefM_total: "\<forall>m. isTotal (prefM m)" 
    and prefM_asym: "\<forall>m. isAsymm (prefM m)"
    and prefM_trans: "\<forall>m. isTrans (prefM m)"
    and prefW_total: "\<forall>w. isTotal (prefW w)" 
    and prefW_asym: "\<forall>w. isAsymm (prefW w)"
    and prefW_trans: "\<forall>w. isTrans (prefW w)"
begin

abbreviation attacksM::"('m\<times>'w)\<Rightarrow>('m\<times>'w)\<Rightarrow>bool" (infix "\<rightarrow>\<^sub>m" 50)
  where "x \<rightarrow>\<^sub>m y \<equiv> (fst x = fst y) \<and> prefM (fst x) (snd x) (snd y)"

abbreviation attacksW::"('m\<times>'w)\<Rightarrow>('m\<times>'w)\<Rightarrow>bool" (infix "\<rightarrow>\<^sub>w" 50)
  where "x \<rightarrow>\<^sub>w y \<equiv> (snd x = snd y) \<and> prefW (snd x) (fst x) (fst y)"
  
abbreviation attacks::"('m\<times>'w)\<Rightarrow>('m\<times>'w)\<Rightarrow>bool" (infix "\<rightarrow>" 50) where "x \<rightarrow> y \<equiv> x \<rightarrow>\<^sub>m y \<or> x \<rightarrow>\<^sub>w y"

lemma "admissible(attacks) Lab" nitpick[satisfy,show_all] oops
lemma "findFor2 attacks preferred Labs"
  nitpick[satisfy,box=true] oops

lemma "complete(attacks) Lab" nitpick[satisfy] oops 
lemma "stable(attacks) Lab" nitpick[satisfy,card 'm=3, card 'w=3] oops (*finds one - TODO: verify*)
lemma "findFor2 attacks stable Labs"
  nitpick[satisfy,box=true] oops
lemma "grounded(attacks) Lab"  oops  (* no result *)
lemma "preferred(attacks) Lab"  oops (* no result *)
lemma "findFor2 attacks preferred Labs" (* this works, on the contrary; why is that? *)
  nitpick[satisfy,box=true] oops
lemma "findFor2 attacks preferred Labs" (* this works, on the contrary; why is that? *)
  nitpick[satisfy,card 'w = 2, card 'm = 2,box=false] oops
(* result: Labs =
      {(\<lambda>x. _)
       ((m\<^sub>1, w\<^sub>1) := Out, (m\<^sub>1, w\<^sub>2) := In, (m\<^sub>2, w\<^sub>1) := In,
        (m\<^sub>2, w\<^sub>2) := Out)} *)

lemma "findFor2 attacks stable Labs" (* this works, on the contrary; why is that? *)
  nitpick[satisfy,card 'w = 2, card 'm = 2,box=true] oops
(* result: Labs =
      {(\<lambda>x. _)
       ((m\<^sub>1, w\<^sub>1) := In, (m\<^sub>1, w\<^sub>2) := Out, (m\<^sub>2, w\<^sub>1) := Out,
        (m\<^sub>2, w\<^sub>2) := In)} *)


end

(*Example SMP (finitistic variant for n=3)*)
datatype w = w1 | w2 | w3
datatype m = m1 | m2 | m3
type_synonym c = "m\<times>w" (*couples*)
locale SMP_finite =
 fixes prefM::"m\<Rightarrow>w\<Rightarrow>w\<Rightarrow>bool"
 and prefW::"w\<Rightarrow>m\<Rightarrow>m\<Rightarrow>bool"
assumes  prefM_total: "\<forall>m. isTotal (prefM m)" 
                 and prefM_asym: "\<forall>m. isAsymm (prefM m)"
                 and prefM_trans: "\<forall>m. isTrans (prefM m)"
                 and prefW_total: "\<forall>w. isTotal (prefW w)" 
                 and prefW_asym: "\<forall>w. isAsymm (prefW w)"
                 and prefW_trans: "\<forall>w. isTrans (prefW w)"
begin

abbreviation attacksM::"c\<Rightarrow>c\<Rightarrow>bool" (infix "\<rightarrow>\<^sub>m" 50)
  where "x \<rightarrow>\<^sub>m y \<equiv> (fst x = fst y) \<and> prefM (fst x) (snd x) (snd y)"

abbreviation attacksW::"c\<Rightarrow>c\<Rightarrow>bool" (infix "\<rightarrow>\<^sub>w" 50)
  where "x \<rightarrow>\<^sub>w y \<equiv> (snd x = snd y) \<and> prefW (snd x) (fst x) (fst y)"

abbreviation attacks::"c\<Rightarrow>c\<Rightarrow>bool" (infix "\<rightarrow>" 50) where "x \<rightarrow> y \<equiv> x \<rightarrow>\<^sub>m y \<or> x \<rightarrow>\<^sub>w y"


lemma "admissible(attacks) Lab" nitpick[satisfy] oops
(* gives us:  Lab =
      (\<lambda>x. _)
      ((m\<^sub>1, w\<^sub>1) := In, (m\<^sub>1, w\<^sub>2) := Undec, (m\<^sub>1, w\<^sub>3) := Undec,
       (m\<^sub>2, w\<^sub>1) := Out, (m\<^sub>2, w\<^sub>2) := Undec, (m\<^sub>2, w\<^sub>3) := In,
       (m\<^sub>3, w\<^sub>1) := Undec, (m\<^sub>3, w\<^sub>2) := In, (m\<^sub>3, w\<^sub>3) := Undec *)
lemma "preferred(attacks) Lab" (*nitpick[satisfy,timeout=60]*) oops
lemma "complete(attacks) Lab" nitpick[satisfy] oops
lemma "findFor2 attacks stable Labs" oops 
(* doesnt work, scaling is a problem*)

end


end

