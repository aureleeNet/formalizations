theory correspondence
  imports labellings extensions
begin

nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=2] (*default settings*)

(* Define mappings between extensions and labellings. *)
abbreviation Lab2Ext::\<open>'a Labelling \<Rightarrow> 'a Set\<close>
  where \<open>Lab2Ext Lab \<equiv> in(Lab)\<close>
abbreviation Ext2Lab::\<open>'a \<A>\<F> \<Rightarrow> 'a Set \<Rightarrow> 'a Labelling\<close> (* Warning: works only for conflict-free sets! *)
  where \<open>Ext2Lab AF E \<equiv> \<lambda>a. if (E a) then In else (if ([AF|E]\<^sup>+ a) then Out else Undec)\<close>

(*conflict-free*)

lemma conflictfree_LE:  "conflictfree AF Lab \<longrightarrow> conflictfree_ext AF (Lab2Ext Lab)" 
  by (metis (mono_tags, lifting) conflictfree_ext_def conflictfree_def legallyOut_def)

lemma conflictfree_LE': "conflictfree_ext AF (Lab2Ext Lab) \<longrightarrow> conflictfree AF Lab"
  nitpick oops (*as expected*)

lemma conflictfree_EL:  "conflictfree_ext AF E \<longrightarrow> conflictfree AF (Ext2Lab AF E)" 
  unfolding conflictfree_ext_def conflictfree_def
  by (smt (verit, best) Label.distinct(1) Label.distinct(3) Label.distinct(5) inset_def legallyOut_def outset_def plusset_def)

lemma conflictfree_EL': "conflictfree AF (Ext2Lab AF E) \<longrightarrow> conflictfree_ext AF E"
  unfolding conflictfree_ext_def conflictfree_def by (simp add: inset_def legallyOut_def)

(*admissible*)

lemma admissible_LE:  "admissible AF Lab \<longrightarrow> admissible_ext AF (Lab2Ext Lab)" 
  unfolding admissible_ext_def admissible_def 
  by (metis (mono_tags, hide_lams) Label.distinct(1) defends_def conflictfree_ext_def inset_def legallyIn_def legallyOut_def outset_def)

lemma admissible_LE': "admissible_ext AF (Lab2Ext Lab) \<longrightarrow> admissible AF Lab"
  nitpick oops (*as expected*)

lemma admissible_EL:  "admissible_ext AF E \<longrightarrow> admissible AF (Ext2Lab AF E)"
  unfolding admissible_ext_def admissible_def 
  by (smt (verit, del_insts) Label.distinct(1) Label.distinct(3) Label.distinct(5) defends_def conflictfree_ext_def inset_def legallyIn_def legallyOut_def outset_def plusset_def)

lemma admissible_EL': "admissible AF (Ext2Lab AF E) \<longrightarrow> admissible_ext AF E"
  unfolding admissible_ext_def admissible_def
  by (smt (verit, best) Label.distinct(1) Label.distinct(5) conflictfree_ext_def defends_def2 inset_def legallyIn_def minusset_def outset_def)

(*complete*)

lemma complete_LE:  "complete AF Lab \<longrightarrow> complete_ext AF (Lab2Ext Lab)" 
  unfolding complete_ext_def  
  by (metis admissible_LE complete2_def complete_def complete_def2 defends_def legallyIn_def legallyOut_def)

lemma complete_LE': "complete_ext AF (Lab2Ext Lab) \<longrightarrow> complete AF Lab"
  nitpick oops (*as expected*)

lemma complete_EL:  "complete_ext AF E \<longrightarrow> complete AF (Ext2Lab AF E)"
  unfolding complete_ext_def complete_def2
  by (smt (z3) Label.distinct(1) Label.distinct(3) Label.distinct(5) admissible_ext_def complete2_def conflictfree_ext_def defends_def inset_def legallyIn_def legallyOut_def outset_def plusset_def)

lemma complete_EL': "complete AF (Ext2Lab AF E) \<longrightarrow> complete_ext AF E" 
  unfolding complete_ext_def complete_def
  by (smt (verit, del_insts) Label.distinct(1) Label.distinct(3) MONO_def \<F>_mono admissible_ext_def complete_LE complete_def complete_ext_def conflictfree_ext_def inset_def) 

(*preferred*)

lemma preferred_LE:  "preferred AF Lab \<longrightarrow> preferred_ext AF (Lab2Ext Lab)"
  unfolding preferred_ext_def preferred_def
  (*nitpick[timeout=100]*) oops (*TODO*)

lemma preferred_LE': "preferred_ext AF (Lab2Ext Lab) \<longrightarrow> preferred AF Lab"
  nitpick oops (*as expected*)

lemma preferred_EL:  "preferred_ext AF E \<longrightarrow> preferred AF (Ext2Lab AF E)"
  unfolding preferred_ext_def preferred_def 
  oops (*TODO*)

lemma preferred_EL': "preferred AF (Ext2Lab AF E) \<longrightarrow> preferred_ext AF E"
  unfolding preferred_ext_def preferred_def
  (*nitpick[timeout=100]*) oops (*TODO*)

(*grounded*)

lemma grounded_LE:  "grounded AF Lab \<longrightarrow> grounded_ext AF (Lab2Ext Lab)"
  unfolding grounded_ext_def grounded_def
  by (smt (verit, ccfv_SIG) Label.distinct(1) Label.distinct(3) complete_EL complete_LE id_apply inset_def minimal_def)

lemma grounded_LE': "grounded_ext AF (Lab2Ext Lab) \<longrightarrow> grounded AF Lab"
  nitpick oops (*as expected*)

lemma grounded_EL:  "grounded_ext AF E \<longrightarrow> grounded2 AF (Ext2Lab AF E)"
  oops (*TODO*)

lemma grounded_EL': "grounded2 AF (Ext2Lab AF E) \<longrightarrow> grounded_ext AF E"
  oops (*TODO*)

end
