theory correspondence
  imports labellings 
begin

nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=2] (*default settings*)

(*conflict-free*)

lemma "conflictfree AF Lab \<longrightarrow> conflictfree_ext AF (Lab2Ext Lab)" 
  by (metis (mono_tags, lifting) conflictfree_ext_def conflictfree_def legallyOut_def)

lemma "conflictfree_ext AF (Lab2Ext Lab) \<longrightarrow> conflictfree AF Lab"
  nitpick oops (*as expected*)

lemma "conflictfree_ext AF E \<longrightarrow> conflictfree AF (Ext2Lab AF E)" 
  unfolding conflictfree_ext_def conflictfree_def
  by (smt (verit, best) Label.distinct(1) Label.distinct(3) Label.distinct(5) inset_def legallyOut_def outset_def plusset_def)

lemma "conflictfree AF (Ext2Lab AF E) \<longrightarrow> conflictfree_ext AF E"
  unfolding conflictfree_ext_def conflictfree_def by (simp add: inset_def legallyOut_def)

(*admissible*)

lemma "admissible AF Lab \<longrightarrow> admissible_ext AF (Lab2Ext Lab)" 
  unfolding admissible_ext_def admissible_def 
  by (metis (mono_tags, hide_lams) Label.distinct(1) defends_def conflictfree_ext_def inset_def legallyIn_def legallyOut_def outset_def)

lemma "admissible_ext AF (Lab2Ext Lab) \<longrightarrow> admissible AF Lab"
  nitpick oops (*as expected*)

lemma "admissible_ext AF E \<longrightarrow> admissible AF (Ext2Lab AF E)"
  unfolding admissible_ext_def admissible_def 
  by (smt (verit, del_insts) Label.distinct(1) Label.distinct(3) Label.distinct(5) defends_def conflictfree_ext_def inset_def legallyIn_def legallyOut_def outset_def plusset_def)

lemma "admissible AF (Ext2Lab AF E) \<longrightarrow> admissible_ext AF E"
  unfolding admissible_ext_def admissible_def
  by (smt (verit, best) Label.distinct(1) Label.distinct(5) conflictfree_ext_def defends_def2 inset_def legallyIn_def minusset_def outset_def)

(*complete*)

lemma "complete AF Lab \<longrightarrow> complete_ext AF (Lab2Ext Lab)" 
  unfolding complete_ext_def complete_def2
  by (smt (verit) Label.distinct(1) defends_def admissible_ext_def conflictfree_ext_def inset_def legallyIn_def legallyOut_def outset_def)

lemma "complete_ext AF (Lab2Ext Lab) \<longrightarrow> complete AF Lab"
  nitpick oops (*as expected*)

lemma "complete_ext AF E \<longrightarrow> complete AF (Ext2Lab AF E)"
  unfolding complete_ext_def complete_def2 
  by (smt (z3) Label.distinct(1) Label.distinct(3) Label.distinct(5) defends_def admissible_ext_def conflictfree_ext_def inset_def legallyIn_def legallyOut_def outset_def plusset_def)

lemma "complete AF (Ext2Lab AF E) \<longrightarrow> complete_ext AF E" 
  unfolding complete_ext_def complete_def oops (*TODO*)
   (* by (smt (z3) Label.distinct(1) Label.distinct(5) defends_def extensions.admissible_def extensions.conflictfree_def legallyIn_def legallyUndec_def plusset_def) *)

(*preferred*)

lemma "preferred AF Lab \<longrightarrow> preferred_ext AF (Lab2Ext Lab)" 
  unfolding preferred_ext_def preferred_def
  (*nitpick[timeout=100]*) oops (*TODO*)

lemma "preferred_ext AF (Lab2Ext Lab) \<longrightarrow> preferred AF Lab"
  nitpick oops (*as expected*)

lemma "preferred_ext AF E \<longrightarrow> preferred AF (Ext2Lab AF E)"
  unfolding preferred_ext_def preferred_def
  oops (*TODO*)

lemma "preferred AF (Ext2Lab AF E) \<longrightarrow> preferred_ext AF E"
  unfolding preferred_ext_def preferred_def
  (*nitpick[timeout=100]*) oops (*TODO*)
end