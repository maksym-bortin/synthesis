(* ****************************************************************************************

    Theory Preliminaries.thy is part of a package supplementing  
    'Structured development of implementations for divide-and-conquer specifications'.
    Copyright (c) 2023  M. Bortin

    The package is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the package.
    
   *************************************************************************************** *)


theory Preliminaries
imports Main
begin

section "Preliminaries"

text "Arrows in this setting are relations between  
      sets of values classified by the source and target types."
type_synonym ('a, 'b) arrow = "('a \<times> 'b) set" ("_ \<rightarrow> _" [50, 50] 51)

abbreviation relcomp'  :: "'a \<rightarrow> 'b \<Rightarrow> 'b \<rightarrow> 'c \<Rightarrow> 'a \<rightarrow> 'c"  (infixr "\<diamondop>" 75)
  where "r \<diamondop> s \<equiv> r O s"

abbreviation converse' :: "'a \<rightarrow> 'b \<Rightarrow> 'b \<rightarrow> 'a"  ("(_\<^sup>\<circ>)" [1000] 999)
  where "r\<^sup>\<circ> \<equiv> r\<inverse>"



subsection "Arrow divisions"

definition ldiv :: "'a \<rightarrow> 'c \<Rightarrow> 'b \<rightarrow> 'c \<Rightarrow> 'a \<rightarrow> 'b" (infixl "ldiv" 55)
  where "s ldiv r = \<Union>{x. x \<diamondop> r \<subseteq> s}"

lemma ldiv_univ :
"(x \<diamondop> r \<subseteq> s) = (x \<subseteq> s ldiv r)"
  by(simp add: ldiv_def, rule iffI, blast+)

lemma ldiv_mono :
"r \<subseteq> r' \<Longrightarrow> r ldiv s \<subseteq> r' ldiv s"
  by (meson dual_order.trans ldiv_univ subset_refl)

lemma ldiv_mono2 :
"r \<subseteq> r' \<Longrightarrow> s ldiv r' \<subseteq> s ldiv r"
  by (meson dual_order.refl dual_order.trans ldiv_univ relcomp_mono)


definition rdiv :: "'a \<rightarrow> 'b \<Rightarrow> 'a \<rightarrow> 'c \<Rightarrow> 'c \<rightarrow> 'b" (infixl "rdiv" 55)
  where "s rdiv r = \<Union>{x. r \<diamondop> x \<subseteq> s}"

lemma rdiv_univ :
"(r \<diamondop> x \<subseteq> s) = (x \<subseteq> s rdiv r)"
  by(simp add: rdiv_def, rule iffI, blast+)


lemma ldiv_rdiv_comm :
"(r ldiv a) rdiv b = (r rdiv b) ldiv a"
  apply(rule equalityI)
   apply(subst ldiv_univ[THEN sym])
   apply(subst rdiv_univ[THEN sym])
   apply(subst O_assoc[THEN sym])
   apply(subst ldiv_univ)
   apply(subst rdiv_univ, simp)
  apply(subst rdiv_univ[THEN sym])
  apply(subst ldiv_univ[THEN sym])
  apply(subst O_assoc)
  apply(subst rdiv_univ)
  apply(subst ldiv_univ, simp)
  done


subsection "Functions as relations"

definition "graph_of f = {(a, f a) |a. a \<in> UNIV}"
definition "funct_of r = (\<lambda>u. THE v. (u, v) \<in> r)" 

lemma graph_of_funct_of :
"funct_of(graph_of f) = f"
  by(simp add: graph_of_def funct_of_def)
  
lemma graph_of_inj :
"inj graph_of"
  by (metis graph_of_funct_of injI)

lemma graph_of_id :
"graph_of id = Id"
  by(simp add: graph_of_def, blast)


lemma graph_of_comp :
"graph_of(g \<circ> f) = graph_of f \<diamondop> graph_of g"
  by(simp add: graph_of_def, blast)

lemma graph_of_eqD :
"r = graph_of f \<Longrightarrow> (\<forall>x. (x, f x) \<in> r \<and> (\<forall>v. (x, v) \<in> r \<longrightarrow> v = f x))"
  by(clarsimp simp: graph_of_def)


lemma graph_of_sub :
"graph_of f \<subseteq> graph_of g \<Longrightarrow> f = g"
  using graph_of_def graph_of_eqD by blast



subsection "Simple and entire arrows"

definition "simple r = (r\<^sup>\<circ> \<diamondop> r \<subseteq> Id)"
definition "entire r = (Id \<subseteq> r \<diamondop> r\<^sup>\<circ>)"

lemma mapping :
"simple r \<Longrightarrow> entire r \<Longrightarrow> \<exists>f. r = graph_of f"
  apply(rule_tac x="\<lambda>x. (SOME v. (x, v) \<in> r)" in exI)
  apply(simp add: simple_def entire_def graph_of_def)
  apply(rule set_eqI, clarsimp)
  apply(rule iffI)
   apply(rule someI2, assumption)
   apply(drule_tac c="(b, v)" in subsetD, fast, simp)
  apply clarify
  apply(drule_tac c="(a, a)" in subsetD, rule IdI)
  apply clarsimp
  apply(erule someI)
  done



subsection "Monotype factor"

definition "monotypeF r s = (r \<diamondop> s) ldiv r"

lemma monotypeF_mono :
"mono (monotypeF r)"
  by (simp add: ldiv_mono monoI monotypeF_def relcomp_mono) 

lemma monotypeF_univ :
"(x \<diamondop> r \<subseteq> r \<diamondop> s) = (x \<subseteq> monotypeF r s)"
  by(simp add: monotypeF_def, rule ldiv_univ)

lemma monotypeF1 :
"monotypeF r s \<diamondop> r \<subseteq> r \<diamondop> s"
  by(subst monotypeF_univ, simp)




subsection "A least fixed point fusion property"

lemma lfp_fusionG :
"\<forall>x. (F \<circ> H) x \<subseteq> (H \<circ> G) x \<Longrightarrow> G f = f \<Longrightarrow> lfp F \<subseteq> H f"
  by (metis comp_def lfp_lowerbound)


lemma lfp_fusion :
"mono G \<Longrightarrow> \<forall>x. (F \<circ> H) x \<subseteq> (H \<circ> G) x \<Longrightarrow> lfp F \<subseteq> H(lfp G)"
  by (metis lfp_fusionG lfp_unfold)


subsection "Sorted lists"

definition sorted_by :: "('a \<Rightarrow> 'b :: linorder) \<Rightarrow> 'a list \<Rightarrow> bool"
where "sorted_by f = sorted_wrt (\<lambda>a b. f a \<le> f b)"


lemma sorted_by_Cons:
"sorted_by f (x#xs) = (sorted_by f xs \<and> (\<forall>a\<in>set xs. f x \<le> f a))"
  by(fastforce simp add: sorted_by_def)

lemma sorted_by_append:
"sorted_by f (xs@ys) = (sorted_by f xs \<and> sorted_by f ys \<and> (\<forall>x\<in>set xs. \<forall>y\<in>set ys. f x \<le> f y))"
  by(simp add: sorted_by_def sorted_wrt_append)

lemma sorted_by_rem1 :
"sorted_by f xs \<Longrightarrow> sorted_by f (remove1 x xs)"
  by (metis sorted_by_def sorted_map_remove1 sorted_wrt_map)

lemma sorted_by_filter :
"sorted_by f xs \<Longrightarrow> sorted_by f (filter P xs)"
  by(simp add: sorted_by_def sorted_wrt_filter)

lemma sorted_by_nth :
"j < length xs \<Longrightarrow> i \<le> j \<Longrightarrow> sorted_by f xs \<Longrightarrow> f(xs!i) \<le> f(xs!j)"
  by (metis sorted_by_def dual_order.refl nat_less_le sorted_wrt_iff_nth_less)



subsection "A few more auxiliaries"

definition monotype :: "'a set \<Rightarrow> 'a \<rightarrow> 'a"
  where "monotype A = {(x,x) |x. x\<in>A}"

lemma monotype_eq :
"((a, b) \<in> monotype A) = (a = b \<and> a \<in> A)"
  by(simp add: monotype_def, fast)

lemma singleton_eq :
"(a \<in> A) = ({a} \<subseteq> A)"
  by fast

lemma mem_nth :
"x \<in> set xs \<Longrightarrow> \<exists>i<length xs. xs!i = x"
  by(induct xs, fastforce+)


lemma set_drop :
"set(drop k xs) = {xs!i |i. k \<le> i \<and> i < length xs}"
  apply(induct xs arbitrary:k, simp)
  apply(case_tac k, simp)
   apply(subst set_conv_nth)
   apply(rule set_eqI, simp)
   apply(rule iffI)
    apply(erule disjE, rule_tac x=0 in exI, simp)
    apply clarify
    apply(rule_tac x="i+1" in exI, simp)
   apply (metis Suc_length_conv in_set_conv_nth set_ConsD)
  apply clarsimp
  apply(rename_tac n)
  apply(rule set_eqI, simp)
  apply(rule iffI)
   apply clarify
   apply(rule_tac x="i+1" in exI, simp)
  apply clarsimp
  by(case_tac i, simp, fastforce)


corollary set_dropI :
"i < length xs \<Longrightarrow> n \<le> i \<Longrightarrow> xs!i \<in> set(drop n xs)"
  by(subst set_drop, fast)


lemma card_less_diff :
"card A < card B \<Longrightarrow> C \<subseteq> A \<Longrightarrow> D \<subseteq> B \<Longrightarrow> card C = card D \<Longrightarrow> finite A \<Longrightarrow> finite B \<Longrightarrow>
 card (A - C) < card (B - D)"
  by (metis card_Diff_subset card_mono diff_less_mono finite_subset)


end



