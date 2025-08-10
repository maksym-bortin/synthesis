(* ****************************************************************************************

    Theory Greedy.thy is part of a package supplementing  
    'Structured development of implementations for divide-and-conquer specifications'.
    Copyright (c) 2023  M. Bortin

    The package is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the package.
    
   *************************************************************************************** *)


theory Greedy
imports DaC_synthesis
begin



text "Independent families of sets"
definition Independent :: "'a set set \<Rightarrow> bool"
where "Independent \<I> = ({} \<in> \<I> \<and> (\<forall>S T. S \<in> \<I> \<longrightarrow> T \<subseteq> S \<longrightarrow> T \<in> \<I>) \<and>
                        (\<forall>S T. finite S \<longrightarrow> finite T \<longrightarrow> S \<in> \<I> \<longrightarrow> T \<in> \<I> \<longrightarrow> card S < card T \<longrightarrow> 
                          (\<exists>e. e \<in> T - S \<and> {e} \<union> S \<in> \<I>)))"


lemma Independent_D1 :
"Independent \<I> \<Longrightarrow> {} \<in> \<I>"
  by(simp add: Independent_def)


text "The hereditary property"
lemma Independent_D2 :
"Independent \<I> \<Longrightarrow> S \<in> \<I> \<Longrightarrow> T \<subseteq> S \<Longrightarrow> T \<in> \<I>"
  by(simp add: Independent_def)


text "The exchange property"
lemma Independent_D3 :
"Independent \<I> \<Longrightarrow> S \<in> \<I> \<Longrightarrow> T \<in> \<I> \<Longrightarrow> card S < card T \<Longrightarrow> finite S \<Longrightarrow> finite T \<Longrightarrow>
 \<exists>e. e \<in> T - S \<and> {e} \<union> S \<in> \<I>"
  by(simp add: Independent_def)



section "Weights"

text "The weight of a set of elements: for simplicity's sake we assume that
      integers (not reals) will be attached to the elements as a weight."
definition "weight (w :: 'a \<Rightarrow> int) A = (\<Sum>x\<in>A. w x)" 
definition "neg (w :: 'a \<Rightarrow> int) = (\<lambda>x. - w x)"

lemma sorted_by_neg :
"sorted_by (neg w) xs = sorted_by w (rev xs)"
  by(induct xs, (fastforce simp add: sorted_by_def neg_def sorted_wrt_append)+)


lemma weight0 :
"weight w {} = 0"
  by(simp add: weight_def)

lemma weight_neg :
"weight (neg w) S = -weight w S"
  by(simp add: weight_def neg_def, rule sum_negf)

lemma weight_mono :
"S \<subseteq> T \<Longrightarrow> finite T \<Longrightarrow> \<forall>x\<in>T-S. w x \<ge> 0 \<Longrightarrow> weight w S \<le> weight w T"
  by(simp add: weight_def, meson sum_mono2)
 
lemma weight_remove :
"x \<in> T \<Longrightarrow> finite T \<Longrightarrow> weight w T = w x + weight w (T - {x})"
  by (simp add: weight_def sum.remove)

lemma weight_insert :
"x \<notin> T \<Longrightarrow> finite T \<Longrightarrow> w x + weight w T = weight w ({x} \<union> T)"
  by (simp add: weight_def)




section "Finite matroids"


locale finite_matroids =
  fixes \<I> :: "'a set set"
  assumes independence  : "Independent \<I>"
begin

definition "basis G X = (finite G \<and> X \<in> \<I> \<and> X \<subseteq> G \<and> (\<forall>X'. X' \<subseteq> G \<longrightarrow> X' \<in> \<I> \<longrightarrow> card X' \<le> card X))"


text "maximum/minimum weight bases"
definition "max_weight_basis w G X = (basis G X \<and> (\<forall>B. basis G B \<longrightarrow> weight w B \<le> weight w X))"
definition "min_weight_basis w G X = (basis G X \<and> (\<forall>B. basis G B \<longrightarrow> weight w B \<ge> weight w X))"

lemma basisD1 :
"basis G X \<Longrightarrow> finite G \<and> X \<in> \<I>" by(simp add: basis_def)

lemma basisD2 :
"basis G X \<Longrightarrow> X \<subseteq> G" by(simp add: basis_def)

lemma basisD3 :
"basis G X \<Longrightarrow> X' \<subseteq> G \<Longrightarrow> X' \<in> \<I> \<Longrightarrow> card X' \<le> card X" by(simp add: basis_def)


lemma basis_card_eq :
"basis G X \<Longrightarrow> basis G X' \<Longrightarrow> card X = card X'"
  by (simp add: basis_def dual_order.eq_iff) 

lemma basis_ext :
"A \<in> \<I> \<Longrightarrow> A \<subseteq> G \<Longrightarrow> finite G \<Longrightarrow> \<exists>A'. A \<subseteq> A' \<and> basis G A'"
  apply(induct A rule: measure_induct[where f="\<lambda>x. card G - card x"], simp)
  apply(rename_tac A)
  apply(case_tac "basis G A", fast)
  apply(subgoal_tac "\<exists>X. X \<subseteq> G \<and> X \<in> \<I> \<and> card X > card A")
   apply clarify
   apply(drule Independent_D3[OF independence, rotated 2])
       apply(erule finite_subset, assumption)+
     apply assumption+
   apply clarify
   apply(drule_tac x="{e} \<union> A" in spec, simp)
   apply (metis card_seteq diff_less_mono2 finite_insert insertCI leI rev_finite_subset subset_iff)
  apply (metis basis_def not_le_imp_less)
  done


subsection "The duality between maximum and minimum weight bases"

lemma max_weight_basis_neg :
"max_weight_basis (neg w) G X = min_weight_basis w G X"
  unfolding max_weight_basis_def min_weight_basis_def
  by (metis neg_le_iff_le weight_neg)


subsection "The auxiliary lemmas on bases of extended/reduced ground sets"

text "The lemma A1 gets split into the following two lemmas:"
lemma A1_1 :
"basis G X \<Longrightarrow> {x} \<union> X \<in> \<I> \<Longrightarrow> basis ({x} \<union> G) ({x} \<union> X)"
  apply(case_tac "x \<in> X")
   apply(frule basisD2)
   apply (metis le_sup_iff singleton_eq sup.absorb2)
  apply(subst basis_def, simp)
  apply(frule basisD1)
  apply clarsimp
  apply(rule conjI)
   apply(drule basisD2, fast)
  apply clarsimp
  apply(frule basisD2)
  apply(rename_tac A)
  apply(drule_tac X'="A - {x}" in basisD3)
    apply fast
   apply(erule_tac S=A in Independent_D2[OF independence], fast)
  apply(case_tac "x \<in> A")
   apply (simp add: finite_subset)+
  done


lemma A1_2 :
"basis G X \<Longrightarrow> {x} \<union> X \<notin> \<I> \<Longrightarrow> basis ({x} \<union> G) X"
  apply(case_tac "x \<in> G")
   apply (simp add: singleton_eq subset_Un_eq)
  apply(subst basis_def, simp)
  apply(frule basisD1)
  apply clarsimp
  apply(rule conjI)
   apply(drule basisD2, fast)
  apply clarsimp
  apply(frule basisD2)
  apply(rule ccontr)
  apply(frule_tac T=X' in Independent_D3[OF independence])
       apply assumption+
     apply simp
    apply(erule finite_subset, assumption)
   apply(erule finite_subset)
   apply clarsimp+
  apply(rename_tac x')
  apply(drule_tac X'="{x'} \<union> X" in basisD3)
    apply fastforce
  by (simp add: finite_subset)+


lemma A2 :
"basis G X \<Longrightarrow> x \<notin> X \<Longrightarrow> basis (G - {x}) X"
  by (simp add: basis_def subset_Diff_insert)


lemma A3 :
"basis G X \<Longrightarrow> x \<in> X \<Longrightarrow> 
 basis (G - {x}) (X - {x}) \<or> (\<exists>x'\<in>G. x' \<notin> X \<and> basis (G - {x}) ({x'} \<union> (X - {x})))"
  apply clarsimp
  apply(subst basis_def, simp)
  apply(frule basisD1)
  apply clarsimp
  apply(rule conjI)
   apply(erule Independent_D2[OF independence], fast)
  apply(rule conjI)
   apply(drule basisD2, fast)
  apply clarsimp
  apply(frule basisD2)
  apply(rule ccontr)
  apply(subgoal_tac "\<exists>x'. x' \<in> X' - (X - {x}) \<and> {x'} \<union> (X - {x}) \<in> \<I>")
   apply clarify
   apply(subgoal_tac "basis (G - {x}) ({x'} \<union> (X - {x}))")
    apply fastforce
   apply(subgoal_tac "card({x'} \<union> (X - {x})) = card X")
    apply(subst basis_def)
    apply(rule conjI, fastforce)+
    apply(subst (asm) basis_def)
    apply (metis Diff_empty subset_Diff_insert)
   apply (metis card.insert_remove card_insert_if finite_Diff finite_subset insert_is_Un)
  apply(rule Independent_D3[OF independence])
      apply(erule Independent_D2[OF independence])
      apply fastforce+
   apply (metis finite_Diff finite_subset)
  using finite_subset by blast


end (* the finite matroids locale *)


  
section "A greedy tactic for lists with weighted elements"


locale language =
  fixes \<L> :: "'a list set"
  assumes \<L>_prop : "xs \<in> \<L> \<Longrightarrow> set xs = set xs' \<Longrightarrow> distinct xs \<Longrightarrow> distinct xs' \<Longrightarrow> 
                    xs' \<in> \<L>"
begin

definition \<L>_img :: "'a set set"
 where "\<L>_img = {set xs |xs. distinct xs \<and> xs \<in> \<L>}"


lemma \<L>_img_eq :
"distinct xs \<Longrightarrow> (set xs \<in> \<L>_img) = (xs \<in> \<L>)"
  using \<L>_img_def \<L>_prop by fastforce

end (* language locale *)



locale greedy_tactic = language +
  fixes w :: "'a \<Rightarrow> int" 
  assumes \<L>_img_independence : "Independent \<L>_img"
begin

text "In addition to the language locale we have assumed that 
        (i)  the elements of type @{typ 'a} are weighted by the function @{term w}
        (ii) @{term \<L>_img} forms a family of independent sets 

      and can interpret the finite matroids locale in this context:"
interpretation fm : finite_matroids \<L>_img
  by(unfold_locales, rule \<L>_img_independence)

definition "max_weight_basis = fm.max_weight_basis"
 
definition "greedy_spec = {(G, X) |G X. max_weight_basis w G X}"

definition "decomp_spec = {({}, Empty)} \<union> {(G, Dcmp x (G - {x})) |G x. x \<in> G \<and> (\<forall>z\<in>G. w x \<le> w z)}"

definition "comp_spec = {(Empty, {})} \<union> {(Dcmp x A, {x} \<union> A) |x A. {x} \<union> A \<in> \<L>_img} \<union> 
                                        {(Dcmp x A, A) |x A. {x} \<union> A \<notin> \<L>_img}"

definition "decomp_impl = (\<lambda>xs. case xs of
                               [] \<Rightarrow> Empty
                             | x # xs' \<Rightarrow> Dcmp x xs')"


definition "comp_impl = (\<lambda>x. case x of
                           Empty \<Rightarrow> []
                         | Dcmp a xs \<Rightarrow> (if a#xs \<in> \<L> then a#xs else xs))"



text "problem reduction principle"
theorem prefixed_point_property :
"DaC_scheme decomp_spec comp_spec greedy_spec \<subseteq> greedy_spec"
  apply(clarsimp simp: DaC_scheme_def)
  apply(rename_tac G a b c)
  apply(case_tac "G = {}")
   apply(clarsimp simp: \<L>_img_independence decomp_spec_def comp_spec_def greedy_spec_def Relt_def 
         max_weight_basis_def fm.max_weight_basis_def fm.basis_def)
   apply(rule Independent_D1, rule \<L>_img_independence)
  apply(clarsimp simp: decomp_spec_def comp_spec_def Relt_def)
  apply(rename_tac a X)
  apply(clarsimp simp: greedy_spec_def max_weight_basis_def fm.max_weight_basis_def)
  apply(frule fm.basisD2)
  apply(erule disjE, clarsimp)
   apply(frule_tac x=a in fm.A1_1, simp+)
   apply(subst (asm) insert_absorb, assumption+)
   apply clarsimp
   apply(rename_tac Y)
   apply(case_tac "a \<notin> Y")
    apply(frule fm.A2, assumption+)
    apply(drule fm.basis_card_eq, assumption)+
    apply (metis fm.basisD1 card_subset_eq finite_insert finite_subset subset_insertI)
   apply simp
   apply(frule fm.A3, assumption+)
   apply(erule disjE)
    apply(drule_tac x="Y - {a}" in spec, drule mp, assumption)
    apply(subgoal_tac "w a + weight w (Y - {a}) \<le> w a + weight w X")
     apply (metis Diff_insert_absorb finite_subset fm.basis_def insertCI subset_Diff_insert weight_remove)
    apply linarith
   apply clarsimp
   apply(drule fm.basis_card_eq, assumption)+
   apply(subgoal_tac "card X = card Y")
    apply (metis card_Suc_eq_finite fm.basis_def infinite_super n_not_Suc_n subset_Diff_insert)
   apply (metis Diff_iff card.remove card_Suc_eq_finite finite_Diff finite_subset fm.basis_def)
  apply(clarsimp simp: greedy_spec_def fm.max_weight_basis_def)
  apply(rename_tac X a)
  apply(frule_tac x=a in fm.A1_2, simp+)
  apply(subst (asm) insert_absorb, assumption+)
  apply clarsimp
  apply(rename_tac Y)
  apply(case_tac "a \<notin> Y")
   apply(frule fm.A2, assumption+)
   apply(drule spec, erule mp, assumption)
  apply simp
  apply(frule fm.A3, assumption+)
  apply(erule disjE)
   apply(drule fm.basis_card_eq, assumption)+
   apply (metis card_Diff1_less_iff finite_subset fm.basis_def nless_le)
  apply clarsimp
  apply(drule_tac x="{x'} \<union> (Y - {a})" in spec, drule mp, simp)
  apply(erule order_trans[rotated 1])
  apply(subst weight_remove, assumption)
   apply (meson finite_subset fm.basisD1 fm.basisD2)
  apply(subgoal_tac "w a + weight w (Y - {a}) \<le> w x' + weight w (Y - {a})")
   apply(erule order_trans)
   apply(subst weight_insert, simp)
    apply (meson finite_Diff finite_subset fm.basisD1 fm.basisD2)
   apply(rule order_refl)
  by simp


text "applying the divide-and-conquer synthesis rule:" 
interpretation greedy: DaC_synthesis 
"{(xs, set xs) |xs. distinct xs \<and> sorted_by w xs}"                 (* \<alpha>\<^sub>1 *)
"{(xs, set xs) |xs. distinct xs}"                                  (* \<alpha>\<^sub>2 *)
greedy_spec decomp_spec comp_spec decomp_impl comp_impl
  apply(unfold_locales)
     apply(rule prefixed_point_property)

  text "decomposition implementation:"
    apply(clarsimp simp: decomp_spec_def decomp_impl_def graph_of_def Relt_def)
    apply(case_tac xs, simp)
     apply(rule_tac b=Empty in relcompI, clarsimp+)
    apply(rename_tac x xs)
    apply(rule_tac b="Dcmp x (set xs)" in relcompI)
     apply(simp add: sorted_by_def)+

  text "composition implementation:"
   apply(clarsimp simp: comp_spec_def comp_impl_def graph_of_def Relt_def)
   apply(rename_tac xs)
   apply(case_tac xs, simp)
    apply(rule_tac b=Empty in relcompI, clarsimp+)
   apply(rename_tac x xs)
   apply(case_tac "x#xs \<in> \<L>", clarsimp)
    apply(subgoal_tac "{x} \<union> set xs \<in> \<L>_img")
     apply(rule_tac b="Dcmp x (set xs)" in relcompI, fast)
     apply fastforce
    apply(subst (asm) \<L>_img_eq[THEN sym], simp+)
   apply(case_tac "x \<in> set xs")
    apply(rule_tac b="Dcmp x (set xs)" in relcompI, fast)
    apply fastforce
   apply(subgoal_tac "{x} \<union> set xs \<notin> \<L>_img")
    apply(rule_tac b="Dcmp x (set xs)" in relcompI, fast)
    apply fastforce
   apply(subst (asm) \<L>_img_eq[THEN sym], simp+)

  text "reductivity:"
  apply clarsimp
  apply(rename_tac xs)
  apply(induct_tac xs rule: length_induct, clarsimp)
  apply(rename_tac xs)
  apply(subst lfp_unfold)
   apply(rule monoI)
   apply(rule monoD[OF monotypeF_mono])
   apply(erule monoD[OF Relt_mono])
  apply(subst singleton_eq)
  apply(rule monotypeF_univ[THEN iffD1])
  apply(subst graph_of_def, subst graph_of_def)
  apply(clarsimp simp: decomp_impl_def)
  apply(rename_tac xs)
  apply(case_tac xs, simp)
   apply(rule_tac b="Empty" in relcompI, simp, simp add: Relt_def)
  apply clarsimp
  apply(rename_tac x xs)
  apply(rule_tac b="Dcmp x xs" in relcompI, simp)
  apply(subst Relt_def, simp)
  done

text "Renaming the synthesised function explicitly:"
definition "syn_greedy = greedy.dac"

text "Deriving the recursive equations for the synthesised function:"
lemma syn_greedy_eqs[simp] :
"syn_greedy [] = []"
"syn_greedy (x#xs) = (if x # syn_greedy xs \<in> \<L> then x # syn_greedy xs else syn_greedy xs)"
unfolding syn_greedy_def by(subst greedy.dac_unfold, simp add: decomp_impl_def comp_impl_def ReltF_eqs)+


lemma syn_greedy_sub[simp] :
"set(syn_greedy xs) \<subseteq> set xs"
  by(induct xs, simp+, fast)


lemma syn_greedy_dist :
"distinct xs \<Longrightarrow> distinct (syn_greedy xs)"
  apply(induct xs, clarsimp+)
  apply(drule subsetD[OF syn_greedy_sub])
  by simp


lemma syn_greedy_max_basis :
"distinct xs \<Longrightarrow> sorted_by w xs \<Longrightarrow> 
 max_weight_basis w (set xs) (set(syn_greedy xs))"
  apply(insert greedy.dac_impl)
  apply(drule_tac c="(set xs, set(syn_greedy xs))" in subsetD)
  apply(rule_tac b=xs in relcompI, simp)
  apply(rule_tac b="syn_greedy xs" in relcompI, simp add: graph_of_def syn_greedy_def)
  apply(simp add: syn_greedy_dist)
  apply(simp add: greedy_spec_def)
  done

end (* the greedy tactic locale *)



section "Two program transformation steps"

locale enhanced_greedy = greedy_tactic +
  fixes ins :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
    and \<L>' :: "'a list set"
  assumes set_ins : "set(ins x xs) = set(x#xs)"
     and  transl  : "distinct xs \<Longrightarrow> (foldr ins xs [] \<in> \<L>') = (xs \<in> \<L>)"
begin

subsection "The first transformation step"

fun greedy where
  "greedy [] = []"
| "greedy (x#xs) = (let g = greedy xs in
                     let xs' = ins x g in
                        if xs' \<in> \<L>' then xs' else g)"


text "Connection to the synthesised function @{term syn_greedy}: "
lemma greedy_eq_syn :
"distinct xs \<Longrightarrow> greedy xs = foldr ins (syn_greedy xs) []"
  apply(induct xs, simp+)
  apply clarify
  apply(frule syn_greedy_dist)
  apply(subgoal_tac "distinct (a#syn_greedy xs)")
  apply(drule_tac xs="a#syn_greedy xs" in transl)
  apply(simp add: Let_def)
  apply clarsimp
  apply(drule subsetD[OF syn_greedy_sub])
  by clarify
  

lemma ins_gen :
"set(foldr ins xs []) = set xs"
  by(induct xs, simp_all add: set_ins)


lemma transformation1_correctness :
"distinct xs \<Longrightarrow> set(greedy xs) = set(syn_greedy xs)"
  apply(drule greedy_eq_syn)
  apply(erule ssubst)
  by(simp add: ins_gen)


subsection "The second transformation (tail-recursion)"


fun greedy_tr 
  where "greedy_tr [] rs = rs" |
        "greedy_tr (x#xs) rs = (let v = ins x rs in
                                 if v \<in> \<L>' then greedy_tr xs v 
                                         else greedy_tr xs rs)"

lemma greedy_tr_app[rule_format] :
"\<forall>rs. greedy_tr (xs@xs') rs = greedy_tr xs' (greedy_tr xs rs)"
  by(induct_tac xs, simp_all add: Let_def)
  
text "Connection to the function @{term greedy} :"  
lemma greedy_greedy_tr :
"greedy (xs @ rs) = greedy_tr (rev xs) (greedy rs)"
  by(induct xs, (clarsimp simp: Let_def greedy_tr_app)+)

corollary transformation2_correctness :
"greedy (rev xs) = greedy_tr xs []"
  by(subst greedy_greedy_tr[rule_format, where rs="[]", simplified], simp)


text "Note that one can also directly show the identity:"
lemma greedy_greedy_tr' :
"greedy xs = greedy_tr (rev xs) []"
  by(induct xs, (clarsimp simp: Let_def greedy_tr_app)+)




text "Summarising the main result of the greedy tactic (synthesis + transformations): "
corollary greedy_tr_max_basis :
"distinct xs \<Longrightarrow> sorted_by (neg w) xs \<Longrightarrow> 
 max_weight_basis w (set xs) (set(greedy_tr xs []))"
  apply(subst transformation2_correctness[THEN sym])
  apply(subst transformation1_correctness, simp)
  apply(subst set_rev[THEN sym])
  apply(rule syn_greedy_max_basis)
  apply simp
  apply(subst sorted_by_neg[THEN sym])
  apply assumption+
  done


end (* the enhanced greedy locale *)



end



