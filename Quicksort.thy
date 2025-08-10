(* ****************************************************************************************

    Theory Quicksort.thy is part of a package supplementing  
    'Structured development of implementations for divide-and-conquer specifications'.
    Copyright (c) 2023  M. Bortin

    The package is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the package.
    
   *************************************************************************************** *)


theory Quicksort
imports DaC_synthesis2
begin


section "Deriving Quicksort"

text "To underline that the basic principles remain the same,
      the divide-and-conquer tactic shall be applied below
      to derive the well-known quicksort algorithm."

interpretation quicksort: DaC_synthesis 
"{(xs, xs) |xs. distinct xs}"                 (* \<alpha>\<^sub>1 *)
"Id"                                          (* \<alpha>\<^sub>2 *)

(* the specification of sorting on distinct lists: *)
"{(il, ol). set il = set ol \<and> distinct ol \<and> sorted ol}"          

(* decomposition specification: *)
"{([], Empty)} \<union> {(x#xs, Dcmp x l r) |x xs l r. set xs = set(l@r) \<and> (\<forall>a\<in>set l. a < x) \<and> (\<forall>a\<in>set r. x < a)}"

(* composition specification: *)
"{(Empty, [])} \<union> {(Dcmp x l r, xs) |x l r xs. xs = l@[x]@r}"

(* decomposition implementation: *)
"(\<lambda>xs. case xs of
        [] \<Rightarrow> Empty
      | x#xs' \<Rightarrow> Dcmp x (filter (\<lambda>a. a < x) xs') (filter (\<lambda>a. x < a) xs'))"

(* composition implementation: *)
"(\<lambda>x. case x of
       Empty \<Rightarrow> []
     | Dcmp x l r \<Rightarrow> l@[x]@r)"
(* showing the applicability conditions: *)
  apply(unfold_locales)
     apply(clarsimp simp: Relt_def DaC_scheme_def)
     apply(erule disjE, clarsimp+)
     apply(rule conjI, fastforce)+
     apply(subst sorted_wrt_append, fastforce)
    apply(clarsimp simp: graph_of_def Relt_def)
    apply(case_tac xs, fastforce)
    apply clarsimp
    apply(rename_tac x xs)
    apply(rule_tac b="Dcmp x (filter ((>) x) xs) (filter ((<) x) xs)" in relcompI)
     apply simp
     apply(rule set_eqI)
     using linorder_neq_iff apply fastforce
       apply clarsimp
      apply(clarsimp simp: graph_of_def Relt_def)
      apply(rename_tac x)
      apply(case_tac x, fastforce)
      apply clarsimp
      apply(rename_tac x l r)
      apply(rule_tac b="Dcmp x l r" in relcompI, fast, simp)
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
     apply clarsimp
     apply(rename_tac xs)
     apply(case_tac xs, simp)
     apply(rule_tac b="Empty" in relcompI, simp, simp add: Relt_def)
     apply clarsimp
     apply(rename_tac x xs)
     apply(rule_tac b="Dcmp x (filter ((>) x) xs) (filter ((<) x) xs)" in relcompI, simp)
     apply(subst Relt_def, simp)
     apply(frule_tac x="filter ((>) x) xs" in spec)
     apply(drule_tac x="filter ((<) x) xs" in spec)
     using length_filter_le less_Suc_eq_le by blast



lemma quicksort_eqs :
"quicksort.dac [] = []"
"quicksort.dac (x#xs) = (let l = filter ((>) x) xs in
                         let r = filter ((<) x) xs in
                          quicksort.dac l @ [x] @ quicksort.dac r)"
  by(subst quicksort.dac_unfold, simp add: ReltF_eqs)+



lemma quicksort_impl :
"distinct xs \<Longrightarrow>
 set(quicksort.dac xs) = set xs \<and> distinct(quicksort.dac xs) \<and> sorted (quicksort.dac xs)"
  apply(insert quicksort.dac_impl)
  apply(drule_tac c="(xs, quicksort.dac xs)" in subsetD)
   apply(rule_tac b=xs in relcompI, simp)
   apply(rule_tac b="quicksort.dac xs" in relcompI, simp add: graph_of_def)
   apply simp
  by blast



end