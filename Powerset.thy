(* ********************************************************************************

    Theory Powerset.thy is part of a package providing supplementary material 
    to 'Synthesis of Implementations for Divide-and-conquer Specifications'.
    Copyright (c) 2023  M. Bortin

    The package is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the package.
    
   ******************************************************************************* *)

theory Powerset
imports DaC_synthesis
begin


text "The following theory contains an introductory example application of the 
      divide-and-conquer design tactic synthesising a function that computes a 
      list representation for the power set of a given finite set." 

text "Note that the explicit typing merely caters better readability and 
      may be omitted as well." 
definition pow :: "'a set \<rightarrow> 'a set set" 
  where "pow = {(S, P) |S P. \<forall>X. (X \<in> P) = (X \<subseteq> S)}"

definition decomp_spec :: "'a set \<rightarrow> ('a, 'a set) Relt"
  where "decomp_spec = {({}, Empty)} \<union> {(G, Dcmp a (G - {a})) |G a. a \<in> G}"

definition comp_spec :: "('a, 'a set set) Relt \<rightarrow> 'a set set"
  where "comp_spec = {(Empty, {{}})} \<union> 
                     {(Dcmp a P, P \<union> {{a} \<union> A |A. A \<in> P}) |a P. True}"

definition decomp_impl :: "'a list \<Rightarrow> ('a, 'a list) Relt"
  where "decomp_impl = (\<lambda>xs. case xs of
                               [] \<Rightarrow> Empty
                             | x # xs' \<Rightarrow> Dcmp x xs')"


definition comp_impl :: "('a, 'a list list) Relt \<Rightarrow> 'a list list"
  where "comp_impl = (\<lambda>x. case x of
                           Empty \<Rightarrow> [[]]
                         | Dcmp a xxs \<Rightarrow> xxs @ map (\<lambda>xs. a#xs) xxs)"




text "Next we apply the divide-and-conquer synthesis rule: " 
interpretation powerset: DaC_synthesis 
"{(xs, set xs) |xs. distinct xs}"                 (* \<alpha>\<^sub>1 *)
"{(xxs, {set xs |xs. xs \<in> set xxs}) |xxs. True}"                               (* \<alpha>\<^sub>2 *)
pow decomp_spec comp_spec decomp_impl comp_impl
  apply(unfold_locales)

  text "problem reduction principle:"
     apply(clarsimp simp: DaC_scheme_def decomp_spec_def comp_spec_def Relt_def pow_def)
     apply(elim disjE, clarsimp+)
     apply (metis insert_Diff insert_mono subset_Diff_insert subset_insert_iff)

  text "decomposition implementation:"
    apply(clarsimp simp: decomp_spec_def decomp_impl_def graphF_def Relt_def)
    apply(case_tac xs, simp)
     apply(rule_tac b=Empty in relcompI, clarsimp+)
    apply(rename_tac x xs)
    apply(rule_tac b="Dcmp x (set xs)" in relcompI)
     apply simp+

  text "composition implementation:"
   apply(clarsimp simp: comp_spec_def comp_impl_def graphF_def Relt_def)
   apply(rename_tac xxs)
   apply(case_tac xxs, simp)
    apply(rule_tac b=Empty in relcompI, clarsimp+)
   apply(rename_tac x xxs)
   apply(rule_tac b="Dcmp x {set xs |xs. xs \<in> set xxs}" in relcompI)
    apply fast
   apply clarsimp
  apply(rule set_eqI, rule iffI)
    apply (clarsimp, metis imageE list.simps(15))
   apply (clarsimp, metis imageI list.simps(15))

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
  apply(subst graphF_def, subst graphF_def)
  apply(clarsimp simp: decomp_impl_def)
  apply(rename_tac xs)
  apply(case_tac xs, simp)
   apply(rule_tac b="Empty" in relcompI, simp, simp add: Relt_def)
  apply clarsimp
  apply(rename_tac x xs)
  apply(rule_tac b="Dcmp x xs" in relcompI, simp)
  apply(subst Relt_def, simp)
  done



text "Deriving the recursive equations for the synthesised function:"
lemma syn_powerset_eqs[simp] :
"powerset.dac [] = [[]]"
"powerset.dac (x#xs) = (let xxs = powerset.dac xs in xxs @ map (\<lambda>xs. x#xs) xxs)"
  by(subst powerset.dac_unfold, simp add: Let_def decomp_impl_def comp_impl_def ReltF_eqs)+



text "The correctness of the synthesised @{term powerset.dac} follows from the 
      implementation property @{thm powerset.dac_impl} :"
lemma syn_powerset_corr :
"distinct xs \<Longrightarrow> (X \<subseteq> set xs) = (\<exists>ys \<in> set(powerset.dac xs). set ys = X)"
  apply(insert powerset.dac_impl)
  apply(drule_tac c="(set xs, {set ys |ys. ys \<in> set(powerset.dac xs)})" in subsetD)
   apply(rule_tac b=xs in relcompI, simp)
   apply(rule_tac b="powerset.dac xs" in relcompI, simp add: graphF_def)
   apply simp
  apply(clarsimp simp: pow_def)
  by metis



text "The purpose of the restriction of inputs to distinct lists is
       (a) no more list representations will be generated than needed:"
lemma syn_powerset_length :
"distinct xs \<Longrightarrow> length(powerset.dac xs) = 2^(length xs)"
  by(induct xs, (simp add: Let_def)+)

text "and (b) each of the representations is in turn distinct:"
lemma syn_powerset_distinct :
"distinct xs \<Longrightarrow> \<forall>ys\<in>set(powerset.dac xs). distinct ys"
  apply(induct xs, (clarsimp simp: Let_def)+)
  apply(erule disjE, fast)
  by (smt (verit, ccfv_SIG) distinct.simps(2) imageE subsetD syn_powerset_corr)



text "Finally we can replace the synthesised function by the tail-recursive function:" 
fun pow_tr where
"pow_tr [] rs = rs" |
"pow_tr (x#xs) rs = pow_tr xs (rs @ map (\<lambda>xs. x#xs) rs)"

lemma pow_tr_app :
"pow_tr (xs @ ys) rs = pow_tr ys (pow_tr xs rs)"
  by(induct xs arbitrary: rs, simp+)


lemma dac_pow_tr :
"powerset.dac (xs @ ys) = pow_tr (rev xs) (powerset.dac ys)"
  by(induct xs arbitrary: ys, simp_all add: Let_def pow_tr_app)

corollary pow_tr :
"pow_tr xs [[]] = powerset.dac (rev xs)"
  by (metis append_Nil2 dac_pow_tr rev_rev_ident syn_powerset_eqs(1))


text "The correctness of @{term pow_tr} now follows straight:" 
lemma pow_tr_corr :
"distinct xs \<Longrightarrow> (X \<subseteq> set xs) = (\<exists>ys \<in> set(pow_tr xs [[]]). set ys = X)"
  apply(subst pow_tr)
  apply(subst syn_powerset_corr[THEN sym])
  by simp+


lemma pow_tr_length :
"distinct xs \<Longrightarrow> length(pow_tr xs [[]]) = 2^(length xs)"
  by(subst pow_tr, subst syn_powerset_length, simp+)

lemma pow_tr_distinct :
"distinct xs \<Longrightarrow> \<forall>ys\<in>set(pow_tr xs [[]]). distinct ys"
  by(subst pow_tr, rule syn_powerset_distinct, simp)

end