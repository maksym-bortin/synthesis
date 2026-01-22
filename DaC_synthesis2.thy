(* ****************************************************************************************

    Theory DaC_synthesis2.thy is part of a package supplementing  
    'Structured development of implementations for divide-and-conquer specifications'.
    Copyright (c) 2023  M. Bortin

    The package is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the package.
    
   *************************************************************************************** *)

theory DaC_synthesis2
  imports Preliminaries
begin

section "The divide-and-conquer tactic for another relator" 

text "To illustrate how the design tactic may work also without support for
      type constructor classes, this theory sets up the same synthesis rule 
      but for another relator instance which enables two recursive calls of
      the synthesised function (e.g. the quicksort algorithm proceeds this way)."

datatype ('u, 'a) Relt = Empty | Dcmp 'u 'a 'a

definition Relt :: "'a \<rightarrow> 'b \<Rightarrow> ('v, 'a) Relt \<rightarrow> ('v, 'b) Relt"
  where  "Relt r = {(Empty, Empty)} \<union> 
                    {(Dcmp x A A', Dcmp x B B') |x A B A' B'. (A, B) \<in> r \<and> (A', B') \<in> r}"


subsection "Showing the relator axioms"

lemma Relt_mono:
"mono Relt"
  unfolding Relt_def
  by(rule monoI, fast)

lemma Relt_comp:
"Relt r \<diamondop> Relt s = Relt (r \<diamondop> s)"
  unfolding Relt_def
  by(rule equalityI, blast+)
  
lemma Relt_Id:
"Relt Id = Id"
  unfolding Relt_def  
  by (clarsimp, rule set_eqI, smt (verit, best) IdE IdI Relt.exhaust insert_iff mem_Collect_eq)
  
lemma Relt_conv:
"(Relt r)\<^sup>\<circ> \<subseteq> Relt (r\<^sup>\<circ>)"
  unfolding Relt_def
  by blast

subsection "Derived properties"

lemma Relt_conv_eq :
"(Relt r)\<^sup>\<circ> = Relt (r\<^sup>\<circ>)"
  by (metis Relt_conv converse_converse converse_subset_swap subset_antisym)


lemma Relt_simple : 
"simple r \<Longrightarrow> simple(Relt r)"
  by (metis Relt_Id Relt_comp Relt_conv_eq Relt_mono monoD simple_def)

lemma Relt_entire :
"entire r \<Longrightarrow> entire(Relt r)"
  by (metis Relt_Id Relt_comp Relt_conv_eq Relt_mono entire_def monoE)


lemma Relt_graph_of :
"\<exists>g. Relt(graph_of f) = graph_of g"
  apply(subgoal_tac "simple (graph_of f)")
  apply(subgoal_tac "entire (graph_of f)")
  apply (simp add: Relt_entire Relt_simple mapping)
  by(simp add: graph_of_def simple_def entire_def, fast)+


subsubsection "The induced endofunctor"

definition
  "ReltF f = funct_of(Relt (graph_of f))"

lemma ReltF_eqs :
"ReltF f Empty = Empty"
"ReltF f (Dcmp x u v) = Dcmp x (f u) (f v)"
  by(simp add: ReltF_def Relt_def funct_of_def graph_of_def)+

lemma ReltF :
"Relt(graph_of f) = graph_of(ReltF f)"
  by (metis ReltF_def Relt_graph_of graph_of_funct_of)


text "showing the functor axioms:"

lemma ReltF1 :
"ReltF id = id"
  by (metis ReltF_def Relt_Id graph_of_funct_of graph_of_id)


lemma ReltF2 :
"ReltF (g \<circ> f) = ReltF g \<circ> ReltF f"
  by (metis ReltF Relt_comp graph_of_comp graph_of_funct_of)



text "Note that the remainder is actually just copied
      from the theory DaC-synthesis.thy"

definition
"DaC_scheme decompose compose = (\<lambda>r. decompose \<diamondop> Relt r \<diamondop> compose)"

lemma DaC_mono :
"decompose \<subseteq> decompose' \<Longrightarrow> compose \<subseteq> compose' \<Longrightarrow> r \<subseteq> r' \<Longrightarrow> 
 DaC_scheme decompose compose r \<subseteq> DaC_scheme decompose' compose' r'"
proof(simp add: DaC_scheme_def, erule relcomp_mono, erule relcomp_mono[rotated 1])
qed(rule monoD[OF Relt_mono])


corollary DaC_mono' :
"mono (DaC_scheme decompose compose)"
  by (simp add: DaC_mono monoI)


locale DaC_synthesis =
  fixes \<alpha>\<^sub>1 :: "'a \<rightarrow> 'b"
    and \<alpha>\<^sub>2 :: "'c \<rightarrow> 'd"
  and spec :: "'b \<rightarrow> 'd"
  and abs_dcmp :: "'b \<rightarrow> ('x, 'b) Relt"
  and abs_cmp  :: "('x, 'd) Relt \<rightarrow> 'd"
  and dcmp     :: "'a \<Rightarrow> ('x, 'a) Relt"
  and cmp      :: "('x, 'c) Relt \<Rightarrow> 'c" 
assumes
  DaC : "DaC_scheme abs_dcmp abs_cmp spec \<subseteq> spec"
and
  decomp : "\<alpha>\<^sub>1\<^sup>\<circ> \<diamondop> (graph_of dcmp) \<subseteq> abs_dcmp \<diamondop> Relt (\<alpha>\<^sub>1\<^sup>\<circ>)"
and
  comp   : "(graph_of cmp) \<diamondop> \<alpha>\<^sub>2 \<subseteq> Relt \<alpha>\<^sub>2 \<diamondop> abs_cmp"
and
  reduct : "Id \<subseteq> lfp(\<lambda>x. monotypeF (graph_of dcmp) (Relt x))"
begin


lemma DaC_simple :
"simple d \<Longrightarrow> simple c \<Longrightarrow> simple (lfp (DaC_scheme d c))"
  apply(simp add: simple_def)
  apply(subst rdiv_univ)
  apply(rule lfp_lowerbound)
  apply(subst rdiv_univ[THEN sym])
  apply(subst lfp_unfold)
   apply(rule monoI, rule DaC_mono, rule subset_refl, rule subset_refl, assumption)
  apply(simp add: DaC_scheme_def)
  apply(fold DaC_scheme_def)
  apply(subst converse_relcomp)+
  apply(subst Relt_conv_eq)
  apply(subst O_assoc)+
  apply(rule subset_trans)
   apply(rule relcomp_mono[rotated 1])
    apply(rule relcomp_mono[rotated 1])
     apply(subst O_assoc[THEN sym])+
     apply(rule relcomp_mono)
      apply(erule relcomp_mono)
      apply(rule subset_refl)+
  apply simp
  apply(rule subset_trans)
   apply(rule relcomp_mono[rotated 1])
    apply(subst O_assoc[THEN sym])
    apply(rule relcomp_mono)
     apply(subst Relt_comp)
     apply(rule monoD[OF Relt_mono])
     apply(rule rdiv_univ[THEN iffD2])
     apply(rule subset_refl)+
  apply(subst Relt_Id)
  by simp



lemma DaC_entire :
"entire c \<Longrightarrow> entire(lfp(DaC_scheme (graph_of dcmp) c))"
  apply(simp add: entire_def)
  apply(rule subset_trans, rule reduct)
  apply(rule_tac H="\<lambda>x. x \<diamondop> x\<^sup>\<circ>" in lfp_fusion)
  apply(rule monoI, rule DaC_mono, simp+)
  apply(rule allI)
  apply(subgoal_tac "monotypeF (graph_of dcmp) (Relt (x \<diamondop> x\<^sup>\<circ>)) \<subseteq> 
                    (monotypeF (graph_of dcmp) (Relt (x \<diamondop> x\<^sup>\<circ>)) \<diamondop> (graph_of dcmp)) \<diamondop> (graph_of dcmp)\<^sup>\<circ>")
   apply(erule subset_trans)
   apply(rule subset_trans)
    apply(rule relcomp_mono)
     apply(rule monotypeF1)
    apply(rule subset_refl)
   apply(subst Relt_comp[THEN sym])
   apply(simp add: DaC_scheme_def)
   apply(subst converse_relcomp)+
   apply(subst Relt_conv_eq)
   apply(subst O_assoc)+
   apply(rule relcomp_mono, rule subset_refl)+
   apply(rule subset_trans[rotated 1])
    apply(subst O_assoc[THEN sym])+
    apply(rule relcomp_mono)
     apply(erule relcomp_mono)
     apply(rule subset_refl)+
   apply simp
  apply(subst O_assoc)+
  apply(rule subset_trans[rotated 1])
   apply(rule_tac s'=Id in relcomp_mono)
    apply(rule subset_refl)
   apply(clarsimp simp: graph_of_def, fast)
  by simp



lemma DaC_impl :
"\<alpha>\<^sub>1\<^sup>\<circ> \<diamondop> lfp(DaC_scheme (graph_of dcmp) (graph_of cmp)) \<diamondop> \<alpha>\<^sub>2 \<subseteq> spec"
  apply(subst O_assoc[THEN sym])
  apply(subst ldiv_univ)
  apply(subst rdiv_univ)
  apply(rule lfp_lowerbound)
  apply(subst rdiv_univ[THEN sym])
  apply(subst ldiv_univ[THEN sym])
  apply(simp add: DaC_scheme_def)
  apply(rule subset_trans[rotated 1])
   apply(rule DaC) 
  apply(subst O_assoc[THEN sym])+
  apply(rule subset_trans)
   apply(rule relcomp_mono)
    apply(rule relcomp_mono)
     apply(rule relcomp_mono)
      apply(rule decomp)
     apply(rule subset_refl)+
  apply(subst O_assoc)+
  apply(rule subset_trans)
   apply(rule relcomp_mono[rotated 1])
    apply(rule relcomp_mono[rotated 1])
     apply(rule relcomp_mono[rotated 1])
      apply(rule comp)
     apply(rule subset_refl)+
  apply(simp add: DaC_scheme_def)
  apply(rule relcomp_mono, rule subset_refl)
  apply(subst O_assoc[THEN sym])+
  apply(subst Relt_comp)+
  apply(rule relcomp_mono[rotated 1], rule subset_refl)
  apply(rule monoD[OF Relt_mono])
  apply(rule subset_trans)
   apply(rule relcomp_mono)
    apply(rule rdiv_univ[THEN iffD2])
    apply(rule subset_refl)+
  apply(rule ldiv_univ[THEN iffD2])
  by(rule subset_refl)


theorem DaC_synthesis :
"\<exists>\<phi>. lfp(DaC_scheme (graph_of dcmp) (graph_of cmp)) = graph_of \<phi> \<and>
     \<alpha>\<^sub>1\<^sup>\<circ> \<diamondop> graph_of \<phi> \<diamondop> \<alpha>\<^sub>2 \<subseteq> spec"
  apply(subgoal_tac "\<exists>\<phi>. lfp(DaC_scheme (graph_of dcmp) (graph_of cmp)) = graph_of \<phi>")
   apply clarify
   apply(rule exI, rule conjI, assumption)
   apply(erule subst)
   apply(rule DaC_impl)
  apply(rule mapping)
   apply(rule DaC_simple)
    apply(clarsimp simp: simple_def graph_of_def)
   apply(clarsimp simp: simple_def graph_of_def)
  apply(rule DaC_entire)
  apply(clarsimp simp: entire_def graph_of_def)
  by fast



definition "dac = (THE \<phi>. lfp(DaC_scheme (graph_of dcmp) (graph_of cmp)) = graph_of \<phi>)"


lemma dac_lfp :
"graph_of dac = lfp(DaC_scheme (graph_of dcmp) (graph_of cmp))"
  by (smt (verit, del_insts) DaC_synthesis dac_def graph_of_funct_of theI')


lemma dac_unq :
"lfp (DaC_scheme (graph_of dcmp) (graph_of cmp)) = graph_of f \<Longrightarrow> f = dac"
  by(rule injD[OF graph_of_inj], simp add: dac_lfp)


lemma dac_unfold :
"dac = cmp \<circ> ReltF dac \<circ> dcmp"
  apply(rule injD[OF graph_of_inj])
  apply(simp add: graph_of_comp ReltF[THEN sym])
  by (metis DaC_mono' DaC_scheme_def dac_lfp lfp_unfold)



lemma dac_unq_function :
"f = cmp \<circ> ReltF f \<circ> dcmp \<Longrightarrow> f = dac"
  apply(rule sym, rule graph_of_sub)
  apply(drule_tac f=graph_of in arg_cong)
  apply(simp add: graph_of_comp ReltF[THEN sym])
  by (simp add: DaC_scheme_def dac_lfp lfp_lowerbound)


lemma dac_impl :
"\<alpha>\<^sub>1\<^sup>\<circ> \<diamondop> (graph_of dac) \<diamondop> \<alpha>\<^sub>2 \<subseteq> spec"
  by (simp add: DaC_impl dac_lfp)


lemma dac_impl_inversion :
"simple spec \<Longrightarrow> entire \<alpha>\<^sub>2 \<Longrightarrow> \<alpha>\<^sub>1 \<diamondop> spec \<subseteq> (graph_of dac) \<diamondop> \<alpha>\<^sub>2"
  apply clarsimp
  apply(rename_tac u v w)
  apply(simp add: entire_def)
  apply(drule_tac c="(dac u, dac u)" in subsetD, clarsimp+)
  apply(rename_tac w')
  apply(subgoal_tac "(v, w') \<in> spec")
   apply(simp add: simple_def)
   apply(drule_tac c="(w, w')" in subsetD, fast)
   apply clarsimp
   apply (meson converse_iff graph_of_eqD relcomp.simps)
  apply(rule subsetD[OF dac_impl])
  apply (meson converse_iff graph_of_eqD relcomp.simps)
  done


end  (* the divide-and-conquer tactic *)

end




