(* ********************************************************************************

    Theory Scheduling.thy is part of a package providing supplementary material 
    to 'Synthesis of Implementations for Divide-and-conquer Specifications'.
    Copyright (c) 2023  M. Bortin

    The package is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the package.
    
   ******************************************************************************* *)


theory Scheduling
  imports Greedy 
begin


record job =
 val  :: nat
 date :: nat



fun adm' :: "nat \<Rightarrow> job list \<Rightarrow> bool"
where "adm' i [] = True" |
  "adm' i (j#js) = (i \<le> date j \<and> adm' (i+1) js)"

lemma adm'_eq[rule_format] :
"\<forall>i. adm' i js = (\<forall>k<length js. k + i \<le> date (js!k))"
  apply(induct_tac js, simp_all)
  apply clarify
  apply(rule iffI)
   apply clarify
   apply(subst nth_Cons)
   apply(case_tac k, clarsimp+)
  apply(rule conjI)
   apply(drule_tac x=0 in spec, drule mp, clarsimp+)
  apply(drule_tac x="Suc k" in spec, drule mp, clarsimp+)
  done


lemma adm'_shift :
"adm' i js \<Longrightarrow> k \<le> i \<Longrightarrow> adm' k js"
  by(fastforce simp: adm'_eq)


lemma adm'_comp_eq :
"(adm' d xs \<and> adm' (d + length xs) xs') = adm' d (xs@xs')"
  apply(induct xs arbitrary:d xs', clarsimp+)
  apply(drule_tac x="d+1" in meta_spec)
  apply(drule_tac x="xs'" in meta_spec)
  by simp

lemmas adm'_comp = adm'_comp_eq[THEN iffD1, OF conjI]

lemma adm'_drop :
  "adm' d xs \<Longrightarrow> adm' (d+n) (drop n xs)"
  apply(case_tac "length xs < n", simp)
  apply(subst (asm) append_take_drop_id[where n=n, THEN sym])
  apply(subst (asm) adm'_comp_eq[THEN sym])
  by(simp add: min_def split: if_splits)
  

lemma adm'_rem1 :
"adm' (Suc d) (remove1 a xs) \<Longrightarrow> d \<le> date a \<Longrightarrow> a \<in> set xs \<Longrightarrow> Sorted date xs \<Longrightarrow> 
 adm' d xs"
  apply(induct xs arbitrary:d)
   apply simp_all
  by (smt (verit, ccfv_SIG) Suc_eq_plus1 Suc_le_eq adm'.simps(2) le_eq_less_or_eq linorder_not_le)


lemma adm'_subset :
"Sorted date xs \<Longrightarrow> set xs \<subseteq> set xs' \<Longrightarrow>
 distinct xs \<Longrightarrow> adm' d xs' \<Longrightarrow> d' \<le> d \<Longrightarrow>
 adm' d' xs" 
  apply(induct xs' arbitrary:xs d d', simp)
  apply clarsimp
  apply(rename_tac x xs' xs d d')
  apply(case_tac "x \<in> set xs")
   apply(drule_tac x="remove1 x xs" in meta_spec)
   apply(drule_tac x="Suc d" in meta_spec)
   apply(drule_tac x="Suc d'" in meta_spec)
   apply(drule meta_mp, erule Sorted_rem1)
   apply(drule meta_mp, fastforce)
   apply(drule meta_mp, erule distinct_remove1)
   apply simp
   apply(erule adm'_rem1)
   apply simp
   apply assumption+
  apply(drule_tac x=xs in meta_spec)
  apply(drule_tac x="Suc d" in meta_spec, simp)
  apply(drule_tac x="d'" in meta_spec)
  apply(drule meta_mp, fastforce)
  by simp
 

corollary adm'_subset' :
"Sorted date xs \<Longrightarrow> set xs \<subseteq> set xs' \<Longrightarrow> distinct xs \<Longrightarrow> adm' d xs' \<Longrightarrow>
  adm' d xs"
  by(erule adm'_subset, simp+)


lemma adm' :
"adm' d xs \<Longrightarrow> Sorted date xs' \<Longrightarrow> set xs = set xs' \<Longrightarrow> distinct xs' \<Longrightarrow>
 adm' d xs'"
  by(erule adm'_subset'[rotated 2], assumption+, simp)



definition "adm = {xs. adm' 1 xs}"

corollary adm_eq :
"(js \<in> adm) = (\<forall>k < length js. k + 1 \<le> date (js!k))"
  by (simp add: adm'_eq adm_def)



fun ins :: "job \<Rightarrow> job list \<Rightarrow> job list"
  where "ins j [] = [j]" |
  "ins j (x#xs) = (if date j \<le> date x then j#x#xs else x#(ins j xs))"

lemma ins_length[simp] :
  "length (ins x xs) = 1 + length xs"
  by(induct xs, simp_all)


lemma ins_set[simp] :
  "set(ins x xs) = set(x#xs)"
  by(induct xs, simp_all, fastforce)

lemma set_ins_fold[simp] :
  "set(foldr ins xs []) = set xs"
  by(induct xs, simp_all)

lemma sorted_ins :
  "Sorted date xs \<Longrightarrow> Sorted date (ins x xs)"
  by(induct xs, simp_all, fastforce)
  
lemma ins_sorted :
  "Sorted date (foldr ins xs [])"
  by(induct xs, simp_all, erule sorted_ins)

lemma ins_dist :
 "distinct xs \<Longrightarrow> x \<notin> set xs \<Longrightarrow> distinct (ins x xs)"
by(induct xs, simp_all, fast) 

lemma dist_ins_fold :
  "distinct xs \<Longrightarrow> distinct(foldr ins xs [])"
  apply(induct xs, simp_all)
  apply(erule ins_dist, clarsimp)
  done



section "Applying the greedy tactic"

definition "w_job = int \<circ> val"
definition "\<L>_job = {xs. foldr ins xs [] \<in> adm}"


lemma \<L>_jobD :
  "distinct xs \<Longrightarrow> xs \<in> \<L>_job \<Longrightarrow> 
   \<exists>xs'. distinct xs' \<and> Sorted date xs' \<and> adm' 1 xs' \<and> set xs' = set xs"
  apply(clarsimp simp: \<L>_job_def adm_def)
  using dist_ins_fold ins_sorted set_ins_fold by blast


lemma adm'_\<L>_job :
  "adm' 1 xs \<Longrightarrow> distinct xs \<Longrightarrow> xs \<in> \<L>_job"
  apply(clarsimp simp: \<L>_job_def adm_def)
  using adm' dist_ins_fold ins_sorted set_ins_fold by blast






lemma job_Independent :
"Independent (language_struct.\<L>_img \<L>_job)"
proof(subst language_struct.\<L>_img_def)
  show "language_struct \<L>_job"
    by (simp add: \<L>_job_def adm' adm_def dist_ins_fold ins_sorted language_struct_def)
next
  show "Independent {set xs |xs. distinct xs \<and> xs \<in> \<L>_job}"
  proof(simp add: Independent_def, intro conjI, simp add: \<L>_job_def adm_def, 
        clarify, drule \<L>_jobD, assumption, clarsimp simp: \<L>_job_def adm_def)
  fix xs' xs T assume a: "adm' (Suc 0) xs'"
                  and b: "set xs' = set xs"
                  and c: "T \<subseteq> set xs" 
  have "\<exists>ys. set ys = T \<and> distinct ys"
    by (meson List.finite_set c finite_distinct_list finite_subset)
  with b and c obtain ys where d: "distinct ys \<and> set ys \<subseteq> set xs' \<and> T = set ys" by fast
  show "\<exists>xs. T = set xs \<and> distinct xs \<and> adm' (Suc 0) (foldr ins xs [])"
    using a adm'_subset' d dist_ins_fold ins_sorted by auto
next
  show "\<forall>S. finite S \<longrightarrow>
        (\<forall>T. finite T \<longrightarrow>
             (\<exists>xs. S = set xs \<and> distinct xs \<and> xs \<in> \<L>_job) \<longrightarrow>
             (\<exists>xs. T = set xs \<and> distinct xs \<and> xs \<in> \<L>_job) \<longrightarrow>
             card S < card T \<longrightarrow> (\<exists>e. e \<in> T \<and> e \<notin> S \<and> 
              (\<exists>xs. insert e S = set xs \<and> distinct xs \<and> xs \<in> \<L>_job)))"
  proof clarsimp
    fix xs' :: "job list"
    fix ys' :: "job list"
    assume a: "xs' \<in> \<L>_job"
    assume b: "ys' \<in> \<L>_job"
    assume c: "card(set xs') < card(set ys')"
    assume d: "distinct ys'"
    assume e: "distinct xs'"

    have "\<exists>xs. distinct xs \<and> Sorted date xs \<and> adm' 1 xs \<and> set xs = set xs'"
      by(rule \<L>_jobD, rule e, rule a)
    then obtain xs where 1: "distinct xs \<and> Sorted date xs \<and> adm' 1 xs \<and> set xs = set xs'" ..
    have "\<exists>xs. distinct xs \<and> Sorted date xs \<and> adm' 1 xs \<and> set xs = set ys'"
      by(rule \<L>_jobD, rule d, rule b)
    then obtain ys where 2: "distinct ys \<and> Sorted date ys \<and> adm' 1 ys \<and> set ys = set ys'" ..
    with 1 and c have c' : "card(set xs) < card(set ys)" 
      by simp
    have "\<exists>x. x \<in> set ys \<and> x \<notin> set xs"
      by (metis "1" "2" List.finite_set c card_mono linorder_not_le subsetI)
    then obtain x where 3: "x \<in> set ys \<and> x \<notin> set xs"..
    have 4: "\<exists>i<length ys. ys!i \<notin> set xs" 
      using "3" mem_nth by fastforce 
    then obtain i where 5: "i<length ys \<and> ys!i \<notin> set xs" ..

    let ?\<nu> = "Max{i. i<length ys \<and> ys!i \<notin> set xs}"
    let ?e = "ys!?\<nu>"
    have "?\<nu> \<in> {i. i<length ys \<and> ys!i \<notin> set xs}" 
      by(rule Max_in, simp+, rule 4)
    hence \<nu>_prop : "?\<nu> < length ys" "?e \<notin> set xs" "\<forall>i<length ys. ?\<nu> < i \<longrightarrow> ys!i \<in> set xs"
      by(blast+, clarsimp, subst (asm) Max_less_iff, simp, fast, fast)
    hence "?\<nu>+1 \<le> length ys"
      by linarith 
    hence min: "min (length ys) (?\<nu>+1) = ?\<nu>+1" 
      by fastforce
    have e_prop : "?e \<in> set ys" 
      by (simp add: \<nu>_prop)

    let ?ysL = "take (?\<nu>+1) ys"
    let ?ysR = "drop (?\<nu>+1) ys"
    let ?ysR' = "drop ?\<nu> ys"
    have y_adm : "adm' (1 + ?\<nu>) ?ysR'" 
      by(rule adm'_drop, simp add: 2[simplified])
    have y0: "?ysR' = ?e # ?ysR" 
      by (simp add: Cons_nth_drop_Suc \<nu>_prop(1)) 
    have y1: "distinct ?ysL" 
      by (simp add: "2")
    have y2: "length ?ysL = ?\<nu> + 1" 
      by(subst length_take, subst min, simp)
    have y3: "set ?ysR = {ys!i |i. ?\<nu> < i \<and> i < length ys}" 
      by(subst set_drop, fastforce)
    have y4: "set ?ysL \<union> set ?ysR = set ys"
      by (metis append_take_drop_id set_append)
    have "set ?ysL \<inter> set ?ysR = {}"
      by (meson "2" dual_order.refl set_take_disj_set_drop_if_distinct)
    hence y5: "set ?ysL = set ys - set ?ysR"
      using Un_Diff y4 by fast
    have y6: "card(set ?ysL) = ?\<nu> + 1"
      using distinct_card y1 y2 by fastforce

    let ?xsL = "filter (\<lambda>x. \<forall>j<length ys. ?\<nu> < j \<longrightarrow> ys!j \<noteq> x) xs"
    let ?xsR = "filter (\<lambda>x. \<exists>j<length ys. ?\<nu> < j \<and> ys!j = x) xs"
    have x0 : "set xs = set(?xsL @ ?xsR)" 
      by fastforce
    have x1: "set ?xsL = set xs - set ?xsR" 
      by fastforce
    have eq1: "set ?xsR = set ?ysR"
      by (smt (verit, del_insts) \<nu>_prop(3) mem_Collect_eq set_filter subsetI subset_antisym y3)
    hence eq2: "set (?e # ?xsR) = set ?ysR'" 
      by (simp add: y0)
    have ineq: "length ?xsL \<le> ?\<nu>"
    proof-
      have "length ?xsL < length ?ysL" 
      proof-
        have less: "card(set ?xsL) < card(set ?ysL)"
          by (metis (no_types, lifting) List.finite_set c' card_less_diff eq1 filter_is_subset set_drop_subset x1 y5)
        show ?thesis
          by (metis (no_types, lifting) "1" distinct_card distinct_filter less y2 y6) 
      qed
      with y2 show ?thesis by fastforce
    qed

    show "\<exists>e. e \<in> set ys' \<and> e \<notin> set xs' \<and> 
             (\<exists>xs''. insert e (set xs') = set xs'' \<and> distinct xs'' \<and> xs'' \<in> \<L>_job)"
    proof(rule_tac x="?e" in exI, intro conjI)
      show "?e \<in> set ys'" 
        by(simp add: 1, simp add: e_prop[simplified 1, simplified 2])
    next
      show "?e \<notin> set xs'" 
        by(simp add: 1, simp add: \<nu>_prop[simplified 1, simplified 2])
    next
      have ext_dist: "distinct (?xsL @ ?e # ?xsR)" 
      proof-
        have "distinct (?e # (?xsL @ ?xsR))"
          by(subst distinct.simps, subst x0[THEN sym], rule conjI, rule \<nu>_prop(2), fastforce simp: 1)
        thus ?thesis by simp
      qed

     show "\<exists>xs''. insert ?e (set xs') = set xs'' \<and> distinct xs'' \<and> xs'' \<in> \<L>_job"
     proof(rule_tac x="?xsL @ ?e # ?xsR" in exI, intro conjI)
       have "set xs' = set(?xsL @ ?xsR)" using "1" x0 by blast 
       thus "insert ?e (set xs') = set(?xsL @ ?e # ?xsR)" by simp
     next 
       show "?xsL @ ?e # ?xsR \<in> \<L>_job"
       proof(rule adm'_\<L>_job[OF _ ext_dist], rule adm'_comp)
         show "adm' 1 ?xsL"
           by(rule_tac xs'=xs in adm'_subset', rule Sorted_filter, simp add: 1, fastforce, 
               (simp add: 1[simplified])+)
       next
         show "adm' (1 + length ?xsL) (?e # ?xsR)"
         proof(rule adm'_subset[rotated 3], rule y_adm, simp add: ineq)
           show "set(?e # ?xsR) \<subseteq> set ?ysR'" by(subst eq2, rule subset_refl)
         next
           show "distinct (?e # ?xsR)" using distinct_append ext_dist by blast
         next
           show "Sorted date (?e # ?xsR)"
             by(simp, rule conjI, rule Sorted_filter, (clarsimp simp: 1)+, rule Sorted_nth, (simp add: 2)+)
         qed
       qed
     qed(rule ext_dist)
   qed
 qed
qed
qed



interpretation scheduling : greedy_tactic \<L>_job w_job
  apply unfold_locales
   apply(simp add: \<L>_job_def adm_def)
   apply(erule adm')
     apply(rule ins_sorted)
    apply simp
   apply(erule dist_ins_fold)
  by(rule job_Independent)

thm scheduling.greedy_tr_max_basis

theorem opt_scheduling :
 "distinct xs \<Longrightarrow> Sorted (neg w_job) xs \<Longrightarrow> 
  finite_matroids.max_weight_basis scheduling.\<L>_img w_job (set xs) (set(scheduling.greedy_tr adm ins xs []))"
  apply(erule scheduling.greedy_tr_max_basis, assumption)
  apply simp
  apply(simp add: adm_def \<L>_job_def)
  done

lemma fm[simp]: "finite_matroids scheduling.\<L>_img" by(unfold_locales, rule job_Independent)


section "The example"

definition "j\<^sub>1 = \<lparr> val = 50, date = 2 \<rparr>"
definition "j\<^sub>2 = \<lparr> val = 10, date = 1 \<rparr>"
definition "j\<^sub>3 = \<lparr> val = 15, date = 2 \<rparr>"
definition "j\<^sub>4 = \<lparr> val = 30, date = 1 \<rparr>"

lemma example_eval : 
"scheduling.greedy_tr adm ins [j\<^sub>1, j\<^sub>4, j\<^sub>3, j\<^sub>2] [] = [j\<^sub>4, j\<^sub>1]"
  by(simp add: adm_def j\<^sub>1_def j\<^sub>2_def j\<^sub>3_def j\<^sub>4_def)

lemma example_conclusion :
"finite_matroids.max_weight_basis scheduling.\<L>_img w_job {j\<^sub>1, j\<^sub>4, j\<^sub>3, j\<^sub>2} {j\<^sub>4, j\<^sub>1}"
  apply(subgoal_tac "distinct [j\<^sub>1, j\<^sub>4, j\<^sub>3, j\<^sub>2]")
   apply(drule opt_scheduling)
    apply(simp add: j\<^sub>1_def j\<^sub>2_def j\<^sub>3_def j\<^sub>4_def neg_def w_job_def)
   apply(subst (asm) example_eval)
  apply simp
  apply(simp add: j\<^sub>1_def j\<^sub>2_def j\<^sub>3_def j\<^sub>4_def)
  done



text "Interpreted in this particular setting:"
lemma
"distinct xs \<Longrightarrow> set xs \<subseteq> {j\<^sub>1, j\<^sub>4, j\<^sub>3, j\<^sub>2} \<Longrightarrow> xs \<in> \<L>_job \<Longrightarrow>
 length xs \<le> 2 \<and> weight w_job (set xs) \<le> 80"
  apply(insert example_conclusion)
  apply(clarsimp simp: finite_matroids.max_weight_basis_def)
  apply(rule conjI)
   apply (metis One_nat_def Suc_1 card.empty card.insert distinct_card finite_insert finite_matroids.basis_def fm insert_absorb le_SucI scheduling.\<L>_img_eq)
  apply(subgoal_tac "set xs \<in> scheduling.\<L>_img")
   apply(drule finite_matroids.basis_ext[OF fm], assumption, simp)
   apply clarify
   apply(drule_tac x=A' in spec, simp)
   apply(rule order_trans, erule_tac T=A' in weight_mono)
     apply(drule finite_matroids.basisD2[OF fm])+
     apply(erule finite_subset, simp)
    apply(simp add: w_job_def)
   apply(erule order_trans)
   apply(simp (no_asm) add: weight_def w_job_def j\<^sub>1_def j\<^sub>4_def)
  apply(subst scheduling.\<L>_img_def, fast)
  done


end






