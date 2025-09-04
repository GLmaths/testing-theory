(*
   Copyright (c) 2024 Gaëtan Lopez <glopez@irif.fr>

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
*)

From Coq Require ssreflect Setoid.
From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
Import ListNotations.
From Coq.Program Require Import Wf Equality.
From Coq.Wellfounded Require Import Inverse_Image.
From Coq.Logic Require Import JMeq ProofIrrelevance.

From stdpp Require Import base countable list decidable finite gmap gmultiset.
From Must Require Import gLts InputOutputActions OldTransitionSystems Subset_Act
  FiniteImageLTS Bisimulation Lts_OBA Lts_OBA_FB Lts_FW InteractionBetweenLts
  MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction.
(* From Must Require Import VCCS_Instance VACCS_Instance. *)
(* Genarilization via essential actions, non_blocking actions *)
From Must Require Import ActTau.

Definition all_blocking_action `{Label A} (μ : ExtAct A) := False.

#[global] Program Instance all_blocking_action_dec `{Label A} μ :
    Decision (all_blocking_action μ).
Next Obligation.
  intros. right. intro imp. inversion imp.
Defined.

Definition non_blocking_output `{Label A} (μ : ExtAct A) := (is_output μ).

#[global] Program Instance non_blocking_output_dec `{Label A} μ :
    Decision (non_blocking_output μ).
Next Obligation.
  intros. destruct μ as [a | a].
  + right. intro imp. inversion imp; eauto. inversion H0.
  + left. exists a. eauto.
Defined.

(* ExtAction for output are non_blocking *)

#[global] Program Instance gLabel_nb
  `{Label A} : ExtAction (ExtAct A) :=
   {| non_blocking η := non_blocking_output η ;
      dual μ1 μ2 := ext_act_match μ1 μ2 ;
      gLts.co ɣ := InputOutputActions.co ɣ |}.
Next Obligation.
 intros. simpl. destruct a.
 * right. intro Hyp. destruct Hyp as (a' & eq). inversion eq.
 * left. exists a. eauto.
Defined.
Next Obligation.
 intros ? ? ? ? nb dual; simpl in *.
 destruct nb as (a & eq). subst. eapply simplify_match_output in dual.
 subst. intro imp. inversion imp. inversion H0.
Defined.
Next Obligation.
 intros A H η ɣ nb dual; simpl in *.
 destruct nb as (a & eq); subst; simpl in *.
 destruct ɣ as [ (* Input *) a' | (* Output *) a' ].
 + subst; eauto.
 + inversion dual.
Defined.
Next Obligation. 
  intros. exists (co η). unfold ext_act_match.
  destruct η; simpl in *; eauto. 
Defined.
Next Obligation.
  intros A ? ? ? ? (a & eq) Hyp Hyp'; subst.
  exists a. eapply simplify_match_output in Hyp; subst.
  symmetry in Hyp'. eapply simplify_match_input in Hyp'; eauto.
Defined.


#[global] Program Instance gLabel_b
  `{Label A} :
        gLts.ExtAction (ExtAct A) :=
   {| non_blocking η := all_blocking_action η ;
      dual μ1 μ2 := ext_act_match μ1 μ2 ;
      gLts.co ɣ := InputOutputActions.co ɣ |}.
Next Obligation.
  intros ? ? ? ? nb ; simpl in *. inversion nb.
Defined.
Next Obligation.
 intros ? ? ? ? nb dual; simpl in *. inversion nb.
Defined.
Next Obligation. 
  intros. exists (co η). unfold ext_act_match.
  destruct η; simpl in *; eauto. 
Defined.
Next Obligation. 
  intros ? ? ? ? ? nb; simpl in *. inversion nb.
Defined.

#[global] Program Instance ggLts {A : Type}
  (H : ExtAction (ExtAct A)) `{LtsP: Lts P A} : @gLts P (ExtAct A) H :=
  {| gLts.lts_step p1 α p2 := p1 ⇾{ α } p2 ;
     lts_refuses p α := lts_stable p α |}.
Next Obligation.
  destruct α as [ μ |].
  + intro not_stable. exact (lts_stable_spec1 p (ActExt μ) not_stable).
  + intro not_stable. exact (lts_stable_spec1 p τ not_stable).
Qed.
Next Obligation.
  destruct α as [ μ |].
  + intro wit_not_stable. exact (lts_stable_spec2 p (ActExt μ) wit_not_stable).
  + intro wit_not_stable. exact (lts_stable_spec2 p τ wit_not_stable).
Qed.


#[global] Program Instance ggFiniteLts {A : Type}
  (H : ExtAction (ExtAct A)) `{FiniteLts P A} : @FiniteImagegLts P (ExtAct A) H (ggLts H).

#[global] Program Instance ggLtsEq {A : Type}
  (H : ExtAction (ExtAct A)) `{LtsEq P A} : @gLtsEq P (ExtAct A) H (ggLts H).
Next Obligation.
  intros ? ? ? ? LtsP LtsEqP p q α Hyp.
  destruct α as [ μ |].
  + exact (OldTransitionSystems.eq_spec p q (ActExt μ) Hyp).
  + exact (OldTransitionSystems.eq_spec p q τ Hyp).
Qed.

Definition label_to_output {A} (a : A) : ExtAct A := ActOut a.

Definition mo_label_to_mo_output `{Countable A} (m : gmultiset A) : gmultiset (ExtAct A) :=
    gmultiset_map label_to_output m.

(* Definition set_label_to_mo_output `{Countable A}
    (m : gset A) : gset (ExtAct A) :=
    list_to_set (fmap label_to_output (elements m)).
 *)
(* #[global] Instance output_in_gmultiset_dec `{Prop_of_Inter S1 S2 A} 
  η x p1 :
  Decision (η = label_to_output x ∧ x ∈ lts_oba_mo p1). *)


#[global] Program Instance ggLtsOba_nb
  `{LtsOba P A} : @gLtsOba P (ExtAct A) gLabel_nb (ggLts gLabel_nb) (ggLtsEq gLabel_nb) :=
  {| lts_oba_mo p := mo_label_to_mo_output (OldTransitionSystems.lts_oba_mo p) |}.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? nb l.
  destruct η as [a | a].
  + exfalso. inversion nb. inversion H2.
  + eapply elem_of_gmultiset_map.
    exists a. split.
      ++ unfold label_to_output. eauto.
      ++ eapply lts_oba_mo_spec1.
         eapply lts_outputs_spec1.
         exact l.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? Hyp. 
  eapply elem_of_gmultiset_map in Hyp.
  
  assert ({ x : A | η = label_to_output x ∧ x ∈ OldTransitionSystems.lts_oba_mo p1}) as (a & eq & mem).
  eapply choice; eauto. intros.
  destruct (decide (η = label_to_output x)) as [eq | not_eq].
  + destruct (decide (x ∈ OldTransitionSystems.lts_oba_mo p1)).
    ++ left. split; eauto.
    ++ right. intro Hyp'. destruct Hyp' as (eq' & imp). contradiction.
  + right. intro Hyp'. destruct Hyp' as (eq' & imp). contradiction.
  + eapply lts_oba_mo_spec1 in mem.
    eapply lts_outputs_spec2 in mem as (q & l).
    exists q. split.
    ++ exists a. subst. eauto.
    ++ rewrite eq. unfold label_to_output. exact l.
Qed.
Next Obligation.
  unfold ggLtsOba_nb_obligation_1.
  intros ? ? ? ? ? LtsOBAP ? ? ? nb Hyp;simpl in *.
  destruct nb as (a & eq). subst.
  assert (OldTransitionSystems.lts_oba_mo p = {[+ a +]} ⊎ OldTransitionSystems.lts_oba_mo q) as mem.
  eapply OldTransitionSystems.lts_oba_mo_spec2. exact Hyp.
  rewrite mem. simpl in *. unfold mo_label_to_mo_output at 1.
  rewrite gmultiset_map_disj_union. rewrite gmultiset_map_singleton.
  unfold label_to_output at 1. reflexivity.
Qed.
Next Obligation. (* lts_oba_non_blocking_action_delay *)
  intros ? ? ? ? ? LtsOBAP ? ? ? ? ? nb l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst. 
  destruct α as [|].
  + destruct μ as [a' | a'].
    ++ eapply lts_oba_output_commutativity; eauto.
    ++ eapply lts_oba_output_commutativity; eauto.
  + eapply lts_oba_output_commutativity; eauto. 
Qed.
Next Obligation. (* lts_oba_non_blocking_action_confluence *)
  intros ? ? ? ? ? LtsOBAP ? ? ? ? ? nb eq l1 l2 ;simpl in *.
  destruct nb as (a & eq'); subst.
  eapply lts_oba_output_confluence; eauto.
Qed.
Next Obligation. (* lts_oba_output_tau *)
  intros ? ? ? ? ? LtsOBAP ? ? ? ? nb l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst.
  unfold gLabel_nb_obligation_4.
  eapply lts_oba_output_tau in l1 as cases; eauto.
  destruct cases as [computation_without_a | computation_with_a].
  + left. destruct computation_without_a. 
    eexists; eauto.
  + right. exists (ActIn a). split; eauto.
    unfold sc. simpl. eauto.
Qed.
Next Obligation. (* lts_oba_output_deter *)
  intros ? ? ? ? ? LtsOBAP ? ? ? ? nb l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst. 
  eapply lts_oba_output_deter; eauto.
Qed.
Next Obligation. (* lts_oba_non_blocking_action_deter_inv *)
  intros ? ? ? ? ? LtsOBAP ? ? ? ? ? nb l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst.
  eapply lts_oba_output_deter_inv; eauto.
Qed.

#[global] Program Instance ggLtsObaFB_nb
  `{LtsObaFB P A} : @gLtsObaFB P (ExtAct A) gLabel_nb 
  (ggLts gLabel_nb) (ggLtsEq gLabel_nb) ggLtsOba_nb.
Next Obligation.
  intros ? ? ? ? ? LtsOBAP ? ? ? ? ? ? nb dual l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst.
  eapply simplify_match_output in dual; subst.
  eapply OldTransitionSystems.lts_oba_fb_feedback; eauto.
Qed.

#[global] Program Instance ggLtsObaFW_nb
  `{LtsObaFW P A} : @gLtsObaFW P (ExtAct A) gLabel_nb 
  (ggLts gLabel_nb) (ggLtsEq gLabel_nb) ggLtsOba_nb.
Next Obligation.
  intros ? ? ? ? ? ? ? p η μ ;simpl in *.
  destruct (decide (non_blocking_output η)) as [nb | not_nb].
  + destruct nb as (a & eq); subst.
    destruct (OldTransitionSystems.lts_oba_fw_forward p a) as (p' & l1 & l2).
    exists p'. intros Hyp duo. eapply simplify_match_output in duo; subst. split;eauto.
  + exists p. intro. contradiction.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? p p' p'' η μ nb dual l1 l2;simpl in *.
  destruct nb as (a & eq); subst.
  eapply simplify_match_output in dual; subst.
  eapply OldTransitionSystems.lts_oba_fw_feedback in l1; eauto.
Qed.


#[global] Program Instance ggLtsOba_b
  `{LtsEqP : @LtsEq P A H LtsP} :
    @gLtsOba P (ExtAct A) (@gLabel_b A H) 
    (@ggLts A gLabel_b P H LtsP) (@ggLtsEq A gLabel_b P H LtsP LtsEqP) := 
    {| lts_oba_mo p := empty |}.
Next Obligation.
  intros. unfold non_blocking in H0. inversion H0.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? mem. simpl in *. exists p1. inversion mem.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? imp. inversion imp.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? Hyp. inversion Hyp.
Qed.
Next Obligation. (* lts_oba_non_blocking_action_delay *)
  intros ? ? ? ? ? LtsOBAP ? ? ? ? mem. inversion mem.
Qed.
Next Obligation. (* lts_oba_non_blocking_action_confluence *)
  intros ? ? ? ? ? LtsOBAP ? ? ? mem. inversion mem.
Qed.
Next Obligation. (* lts_oba_output_tau *)
  intros ? ? ? ? ? LtsOBAP ? ? ? imp. inversion imp.
Qed.
Next Obligation. (* lts_oba_output_deter *)
  intros ? ? ? ? ? LtsOBAP ? ? ? ? imp. inversion imp.
Qed.

#[global] Program Instance ggLtsObaFB_b
  `{LtsEqP : @LtsEq P A H LtsP} : @gLtsObaFB P (ExtAct A) gLabel_b 
  (ggLts gLabel_b) (ggLtsEq gLabel_b) ggLtsOba_b.
Next Obligation.
  intros ? ? ? ? ? LtsOBAP ? ? ? ? imp. inversion imp.
Qed.

#[global] Program Instance ggLtsObaFW_b
  `{LtsEqP : @LtsEq P A H LtsP} : @gLtsObaFW P (ExtAct A) gLabel_b 
  (ggLts gLabel_b) (ggLtsEq gLabel_b) ggLtsOba_b.
Next Obligation.
  intros ? ? ? ? ? ? ? ?. exists p1. intro imp. inversion imp.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? imp. inversion imp.
Qed.

#[global] Program Instance Inter_FW_IO {A : Type} (H : ExtAction (ExtAct A))
  `{LtsP : @Lts P A L} {ext_m : forall μ1 μ2, dual μ1 μ2 -> ext_act_match μ1 μ2}: 
    @Prop_of_Inter P (mb (ExtAct A)) (ExtAct A) fw_inter H (@ggLts A H P L LtsP) _ :=
    {| lts_essential_actions_left p := empty ;
       lts_essential_actions_right m := dom (mb_without_not_nb m) ; 
       lts_co_inter_action_right m := fun x => empty |}.
Next Obligation. 
  intros ? ? ? ? ? ? ? ? Hyp ;simpl in *.
  inversion Hyp.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? m ? Hyp ;simpl in *.
  eapply gmultiset_elem_of_dom in Hyp. 
  assert (ξ ∈ mb_without_not_nb m) as mem. eauto.
  eapply lts_mb_nb_with_nb_spec1 in mem as (nb & eq).
  eapply gmultiset_disj_union_difference' in eq.
  exists (m ∖ {[+ ξ +]}). rewrite eq at 1.
  eapply lts_multiset_minus; eauto.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? m ? m' ? ? inter;simpl in *.
  right. destruct inter as (duo & nb).
  eapply gmultiset_elem_of_dom.
  eapply non_blocking_action_in_ms in nb as eq'; eauto. 
  rewrite<- eq'.
  assert (mb_without_not_nb ({[+ μ2 +]} ⊎ m') 
  = {[+ μ2 +]} ⊎ (mb_without_not_nb m')) as eq.
  eapply lts_mb_nb_spec1; eauto. rewrite eq.
  multiset_solver.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ξ p;simpl in *.
  destruct (decide (non_blocking ξ)) as [ nb (* Input_case *) | not_nb (* Ouput_case *)].
  + exact {[ co ξ ]}.
  + exact empty.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? m mem l inter;simpl in *.
  unfold Inter_FW_IO_obligation_4.
  destruct inter as (duo & nb). rewrite decide_True; eauto.
  assert (μ = co ξ).
  { eapply ext_m in duo.
    destruct ξ as [a | a].
    + eapply simplify_match_input in duo; subst; eauto.
    + eapply simplify_match_output in duo; subst; eauto. }
  subst; set_solver.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? m mem l inter;simpl in *.
  inversion mem.
Qed.

#[global] Program Instance Inter_parallel_IO {A : Type} (H : ExtAction (ExtAct A))
  `{LtsP : @Lts P A L} `{LtsQ : @Lts Q A L} 
    {ext_m : forall μ1 μ2, parallel_inter μ2 μ1 -> ext_act_match μ1 μ2}: 
    @Prop_of_Inter P Q (ExtAct A) parallel_inter H (@ggLts A H P L LtsP) (@ggLts A H Q L LtsQ) :=
    {| lts_essential_actions_left p := set_map ActOut (lts_outputs p) ;
       lts_essential_actions_right q := set_map ActOut (lts_outputs q)|}.
Next Obligation.
  intros ? ? ? ? ? ? ? ? p ? Hyp ;simpl in *.
  unfold set_map in Hyp. simpl in *.
  eapply elem_of_list_to_set in Hyp.
  eapply elem_of_list_fmap in Hyp.
  destruct ξ.
  + exfalso. destruct Hyp as (a' & eq & mem). inversion eq.
  + eapply lts_outputs_spec2. destruct Hyp as (a' & eq & mem).
    inversion eq. subst. eapply elem_of_elements. eauto.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? q ? Hyp ;simpl in *.
  unfold set_map in Hyp. simpl in *.
  eapply elem_of_list_to_set in Hyp.
  eapply elem_of_list_fmap in Hyp.
  destruct ξ.
  + exfalso. destruct Hyp as (a' & eq & mem). inversion eq.
  + eapply lts_outputs_spec2. destruct Hyp as (a' & eq & mem).
    inversion eq. subst. eapply elem_of_elements. eauto.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? ? q ? q' ? ? inter;simpl in *.
  destruct μ1 as [ (*Input*) a | (*Output*) a].
  + right. symmetry in inter. eapply ext_m in inter. eapply simplify_match_input in inter. subst.
    eapply elem_of_list_to_set.
    eapply elem_of_list_fmap. exists a. split; eauto. 
    eapply elem_of_elements. eapply lts_outputs_spec1; eauto.
  + left. symmetry in inter. eapply ext_m in inter. eapply simplify_match_output in inter. subst.
    eapply elem_of_list_to_set.
    eapply elem_of_list_fmap. exists a. split; eauto. 
    eapply elem_of_elements. eapply lts_outputs_spec1; eauto.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ξ p;simpl in *.
  destruct ξ as [ (*Input*) a | (*Output*) a ].
  + exact empty. 
  + exact {[ ActIn a ]}.
Defined.
Next Obligation.
  unfold Inter_parallel_IO_obligation_4.
  intros ? ? ? ? ? ? ? ? ? ? ? ? q mem l inter;simpl in *. 
  eapply elem_of_list_to_set in mem.
  eapply elem_of_list_fmap in mem.
  destruct mem as ( a & eq & mem ); subst.
  eapply ext_m in inter. eapply simplify_match_output in inter. subst. set_solver.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ξ q;simpl in *.
  destruct ξ as [ (*Input*) a | (*Output*) a ].
  + exact empty. 
  + exact {[ ActIn a ]}.
Defined.
Next Obligation.
  unfold Inter_parallel_IO_obligation_6.
  intros ? ? ? ? ? ? ? ? ? ? ? ? q mem l inter;simpl in *. 
  eapply elem_of_list_to_set in mem.
  eapply elem_of_list_fmap in mem.
  destruct mem as ( a & eq & mem ); subst. symmetry in inter.
  eapply ext_m in inter. eapply simplify_match_output in inter. subst. set_solver.
Defined.


#[global] Program Instance Inter_FW_parallel_IO {A : Type} (H : ExtAction (ExtAct A))
  `{LtsP : @Lts P A L} `{LtsE : @Lts E A L}
    {ext_m : forall μ1 μ2, parallel_inter μ2 μ1 -> ext_act_match μ1 μ2}
    : @Prop_of_Inter (P * mb (ExtAct A)) E (ExtAct A) parallel_inter
      H (@FW_gLts P (ExtAct A) H (@ggLts A H P L LtsP) (@Inter_FW_IO A H P L LtsP ext_m)) (@ggLts A H E L LtsE):=
    {| lts_essential_actions_left p := set_map ActOut (lts_outputs p.1) ∪ (dom (mb_without_not_nb p.2)); 
    (* (@Inter_FW_IO A H P L LtsP ext_m).(lts_essential_actions_left) p.1
          ∪ (@Inter_FW_IO A H P L LtsP ext_m).(lts_essential_actions_right) p.2; *)
       lts_essential_actions_right q := set_map ActOut (lts_outputs q)|}.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (p , m) ? ?. simpl in *.
  eapply elem_of_union in H0. destruct (decide (ξ ∈ dom (mb_without_not_nb m))).
  + eapply gmultiset_elem_of_dom in e.
    eapply lts_mb_nb_with_nb_spec1 in e as (nb & mem).
    assert ({ m'| m = {[+ ξ +]} ⊎ m'}) as (m' & eq).
    { exists (m ∖ {[+ ξ +]}). multiset_solver. }
    subst. exists (p , m'). eapply ParRight. eapply lts_multiset_minus; eauto.
  + assert ((ξ ∈ @set_map A (@gset A (@label_eqdec A L) (@label_countable A L))
      (@gset_elements A (@label_eqdec A L) (@label_countable A L)) (ExtAct A)
      (@gset (ExtAct A) (@eqdec (ExtAct A) H) (@countable (ExtAct A) H))
      (@gset_singleton (ExtAct A) (@eqdec (ExtAct A) H) (@countable (ExtAct A) H))
      (@gset_empty (ExtAct A) (@eqdec (ExtAct A) H) (@countable (ExtAct A) H))
      (@gset_union (ExtAct A) (@eqdec (ExtAct A) H) (@countable (ExtAct A) H)) 
      (@ActOut A) (@lts_outputs P A L LtsP p))) as Hyp.
    { destruct H0. exact H0.  contradiction. }
    unfold set_map in Hyp. simpl in *.
    eapply elem_of_list_to_set in Hyp.
    eapply elem_of_list_fmap in Hyp.
    destruct ξ.
    ++ exfalso. destruct Hyp as (a' & eq & mem). inversion eq.
    ++ assert (a ∈ elements (lts_outputs p)) as mem.
       { destruct Hyp as (y & Hyp'); destruct Hyp' as (eq' & mem). 
         inversion eq'; subst. eauto. }
       apply elem_of_elements in mem. eapply lts_outputs_spec2 in mem.
       destruct mem as (p' & l). exists (p' , m). eapply ParLeft. eauto.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? e ? Hyp ;simpl in *.
  unfold set_map in Hyp. simpl in *.
  eapply elem_of_list_to_set in Hyp.
  eapply elem_of_list_fmap in Hyp.
  destruct ξ as [ (*Input*) a | (*Output*) a].
  + exfalso. decompose record Hyp. inversion H1.
  + assert (a ∈ elements (lts_outputs e)) as mem.
    { destruct Hyp as (y & Hyp'); destruct Hyp' as (eq' & mem). 
      inversion eq'; subst. eauto. }
    apply elem_of_elements in mem. eapply lts_outputs_spec2 in mem. eauto.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? (p1 , m1) ? (p'1, m'1) ? ? ? Tr ? inter;simpl in *.
  eapply ext_m in inter. destruct μ2 as [ (*Input*) a | (*Output*) a].
  - eapply simplify_match_input in inter. subst. left.
    inversion Tr; subst.
    + eapply elem_of_union. left. eapply elem_of_list_to_set.
      eapply elem_of_list_fmap. exists a. split; eauto.
      eapply elem_of_elements. eapply lts_outputs_spec1. eauto.
    + eapply elem_of_union. right. eapply gmultiset_elem_of_dom.
      destruct (decide (non_blocking (ActOut a))) as [nb | b].
      * eapply lts_mb_nb_with_nb_spec2; eauto.
        eapply non_blocking_action_in_ms in l; eauto. set_solver.
      * eapply blocking_action_in_ms in l as (eq & duo & nb);eauto.
        eapply ext_m in duo. symmetry in duo. eapply simplify_match_output in duo. subst.
        rewrite duo in Tr, nb. admit.
  - eapply simplify_match_output in inter. subst. right.
    eapply elem_of_list_to_set.
    eapply elem_of_list_fmap. exists a. split; eauto.
    eapply elem_of_elements. eapply lts_outputs_spec1. eauto.
Admitted.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ξ p ;simpl in *. destruct ξ as [ (*Input*) a | (*Output*) a].
  + exact empty. 
  + exact {[ ActIn a ]}.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? p q ? μ ? mem ? inter;simpl in *.
  unfold Inter_FW_parallel_IO_obligation_4. destruct ξ as [ (*Input*) a | (*Output*) a].
  - eapply elem_of_list_to_set in mem.
    eapply elem_of_list_fmap in mem. destruct mem as (? & eq & ?).
    inversion eq.
  - eapply ext_m in inter. eapply simplify_match_output in inter. subst. set_solver.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ξ e;simpl in *.
  destruct ξ as [ a (* Input_case *) | a (* Ouput_case *)].
  + exact {[ ActOut a ]}.
  + exact {[ ActIn a ]}.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? p q ? μ (p1 , m1) mem ? inter;simpl in *.
  unfold Inter_FW_parallel_IO_obligation_6. symmetry in inter.
  destruct ξ as [ (*Input*) a | (*Output*) a].
  - eapply ext_m in inter. eapply simplify_match_input in inter. subst.
    eapply elem_of_union in mem. destruct mem as [case1 | case2].
    + set_solver.
    + set_solver.
  - eapply ext_m in inter. eapply simplify_match_output in inter. subst. set_solver.
Defined.

Lemma com_only_with_output `{A : Type} (η : ExtAct A) η': 
        ext_act_match η η' -> is_output η \/ is_output η'.
Proof.
  intro duo. destruct η as [ a (* input *) | a (* input *) ].
  + eapply simplify_match_input in duo as eq; subst.
    right. exists a. eauto.
  + eapply simplify_match_output in duo as eq; subst.
    left. exists a. eauto.
Qed.

Lemma fw_does_all_input
  `{@gLtsObaFW Q (ExtAct A) (@gLabel_nb A L) LtsQ LtsEqQ LtsObaQ} :
   forall (q' : Q) μ, ¬ is_output μ -> μ ∈ lts_acc_set_of q'.
Proof.
  intros q' μ not_nb. destruct μ as [ (* Input *) a | (* Output *) a].
  + assert (non_blocking_output (ActOut a)) as nb.
    { exists a. eauto. }
    assert (non_blocking_output (ActOut a)) as nb'; eauto.
    destruct nb as (a' & eq); subst.
    inversion eq. subst.
    assert (dual (ActIn a') (ActOut a')) as duo.
    { simpl. reflexivity. }
    destruct (lts_oba_fw_forward q' (ActOut a') (ActIn a')) as (p' & Hyp).
    simpl in *. unfold gLabel_nb_obligation_1 in Hyp.
    eapply Hyp in nb';eauto. simpl in *.
    eapply lts_refuses_spec2. exists p'.
    destruct nb'. eauto.
  + exfalso. assert (non_blocking_output (ActOut a)).
    exists a; eauto. contradiction.
Qed.

Lemma retrieve_a_better_pre_order
  `{@Lts P A L} `{@Lts Q A L} (p : P) (q : Q) :
   (forall (q' : Q) μ, ¬ is_output μ -> μ ∈ lts_acc_set_of q') -> 
    (lts_acc_set_of p ⊆ lts_acc_set_of q
      <-> lts_outputs p ⊆ lts_outputs q).
Proof.
  intro fw_b_action.
  split.
  + intro inclusion. intro a. intro mem. eapply lts_outputs_spec2 in mem as (p2 & l).
    assert ((ActOut a) ∈ lts_acc_set_of p) as mem.
    eapply lts_refuses_spec2. simpl. eauto.
    eapply inclusion in mem. eapply lts_refuses_spec1 in mem as (q' & l').
    simpl in *. eapply lts_outputs_spec1 in l'. eauto.
  + intro inclusion.
    intros μ mem. destruct μ as [ (* Input *) a | (* Output *) a].
    ++ eapply fw_b_action. intro imp. inversion imp. inversion H1.
    ++ eapply lts_stable_spec2. eapply lts_stable_spec1 in mem as (q' & Tr).
       eapply lts_outputs_spec1 in Tr. eapply inclusion in Tr. eapply lts_outputs_spec2 in Tr; eauto.
Qed.

Lemma retrieve_a_better_pre_order_final
  `{@gLtsObaFW P (ExtAct A) (@gLabel_nb A L) LtsP LtsEqP LtsObaP}
  `{@gLtsObaFW Q (ExtAct A) (@gLabel_nb A L) LtsQ LtsEqQ LtsObaQ}
    (p : P) (q : Q):
    lts_acc_set_of p ⊆ lts_acc_set_of q
      <-> dom (lts_oba_mo p) ⊆ dom (lts_oba_mo q).
Proof.
  split.
  + intros inclusion μ mem. eapply gmultiset_elem_of_dom in mem.
    eapply lts_oba_mo_spec_bis2 in mem as (p' & nb & Tr).
    assert (μ ∈ lts_acc_set_of p) as mem. { eapply lts_refuses_spec2; eauto. }
    eapply inclusion in mem. eapply lts_refuses_spec1 in mem as (q' & Tr').
    eapply gmultiset_elem_of_dom. eapply lts_oba_mo_spec_bis1; eauto.
  + intros inclusion μ mem.
    destruct μ as [ (* Input *) a | (* Output *) a].
    ++ eapply fw_does_all_input. intro imp. inversion imp. inversion H1.
    ++ eapply lts_refuses_spec2. eapply lts_refuses_spec1 in mem as (q' & Tr).
       eapply lts_oba_mo_spec_bis1 in Tr;eauto. assert (ActOut a ∈ lts_oba_mo q) as mem'.
       { multiset_solver. }
       eapply lts_oba_mo_spec_bis2 in mem' as (q'' & nb & Tr''). eauto.
       unfold non_blocking. simpl. exists a; eauto.
Qed.

















