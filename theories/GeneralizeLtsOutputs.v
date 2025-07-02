(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>

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

Require ssreflect.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Wf Setoid.
Require Import Coq.Program.Equality.
From Coq.Logic Require Import ProofIrrelevance.

From stdpp Require Import base countable list decidable finite gmap gmultiset.
From Must Require Import TransitionSystems OldTransitionSystems.

(* Genarilization via essential actions, non_blocking actions *)

#[global] Instance ext_act_match_sym `{Label A} : Symmetric (@ext_act_match A).
Proof. 
  unfold ext_act_match.
  intros μ1 μ2 Hyp.
  destruct μ1; destruct μ2; eauto.
Qed.

Lemma simplify_match_output `{Label A} a μ : @ext_act_match A (ActOut a) μ <-> μ = ActIn a.
Proof.
  split.
  + intros eq.
    unfold ext_act_match in eq.
    destruct μ; subst; eauto; try contradiction.
  + intro. subst. simpl. eauto.
Qed.

Lemma simplify_match_input `{Label A} a μ : @ext_act_match A (ActIn a) μ <-> μ = ActOut a.
Proof.
  split.
  + intros eq.
    unfold ext_act_match in eq.
    destruct μ; subst; eauto; try contradiction.
  + intro. subst. simpl. eauto.
Qed.

Definition encode_ext_act `{Label A} (μ : ExtAct A) : gen_tree (A + A) :=
match μ with
  | ActIn a => GenLeaf (inr a)
  | ActOut a => GenLeaf (inl a)
end.

Definition decode_ext_act `{Label A} (tree : gen_tree (A + A)) : option (ExtAct A) :=
match tree with
  | GenLeaf (inr a) => Some (ActIn a)
  | GenLeaf (inl a) => Some (ActOut a)
  | _ => None
end.

Lemma encode_decide_ext_act `{Label A} μ : decode_ext_act (encode_ext_act μ) = Some μ.
Proof. case μ. 
* intros. simpl. reflexivity.
* intros. simpl. reflexivity.
Qed.


#[global] Instance ext_act_countable `{Label A} : Countable (ExtAct A).
Proof.
  refine (inj_countable encode_ext_act decode_ext_act encode_decide_ext_act).
Qed.

#[global] Program Instance gLabel
  `{Label A} : TransitionSystems.ExtAction (ExtAct A).
Next Obligation.
  intros L H μ. exact (is_output μ).
Defined.
Next Obligation.
 intros. destruct a.
 + right. intro imp. destruct imp as (μ & eq). subst. inversion eq.
 + left. exists a. eauto.
Defined.
Next Obligation.
  intros A H μ1. exact (co μ1).
Defined.
Next Obligation.
  intros. unfold relation. exact ext_act_match.
Defined.
Next Obligation.
  intros. exists (co η). unfold sc. 
  unfold gLabel_obligation_4. unfold ext_act_match.
  destruct η; simpl in *; eauto. 
Defined.
Next Obligation.
  intros. unfold sc. unfold gLabel_obligation_4.
  destruct a; destruct b.
  + right. intro cases. eauto. destruct cases as [case_1 | case_2].
    ++ eapply simplify_match_input in case_1. inversion case_1.
    ++ eapply simplify_match_input in case_2. inversion case_2.
  + destruct (decide (a = a0)) as [eq1 | eq2].
    ++ subst. left. left. simpl. eauto.
    ++ subst. right. intro cases.
       destruct cases as [case_1 | case_2].
       +++ eapply simplify_match_input in case_1. inversion case_1. eauto.
       +++ eapply simplify_match_output in case_2. inversion case_2. eauto.
  + destruct (decide (a = a0)) as [eq1 | eq2].
    ++ subst. left. left. simpl. eauto.
    ++ subst. right. intro cases.
       destruct cases as [case_1 | case_2].
       +++ eapply simplify_match_output in case_1. inversion case_1. eauto.
       +++ eapply simplify_match_input in case_2. inversion case_2. eauto.
  + simpl in *. right. intro Hyp. destruct Hyp; eauto.
Defined.
Next Obligation.
  unfold gLabel_obligation_1.
  unfold gLabel_obligation_4.
  intros A H η μ IsOut eq.
  intro IsOut'. destruct IsOut' as (μ' & eq'); subst.
  unfold sc in eq.
  destruct eq as [eq_1 | eq_2].
  + symmetry in eq_1.
    eapply simplify_match_output in eq_1. subst.
    destruct IsOut as ( a & impossible).
    inversion impossible.
  + eapply simplify_match_output in eq_2. subst.
    destruct IsOut as ( a & impossible).
    inversion impossible.
Defined.
Next Obligation.
  unfold gLabel_obligation_1.
  unfold gLabel_obligation_4.
  unfold sc. unfold gLabel_obligation_3.
  intros A H η μ IsOut eq.
  destruct IsOut as (η' & eq'); subst.
  destruct eq as [eq_1 | eq_2].
  + eapply simplify_match_output in eq_1. subst. simpl. eauto.
  + symmetry in eq_2.
    eapply simplify_match_output in eq_2. subst. simpl. eauto.
Defined.
Next Obligation. 
  unfold sc. unfold gLabel_obligation_1.
  unfold gLabel_obligation_4.
  intros A ? ? ? ? (a & eq) Hyp Hyp'. subst.
  destruct Hyp as [case_1 | case_2]; destruct Hyp' as [case_1' | case_2']; exists a; eauto.
  + eapply simplify_match_output in case_1. subst.
    symmetry in case_1'. eapply simplify_match_input in case_1'. subst.
    eauto.
  + eapply simplify_match_output in case_1. subst.
    eapply simplify_match_input. eauto.
  + symmetry in case_2. eapply simplify_match_output in case_2. subst.
    symmetry in case_1'. eapply simplify_match_input in case_1'. subst.
    eauto.
  + symmetry in case_2.
    eapply simplify_match_output in case_2. subst.
    eapply simplify_match_input in case_2'. subst.
    eauto.
Defined.


#[global] Program Instance gLts
  `{LtsP: Lts P A} : gLts P (ExtAct A).
Next Obligation.
  intros ? ? ? ? p1 α p2.
  destruct α as [|].
  + exact (lts_step p1 (ActExt μ) p2).
  + exact (lts_step p1 τ p2).
Defined.
Next Obligation.
  intros ? ? ? ? p1 α p2. unfold gLts_obligation_1.
  destruct α as [ μ |].
  + exact (lts_step_decidable p1 (ActExt μ) p2).
  + exact (lts_step_decidable p1 τ p2).
Defined.
Next Obligation.
  intros ? ? ? LtsP p α. 
  destruct α as [ μ |].
  + exact (lts_stable p (ActExt μ)).
  + exact (lts_stable p τ).
Defined.
Next Obligation.
  unfold gLts_obligation_3.
  destruct α as [ μ |].
  + exact (lts_stable_decidable p (ActExt μ)).
  + exact (lts_stable_decidable p τ).
Defined.
Next Obligation.
  unfold gLts_obligation_3.
  destruct α as [ μ |].
  + intro not_stable. exact (lts_stable_spec1 p (ActExt μ) not_stable).
  + intro not_stable. exact (lts_stable_spec1 p τ not_stable).
Qed.
Next Obligation.
  unfold gLts_obligation_1.
  unfold gLts_obligation_3.
  destruct α as [ μ |].
  + intro wit_not_stable. exact (lts_stable_spec2 p (ActExt μ) wit_not_stable).
  + intro wit_not_stable. exact (lts_stable_spec2 p τ wit_not_stable).
Defined.


#[global] Program Instance gFiniteLts
  `{FiniteLts P A} : FiniteImagegLts P (ExtAct A).
Next Obligation.
  intros.
  destruct α as [ μ |].
  + exact (folts_next_states_finite p (ActExt μ)).
  + exact (folts_next_states_finite p τ).
Defined.

#[global] Program Instance gLtsEq
  `{LtsEq P A} : gLtsEq P (ExtAct A).
Next Obligation.
  intros ? ? ? LtsP LtsEqP p q α Hyp. 
  destruct α as [ μ |].
  + exact (eq_spec p q (ActExt μ) Hyp).
  + exact (eq_spec p q τ Hyp).
Defined.

Definition label_to_output `{Label A} (a : A) : ExtAct A := ActOut a.

Definition mo_label_to_mo_output `{Label A} (m : gmultiset A) : gmultiset (ExtAct A) :=
    gmultiset_map label_to_output m.

Definition set_label_to_mo_output `{Label A} (m : gset A) : gset (ExtAct A) :=
    list_to_set (fmap label_to_output (elements m)).

(* #[global] Instance output_in_gmultiset_dec `{Prop_of_Inter S1 S2 A} 
  η x p1 :
  Decision (η = label_to_output x ∧ x ∈ lts_oba_mo p1). *)


#[global] Program Instance gLtsOba
  `{LtsOba P A} : gLtsOba P (ExtAct A).
Next Obligation.
  intros.
  exact (mo_label_to_mo_output (lts_oba_mo p)).
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? nb l. unfold gLtsOba_obligation_1.
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
  unfold gLtsOba_obligation_1.
  intros ? ? ? ? ? ? ? ? Hyp. 
  eapply elem_of_gmultiset_map in Hyp.
  
  assert ({ x : A | η = label_to_output x ∧ x ∈ lts_oba_mo p1}) as (a & eq & mem).
  eapply choice; eauto. intros.
  destruct (decide (η = label_to_output x)) as [eq | not_eq].
  + destruct (decide (x ∈ lts_oba_mo p1)).
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
  unfold gLtsOba_obligation_1.
  intros ? ? ? ? ? LtsOBAP ? ? ? nb Hyp;simpl in *.
  destruct nb as (a & eq). subst.
  assert (lts_oba_mo p = {[+ a +]} ⊎ lts_oba_mo q) as mem.
  eapply lts_oba_mo_spec2. exact Hyp.
  rewrite mem. simpl in *. unfold mo_label_to_mo_output at 1.
  rewrite gmultiset_map_disj_union. rewrite gmultiset_map_singleton.
  unfold label_to_output at 1. reflexivity.
Qed.
Next Obligation. (* lts_oba_non_blocking_action_delay *)
  intros ? ? ? ? ? LtsOBAP ? ? ? ? ? nb l1 l2 ;simpl in *.
  unfold gLts_obligation_1 in l2.
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
  unfold gLabel_obligation_4.
  eapply lts_oba_output_tau in l1 as cases; eauto.
  destruct cases as [computation_without_a | computation_with_a].
  + left. destruct computation_without_a as (t & l'1 & l'2).
    exists t; eauto.
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

#[global] Program Instance gLtsObaFB
  `{LtsObaFB P A} : gLtsObaFB P (ExtAct A).
Next Obligation.
  intros ? ? ? ? ? LtsOBAP ? ? ? ? ? ? nb duo l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst.
  destruct duo as [case_1 | case_2].
  + eapply simplify_match_output in case_1; subst.
    eapply lts_oba_fb_feedback; eauto.
  + symmetry in case_2.
    eapply simplify_match_output in case_2; subst.
    eapply lts_oba_fb_feedback; eauto.
Qed.

#[global] Program Instance gLtsObaFW
  `{LtsObaFW P A} : gLtsObaFW P (ExtAct A).
Next Obligation.
  intros ? ? ? ? ? ? ? p η μ ;simpl in *.
  destruct (decide (non_blocking η)) as [nb | not_nb].
  + destruct nb as (a & eq); subst.
    unfold gLabel_obligation_1. unfold gLabel_obligation_4.
    destruct (lts_oba_fw_forward p a) as (p' & l1 & l2).
    exists p'. intros Hyp duo. destruct duo as [case_1 | case_2].
    ++ eapply simplify_match_output in case_1; subst. split;eauto.
    ++ eapply symmetry, simplify_match_output in case_2; subst. split;eauto.
  + exists p. intro. contradiction.
Qed.

#[global] Program Instance Inter_FW
  `{LtsP : Lts P A} : 
    Prop_of_Inter P (TransitionSystems.mb (ExtAct A)) (ExtAct A) fw_inter.
Next Obligation.
  intros ? ? ? ? p. exact (set_label_to_mo_output (lts_outputs p)).
Defined.
Next Obligation.
  unfold Inter_FW_obligation_1. unfold set_label_to_mo_output.
  intros ? ? ? ? ? ? Hyp ;simpl in *.
  eapply elem_of_list_to_set in Hyp.
  eapply elem_of_list_fmap in Hyp.

  assert {x : A | ξ = label_to_output x ∧ x ∈ elements (lts_outputs p)} as wit.
  eapply choice;eauto. intro.
  destruct (decide (ξ = label_to_output x)).
  + destruct (decide (x ∈ elements (lts_outputs p))).
    ++ left; eauto.
    ++ right. intros (Hyp1 & imp). contradiction.
  + right. intros (imp & Hyp2). contradiction.
  
  + destruct wit as ( a & eq & mem ).
    unfold label_to_output in eq; subst.
    assert (a ∈ lts_outputs p) as mem'.
    eapply elem_of_elements; eauto.
    eapply lts_outputs_spec2 in mem'. 
    eauto.
Qed.
Next Obligation.
  intros ? ? ? ? m;simpl in *.
  exact (dom (mb_without_not_nb m)).
Defined.
Next Obligation.
  unfold Inter_FW_obligation_3.
  intros ? ? ? ? m ? Hyp ;simpl in *.
  eapply gmultiset_elem_of_dom in Hyp. 
  assert (ξ ∈ mb_without_not_nb m) as mem. eauto.
  eapply lts_mb_nb_with_nb_spec1 in mem as (nb & eq).
  eapply gmultiset_disj_union_difference' in eq.
  exists (m ∖ {[+ ξ +]}). rewrite eq at 1.
  eapply lts_multiset_minus; eauto.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? m ? m' ? ? inter;simpl in *.
  right. destruct inter as (duo & nb).
  unfold Inter_FW_obligation_3.
  eapply gmultiset_elem_of_dom.
  eapply non_blocking_action_in_ms in nb as eq'; eauto. 
  rewrite<- eq'.
  assert (mb_without_not_nb ({[+ α2 +]} ⊎ m') 
  = {[+ α2 +]} ⊎ (mb_without_not_nb m')) as eq.
  eapply lts_mb_nb_spec1; eauto. rewrite eq.
  multiset_solver.
Defined.
Next Obligation.
  intros ? ? ? ? ξ p;simpl in *.
  destruct ξ as [ a (* Input_case *) | a (* Ouput_case *)].
  + exact empty. 
  + exact {[ ActIn a ]}.
Defined.
Next Obligation.
  unfold Inter_FW_obligation_6.
  unfold Inter_FW_obligation_3.
  intros ? ? ? ? ? ? ? ? m mem l inter;simpl in *.
  destruct inter as (duo & nb). destruct nb as (a & eq).
  subst. destruct duo as [case_1 | case_2]; unfold gLabel_obligation_4 in *.
  + eapply simplify_match_output in case_1. subst. set_solver.
  + symmetry in case_2. eapply simplify_match_output in case_2. subst. set_solver.
Defined.
Next Obligation.
  intros. exact empty.
Defined.
Next Obligation.
  unfold Inter_FW_obligation_8. unfold Inter_FW_obligation_1.
  intros ? ? ? ? ? ? ? ? m mem l inter;simpl in *.
  exfalso.
  destruct inter as (duo & nb). destruct nb as (a & eq). subst.
  unfold set_label_to_mo_output in mem.
  eapply elem_of_list_to_set in mem.
  eapply elem_of_list_fmap in mem. destruct mem as (a' & eq & mem').
  subst. destruct duo as [case_1 | case_2].
  + eapply simplify_match_output in case_1. inversion case_1.
  + eapply simplify_match_output in case_2. inversion case_2.
Defined.


#[global] Program Instance Inter_par
  `{@Lts P A H} `{@Lts Q A H}: 
    Prop_of_Inter P Q (ExtAct A) parallel_inter (* (@gLabel A H) gLts gLts *).
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

#[global] Program Instance Inter_FW_par
  `{@Lts P A H} `{@Lts E A H}: Prop_of_Inter (P * mb A) E (ExtAct A) parallel_inter.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Lemma com_only_with_non_blocking `{LtsP : Lts P A} (η : ExtAct A) η': 
        dual η η' -> non_blocking η \/ non_blocking η'.
Proof.
Admitted.

Lemma (p , m) 


