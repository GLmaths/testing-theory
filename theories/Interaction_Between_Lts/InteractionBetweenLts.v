(* begin hide *)
(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
   Copyright (c) 2025 Gaëtan Lopez <glopez@irif.fr>

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
(* end hide *)

From Stdlib Require ssreflect Setoid.
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Wellfounded Require Import Inverse_Image.
From Stdlib.Logic Require Import JMeq ProofIrrelevance.
From Stdlib.Program Require Import Wf Equality.
From stdpp Require Import base countable list decidable finite gmap gmultiset.
From TestingTheory Require Import ActTau ForAllHelper MultisetHelper gLts Bisimulation Lts_OBA Lts_FW FiniteImageLTS 
    WeakTransitions StateTransitionSystems Convergence Termination ActTau.

(** ******* Interaction between two LTS *)

(* Pre-requirements for the interaction *)
Class Prop_of_Inter (P1 P2 A1 A2 : Type) (inter : A1 -> A2 -> Prop)
  `{@gLts P1 A1 H1} `{@gLts P2 A2 H2} :=
  MkProp_of_Inter {
      inter_dec a b: Decision (inter a b);

      lts_essential_actions_left : P1 -> gset A1;
      lts_essential_action_spec_left p ξ :
      ξ ∈ lts_essential_actions_left p
        -> {p' | p ⟶[ξ] p'} ;

      lts_essential_actions_right : P2 -> gset A2;
      lts_essential_action_spec_right p ξ :
      ξ ∈ lts_essential_actions_right p
        -> {p' | p ⟶[ξ] p'} ;

      lts_essential_actions_spec_interact (p1 : P1) μ1 p'1 (p2 : P2) μ2 p'2: 
      p1 ⟶[μ1] p'1 -> p2 ⟶[μ2] p'2 -> inter μ1 μ2
        -> μ1 ∈ lts_essential_actions_left p1 \/ μ2 ∈ lts_essential_actions_right p2;

      lts_co_inter_action_left : A2 -> P1 -> gset A1;
      lts_co_inter_action_spec_left p1 p'1 ξ μ p2 : 
      ξ ∈ lts_essential_actions_right p2 -> p1 ⟶[μ] p'1 -> inter μ ξ
        -> μ ∈ lts_co_inter_action_left ξ p1;

      lts_co_inter_action_right : A1 -> P2 -> gset A2;
      lts_co_inter_action_spec_right p2 p'2 ξ μ p1 : 
      ξ ∈ lts_essential_actions_left p1 ->  p2 ⟶[μ] p'2 -> inter ξ μ 
        -> μ ∈ lts_co_inter_action_right ξ p2;
    }.

#[global] Existing Instance inter_dec.


(** ****** Definition of the transition *)
Inductive inter_step `{M12 : Prop_of_Inter P1 P2 A A inter}
            : P1 * P2 → Labels A → P1 * P2 → Prop :=
| ParLeft 𝜆 a1 a2 b (l : a1 ⟶{𝜆} a2) : inter_step (a1, b) 𝜆 (a2, b)
| ParRight 𝜆 a b1 b2 (l : b1 ⟶{𝜆} b2) : inter_step (a, b1) 𝜆 (a, b2)
| ParSync μ1 μ2 a1 a2 b1 b2 (eq : inter μ1 μ2) (l1 : a1 ⟶[μ1] a2) (l2 : b1 ⟶[μ2] b2) : inter_step (a1, b1) τ (a2, b2)
.

Global Hint Constructors inter_step:mdb.

Fixpoint search_co_steps_right `{Prop_of_Inter S1 S2 A1 A2 inter} 
  (s2: S2) s'2 ξ candidates (s1 : S1) :=
  match candidates with
  | [] => None
  | μ :: xs =>
    if decide (ξ ∈ lts_essential_actions_left s1 /\ s2 ⟶[μ] s'2  /\ inter ξ μ) 
      then Some μ
      else search_co_steps_right s2 s'2 ξ xs s1
  end.

Lemma search_co_steps_spec_helper_right `{Prop_of_Inter S1 S2 A1 A2 inter}
  lnot (s2 : S2) (s'2 : S2) l (ξ : A1) (s1 : S1) :
  (elements $ lts_co_inter_action_right ξ s2) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ)) →
  is_Some $ search_co_steps_right s2 s'2 ξ l s1 ->
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ)}.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc. done. }
  {intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[a] s'2 ∧ inter ξ a)).
  + eauto.
  + apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%list_elem_of_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_helper_right_rev `{Prop_of_Inter S1 S2 A1 A2 inter} 
  lnot (s2 : S2) s'2 l ξ (s1 : S1) :
  (elements $ lts_co_inter_action_right ξ s2) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ)) →
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ)}  -> is_Some $ search_co_steps_right s2 s'2 ξ l s1.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc as (μ & ess_act & Hstep & duo).
   eapply (lts_co_inter_action_spec_right s2 s'2 ξ μ s1) in Hstep as Hyp. simplify_list_eq. set_solver. exact ess_act. exact duo. }
  { intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[a] s'2 ∧ inter ξ a)).
  + eauto.
  + apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%list_elem_of_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_1_right `{Prop_of_Inter S1 S2 A1 A2 inter} 
  (s2 : S2) s'2 ξ s1:
  is_Some $ search_co_steps_right s2 s'2 ξ (elements $ lts_co_inter_action_right ξ s2) s1 ->
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ)}.
Proof. apply (search_co_steps_spec_helper_right []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_1_right_rev `{Prop_of_Inter S1 S2 A1 A2}
  (s2 : S2) s'2 ξ s1:
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ)} 
  -> is_Some $ search_co_steps_right s2 s'2 ξ (elements $ lts_co_inter_action_right ξ s2) s1.
Proof. apply (search_co_steps_spec_helper_right_rev []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_2_right `{Prop_of_Inter S1 S2 A1 A2 inter}
  μ s2 s'2 l ξ s1:
  search_co_steps_right s2 s'2 ξ l s1 = Some μ →
  (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ).
Proof.
  induction l; [done|]. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[a] s'2 ∧ inter ξ a)) ; [|eauto].
  intros ?. simplify_eq. done.
Qed. 

Definition decide_co_step_right `{Prop_of_Inter S1 S2 A1 A2 inter}
  (s2: S2) (s'2 : S2) (ξ : A1) (s1 : S1) :
  Decision (∃ μ, ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ).
  destruct (search_co_steps_right s2 s'2 ξ (elements $ lts_co_inter_action_right ξ s2) s1) as [a|] eqn:Hpar1.
  { left. apply search_co_steps_spec_2_right in Hpar1. exists a. done. }
  { right; intros contra. destruct contra. assert ({ μ | (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ)} ). 
    exists x. eauto. apply search_co_steps_spec_1_right_rev in X. 
  inversion X. simplify_eq. }
Defined.

Lemma implication_simplified_right `{Prop_of_Inter S1 S2 A1 A2 inter} 
  (s1: S1) (* (s'1 : S1) *) (s2 : S2) (s'2 : S2)  (ξ : A1) :
  Decision (∃ μ, ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ) 
  -> Decision (ξ ∈ lts_essential_actions_left s1 ∧ ∃ μ, s2 ⟶[μ] s'2 ∧ inter ξ μ).
Proof.
  intros Hyp. destruct Hyp as [case1 | case2]. 
  + left. decompose record case1. repeat split; eauto.
  + right. intro Hyp. apply case2. decompose record Hyp. eexists. repeat split; eauto.
Qed.

Definition decide_co_step_right' `{Prop_of_Inter S1 S2 A1 A2} 
  (s1: S1) (* (s'1 : S1) *) (s2 : S2) (s'2 : S2)  (ξ : A1) :
  Decision (ξ ∈ lts_essential_actions_left s1 ∧ ∃ μ, s2 ⟶[μ] s'2 ∧ inter ξ μ).
  eapply implication_simplified_right. 
    + eapply decide_co_step_right.
Defined.

#[local] Instance dec_co_act_right `{Prop_of_Inter S1 S2 A1 A2} 
  (s1: S1) (* (s'1 : S1) *) (s2 : S2) (s'2 : S2)  (ξ : A1) :
  Decision (ξ ∈ lts_essential_actions_left s1 ∧ ∃ μ, s2 ⟶[μ] s'2 ∧ inter ξ μ).
  eapply decide_co_step_right'.
Defined.

Fixpoint search_steps_essential_left `{Prop_of_Inter S1 S2 A1 A2}
  (s1: S1) (s2: S2) s'1 s'2 candidates :=
  match candidates with
  | [] => None
  | ξ::xs => if (decide (ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1
              ∧ is_Some $ (search_co_steps_right s2 s'2 ξ (elements $ lts_co_inter_action_right ξ s2) s1)))
                then Some ξ
                else search_steps_essential_left s1 s2 s'1 s'2 xs
  end.

Lemma search_steps_spec_helper_essential_left `{M12 : Prop_of_Inter S1 S2 A1 A2}
  lnot (s1 :S1) (s2 : S2) s'1 s'2 l:
  (elements $ lts_essential_actions_left s1) = lnot ++ l →
  (∀ ξ, ξ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 
          ∧ is_Some $ search_co_steps_right s2 s'2 ξ (elements $ lts_co_inter_action_right ξ s2) s1)) →
  is_Some $ search_steps_essential_left s1 s2 s'1 s'2 l ->
  { ξ & { μ | ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ}}.
Proof.
  revert lnot. induction l as [| ξ l]; intro lnot.
  { simpl. intros Hels Hnots Hc. exfalso. inversion Hc. done. }
  { intros Helems Hnots. simpl. 
        destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 
        ∧ is_Some (search_co_steps_right s2 s'2 ξ (elements (lts_co_inter_action_right ξ s2)) s1))) as [case1 | case2].
   + intro. destruct case1 as (ess_act & HypTr & Hyp_co_step). 
     eapply search_co_steps_spec_helper_right in Hyp_co_step. 
     destruct Hyp_co_step as (μ & ess_act' & HypTr_right & duo). exists ξ. exists μ. split; eauto.
     instantiate (1:= []). eauto. intro. intro impossible. inversion impossible.
   + apply (IHl (lnot ++ [ξ])); [by simplify_list_eq|].
  intros x [Hin | Hin%list_elem_of_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_steps_spec_helper_essential_left_rev `{M12 : Prop_of_Inter S1 S2 A1 A2}
  lnot s1 s2 s'1 s'2 l:
  (elements $ lts_essential_actions_left s1) = lnot ++ l →
  (∀ ξ, ξ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 
          ∧ is_Some $ search_co_steps_right s2 s'2 ξ (elements $ lts_co_inter_action_right ξ s2) s1)) →
  { ξ & { μ | ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ}} ->
  is_Some $ search_steps_essential_left s1 s2 s'1 s'2 l.
Proof.
  revert lnot. induction l as [| ξ l]; intros lnot.
  { simpl. intros Hels Hnots. intros (ξ & μ & ess_act & Hstep1 & Hstep2 & duo). exfalso.
    simplify_list_eq. 
    eapply (Hnots ξ). eapply elem_of_elements. exact ess_act.
    split. exact ess_act. split. exact Hstep1.
    apply search_co_steps_spec_1_right_rev. exists μ. repeat split; eauto. }
  { intros Helems Hnots. simpl. 
       destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 
       ∧ is_Some (search_co_steps_right s2 s'2 ξ (elements (lts_co_inter_action_right ξ s2)) s1))) as [case1 | case2].
   + intro Hyp. eauto.
   + apply (IHl (lnot ++ [ξ])); [by simplify_list_eq|].
  intros x [Hin | Hin%list_elem_of_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_steps_spec_1_essential_left `{M12 : Prop_of_Inter S1 S2 A1 A2}
  (s1 : S1) (s2 : S2) s'1 s'2:
  is_Some $ search_steps_essential_left s1 s2 s'1 s'2 (elements $ lts_essential_actions_left s1) ->
  { ξ & { μ | ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ}}.
Proof. apply (search_steps_spec_helper_essential_left []) ; [done| intros ??; set_solver]. Qed.

Lemma search_steps_spec_1_essential_left_rev `{M12 : Prop_of_Inter S1 S2 A1 A2}
  s1 s2 s'1 s'2:
  { ξ & { μ | ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 ∧ s2 ⟶[μ] s'2 ∧ inter ξ μ}} ->
  is_Some $ search_steps_essential_left s1 s2 s'1 s'2 (elements $ lts_essential_actions_left s1).
Proof. apply (search_steps_spec_helper_essential_left_rev []) ; [done| intros ??; set_solver]. Qed.

Lemma search_steps_spec_2_essential_left `{M12 : Prop_of_Inter S1 S2 A1 A2}
  ξ (s1 : S1) (s2 : S2) s'1 s'2 l:
  search_steps_essential_left s1 s2 s'1 s'2 l = Some ξ →
  { μ | ξ ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ] s'1 ∧ s2 ⟶[μ] s'2  ∧ inter ξ μ}.
Proof.
  induction l as [| ξ' l] ; [done|]. simpl.
  destruct (decide (ξ' ∈ lts_essential_actions_left s1 ∧ s1 ⟶[ξ'] s'1 
    ∧ is_Some (search_co_steps_right s2 s'2 ξ' (elements (lts_co_inter_action_right ξ' s2)) s1))) as [case1 | case2].
  intros ?;simplify_eq. destruct case1 as (ess_act & HypTr & Hyp_co_step). 
  eapply search_co_steps_spec_1_right in Hyp_co_step. destruct Hyp_co_step as (μ & ess_act' & HypTr_right & duo). 
  exists μ. done. eauto.
Qed.

Fixpoint search_co_steps_left `{Prop_of_Inter S1 S2 A1 A2}
  (s1: S1) s'1 ξ candidates (s2 : S2) :=
  match candidates with 
  | [] => None
  | μ :: xs =>
    if decide (ξ ∈ lts_essential_actions_right s2 /\ s1 ⟶[μ] s'1  /\ inter μ ξ)
      then Some μ
      else search_co_steps_left s1 s'1 ξ xs s2
  end.

Lemma search_co_steps_spec_helper_left `{Prop_of_Inter S1 S2 A1 A2}
  lnot (s1 : S1) (s'1 : S1) l (ξ : A2) s2 :
  (elements $ lts_co_inter_action_left ξ s1) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)) →
  is_Some $ search_co_steps_left s1 s'1 ξ l s2->
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)}.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc. done. }
  {intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[a] s'1 ∧ inter a ξ)).
  + eauto.
  + apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%list_elem_of_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_helper_left_rev `{Prop_of_Inter S1 S2 A1 A2}
  lnot s1 s'1 l ξ s2:
  (elements $ lts_co_inter_action_left ξ s1) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)) →
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)}  -> is_Some $ search_co_steps_left s1 s'1 ξ l s2.
Proof.
  revert lnot. induction l as [|μ l]; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc as (μ & ess_act & Hstep & duo).
   eapply (lts_co_inter_action_spec_left s1 s'1 ξ μ) in Hstep as Hyp. simplify_list_eq. set_solver. exact ess_act. exact duo. }
  { intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)).
  + eauto.
  + apply (IHl (lnot ++ [μ])); [by simplify_list_eq|].
  intros x [Hin | Hin%list_elem_of_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_1_left `{Prop_of_Inter S1 S2 A1 A2}
  (s1 : S1) s'1 ξ s2:
  is_Some $ search_co_steps_left s1 s'1 ξ (elements $ lts_co_inter_action_left ξ s1) s2 ->
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)}.
Proof. apply (search_co_steps_spec_helper_left []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_1_left_rev `{Prop_of_Inter S1 S2 A1 A2}
  (s1 : S1) s'1 ξ s2:
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)} 
  -> is_Some $ search_co_steps_left s1 s'1 ξ (elements $ lts_co_inter_action_left ξ s1) s2.
Proof. apply (search_co_steps_spec_helper_left_rev []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_2_left `{Prop_of_Inter S1 S2 A1 A2}
  μ s1 s'1 l ξ s2:
  search_co_steps_left s1 s'1 ξ l s2 = Some μ →
  (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ).
Proof.
  induction l  as [| μ' l ]; [done|]. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ'] s'1 ∧ inter μ' ξ)) ; [|eauto].
  intros ?. simplify_eq. done.
Qed. 

Definition decide_co_step_left `{Prop_of_Inter S1 S2 A1 A2}
  (s1: S1) (s'1 : S1) (ξ : A2) (s2 : S2) :
  Decision (∃ μ, ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ).
  destruct (search_co_steps_left s1 s'1 ξ (elements $ lts_co_inter_action_left ξ s1) s2) as [a|] eqn:Hpar1.
  { left. apply search_co_steps_spec_2_left in Hpar1. exists a. done. }
  { right; intros contra. destruct contra as (μ & Hyp). 
    assert ({ μ | (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ)} ) as HypSup. 
    exists μ. eauto. apply search_co_steps_spec_1_left_rev in HypSup. 
    inversion HypSup. simplify_eq. }
Defined.

Lemma implication_simplified_left `{Prop_of_Inter S1 S2 A1 A2} 
  (s1: S1) (s'1 : S1) (s2 : S2) (* (s'2 : S2) *)  (ξ : A2) :
  Decision (∃ μ, ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ) 
  -> Decision (ξ ∈ lts_essential_actions_right s2 ∧ ∃ μ, s1 ⟶[μ] s'1 ∧ inter μ ξ).
Proof.
  intros Hyp. destruct Hyp as [case1 | case2]. left. decompose record case1. repeat split; eauto.
  right. intro HypContra. apply case2. decompose record HypContra. eexists. repeat split; eauto.
Qed.

Definition decide_co_step_left' `{Prop_of_Inter S1 S2 A1 A2} 
  (s1: S1) (s'1 : S1) (s2 : S2) (* (s'2 : S2) *)  (ξ : A2) :
  Decision (ξ ∈ lts_essential_actions_right s2 ∧ ∃ μ, s1 ⟶[μ] s'1 ∧ inter μ ξ ).
  eapply implication_simplified_left. 
    + eapply decide_co_step_left.
Defined.

#[local] Instance dec_co_act_left `{M12 : Prop_of_Inter S1 S2 A1 A2}
  (s1: S1) (s'1 : S1) (s2 : S2) (* (s'2 : S2) *)  (ξ : A2) :
  Decision (ξ ∈ lts_essential_actions_right s2 ∧ ∃ μ, s1 ⟶[μ] s'1 ∧ inter μ ξ).
  eapply decide_co_step_left'. 
Defined.  

Fixpoint search_steps_essential_right `{M12 : Prop_of_Inter S1 S2 A1 A2}
  (s1: S1) (s2: S2) s'1 s'2 candidates :=
  match candidates with
  | [] => None
  | ξ::xs => if (decide (ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 
          ∧ is_Some $ search_co_steps_left s1 s'1 ξ (elements $ lts_co_inter_action_left ξ s1) s2))
                then Some ξ
                else search_steps_essential_right s1 s2 s'1 s'2 xs
  end.

Lemma search_steps_spec_helper_essential_right `{M12 : Prop_of_Inter S1 S2 A1 A2}
  lnot (s1 :S1) (s2 : S2) s'1 s'2 l:
  (elements $ lts_essential_actions_right s2) = lnot ++ l →
  (∀ ξ, ξ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 
    ∧ is_Some $ search_co_steps_left s1 s'1 ξ (elements $ lts_co_inter_action_left ξ s1) s2)) →
  is_Some $ search_steps_essential_right s1 s2 s'1 s'2 l ->
  { ξ & { μ | ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ}}.
Proof.
  revert lnot. induction l as [| ξ l]; intros lnot.
  { simpl. intros Hels Hnots Hc. exfalso. inversion Hc. done. }
  { intros Helems Hnots. simpl. 
        destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 
          ∧ is_Some (search_co_steps_left s1 s'1 ξ (elements (lts_co_inter_action_left ξ s1)) s2 )))  as [case1 | case2].
   + intro. destruct case1 as (ess_act & HypTr_right & Hyp_co_act_left). 
     eapply search_co_steps_spec_helper_left in Hyp_co_act_left. 
     destruct Hyp_co_act_left as (μ & ess_act' & HypTr_left & duo). 
     exists ξ. exists μ. split; eauto.
     instantiate (1:= []). eauto. intro. intro Hyp. inversion Hyp.
   + apply (IHl (lnot ++ [ξ])); [by simplify_list_eq|].
  intros x [Hin | Hin%list_elem_of_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_steps_spec_helper_essential_right_rev `{M12 : Prop_of_Inter S1 S2 A1 A2}
  lnot s1 s2 s'1 s'2 l:
  (elements $ lts_essential_actions_right s2) = lnot ++ l →
  (∀ ξ, ξ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 
    ∧ is_Some $ search_co_steps_left s1 s'1 ξ (elements $ lts_co_inter_action_left ξ s1) s2)) →
  { ξ & { μ | ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ}} ->
  is_Some $ search_steps_essential_right s1 s2 s'1 s'2 l.
Proof.
  revert lnot. induction l as [| ξ l] ; intros lnot.
  { simpl. intros Hels Hnots. intros (ξ & μ & ess_act & Hstep1 & Hstep2 & duo). exfalso.
    simplify_list_eq. 
    eapply (Hnots ξ). eapply elem_of_elements. exact ess_act.
    split. exact ess_act. split. exact Hstep1.
    apply search_co_steps_spec_1_left_rev. exists μ. repeat split; eauto. }
  { intros Helems Hnots. simpl. 
        destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 
          ∧ is_Some (search_co_steps_left s1 s'1 ξ (elements (lts_co_inter_action_left ξ s1)) s2 )))  as [case1 | case2].
   + intro Hyp. eauto.
   + apply (IHl (lnot ++ [ξ])); [by simplify_list_eq|].
  intros x [Hin | Hin%list_elem_of_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed. 

Lemma search_steps_spec_1_essential_right `{M12 : Prop_of_Inter S1 S2 A1 A2}
  (s1 : S1) (s2 : S2) s'1 s'2:
  is_Some $ search_steps_essential_right s1 s2 s'1 s'2 (elements $ lts_essential_actions_right s2) ->
  { ξ & { μ | ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ}}.
Proof. apply (search_steps_spec_helper_essential_right []) ; [done| intros ??; set_solver]. Qed.

Lemma search_steps_spec_1_essential_right_rev `{M12 : Prop_of_Inter S1 S2 A1 A2}
  s1 s2 s'1 s'2:
  { ξ & { μ | ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 ∧ s1 ⟶[μ] s'1 ∧ inter μ ξ}} ->
  is_Some $ search_steps_essential_right s1 s2 s'1 s'2 (elements $ lts_essential_actions_right s2).
Proof. apply (search_steps_spec_helper_essential_right_rev []) ; [done| intros ??; set_solver]. Qed.

Lemma search_steps_spec_2_essential_right `{M12 : Prop_of_Inter S1 S2 A1 A2}
  ξ (s1 : S1) (s2 : S2) s'1 s'2 l:
  search_steps_essential_right s1 s2 s'1 s'2 l = Some ξ →
  { μ | ξ ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ] s'2 ∧ s1 ⟶[μ] s'1  ∧ inter μ ξ}.
Proof.
  induction l as [| ξ' l]; [done|].  simpl.
  destruct (decide (ξ' ∈ lts_essential_actions_right s2 ∧ s2 ⟶[ξ'] s'2 
      ∧ is_Some (search_co_steps_left s1 s'1 ξ' (elements (lts_co_inter_action_left ξ' s1)) s2))) as [case1 | case2].
  intros ?. simplify_eq. destruct case1 as (ess_act & HypTr_right & Hyp_co_act_left). 
  eapply search_co_steps_spec_1_left in Hyp_co_act_left. 
  destruct Hyp_co_act_left as (μ & ess_act' & HypTr_left & duo). exists μ. done. eauto.
Qed.


Definition decide_inter_step `{M12 : Prop_of_Inter S1 S2 A A inter}
            (s1: S1) (s2: S2) 𝜆 s'1 s'2:
  Decision (inter_step (s1, s2) 𝜆 (s'1, s'2)).
Proof.
  destruct (decide (s1 ⟶{𝜆} s'1 ∧ s2 = s'2)) as [[??]|Hnot1].
  { simplify_eq. left. by constructor. }
  destruct (decide (s2 ⟶{𝜆} s'2 ∧ s1 = s'1)) as [[??]|Hnot2].
  { simplify_eq. left. by constructor. }
  destruct 𝜆.
  { right. intros contra; inversion contra; simplify_eq; eauto. }
  destruct (search_steps_essential_left s1 s2 s'1 s'2 (elements $ lts_essential_actions_left s1)) as [ξ|] eqn:Hpar1.
  { apply search_steps_spec_2_essential_left in Hpar1 as (μ & ess_act & step_left & step_right & duo). 
   left; eapply ParSync; eauto. }
  destruct (search_steps_essential_right s1 s2 s'1 s'2 (elements $ lts_essential_actions_right s2)) as [ξ|] eqn:Hpar2.
  { apply search_steps_spec_2_essential_right in Hpar2 as (μ & ess_act & step_right & step_left & duo).  
   left; eapply ParSync; eauto. }
  right; intros contra; inversion contra; simplify_eq; eauto.
  eapply lts_essential_actions_spec_interact in eq as case_essential; eauto. destruct case_essential as [ess_act1 | ess_act2].
  - assert (is_Some $ search_steps_essential_left s1 s2 s'1 s'2 (elements (lts_essential_actions_left s1))) as Hc; [|].
    eapply search_steps_spec_1_essential_left_rev. exists μ1. exists μ2. repeat split; eauto.
    inversion Hc. simplify_eq.
  - assert (is_Some $ search_steps_essential_right s1 s2 s'1 s'2 (elements (lts_essential_actions_right s2))) as Hc; [|].
    eapply search_steps_spec_1_essential_right_rev. exists μ2. exists μ1. repeat split; eauto.
    inversion Hc. simplify_eq.
Defined.

Definition inter_performs_essential_left
  `{Prop_of_Inter S1 S2 A1 A2}
          (s1: S1) (s2 : S2) (ξ : A1) :=
        s1 ⟶[ξ] ∧ (∃ μ, s2 ⟶[μ] 
          ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1). 

Fixpoint search_co_steps_right_performs `{Prop_of_Inter S1 S2 A1 A2 inter} 
  (s2: S2) ξ candidates (s1 : S1) :=
  match candidates with
  | [] => None
  | μ :: xs =>
    if decide (ξ ∈ lts_essential_actions_left s1 /\ s2 ⟶[μ] /\ inter ξ μ) 
      then Some μ
      else search_co_steps_right_performs s2 ξ xs s1
  end.

Lemma search_co_steps_spec_helper_right_performs `{Prop_of_Inter S1 S2 A1 A2 inter}
  lnot (s2 : S2) l (ξ : A1) (s1 : S1) :
  (elements $ lts_co_inter_action_right ξ s2) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_left s1 ∧  s2 ⟶[μ] ∧ inter ξ μ)) →
  is_Some $ search_co_steps_right_performs s2 ξ l s1 ->
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧  s2 ⟶[μ] ∧ inter ξ μ)}.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc. done. }
  {intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[a] ∧ inter ξ a)).
  + eauto.
  + apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%list_elem_of_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_helper_right_performs_rev `{Prop_of_Inter S1 S2 A1 A2 inter} 
  lnot (s2 : S2) l ξ (s1 : S1) :
  (elements $ lts_co_inter_action_right ξ s2) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] ∧ inter ξ μ)) →
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] ∧ inter ξ μ)}  
  -> is_Some $ search_co_steps_right_performs s2 ξ l s1.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc as (μ & ess_act & Hstep & duo).
   eapply lts_performs_spec1 in Hstep as (s'2 & Hstep); eauto.
   eapply (lts_co_inter_action_spec_right s2 s'2 ξ μ s1) in Hstep as Hyp; eauto.
   simplify_list_eq.
   eapply elem_of_elements in Hyp. eapply Hnots; eauto.
   repeat split; eauto. eapply lts_performs_spec2. eauto. }
  { intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[a] ∧ inter ξ a)).
  + eauto.
  + apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%list_elem_of_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_1_right_performs `{Prop_of_Inter S1 S2 A1 A2 inter} 
  (s2 : S2) ξ s1:
  is_Some $ search_co_steps_right_performs s2 ξ (elements $ lts_co_inter_action_right ξ s2) s1 ->
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] ∧ inter ξ μ)}.
Proof. apply (search_co_steps_spec_helper_right_performs []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_1_right_performs_rev `{Prop_of_Inter S1 S2 A1 A2}
  (s2 : S2) ξ s1:
  { μ | (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] ∧ inter ξ μ)} 
  -> is_Some $ search_co_steps_right_performs s2 ξ (elements $ lts_co_inter_action_right ξ s2) s1.
Proof. apply (search_co_steps_spec_helper_right_performs_rev []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_2_right_performs `{Prop_of_Inter S1 S2 A1 A2 inter}
  μ s2 l ξ s1:
  search_co_steps_right_performs s2 ξ l s1 = Some μ →
  (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] ∧ inter ξ μ).
Proof.
  induction l; [done|]. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[a] ∧ inter ξ a)) ; [|eauto].
  intros ?. simplify_eq. done.
Qed.

#[local] Instance dec_co_act_performs_essential_left `{Prop_of_Inter S1 S2 A1 A2}
       (s1: S1) (s2 : S2) (ξ : A1)
      : Decision (inter_performs_essential_left s1 s2 ξ).
Proof.
  destruct (decide (is_Some $ search_co_steps_right_performs s2 ξ 
  (elements $ lts_co_inter_action_right ξ s2) s1)) as [wit | not_wit].
  + left. 
    eapply search_co_steps_spec_1_right_performs in wit.
    destruct wit as (μ' & h1 & h2 & h3). repeat split; eauto.
    eapply lts_essential_action_spec_left in h1. eapply lts_performs_spec2; eauto.
  + right. intros (μ' & h1 & h2 & h3 & h4).
    assert ({ μ | (ξ ∈ lts_essential_actions_left s1 ∧ s2 ⟶[μ] ∧ inter ξ μ)}) as wit.
    eauto. eapply search_co_steps_spec_1_right_performs_rev in wit.
    contradiction.
Qed.

Lemma transition_to_performs_essential_left `{Prop_of_Inter S1 S2 A1 A2}
  (s1 : S1) (s2 : S2) (s'2 : S2) (ξ : A1) : 
  { μ | s2 ⟶[μ] s'2 ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1} 
  -> { μ | s2 ⟶[μ] ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1}.
Proof.
  intro Hyp. destruct Hyp as [μ [HypTr2 [inter_prop ess_act]]]. eexists.
  repeat split; eauto. eapply lts_performs_spec2. exists s'2. eauto.
Qed.

Lemma performs_to_transition_essential_left `{Prop_of_Inter S1 S2 A1 A2}
  (s1 : S1) (s2 : S2) (* (s'2 : S2) *) (ξ : A1) : 
  { μ | s2 ⟶[μ] ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1} 
  -> {s'2 & { μ | s2 ⟶[μ] s'2 ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1}}.
Proof.
  intro Hyp. destruct Hyp as [μ [HypNotStable2 [inter_prop ess_act]]]. eapply lts_performs_spec1 in HypNotStable2. 
  destruct HypNotStable2 as [s'2 HypTr2]. eexists. eexists. repeat split; eauto.
Qed.

Definition com_with_ess_left `{Prop_of_Inter S1 S2 A1 A2} 
    (s1 : S1) (s2 : S2) (ξ : A1) (μ : A2)
 := s2 ⟶[μ] ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1.

Lemma some_witness1_right' `{Prop_of_Inter S1 S2 A1 A2}
  (s1 : S1) (s2 : S2) (ξ : A1) : 
  (∃ μ : A2, s2 ⟶[μ] ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1) 
  -> { μ | s2 ⟶[μ] ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1}.
Proof.
  intro Hyp. exact (choice (com_with_ess_left s1 s2 ξ) Hyp).
Qed.

Lemma some_witness1_right `{Prop_of_Inter S1 S2 A1 A2}
  (s1 : S1) (s2 : S2) (ξ : A1) : 
  (∃ μ : A2, s2 ⟶[μ] ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1) 
  -> { μ & { s'2 | s2 ⟶[μ] s'2 ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1}}.
Proof.
  intro Hyp.
  eapply some_witness1_right' in Hyp.
  destruct Hyp as (μ & Hperf & inter_h & ess_act).
  eapply lts_performs_spec1 in Hperf.
  destruct Hperf as (s'2 & HypTr).
  exists μ. exists s'2. repeat split; eauto.
Qed.

Fixpoint inter_lts_performs_helper_essential_left
  `{Prop_of_Inter S1 S2 A1 A2}
  (s1: S1) (s2: S2) (l: list A1) : bool :=
  match l with
  | [] => false
  | ξ::bs =>
      if decide (inter_performs_essential_left s1 s2 ξ)
        then true 
        else inter_lts_performs_helper_essential_left s1 s2 bs
  end.

Lemma inter_sts_performs_helper_spec_1_essential_left `{Prop_of_Inter S1 S2 A1 A2}
  (s1: S1) (s2: S2) (l: list A1) :
  inter_lts_performs_helper_essential_left s1 s2 l = true →
  {s' | ∃ μ1 μ2, inter μ1 μ2 ∧ s1 ⟶[μ1] s'.1 ∧ s2 ⟶[μ2] s'.2}.
Proof.
  induction l as [| ξ l ]; [done|].
  simpl. destruct (decide (inter_performs_essential_left s1 s2 ξ)) as [Hyp | Hyp]; eauto. intros _.
  destruct Hyp as [Hperf1 act_founded]. eapply some_witness1_right in act_founded.
  destruct act_founded as (μ & s'2 & HypTr2 & duo & ess_act).
  apply lts_performs_spec1 in Hperf1 as [s'1 HypTr1].
  exists (s'1, s'2). by exists ξ, μ.
Qed.

Lemma inter_sts_performs_helper_spec_2_essential_left `{Prop_of_Inter S1 S2 A1 A2}
  (s1: S1) (s2: S2) ξ μ s'1 s'2 :
  s1 ⟶[ξ] s'1 → s2 ⟶[μ] s'2 → inter ξ μ → ξ ∈ lts_essential_actions_left s1 →
  inter_lts_performs_helper_essential_left s1 s2 (elements $ lts_essential_actions_left s1) = true.
Proof.
  intros Hs1 Hs2 duo ess_act.
  assert (∀ l rest,
             (elements $ lts_essential_actions_left s1) = rest ++ l →
             (∀ ξ, ξ ∈ rest → ¬ (s1 ⟶[ξ] s'1 ∧ (exists μ, s2 ⟶[μ] s'2 ∧ inter ξ μ ∧ ξ ∈ lts_essential_actions_left s1 ))) →
             inter_lts_performs_helper_essential_left s1 s2 l = true) as Hccl.
  induction l as [| b l IHl].
  - intros rest Hrest Hnots. (* pose proof (lts_essential_action_spec_left _ ξ ess_act Hs1) as Hin.  *)
    simplify_list_eq.
    exfalso. eapply Hnots; eauto. set_solver.
  - intros rest Hrest Hnots. simplify_list_eq.
    destruct (decide (inter_performs_essential_left s1 s2 b)) as [case1 | case2]; [auto|].
    eapply (IHl (rest ++ [b])); [by simplify_list_eq|].
    intros x [Hin | ->%list_elem_of_singleton]%elem_of_app; [eauto|].
    intros [Hstep1 Hstep2]. eapply case2. split. eapply lts_performs_spec2. exists s'1. assumption.
    destruct Hstep2 as (μ2 & Tr2 & duo2 & ess_act2). exists μ2. split. eapply lts_performs_spec2. exists s'2. assumption.
    split; eauto. 
  - apply (Hccl _ []); eauto. set_solver.
Qed.

Definition inter_performs_essential_right
  `{Prop_of_Inter S1 S2 A1 A2}
          (s1: S1) (s2 : S2) (ξ : A2) :=
        s2 ⟶[ξ] ∧ (∃ μ, s1 ⟶[μ] ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2). 

Fixpoint search_co_steps_left_performs `{Prop_of_Inter S1 S2 A1 A2 inter} 
  (s1: S1) ξ candidates (s2 : S2) :=
  match candidates with
  | [] => None
  | μ :: xs =>
    if decide (ξ ∈ lts_essential_actions_right s2 /\ s1 ⟶[μ] /\ inter μ ξ) 
      then Some μ
      else search_co_steps_left_performs s1 ξ xs s2
  end.

Lemma search_co_steps_spec_helper_left_performs `{Prop_of_Inter S1 S2 A1 A2 inter}
  lnot (s1 : S1) l (ξ : A2) (s2 : S2) :
  (elements $ lts_co_inter_action_left ξ s1) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_right s2 ∧  s1 ⟶[μ] 
  ∧ inter μ ξ)) →
  is_Some $ search_co_steps_left_performs s1 ξ l s2 ->
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧  s1 ⟶[μ] ∧ inter μ ξ )}.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc. done. }
  {intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[a] ∧ inter a ξ)).
  + eauto.
  + apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%list_elem_of_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_helper_left_performs_rev `{Prop_of_Inter S1 S2 A1 A2 inter} 
  lnot (s1 : S1) l ξ (s2 : S2) :
  (elements $ lts_co_inter_action_left ξ s1) = lnot ++ l →
  (∀ μ, μ ∈ lnot → ¬ (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] 
  ∧ inter μ ξ )) →
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] ∧ inter μ ξ )}  
  -> is_Some $ search_co_steps_left_performs s1 ξ l s2.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. intros Hc. exfalso. inversion Hc as (μ & ess_act & Hstep & duo).
   eapply lts_performs_spec1 in Hstep as (s'1 & Hstep); eauto.
   eapply (lts_co_inter_action_spec_left s1 s'1 ξ μ s2) in Hstep as Hyp; eauto.
   simplify_list_eq.
   eapply elem_of_elements in Hyp. eapply Hnots; eauto.
   repeat split; eauto. eapply lts_performs_spec2. eauto. }
  { intros Helems Hnots. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[a] ∧ inter a ξ )).
  + eauto.
  + apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%list_elem_of_singleton]%elem_of_app; simplify_eq ; eauto. }
Qed.

Lemma search_co_steps_spec_1_left_performs `{Prop_of_Inter S1 S2 A1 A2 inter} 
  (s1 : S1) ξ s2:
  is_Some $ search_co_steps_left_performs s1 ξ (elements $ lts_co_inter_action_left ξ s1) s2 ->
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] ∧ inter μ ξ )}.
Proof. apply (search_co_steps_spec_helper_left_performs []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_1_left_performs_rev `{Prop_of_Inter S1 S2 A1 A2}
  (s1 : S1) ξ s2:
  { μ | (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] ∧ inter μ ξ )} 
  -> is_Some $ search_co_steps_left_performs s1 ξ 
      (elements $ lts_co_inter_action_left ξ s1) s2.
Proof. apply (search_co_steps_spec_helper_left_performs_rev []); [done| intros ??; set_solver]. Qed.

Lemma search_co_steps_spec_2_left_performs `{Prop_of_Inter S1 S2 A1 A2 inter}
  μ s1 l ξ s2:
  search_co_steps_left_performs s1 ξ l s2 = Some μ →
  (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] ∧ inter μ ξ).
Proof.
  induction l; [done|]. simpl.
  destruct (decide (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[a] ∧ inter a ξ )) ; [|eauto].
  intros ?. simplify_eq. done.
Qed.

#[local] Instance dec_co_act_performs_essential_right `{Prop_of_Inter S1 S2 A1 A2}
       (s1: S1) (s2 : S2) (ξ : A2)
      : Decision (inter_performs_essential_right (* M1 M2 *) s1 s2 ξ).
Proof. 
  destruct (decide (is_Some $ search_co_steps_left_performs s1 ξ 
  (elements $ lts_co_inter_action_left ξ s1) s2)) as [wit | not_wit].
  + left. 
    eapply search_co_steps_spec_1_left_performs in wit.
    destruct wit as (μ' & h1 & h2 & h3). repeat split; eauto.
    eapply lts_essential_action_spec_right in h1. eapply lts_performs_spec2; eauto.
  + right. intros ( h1 & μ'  & h2 & h3 & h4).
    assert ({ μ | (ξ ∈ lts_essential_actions_right s2 ∧ s1 ⟶[μ] ∧ inter μ ξ)}) as wit.
    eauto. eapply search_co_steps_spec_1_left_performs_rev in wit.
    contradiction.
Qed.

Lemma transition_to_performs_essential_right `{Prop_of_Inter S1 S2 A1 A2}
  (s1 : S1) (s2 : S2) (s'1 : S1) (ξ : A2) : 
  { μ | s1 ⟶[μ] s'1 ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2} 
  -> { μ | s1 ⟶[μ] ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2}.
Proof.
  intro Hyp. destruct Hyp as [μ [HypTr2 [inter_prop ess_act]]].  eexists. repeat split; eauto. 
  eapply lts_performs_spec2. exists s'1. eauto.
Qed.

Lemma performs_to_transition_essential_right `{Prop_of_Inter S1 S2 A1 A2}
  (s1 : S1) (s2 : S2) (* (s'2 : S2) *) (ξ : A2) : 
  { μ | s1 ⟶[μ] ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2} 
  -> {s'1 & { μ | s1 ⟶[μ] s'1 ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2}}.
Proof.
  intro Hyp. destruct Hyp as [μ [HypNotStable2 [inter_prop ess_act]]]. eapply lts_performs_spec1 in HypNotStable2. 
  destruct HypNotStable2 as [s'2 HypTr2]. eexists. eexists. repeat split; eauto.
Qed.

Definition com_with_ess_right `{Prop_of_Inter S1 S2 A1 A2} 
    (s1 : S1) (s2 : S2) (ξ : A2) (μ : A1)
 := s1 ⟶[μ] ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2.

Lemma some_witness1_left' `{Prop_of_Inter S1 S2 A1 A2}
  (s1 : S1) (s2 : S2) (ξ : A2) : 
  (∃ μ : A1, s1 ⟶[μ] ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2)
  -> { μ | s1 ⟶[μ] ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2}.
Proof.
  intro Hyp. exact (choice (com_with_ess_right s1 s2 ξ) Hyp).
Qed.

Lemma some_witness1_left `{Prop_of_Inter S1 S2 A1 A2}
  (s1 : S1) (s2 : S2) (ξ : A2) : 
  (∃ μ : A1, s1 ⟶[μ] ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2)
  -> { μ & { s'1 | s1 ⟶[μ] s'1 ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2}}.
Proof.
  intro Hyp.
  eapply some_witness1_left' in Hyp.
  destruct Hyp as (μ & Hperf & inter_h & ess_act).
  eapply lts_performs_spec1 in Hperf.
  destruct Hperf as (s'1 & HypTr).
  exists μ. exists s'1. repeat split; eauto.
Qed.

Fixpoint inter_lts_performs_helper_essential_right (* {S1 S2 A: Type} `{ExtAction A} {M1: gLts S1 A} {M2: gLts S2 A} *)
  `{Prop_of_Inter S1 S2 A1 A2}
  (s1: S1) (s2: S2) (l: list A2) : bool :=
  match l with
  | [] => false
  | ξ::bs =>
      if decide (inter_performs_essential_right s1 s2 ξ)
        then true 
        else inter_lts_performs_helper_essential_right s1 s2 bs
  end.

Lemma inter_sts_performs_helper_spec_1_essential_right `{Prop_of_Inter S1 S2 A1 A2}
  (s1: S1) (s2: S2) (l: list A2) :
  inter_lts_performs_helper_essential_right s1 s2 l = true →
  {s' | ∃ μ1 μ2, inter μ1 μ2 ∧ s1 ⟶[μ1] s'.1 ∧ s2 ⟶[μ2] s'.2}.
Proof.
  induction l as [| ξ l ]; [done|].
  simpl. destruct (decide (inter_performs_essential_right s1 s2 ξ)) as [Hyp | Hyp]; eauto. intros _.
  destruct Hyp as [Hperf1 act_founded]. eapply some_witness1_left in act_founded.
  destruct act_founded as (μ & s'1 & HypTr1 & duo & ess_act).
  apply lts_performs_spec1 in Hperf1 as [s'2 HypTr2].
  exists (s'1, s'2). by exists μ, ξ.
Qed.

Lemma inter_sts_performs_helper_spec_2_essential_right `{Prop_of_Inter S1 S2 A1 A2}
  (s1: S1) (s2: S2) μ ξ s'1 s'2 :
  s1 ⟶[μ] s'1 → s2 ⟶[ξ] s'2 → inter μ ξ → ξ ∈ lts_essential_actions_right s2 →
  inter_lts_performs_helper_essential_right s1 s2 (elements $ lts_essential_actions_right s2) = true.
Proof.
  intros Hs1 Hs2 duo ess_act.
  assert (∀ l rest,
             (elements $ lts_essential_actions_right s2) = rest ++ l →
             (∀ ξ, ξ ∈ rest → ¬ (s2 ⟶[ξ] s'2 ∧ (exists μ, s1 ⟶[μ] s'1 ∧ inter μ ξ ∧ ξ ∈ lts_essential_actions_right s2 ))) →
             inter_lts_performs_helper_essential_right s1 s2 l = true) as Hccl.
  induction l as [| b l IHl].
  - intros rest Hrest Hnots.
    simplify_list_eq.
    exfalso. eapply Hnots; eauto. set_solver.
  - intros rest Hrest Hnots. simplify_list_eq.
    destruct (decide (inter_performs_essential_right s1 s2 b)) as [case1 | case2]; [auto|].
    eapply (IHl (rest ++ [b])); [by simplify_list_eq|].
    intros x [Hin | ->%list_elem_of_singleton]%elem_of_app; [eauto|].
    intros [Hstep1 Hstep2]. eapply case2. split. eapply lts_performs_spec2. exists s'2. assumption.
    destruct Hstep2 as (μ2 & Tr2 & duo2 & ess_act2). exists μ2. split. eapply lts_performs_spec2. exists s'1. assumption.
    split; eauto. 
  - apply (Hccl _ []); eauto. set_solver.
Qed.

Definition inter_lts_performs `{Prop_of_Inter S1 S2 A A}
  (s1: S1) (s2: S2) (𝜆 : Labels A): Prop :=
  s1 ⟶{𝜆} ∨ s2 ⟶{𝜆} ∨
    match 𝜆 with
    | τ => inter_lts_performs_helper_essential_left s1 s2 (elements $ lts_essential_actions_left s1)
        ∨ inter_lts_performs_helper_essential_right s1 s2 (elements $ lts_essential_actions_right s2)
    | _ => False
    end.


#[global] Instance inter_lts
  `(inter : A -> A -> Prop) {S1 S2 : Type} {H : ExtAction A} {M1 : gLts S1 H} {M2 : gLts S2 H}
  `{!@Prop_of_Inter S1 S2 A A inter H M1 H M2} :
  gLts (S1 * S2) H.
Proof.
  refine (MkgLts _ _ _ inter_step _ _ (λ s 𝜆, inter_lts_performs s.1 s.2 𝜆) _ _ _).
  - intros [s1 s2] 𝜆 [s'1 s'2]. apply decide_inter_step.
  - intros ??. unfold inter_lts_performs.
    apply or_dec; [apply _|apply or_dec; [apply _|]]. destruct 𝜆; apply _.
  - intros [a b] 𝜆 Hp. unfold inter_lts_performs in Hp. simpl in Hp.
    destruct (decide (a ⟶{𝜆})) as [Hp1|Hn1].
    { apply lts_performs_spec1 in Hp1 as [s' ?]. refine ((s', b) ↾ _). by constructor. }
    destruct (decide (b ⟶{𝜆})) as [Hp2|Hn2].
    { apply lts_performs_spec1 in Hp2 as [s' ?]. refine ((a, s') ↾ _). by constructor. }
    destruct 𝜆 as [μ|]; [exfalso; by destruct Hp as [|[|]]|].
    destruct (inter_lts_performs_helper_essential_left a b (elements (lts_essential_actions_left a))) eqn:Hs1.
    { apply inter_sts_performs_helper_spec_1_essential_left in Hs1 as ((s'1, s'2) & hs).
      exists (s'1, s'2). destruct hs as (μ1 & μ2 & hs & l1 & l2). by eapply ParSync. }
    destruct (inter_lts_performs_helper_essential_right a b (elements (lts_essential_actions_right b))) eqn:Hs2.
    { apply inter_sts_performs_helper_spec_1_essential_right in Hs2 as ((s'1, s'2) & hs).
      exists (s'1, s'2). destruct hs as (μ1 & μ2 & hs & l1 & l2). by eapply ParSync. }
    exfalso. destruct Hp as [|[|[|]]]; done.
  - intros [s1 s2] 𝜆 [[s'1 s'2] Hstep].
    unfold inter_lts_performs.
    inversion Hstep; simplify_eq; simpl.
    + left. exact (lts_performs_spec2 _ _ (s'1 ↾ l)).
    + right; left. exact (lts_performs_spec2 _ _ (s'2 ↾ l)).
    + eapply lts_essential_actions_spec_interact in eq as where_is_the_essential_action; eauto.
      destruct where_is_the_essential_action as [ ess_act1 | ess_act2].
      ++ assert (inter_lts_performs_helper_essential_left s1 s2 (elements $ lts_essential_actions_left s1) = true) as Hccl
           by (eapply inter_sts_performs_helper_spec_2_essential_left; eauto).
         right; right; left. by rewrite Hccl.
      ++ assert (inter_lts_performs_helper_essential_right s1 s2 (elements $ lts_essential_actions_right s2) = true) as Hccl
           by (eapply inter_sts_performs_helper_spec_2_essential_right; eauto).
         right; right; right. by rewrite Hccl.
Defined.

#[global]
Instance inter_clts {S1 S2 A: Type} `{H : ExtAction A}  `{!gLts S1 H} `{!gLts S2 H} 
`{M1: !CountablegLts S1 A} 
`{M2: !CountablegLts S2 A} `{inter : A -> A -> Prop} 
`{i : !Prop_of_Inter S1 S2 A A inter}: CountablegLts (S1 * S2) A.
Proof.
  apply MkClts.
  -  eapply prod_countable.
  - intros x 𝜆. apply sig_countable. intros y.
    destruct (decide (bool_decide (x ⟶{𝜆} y))); [left | right]; done.
Qed.