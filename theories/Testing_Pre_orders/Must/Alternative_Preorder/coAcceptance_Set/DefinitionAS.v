(* begin hide *)
(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
   Copyright (c) 2026 Gaëtan Lopez <glopez@irif.fr>

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

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Program Require Import Equality Basics.
From stdpp Require Import finite gmap decidable gmultiset.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Lts_OBA Subset_Act WeakTransitions Testing_Predicate
    StateTransitionSystems InteractionBetweenLts Convergence Termination FiniteImageLTS Subset_Act.


(** ** Label abstractions *)
Class AbsAction (P T : Type) {FinA PreAct : Type} {A : Type} {H : ExtAction A} (αᴛᴇꜱᴛ : A → FinA) (αᴘʀᴏ : FinA → PreAct)
  {Aproc : Type} {Hp : ExtAction Aproc} {gLtsP : gLts P Hp} {gLtsT : gLtsEq T H}
  {SA : SyncAction Aproc A} :=
  MkAbsAction {
    (** Test-side condition for label abstractions *)
    abstraction_test_spec (t : T) (β : A) (β' : A) :
    blocking β -> blocking β' ->
      (αᴛᴇꜱᴛ β) = (αᴛᴇꜱᴛ β') -> β ∈ (R t)-> β' ∈ (R t);
    (** Program-side condition for label abstractions *)
    abstraction_prog_spec (p : P) β β' :
    blocking β -> blocking β' ->
      αᴘʀᴏ (αᴛᴇꜱᴛ β) = αᴘʀᴏ (αᴛᴇꜱᴛ β') -> (αᴛᴇꜱᴛ β) ∈ ⌈ αᴛᴇꜱᴛ ⌉ (coR p) -> (αᴛᴇꜱᴛ β') ∈ ⌈ αᴛᴇꜱᴛ ⌉ (coR p);
  }.

Arguments AbsAction P T {_ _ _ _} αᴛᴇꜱᴛ αᴘʀᴏ {_ _ _ _ _}.

(** ** Finitary Label abstractions *)
Class FinitaryAbsAction (P T : Type) {FinA PreAct : Type} {A : Type} {H : ExtAction A} (αᴛᴇꜱᴛ : A → FinA) (αᴘʀᴏ : FinA → PreAct)
  {Aproc : Type} {Hp : ExtAction Aproc} {gLtsP : gLts P Hp} {gLtsT : gLtsEq T H}
  {SA : SyncAction Aproc A} `{Countable PreAct} :=
  MkFinitaryAbsAction {
      FinitaryAbsAction_Abs :: AbsAction (Aproc := Aproc) (Hp := Hp) (gLtsP := gLtsP) (gLtsT := gLtsT) (SA := SA) P T αᴛᴇꜱᴛ αᴘʀᴏ;

      (** **** αᴘʀᴏ (αᴛᴇꜱᴛ (coR p)) is a finite set, called (coR_abs p) *)
      coR_abs : P -> gset PreAct;
      
      (** **** coR_abs p ⊆ αᴘʀᴏ (αᴛᴇꜱᴛ (coR p)) *)
      coR_abs_spec1 (p : P) (pre_μ : PreAct) : pre_μ ∈ (coR_abs p) -> pre_μ ∈ ⌈ (αᴘʀᴏ ∘ αᴛᴇꜱᴛ) ⌉ (coR p);

      (** **** αᴘʀᴏ (αᴛᴇꜱᴛ (coR p)) ⊆ coR_abs p *)
      coR_abs_spec2 (pre_μ : PreAct) (p : P) : pre_μ ∈ ⌈ (αᴘʀᴏ ∘ αᴛᴇꜱᴛ) ⌉ (coR p) -> pre_μ ∈ (coR_abs p);
  }.

(** ** Termination condition *)
Definition bhv_pre_cond1 `{gLts P A, gLts Q A} 
  (p : P) (q : Q) := forall s, p ⇓ s -> q ⇓ s.

Notation "p ꜀ₙᵥ≼ₐₛ q" := (bhv_pre_cond1 p q) (at level 70).

(** ** Smyth preorder on acceptance sets *)
Definition bhv_pre_cond2 `{
  gLtsP : @gLts P A H, AbsPT : !AbsAction (gLtsT := gLtsT) P T (αᴛᴇꜱᴛ : A → FinA) (αᴘʀᴏP : FinA → PreAct),
  gLtsQ : @gLts Q A H, AbsQT : !AbsAction (gLtsT := gLtsT) Q T (αᴛᴇꜱᴛ : A → FinA) (αᴘʀᴏQ : FinA → PreAct)}
  (p : P) (q : Q) :=
  forall (s : trace A) q',
    p ⇓ s -> q ⟹[s] q' -> q' ↛ ->
    ∃ p', p ⟹[s] p' /\ p' ↛ /\ (⌈ (αᴘʀᴏP ∘ αᴛᴇꜱᴛ) ⌉ (coR p') ⊆ ⌈ (αᴘʀᴏQ ∘ αᴛᴇꜱᴛ) ⌉ (coR q')).

Notation "p ₐ꜀꜀≼ₐₛ q" := (bhv_pre_cond2 p q) (at level 70).

(** ** Definition of the alternative preorder based on acceptance-sets *)
Definition bhv_pre `{
  gLtsP : @gLts P A H, AbsPT : !AbsAction (gLtsT := gLtsT) P T (αᴛᴇꜱᴛ : A → FinA) (αᴘʀᴏP : FinA → PreAct),
  gLtsQ : @gLts Q A H, AbsQT : !AbsAction (gLtsT := gLtsT) Q T (αᴛᴇꜱᴛ : A → FinA) (αᴘʀᴏQ : FinA → PreAct)}
    (p : P) (q : Q) := 
      p ꜀ₙᵥ≼ₐₛ q /\ p ₐ꜀꜀≼ₐₛ q.

Notation "p ≼ₐₛ q" := (bhv_pre p q) (at level 70).

(* No need to define a Abstraction on toFW(L) if it is already define on L. *)
From TestingTheory Require Import MultisetLTSConstruction ForwarderConstruction.

#[global] Program Instance PreActActionForFW
  `{H : ExtAction A, !AbsAction (gLtsP := gLtsP) (gLtsT := gLtsT) P T (αᴛᴇꜱᴛ : A → FinA) (αᴘʀᴏ : FinA → PreAct)} {unique_nb : UniqueDual A}
  `{@Prop_of_Inter P (MO A) A A fw_inter H _ H MbgLts} 
  : AbsAction (gLtsT := gLtsT) (P * MO A) T αᴛᴇꜱᴛ αᴘʀᴏ. (* (toFW gLtsP) *)
Next Obligation.
  intros. eapply abstraction_test_spec in H4;eauto.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? (p1, m1) β β' b b' eq mem.
  assert (αᴛᴇꜱᴛ β ∈ ⌈ αᴛᴇꜱᴛ ⌉ coR (p1 ▷ m1)) as mem_h; eauto.
  destruct mem as (μ'' & mem & eq').
  destruct mem as (η''' & tr' & duo & b'').
  eapply lts_performs_spec1 in tr' as ((p , m) & tr'').
  inversion tr'';subst.
  - assert (αᴛᴇꜱᴛ β ∈ ⌈ αᴛᴇꜱᴛ ⌉ coR p1) as mem_h'.
    { rewrite eq'. eapply map_gamma_of_action. exists η'''.
      repeat split; eauto. eapply lts_performs_spec2;eauto. }
    eapply (abstraction_prog_spec p1 β β') in mem_h';eauto.
    destruct mem_h' as (β'' & eq'' & mem').
    exists β''. repeat split; eauto. destruct eq'' as (μ & tr & duo' & b''').
    exists μ. repeat split; eauto. eapply lts_performs_spec1 in tr as (p'' & tr).
    eapply lts_performs_spec2. exists (p'' ▷ m). eapply ParLeft. eauto.
  - destruct (decide (non_blocking η''')) as [nb''' | b'''].
    * eapply non_blocking_action_in_ms in l; eauto.
      subst. exists μ''. split.
      + exists η'''. repeat split. 
        -- eapply lts_performs_spec2;eauto.
        -- exact duo.
        -- exact b''.
      + rewrite<- eq'. admit.
    * eapply blocking_action_in_ms in l as (eq'' & duo'' & nb''); eauto.
      subst. eapply unique_nb in duo ; subst. contradiction.
Admitted.

#[global] Program Instance FinitaryPreActActionForFW `{CC : Countable PreAct} 
  `{H : ExtAction A, !FinitaryAbsAction (gLtsP := gLtsP) (gLtsT := gLtsT) P T (αᴛᴇꜱᴛ : A → FinA) (αᴘʀᴏ : FinA → PreAct) } {unique_nb : UniqueDual A}
  `{@Prop_of_Inter P (MO A) A A fw_inter H gLtsP H MbgLts} 
  : FinitaryAbsAction (gLtsP := (toFW gLtsP)) (gLtsT := gLtsT) (P * MO A) T αᴛᴇꜱᴛ αᴘʀᴏ :=
  {| coR_abs p := coR_abs p.1 ∪ dom (gmultiset_map (fun x => αᴘʀᴏ (αᴛᴇꜱᴛ (co x))) (MO_without_not_nb p.2));|}.
Next Obligation.
  intros.
  destruct p as (p, m).
  match goal with Hm : _ ∈ _ ∪ _ |- _ => eapply elem_of_union in Hm; destruct Hm as [in_p | in_M] end; simpl in *.
  + eapply coR_abs_spec1 in in_p.
    destruct in_p as (μ & mem & eq). subst.
    exists μ. split.
    - destruct mem as (μ' & tr & duo & b).
      eapply lts_performs_spec1 in tr as (p' & tr).
      exists μ'. repeat split; eauto.
      eapply lts_performs_spec2. exists (p' ▷ m).
      eapply ParLeft. exact tr.
    - eauto.
  + simpl in *. eapply gmultiset_elem_of_dom, elem_of_gmultiset_map in in_M.
    destruct in_M as (μ & eq & mem).
    exists (co μ). split; eauto.
    exists μ. repeat split ;eauto.
    - eapply lts_performs_spec2.
      assert (μ ∈ MO_without_not_nb m) as mem';eauto. 
      eapply lts_MO_nb_with_nb_spec1 in mem as (nb & mem).
      exists (p , m ∖ {[+ μ +]}).
      eapply ParRight.
      assert (m = {[+ μ  +]} ⊎ (m ∖ {[+ μ +]})) as eq''' by multiset_solver.
      rewrite eq''' at 1.
      eapply lts_multiset_minus. exact nb. 
    - exact (proj2_sig (exists_dual μ)).
    - eapply lts_MO_nb_with_nb_spec1 in mem as (nb & mem).
      eapply dual_blocks; eauto. symmetry. exact (proj2_sig (exists_dual μ)).
Qed.
Next Obligation.
  intros. match goal with Hm : _ ∈ ⌈ _ ⌉ _ |- _ => destruct Hm as (μ & mem & eq) end. subst.
  destruct p as (p, m). destruct mem as (μ' & tr & duo & b).
  eapply lts_performs_spec1 in tr as ((p' , m') & eq).
  inversion eq; subst; simpl in *.
  + eapply elem_of_union. left.
    eapply coR_abs_spec2.
    exists μ. repeat split ;eauto. exists μ'. repeat split; eauto.
    eapply lts_performs_spec2. eauto.
  + eapply elem_of_union. right.
    eapply gmultiset_elem_of_dom, elem_of_gmultiset_map.
    destruct (decide (non_blocking μ')) as [nb' | b'].
    - exists μ'. split ;eauto.
      * assert (μ = co μ'). { eapply unique_nb; eauto. }
        subst. eauto.
      * eapply non_blocking_action_in_ms in l;eauto. subst.
        eapply lts_MO_nb_with_nb_spec2;eauto.
        multiset_solver.
    - assert (blocking μ') as Imp; eauto.
      eapply blocking_action_in_ms in Imp as (mem' & duo' & nb'); eauto.
      eapply unique_nb in duo; eauto. subst. contradiction.
Qed.

Global Instance Proper_lts_pre_co_actions `{gLtsEq P A} `{Γ : A -> PreAct}:
  Proper ((eq_rel) ==> (≡)) (fun p => ⌈ Γ ⌉ (coR p)).
Proof.
  intros p p' Heq. intro μ_phi. split.
  (* apply leibniz_equiv. intros Hyp. split. *)
  - intro Hyp. destruct Hyp as (μ & mem_coR & eq);subst.
    destruct mem_coR as (μ' & accepts & duo & b).
    eapply accepts_preserved_by_eq in accepts;eauto.
    assert (μ ∈ coR p') as mem.
    { exists μ'. repeat split; eauto. }
    eapply map_gamma_of_action;eauto.
  - intro Hyp. destruct Hyp as (μ & mem_coR & eq);subst.
    destruct mem_coR as (μ' & accepts & duo & b). symmetry in Heq.
    eapply accepts_preserved_by_eq in accepts;eauto.
    assert (μ ∈ coR p) as mem.
    { exists μ'. repeat split; eauto. }
    eapply map_gamma_of_action;eauto.
Qed.

