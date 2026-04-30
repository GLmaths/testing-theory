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

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Program Require Import Equality Basics.
From stdpp Require Import finite gmap decidable gmultiset.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Subset_Act WeakTransitions Testing_Predicate
    StateTransitionSystems InteractionBetweenLts Convergence Termination FiniteImageLTS Subset_Act.

(* * Alternative preorder for Must based on acceptance-sets *)

(** ** Label abstractions *)

Class AbsAction {P T FinA PreAct: Type} (A : Type) (H : ExtAction A) (Φ : A → FinA) (𝝳 : FinA → PreAct) {gLtsP : gLts P H} {gLtsT : gLtsEq T H} :=
  MkAbsAction {
    (** Client-side condition for label abstractions , Definition 5 (1) **)
    abstraction_test_spec (t : T) (β : A) (β' : A) : blocking β -> blocking β' -> (Φ β) = (Φ β') -> β ∈ (R t)-> β' ∈ (R t);
    (** Server-side condition for label abstractions,  Definition 5 (2) **)
    abstraction_prog_spec (p : P) β β' : blocking β -> blocking β' -> 𝝳 (Φ β) = 𝝳 (Φ β') -> (Φ β) ∈ map_set Φ (coR p) -> (Φ β') ∈ map_set Φ (coR p);
  }.

Arguments AbsAction {_} {_} {_} {_} A H Φ 𝝳 {_} {_}.


(** ** Finitary Label abstractions *)

Class FinitaryAbsAction P T {FinA PreAct: Type} (A : Type) (H : ExtAction A) (Φ : A → FinA) (𝝳 : FinA → PreAct) {gLtsP : gLts P H} {gLtsT : gLtsEq T H}
  `{Countable PreAct} :=
  MkFinitaryAbsAction {
      FinitaryAbsAction_Abs :: @AbsAction P T FinA PreAct A H Φ 𝝳 gLtsP gLtsT;

      (* 𝝳 (Φ (coR p)) is a finite set, called (coR_abs p) *)
      coR_abs : P -> gset PreAct;
      coR_abs_spec1 (p : P) (pre_μ : PreAct) : pre_μ ∈ (coR_abs p) -> pre_μ ∈ ⌈ (𝝳 ∘ Φ) ⌉ (coR p);
      coR_abs_spec2 (pre_μ : PreAct) (p : P) : pre_μ ∈ ⌈ (𝝳 ∘ Φ) ⌉ (coR p) -> pre_μ ∈ (coR_abs p);
  }.

(** ** Termination condition *)
Definition bhv_pre_cond1 `{gLts P A, gLts Q A} 
  (p : P) (q : Q) := forall s, p ⇓ s -> q ⇓ s.

Notation "p ≼₁ q" := (bhv_pre_cond1 p q) (at level 70).

(** ** Smyth preorder on acceptance sets *)
Definition bhv_pre_cond2 `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P  gLtsP gLtsT,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q  gLtsQ gLtsT}
  (p : P) (q : Q) :=
  forall (s : trace A) q',
    p ⇓ s -> q ⟹[s] q' -> q' ↛ ->
    ∃ p', p ⟹[s] p' /\ p' ↛ /\ (⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q')).

Notation "p ≼₂ q" := (bhv_pre_cond2 p q) (at level 70).

(** ** Definition of the alternative preorder *)
Definition bhv_pre `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P  gLtsP gLtsT,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q  gLtsQ gLtsT}
    (p : P) (q : Q) := 
      p ≼₁ q /\ p ≼₂ q.

Notation "p ≼ₐₛ q" := (bhv_pre p q) (at level 70).

(* No need to define a Abstraction on toFW(L) if it is already define on L. *)
From TestingTheory Require Import MultisetLTSConstruction ForwarderConstruction.

#[global] Program Instance PreActActionForFW
  `{@AbsAction P T FinA PreAct A H Φ 𝝳 gLtsP gLtsT}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts} 
  : @AbsAction (P * mb A) T FinA PreAct A H Φ 𝝳 (FW_gLts gLtsP) gLtsT.
Next Obligation.
  intros. eapply abstraction_test_spec in H4;eauto.
Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? ? ? (p1, m1) β β' b b' eq mem.

  assert (Φ β ∈ ⌈ Φ ⌉ coR (p1 ▷ m1)) as mem_h; eauto.
  destruct mem as (μ'' & mem & eq').
  destruct mem as (μ''' & tr' & duo & b'').
  eapply lts_refuses_spec1 in tr' as ((p , m) & tr'').
  inversion tr'';subst.
  - assert (Φ β ∈ ⌈ Φ ⌉ coR p1) as mem_h'.
    { rewrite eq'. eapply map_gamma_of_action. exists μ'''.
      repeat split; eauto. eapply lts_refuses_spec2;eauto. }
    eapply (abstraction_prog_spec p1 β β') in mem_h';eauto.
    destruct mem_h' as (β'' & eq'' & mem').
    exists β''. repeat split; eauto. destruct eq'' as (μ & tr & duo' & b''').
    exists μ. repeat split; eauto. eapply lts_refuses_spec1 in tr as (p'' & tr).
    eapply lts_refuses_spec2. exists (p'' ▷ m). eapply ParLeft. eauto.
  - destruct (decide (non_blocking μ''')) as [nb''' | b'''].
    * eapply non_blocking_action_in_ms in l; eauto.
       subst. admit.
    * eapply blocking_action_in_ms in l as (eq'' & duo'' & nb''); eauto.
      subst. eapply unique_nb in duo ; subst. contradiction.
Admitted.

#[global] Program Instance FinitaryPreActActionForFW `{CC : Countable PreAct} 
  `{@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 gLtsP gLtsT _ _ }
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts} 
  : @FinitaryAbsAction (P * mb A) T FinA PreAct A H Φ 𝝳 (FW_gLts gLtsP) gLtsT _ _ :=
  {| coR_abs p := coR_abs p.1 ∪ dom (gmultiset_map (fun x => 𝝳 (Φ (co x))) (mb_without_not_nb p.2));|}.
Next Obligation.
  intros.
  destruct p. eapply elem_of_union in H2. destruct H2 as [in_p | in_M] ; simpl in *.
  + eapply coR_abs_spec1 in in_p.
    destruct in_p as (μ & mem & eq). subst.
    exists μ. split.
    - destruct mem as (μ' & tr & duo & b).
      eapply lts_refuses_spec1 in tr as (p' & tr).
      exists μ'. repeat split; eauto.
      eapply lts_refuses_spec2. exists (p' ▷ m).
      eapply ParLeft. exact tr.
    - eauto.
  + simpl in *. eapply gmultiset_elem_of_dom, elem_of_gmultiset_map in in_M.
    destruct in_M as (μ & eq & mem).
    exists (co μ). split; eauto.
    exists μ. repeat split ;eauto.
    - eapply lts_refuses_spec2.
      assert (μ ∈ mb_without_not_nb m) as mem';eauto. 
      eapply lts_mb_nb_with_nb_spec1 in mem as (nb & mem).
      exists (p , m ∖ {[+ μ +]}).
      eapply ParRight.
      assert (m = {[+ μ  +]} ⊎ (m ∖ {[+ μ +]})) as eq''' by multiset_solver.
      rewrite eq''' at 1.
      eapply lts_multiset_minus. exact nb. 
    - exact (proj2_sig (exists_dual μ)).
    - eapply lts_mb_nb_with_nb_spec1 in mem as (nb & mem).
      eapply dual_blocks; eauto. symmetry. exact (proj2_sig (exists_dual μ)).
Qed.
Next Obligation.
  intros. destruct H2 as (μ & mem & eq). subst.
  destruct p. destruct mem as (μ' & tr & duo & b).
  eapply lts_refuses_spec1 in tr as ((p' , m') & eq).
  inversion eq; subst; simpl in *.
  + eapply elem_of_union. left.
    eapply coR_abs_spec2.
    exists μ. repeat split ;eauto. exists μ'. repeat split; eauto.
    eapply lts_refuses_spec2. eauto.
  + eapply elem_of_union. right.
    eapply gmultiset_elem_of_dom, elem_of_gmultiset_map.
    destruct (decide (non_blocking μ')) as [nb' | b'].
    - exists μ'. split ;eauto.
      * assert (μ = co μ'). { eapply unique_nb; eauto. }
        subst. eauto.
      * eapply non_blocking_action_in_ms in l;eauto. subst.
        eapply lts_mb_nb_with_nb_spec2;eauto.
        multiset_solver.
    - assert (blocking μ') as Imp; eauto.
      eapply blocking_action_in_ms in Imp as (mem' & duo' & nb'); eauto.
      eapply unique_nb in duo; eauto. subst. contradiction.
Qed.



