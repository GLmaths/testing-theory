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

From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Equality.
From stdpp Require Import finite gmap decidable.
From Must Require Import ActTau gLts Bisimulation Lts_OBA Subset_Act WeakTransitions Testing_Predicate
    StateTransitionSystems InteractionBetweenLts Convergence Termination FiniteImageLTS.

(********************************************* Alt-preorder of Must_i **********************************************)


(********************************** Infinite Branching Lts to Finite Branching Lts **********************)
Class AbsAction `{H : ExtAction A} {E FinA : Type} (LtsE : @gLts E A H) (Φ : A → FinA) :=
  MkAbsAction {
    abstraction_test_spec β β' e : blocking β -> blocking β' -> (Φ β) = (Φ β') -> ¬ e ↛[ β ] -> ¬ e ↛[ β' ]
  }.


(********************************** PreCoAct modulo Finite Branching Lts on Test **********************)
Class PreExtAction `{H : ExtAction A} {P FinA: Type} `{Countable PreAct} 
  {𝝳 : FinA → PreAct} {Φ : A → FinA} (LtsP : @gLts P A H) :=
  MkPreExtAction {
      pre_co_actions_of_fin : P -> FinA -> Prop ;

      preactions_of_fin_test_spec1 (β : A) (p : P) : β ∈ co_actions_of p -> (Φ β) ∈ (pre_co_actions_of_fin p);
      preactions_of_fin_test_spec2 (pre_β : FinA) (p : P) : pre_β ∈ (pre_co_actions_of_fin p)
            -> ∃ β', β' ∈ co_actions_of p /\ pre_β = (Φ β');

      pre_co_actions_of : P -> gset PreAct;
      preactions_of_spec (pre_β : FinA) (p : P) : pre_β ∈ (pre_co_actions_of_fin p) <-> (𝝳 pre_β) ∈ (pre_co_actions_of p);
  }.

From Must Require Import ParallelLTSConstruction.

Definition parallel_inter_trace
  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}
  (s' : trace A) (s : trace A) : Prop := Forall2 parallel_inter s' s.

Definition co_cnv `{gLtsT : @gLts T A H}
  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}
  (p : P) (s : trace A) : Prop :=
  forall s', parallel_inter_trace s' s -> p ⇓ s'.

Notation "p ⇓ᶜᵒ s" := (co_cnv p s) (at level 30, format "p ⇓ᶜᵒ s").

Lemma co_cnv_if_cnv
  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}
  `{@Prop_of_Inter Q T A parallel_inter H gLtsQ gLtsT}
  (p : P) (q : Q) : (forall s', p ⇓ s' -> q ⇓ s') -> (forall s , p ⇓ᶜᵒ s -> q ⇓ᶜᵒ s).
Proof.
  intros Hyp s conv s' inter_trace.
  eapply Hyp. eapply conv. exact inter_trace.
Qed.

Lemma co_cnv_nil `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT} :
  ∀ p : P, p ⤓ → p ⇓ᶜᵒ ε.
Proof.
  intros. intros s inter_trace.
  inversion inter_trace; subst.
  eapply cnv_nil. eauto.
Qed.

Lemma co_cnv_act `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT} :
  ∀ (p : P) (μ' : A) (s : trace A),
                p ⤓ → (∀ q : P , ∀ μ : A, p ⟹{μ} q → parallel_inter μ μ' → q ⇓ᶜᵒ s) 
              → p ⇓ᶜᵒ (μ' :: s).
Proof.
  intros. intros s0 inter_trace.
  inversion inter_trace; subst.
  eapply cnv_act. eauto.
  intros q wt.
  eapply H2 in wt; eauto.
Qed.

Lemma parallel_inter_co_trace `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT} s :
  Forall2 parallel_inter (list_fmap A A (λ x : A, co x) s) s.
Proof.
  dependent induction s.
  + simpl. constructor.
  + simpl in *. constructor.
    * destruct (exists_dual a) as (x & duo).
      symmetry. eauto.
    * eauto.
Qed.

Lemma co_cnv_terminate `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT} :
  ∀ (p : P) (s : trace A), p ⇓ᶜᵒ s → p ⤓.
Proof.
  intros p s co_conv. eapply cnv_terminate.
  eapply co_conv. instantiate (1 := (fmap (fun x => co x) s)).
  { revert co_conv. dependent induction s.
    + simpl. constructor.
    + simpl in *. constructor.
      * destruct (exists_dual a) as (x & duo).
        unfold parallel_inter. symmetry. eauto.
      * eapply (@parallel_inter_co_trace P T). eauto. }
Qed.

Lemma co_cnv_preserved_by_lts_tau `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT} :
     ∀ (s : trace A) (p : P),
         p ⇓ᶜᵒ s → ∀ q : P, p ⟶ q → q ⇓ᶜᵒ s.
Proof.
  intros. intros s0 inter_trace.
  eapply cnv_preserved_by_lts_tau; eauto.
Qed.

Definition bhv_pre_cond1 `{@gLts P A H, @gLts Q A H}
  `{@Prop_of_Inter P T A parallel_inter H gLtsP gLtsT}
  `{@Prop_of_Inter Q T A parallel_inter H gLtsQ gLtsT}
  (p : P) (q : Q) := forall s, p ⇓ᶜᵒ s -> q ⇓ᶜᵒ s.

Notation "p ≼₁ q" := (bhv_pre_cond1 p q) (at level 70).

Definition bhv_pre_cond2 `{
  gLtsP : @gLts P A H, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  gLtsQ : @gLts Q A H, PreAQ : @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @Prop_of_Inter P T A parallel_inter H gLtsP gLtsT,@Prop_of_Inter Q T A parallel_inter H gLtsQ gLtsT
  }
  (p : P) (q : Q) :=
  forall (s : trace A) (s' : trace A) (q' : Q),
    p ⇓ᶜᵒ s -> Forall2 parallel_inter s' s -> q ⟹[s'] q' -> q' ↛ ->
    ∃ (p' : P) (s'' : trace A) , Forall2 parallel_inter s'' s /\ p ⟹[s''] p' /\ p' ↛
    /\ (pre_co_actions_of p' ⊆ pre_co_actions_of q').

Notation "p ≼₂ q" := (bhv_pre_cond2 p q) (at level 70).

Definition bhv_pre (* `{PreA_countable : Countable PreA} *)
  `{
  gLtsP : @gLts P A H, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  gLtsQ : @gLts Q A H, PreAQ : @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @Prop_of_Inter P T A parallel_inter H gLtsP gLtsT, @Prop_of_Inter Q T A parallel_inter H gLtsQ gLtsT
  }
    (p : P) (q : Q) := 
      p ≼₁ q /\ p ≼₂ q.

Notation "p ≼ₐₛ q" := (bhv_pre p q) (at level 70).

