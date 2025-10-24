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

From Coq Require ssreflect Setoid.
From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
Import ListNotations.
From Coq.Program Require Import Wf Equality.
From Coq.Wellfounded Require Import Inverse_Image.
From Coq.Logic Require Import JMeq ProofIrrelevance.
From stdpp Require Import sets base countable finite gmap list finite decidable finite gmap.
From Must Require Import gLts Bisimulation Lts_OBA WeakTransitions Lts_OBA_FB Lts_FW FiniteImageLTS
      InteractionBetweenLts MultisetLTSConstruction ParallelLTSConstruction ForwarderConstruction
       Must Lift Subset_Act Convergence Termination Testing_Predicate DefinitionAS.
From Must Require Import ActTau.

(** Test generators specification. **)

Class gen_spec (* {E A : Type} *)
  `{gLts E A, !gLtsEq E A, !Testing_Predicate E A attaboy}
  (co_of : A -> A) (gen : list A -> E) := {
            co_inter μ : parallel_inter μ (co_of μ);
                (* co_of μ interract with μ *)
            co_inter_spec1 μ μ': 
                parallel_inter μ' (co_of μ)
                          -> μ = μ';
                (* co_of μ interract only with μ *)
    (* 1 *) gen_spec_unattaboy : 
              forall s, ¬ attaboy (gen s) ;
    (* 2 *) gen_spec_mu_lts_co μ1 (* μ2 *) s :
              gen (μ1 :: s) ⟶⋍[co_of μ1] gen s;
    (* 3 *) gen_spec_co_not_nb_lts_tau_ex μ s : 
              ¬ non_blocking (co_of μ) ->
              ∃ e', gen (μ :: s) ⟶ e';
    (* 4 *) gen_spec_co_not_nb_lts_tau_attaboy μ s e : 
              ¬ non_blocking (co_of μ) ->
              gen (μ :: s) ⟶ e -> attaboy e;
    (* 5 *) gen_spec_mu_lts_not_nb_determinacy {μ s e}:
               ¬ non_blocking (co_of μ) ->
              gen (μ :: s) ⟶[co_of μ] e -> e ⋍ gen s;

    (* 6 *) gen_spec_mu_lts_not_nb_side_effect {e μ μ' s} :
              ¬ non_blocking (co_of μ) ->
              gen (μ :: s) ⟶[μ'] e -> μ' ≠ co_of μ -> attaboy e ;
  }.

Lemma co_of_inj `{
  gLts E A, !gLtsEq E A, !Testing_Predicate E A attaboy, !gen_spec co_of f}
  μ μ' :
  co_of μ = co_of μ' -> μ = μ'.
Proof.
  intro eq. 
  assert (parallel_inter μ' (co_of μ)) as inter. rewrite eq.
  eapply co_inter. eapply co_inter_spec1. exact inter.
Qed.

Lemma co_co_is_id `{
  gLts E A, !gLtsEq E A, !Testing_Predicate E A attaboy, !gen_spec co_of f} 
  μ :
  μ = co_of (co_of μ).
Proof.
  assert (parallel_inter (co_of (co_of μ)) (co_of μ)) as inter.
  symmetry. eapply co_inter.
  eapply co_inter_spec1. exact inter.
Qed.

Lemma co_is_co_of_nb `{
  gLts E A, !gLtsEq E A, !Testing_Predicate E A attaboy, !gen_spec co_of f} 
  μ :
  non_blocking (co_of μ) -> co_of μ = co μ.
Proof.
  intro nb. assert (parallel_inter μ (co_of μ)) as inter.
  eapply co_inter. 
  eapply unique_nb; eauto.
Qed.

Lemma co_of_is_co_nb `{
  gLts E A, !gLtsEq E A, !Testing_Predicate E A attaboy, !gen_spec co_of f} 
  μ :
  non_blocking (co μ) -> dual (co μ) μ -> co_of μ = co μ.
Proof.
  intros nb duo.
  assert (parallel_inter μ (co_of μ)) as inter. eapply co_inter.
  assert (¬ non_blocking μ) as not_nb. eapply dual_blocks in nb ; eauto.
  eapply unique_nb; eauto.
  assert (¬ non_blocking (co_of (co μ))) as not_nb'.
  eapply dual_blocks in nb ; eauto. symmetry. eapply co_inter.
  eapply nb_not_nb; eauto.
Qed.

Lemma gen_spec_determinacy `{
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec co_of f} 
  μ1 s e:
  f (μ1 :: s) ⟶[co_of μ1] e -> e ⋍ f s.
Proof.
  intro HypTr.
  destruct (decide (non_blocking (co_of μ1))) as [nb | not_nb].
  + assert (f (μ1 :: s) ⟶⋍[co_of μ1] f s) as (e' & Tr & Eq). eapply gen_spec_mu_lts_co.
    assert (e' ⋍ e) as equiv. eapply lts_oba_non_blocking_action_deter; eauto.
    etransitivity; eauto. symmetry; eauto.
  + eapply gen_spec_mu_lts_not_nb_determinacy in not_nb as equiv; eauto.
Qed.

Class gen_spec_conv
  `{gLts E A, ! gLtsEq E A, !Testing_Predicate E A attaboy}
  (co_of : A -> A) (gen_conv : list A -> E) := {
    gen_conv_spec_gen_spec : gen_spec co_of gen_conv ;
    (* c1 *) gen_spec_conv_nil_refuses_mu μ : gen_conv ε ↛[μ] ;
    (* c2 *) gen_spec_conv_nil_lts_tau_ex : ∃ e', gen_conv ε ⟶ e';
    (* c2 *) gen_spec_conv_nil_lts_tau_attaboy e : gen_conv ε ⟶ e -> attaboy e;
  }.

#[global] Existing Instance gen_conv_spec_gen_spec.

(* Definition union_of_co_actions_without `{gLts P A} `{gLts Q A}
  (p_L : list P * Q) := (⋃ map co_actions_of p_L.1) ∖ (co_actions_of p_L.2).

Definition union_of_pre_co_actions_without 
  `{gLtsP : @gLts P A H, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  `{gLtsQ : @gLts Q A H, PreAQ : @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ}
  (p_L : list P * Q) := ⋃ map pre_co_actions_of p_L.1 ∖ (pre_co_actions_of p_L.2). *)

Class gen_spec_acc (PreA : Type) `{CC : Countable PreA}
  `{gLtsE : @gLts E A H, ! gLtsEq E A, !Testing_Predicate E A attaboy}
  (co_of : A -> A) (gen_acc : gset PreA -> list A -> E) (Γ : A -> PreA)
    := {
    gen_acc_spec_gen_spec (L : gset PreA) : gen_spec co_of (gen_acc L) ;
    (* t1 *) gen_spec_acc_nil_refuses_tau (L : gset PreA) : 
                gen_acc L ε ↛ ; 
    (* t2 *) gen_spec_acc_nil_refuses_nb (L : gset PreA) η : 
                non_blocking η -> gen_acc L ε ↛[η] ;
  (* t4-> *) gen_spec_acc_nil_mu_inv (L : gset PreA) μ e : 
                ¬ non_blocking μ -> gen_acc L ε ⟶[μ] e
                    -> (Γ μ) ∈ L ;
  (* t4<- *) gen_spec_acc_nil_mem_lts_inp (L : gset PreA) pη : 
                pη ∈ L -> 
                ∃ r μ, gen_acc L ε ⟶[μ] r /\ (Γ μ = pη);
    (* t3 *) gen_spec_acc_nil_lts_not_nb_attaboy μ e' (L : gset PreA) : 
                ¬ non_blocking μ -> gen_acc L ε ⟶[μ] e' -> attaboy e' ;
  }.

#[global] Existing Instance gen_acc_spec_gen_spec.

(* Lemma co_inter' `{CC : Countable PreA} `{
  @gLts E A H, ! gLtsEq E A, !Testing_Predicate E A attaboy, !gen_spec_acc co_of gen_acc Γ}
  μ :
  parallel_inter μ (co_of μ).
Proof.
  eapply co_inter. Unshelve. eauto.
Qed.

Lemma co_inter_spec1' {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @gLts E A H, AbE : @AbsAction A H E FinA gLtsE Φ, ! gLtsEq E A, !Testing_Predicate E A attaboy, !gen_spec_acc P Q co_of gen_acc}
  `{L : gset PreA}
  μ μ' :
  parallel_inter μ' (co_of μ)
                          -> μ = μ'.
Proof.
  eapply co_inter_spec1. Unshelve. eauto.
Qed.

Lemma co_of_inj' {P Q : Type}  `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @gLts E A H, AbE : @AbsAction A H E FinA gLtsE Φ, ! gLtsEq E A, !Testing_Predicate E A attaboy, !gen_spec_acc P Q co_of gen_acc}
  `{L : gset PreA}
  μ μ' :
  co_of μ = co_of μ' -> μ = μ'.
Proof.
  eapply co_of_inj. Unshelve. eauto.
Qed.

Lemma co_co_is_id' {P Q : Type}  `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @gLts E A H, AbE : @AbsAction A H E FinA gLtsE Φ, ! gLtsEq E A, !Testing_Predicate E A attaboy, !gen_spec_acc P Q co_of gen_acc}
  `{L : gset PreA}
  μ :
  μ = co_of (co_of μ).
Proof.
  eapply co_co_is_id. Unshelve. eauto.
Qed.

Lemma co_is_co_of_nb' {P Q : Type}  `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @gLts E A H, AbE : @AbsAction A H E FinA gLtsE Φ, ! gLtsEq E A, !Testing_Predicate E A attaboy, !gen_spec_acc P Q co_of gen_acc }
  `{L : gset PreA}
  μ :
  non_blocking (co_of μ) -> co_of μ = co μ.
Proof.
  eapply co_is_co_of_nb. Unshelve. eauto.
Qed.

Lemma co_of_is_co_nb' {P Q : Type}  `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @gLts E A H, AbE : @AbsAction A H E FinA gLtsE Φ, ! gLtsEq E A, !Testing_Predicate E A attaboy, !gen_spec_acc P Q co_of gen_acc }
  `{L : gset PreA}
  μ :
  non_blocking (co μ) -> dual (co μ) μ -> co_of μ = co μ.
Proof.
  eapply co_of_is_co_nb. Unshelve. eauto.
Qed. *)

(* Facts about test generators. *)

Lemma gen_conv_always_reduces `{
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec_conv co_of gen_conv} s :
  ∃ e, gen_conv s ⟶ e.
Proof.
  induction s as [|μ s'].
  - eapply gen_spec_conv_nil_lts_tau_ex.
  - destruct (decide (non_blocking (co_of μ))) as [nb | not_nb]. 
    + destruct IHs' as (e & l).
      destruct (gen_spec_mu_lts_co μ s') as (e' & hl' & heq).
      destruct (eq_spec e' e τ) as (e0 & hl0 & heqe0). eauto with mdb.
      destruct (lts_oba_non_blocking_action_delay nb hl' hl0)
        as (r & l1 & l2); eauto.
    + eapply gen_spec_co_not_nb_lts_tau_ex. exact not_nb.
Qed.

Lemma terminate_must_test_conv_nil `{
  gLtsP : gLts P A, 
  gLtsE : !gLts E A, !gLtsEq E A, !Testing_Predicate E A attaboy, !gen_spec_conv co_of gen_conv}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) : 
  p ⤓ -> must p (gen_conv ε).
Proof.
  intros ht.
  induction ht.
  eapply m_step; eauto with mdb.
  - eapply gen_spec_unattaboy.
  - destruct gen_spec_conv_nil_lts_tau_ex as (e' & l); eauto with mdb.
    exists (p ▷ e'). eapply ParRight; eauto.
  - intros e' l. eapply gen_spec_conv_nil_lts_tau_attaboy in l. eauto with mdb.
  - intros p0 e0 μ μ' inter l1 l2.
    exfalso. eapply lts_refuses_spec2.
    exists e0. eassumption. eapply gen_spec_conv_nil_refuses_mu.
Qed.

Lemma must_gen_conv_wta_mu `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Testing_Predicate E A attaboy, ! gen_spec_conv co_of gen_conv}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  μ s (p q : P): 
  must p (gen_conv (μ :: s)) -> 
    p ⟹{μ} q -> must q (gen_conv s).
Proof.
  intros hm w.
  dependent induction w.
  + eapply IHw; eauto with mdb.
    eapply must_preserved_by_lts_tau_srv; eauto.
  + edestruct gen_spec_mu_lts_co as (t' & hlt' & heqt').
    (* edestruct gen_spec_mu_lts_co as (t' & hlt' & heqt'). *)
    eapply (must_eq_client _ _ _ heqt').
    eapply (must_preserved_by_weak_nil_srv q t); eauto.
    eapply must_preserved_by_synch_if_notattaboy; eauto with mdb.
    eapply gen_spec_unattaboy. eapply co_inter.
Qed.

(** First implication of the first requirement. *)

Lemma cnv_if_must `{
  gLtsP : gLts P A, 
  gLtsE : !gLts E A, !gLtsEq E A, !Testing_Predicate E A attaboy, !gen_spec_conv co_of gen_conv}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  s (p : P) : 
  must p (gen_conv s) -> p ⇓ s.
Proof.
  revert p.
  induction s as [|μ s']; intros p hm.
  - eapply cnv_nil.
    eapply (must_terminate_unattaboy _ _ hm), gen_spec_unattaboy.
  - eapply cnv_act.
    + eapply (must_terminate_unattaboy _ _ hm), gen_spec_unattaboy.
    + intros q w. eapply IHs', must_gen_conv_wta_mu; eauto.
Qed.

Lemma f_gen_lts_mu_in_the_middle `{
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec co_of f} 
  s1 s2 μ:
  Forall exist_co_nba s1
    -> f (s1 ++ μ :: s2) ⟶⋍[co_of μ] f (s1 ++ s2).
Proof.
  revert s2 μ.
  induction s1 as [|ν s']; intros s2 μ his ; simpl in *.
  - eapply (gen_spec_mu_lts_co μ).
  - inversion his as [| ? ? (b & nb & duo) his']. subst.
    destruct (IHs' s2 μ his') as (r & hlr & heqr).
    edestruct (gen_spec_mu_lts_co ν (s' ++ μ :: s2))
      as (t & hlt & heqt).
    assert (non_blocking (co_of ν)) as nb'. eapply nb_not_nb; eauto.
    assert (b = co ν). eapply unique_nb; eauto. subst.
    eapply co_inter.
    edestruct (eq_spec t r) as (u & hlu & hequ). eauto with mdb.
    destruct (lts_oba_non_blocking_action_delay nb' hlt hlu)
      as (v & l1 & (t' & l2 & heq')).
    exists v. split. eassumption.
    destruct (gen_spec_mu_lts_co ν (s' ++ s2)) as (w & hlw & heqw).
    eapply lts_oba_non_blocking_action_deter_inv; try eassumption.
    etrans. eauto. etrans. eauto. etrans. eauto. now symmetry.
Qed.

Lemma f_gen_lts_mu_in_the_middle' `{
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec co_of f} 
  s1 s2 μ p:
  Forall exist_co_nba s1
    -> f (s1 ++ μ :: s2) ⟶⋍[co_of μ] p -> p ⋍ f (s1 ++ s2).
Proof.
  revert s2 μ p.
  induction s1 as [|ν s']; intros s2 μ p his HypTr; simpl in *.
  - destruct (decide (non_blocking (co_of μ))) as [nb | not_nb].
    + assert (f (ε ++ μ :: s2) ⟶⋍[co_of μ] f (ε ++ s2)) as HypTr'.
      eapply f_gen_lts_mu_in_the_middle. eauto.
      destruct HypTr as (e & HypTr & equiv).
      destruct HypTr' as (e' & HypTr' & equiv').
      simpl in *. assert (e ⋍ e').
      eapply lts_oba_non_blocking_action_deter; eauto. 
      etransitivity. symmetry. exact equiv. etransitivity; eauto.
    + destruct HypTr as (e & HypTr & equiv).
      assert (e ⋍ f s2) as equiv'. 
      eapply gen_spec_mu_lts_not_nb_determinacy; eauto.
      etransitivity. symmetry. exact equiv. eauto.
  - inversion his; subst.
    destruct (decide (non_blocking (co_of μ))) as [nb | not_nb].
    + assert (f ((ν :: s') ++ μ :: s2) ⟶⋍[co_of μ] f ((ν :: s') ++ s2)) as HypTr'.
      eapply f_gen_lts_mu_in_the_middle. eauto.
      destruct HypTr as (e & HypTr & equiv).
      destruct HypTr' as (e' & HypTr' & equiv').
      assert (e ⋍ e').
      eapply lts_oba_non_blocking_action_deter; eauto. 
      etransitivity. symmetry. exact equiv. etransitivity; eauto.
    + destruct HypTr as (e & HypTr & equiv).
      destruct (decide (non_blocking (co_of ν))) as [nb' | not_nb'].
      ++ assert (f (ν :: s' ++ μ :: s2) ⟶⋍[co_of ν] f (s' ++ μ :: s2)) as HypTr'.
         eapply gen_spec_mu_lts_co. destruct HypTr' as (e' & HypTr' & equiv').
         assert (co_of μ <> co_of ν) as not_eq. intro imp. rewrite imp in not_nb. contradiction.
         destruct (lts_oba_non_blocking_action_confluence nb' not_eq HypTr' HypTr )
           as (t' & l2 & (t & l1 & heq)).
         assert (f (s' ++ μ :: s2) ⟶⋍[co_of μ] f (s' ++ s2)) as HypTr''.
         eapply f_gen_lts_mu_in_the_middle; eauto.
         edestruct (eq_spec (f (s' ++ μ :: s2)) t' (ActExt (co_of μ)))
          as (v & hlv & heqv).
         exists e'. split; eauto. symmetry; eauto.
         assert (t' ⋍ (f (s' ++ s2))) as heq'. eapply IHs'; eauto.
         exists v. split; eauto.
         assert (f (ν :: s' ++ s2) ⟶⋍[co_of ν] f (s' ++ s2)) as (v' & hlv' & heqv').
         eapply gen_spec_mu_lts_co.
         assert (e ⋍ f (ν :: s' ++ s2)) as final. 
         eapply lts_oba_non_blocking_action_deter_inv; eauto.
         etransitivity. exact heq. etransitivity. exact heq'. symmetry; eauto.
         etransitivity. symmetry. exact equiv. eauto.
      ++ destruct H3 as (ν' & nb & duo).
         assert (parallel_inter ν (co_of ν)). eapply co_inter.
         assert (non_blocking (co_of ν)).
         eapply nb_not_nb; eauto. contradiction.
Qed.


Lemma side_effect_by_blocking_action `{
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec co_of f} 
  s μ μ' e:
  ¬ non_blocking (co_of μ) -> f (μ :: s) ⟶[μ'] e -> ¬ non_blocking μ'.
Proof.
  intros not_nb HypTr.
  intro nb. destruct (decide (μ' = co_of μ)) as [eq | neq].
  + subst ;eauto.
  + assert (attaboy e).
    { eapply gen_spec_mu_lts_not_nb_side_effect; eauto. }
    assert (attaboy (f (μ :: s))).
    { eapply attaboy_preserved_by_lts_non_blocking_action_converse; eauto. }
    assert (¬ attaboy (f (μ :: s))).
    { eapply gen_spec_unattaboy; eauto. }
    contradiction.
Qed.

Lemma f_gen_lts_mu_in_the_middle_not_nb_or_neq `{
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec co_of f} 
  s1 s2 μ μ' e:
  Forall exist_co_nba s1 -> ¬ non_blocking (co_of μ) -> μ' ≠ co_of μ -> ¬ non_blocking μ'
    -> f (s1 ++ μ :: s2) ⟶[μ'] e -> attaboy e.
Proof.
  revert s2 μ μ' e.
  induction s1 as [|ν s']; intros s2 μ μ' e his not_nb neq not_nb' HypTr; simpl in *.
  - eapply gen_spec_mu_lts_not_nb_side_effect; eauto.
  - inversion his as [| ? ? (b & nb & duo) his'];subst.
    assert (non_blocking (co_of ν)) as nb'.
    { eapply nb_not_nb; eauto. eapply co_inter. }
    assert (f (ν :: (s' ++ μ :: s2)) ⟶⋍[co_of ν] f (s' ++ μ :: s2)) as (e'' & hl & equiv).
    { eapply gen_spec_mu_lts_co; eauto. }
    assert (b = co ν). 
    { eapply unique_nb; eauto. } subst.
    destruct (decide (μ' = co_of ν)) as [eq' | neq'].
    + subst. contradiction. 
    + edestruct (lts_oba_non_blocking_action_confluence nb' neq' hl HypTr) 
      as (p' & HypTr''' & p'' & HypTr'' & equiv''').
      edestruct (eq_spec (f (s' ++ μ :: s2)) p') as (t' & HypTr' & equiv'').
      { symmetry in equiv. eauto. }
      assert (attaboy t') as happy.
      { eapply IHs' ;eauto. }
      eapply attaboy_preserved_by_lts_non_blocking_action_converse; eauto.
     eapply attaboy_preserved_by_eq; eauto. etransitivity ;eauto. now symmetry.
Qed.

Lemma inversion_gen_mu_not_nb `{
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec co_of f} 
  s μ' p :
  (forall μ, f ε ↛[μ] \/ (forall e, f ε ⟶[μ] e -> attaboy e)) ->
  f s ⟶[μ'] p ->
  ¬ non_blocking μ' -> 
  attaboy p \/
  ∃  s1 s2 μ, s = s1 ++ μ :: s2 
  /\ p ⋍ f (s1 ++ s2)
  /\ μ' = co_of μ
  /\ Forall exist_co_nba s1.
Proof.
  revert μ' p.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros μ p h l not_nb.
  - edestruct (h μ) as [refuses_f | f_to_attaboy].
    + now eapply lts_refuses_spec2 in refuses_f; eauto.
    + left. eapply f_to_attaboy. eauto.
  - destruct (decide (non_blocking (co_of ν))) as [nb' | not_nb'].
    + assert (f (ν :: s') ⟶⋍[co_of ν] f s') as (v & hlv & eqv).
      eapply gen_spec_mu_lts_co. assert (μ <> (co_of ν)) as not_eq.
      eapply BlockingAction_are_not_non_blocking; eauto.
      destruct (lts_oba_non_blocking_action_confluence nb' not_eq hlv l)
           as (t' & l2 & (t & l1 & heq)).
      destruct (eq_spec (f s') t' (ActExt μ)) as (v' & hlv' & heqv').
      exists v. split. symmetry; eauto. exact l2.
      destruct (decide (attaboy v')) as [happy' | not_happy'].
      ++ left. eapply attaboy_preserved_by_lts_non_blocking_action_converse; eauto.
         eapply attaboy_preserved_by_eq; eauto. etransitivity; eauto. symmetry. eauto.
      ++ edestruct (Hlength s') as [happy | (s1 & s2 & μ' & eq & equiv & eq_action & his)]; eauto.
         +++ contradiction.
         +++ right. subst.
             assert (p ⋍ f ((ν :: s1) ++ s2)). eapply f_gen_lts_mu_in_the_middle'.
             constructor; eauto. exists (co_of ν). split; eauto. eapply co_inter. simpl.
             exists p. split; eauto. reflexivity. 
             exists (ν :: s1). exists s2. exists μ'.
             split. eauto. repeat split; eauto. constructor; eauto.
             exists (co_of ν). split; eauto. eapply co_inter.
    + destruct (decide (μ = (co_of ν))) as [eq | neq].
      ++ right. subst.
         exists ε, s', ν. simpl. repeat split; simpl; eauto with mdb.
         repeat split;eauto. intros. eapply gen_spec_mu_lts_not_nb_determinacy; eauto.
      ++ left. eapply gen_spec_mu_lts_not_nb_side_effect; eauto.
Qed.

Lemma inversion_gen_mu_nb `{
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec co_of f} 
  s μ p :
  (forall μ, f ε ↛[μ] \/ (forall e, f ε ⟶[μ] e -> attaboy e)) ->
  f s ⟶[μ] p ->
  non_blocking μ -> 
  attaboy p \/
  ∃ s1 s2 μ', s = s1 ++ μ' :: s2
  /\ p ⋍ f (s1 ++ s2) 
  /\ μ = co_of μ'
  /\ Forall exist_co_nba s1.
Proof.
  revert μ p.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros μ p h l nb.
  - edestruct (h μ) as [Tr|]; eauto. now eapply lts_refuses_spec2 in Tr; eauto.
  - (* destruct (decide (non_blocking ν)) as [nb'| not_nb']. *)
    + edestruct (gen_spec_mu_lts_co ν s') as (r & hlr & heqr).
      destruct (decide (co_of ν = μ)) as [eq | not_eq].
      ++ right. subst. exists ε, s', ν. repeat split; simpl; eauto with mdb.
         transitivity r; eauto. eapply (lts_oba_non_blocking_action_deter nb l hlr); eauto.
      ++ destruct (lts_oba_non_blocking_action_confluence nb not_eq l hlr )
           as (t' & l2 & (t & l1 & heq)).
         destruct (eq_spec (f s') t (ActExt $ μ)) as (v & hlv & heqv).
         exists r. split; eauto with mdb. now symmetry.
         destruct (decide (attaboy v)) as [happy' | not_happy'].
         +++ exfalso. assert (attaboy (f s')). 
             eapply attaboy_preserved_by_lts_non_blocking_action_converse; eauto.
             assert (¬ attaboy (f s')). eapply gen_spec_unattaboy. contradiction.
         +++ edestruct (Hlength s' ltac:(eauto) μ v h hlv nb)
             as [happy' | (s1' & s2' & μ' & eq0 & eq1 & eq2 & eq3)]; try contradiction.
             destruct (decide (non_blocking (co_of ν))) as [nb' | not_nb'].
             ++++ right. subst. assert (¬ non_blocking ν) as not_nb''.
                  eapply dual_blocks; eauto. eapply co_inter.
                  assert (Forall exist_co_nba (ν :: s1')) as Hyp.
                  constructor. esplit; eauto. split ;eauto. eapply co_inter. eauto.
                  exists (ν :: s1'), s2', μ'. repeat split; eauto.
                  edestruct (f_gen_lts_mu_in_the_middle (ν :: s1') s2' ν)
               as (r' & hlr' & heqr').
                  eauto.
                  edestruct (gen_spec_mu_lts_co ν (s1' ++ s2'))
               as (w & hlw & heqw).
                  eapply lts_oba_non_blocking_action_deter_inv; try eassumption.
                  transitivity t. symmetry. eassumption.
                  transitivity v. now symmetry.
                  transitivity (f (s1' ++ s2')). eassumption. now symmetry.
            ++++ subst. assert (attaboy p).
                 { eapply gen_spec_mu_lts_not_nb_side_effect; eauto. } eauto. 
Qed.

Lemma inversion_gen_mu `{
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec co_of f} 
  s μ p :
  (forall μ, f ε ↛[μ] \/ (forall e, f ε ⟶[μ] e -> attaboy e)) ->
  f s ⟶[μ] p ->
  attaboy p \/
  ∃ s1 s2 μ', s = s1 ++ μ' :: s2 
  /\ p ⋍ f (s1 ++ s2)
  /\ μ = co_of μ'
  /\ Forall exist_co_nba s1.
Proof.
  intros. destruct (decide (non_blocking μ)) as [nb | not_nb].
  + eapply inversion_gen_mu_nb; eauto.
  + eapply inversion_gen_mu_not_nb; eauto.
Qed.

Lemma inversion_gen_mu_gen_conv `{
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec_conv co_of f} 
  s μ p :
  f s ⟶[μ] p ->
  attaboy p \/ 
  ∃ s1 s2 μ', s = s1 ++ μ' :: s2 
  /\ p ⋍ f (s1 ++ s2)
  /\ μ = co_of μ'
  /\ Forall exist_co_nba s1.
Proof.
  intros. eapply inversion_gen_mu; eauto.
  left. eapply @gen_spec_conv_nil_refuses_mu; eauto.
Qed.

Lemma inversion_gen_mu_gen_acc `{CC: Countable PreA} `{
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec_acc PreA co_of f Γ} 
  s μ (p : E) (O : gset PreA) :
  f O s ⟶[μ] p ->
  attaboy p \/ 
  ∃ s1 s2 μ', s = s1 ++ μ' :: s2 
  /\ p ⋍ f O (s1 ++ s2)
  /\ μ = co_of μ'
  /\ Forall exist_co_nba s1.
Proof.
  eapply inversion_gen_mu; eauto. intros μ'.
  destruct (decide (non_blocking μ')) as [nb' | not_nb'].
       +++ left. eapply gen_spec_acc_nil_refuses_nb; eauto.
       +++ right. intro e. eapply gen_spec_acc_nil_lts_not_nb_attaboy; eauto.
Qed.

Lemma inversion_gen_tau `{
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec co_of f}
  s q :
  (f ε ↛ \/ (forall e, f ε ⟶ e -> attaboy e)) ->
  (forall μ, f ε ↛[μ] \/ (forall e, f ε ⟶[μ] e -> attaboy e)) ->
  f s ⟶ q ->
  attaboy q \/
  ∃ μ s1 s2 s3, 
  s = s1 ++ [μ] ++ s2 ++ [co_of μ] ++ s3
  /\ q ⋍ f (s1 ++ s2 ++ s3)
  /\ exist_co_nba μ
  /\ Forall exist_co_nba s1 
  /\ Forall exist_co_nba s2.
Proof.
  revert q. induction s as [|μ' s']; intros q h1 h2 HypTr.
  - destruct h1 as [refuses_f | f_to_attaboy].
    + eauto. now eapply lts_refuses_spec2 in refuses_f ; eauto.
    + eauto. 
  - destruct (decide (non_blocking (co_of μ'))) as [nb | not_nb].
    + destruct (decide (attaboy q)) as [happy | not_happy].
      ++ left. exact happy.
      ++ assert (parallel_inter μ' (co_of μ')) as inter.
         eapply co_inter.
         assert (¬ non_blocking μ') as not_nb.
         eapply dual_blocks; eauto.
         edestruct (gen_spec_mu_lts_co μ' s') as (r & hlr & heqr).
         destruct (lts_oba_non_blocking_action_tau nb hlr HypTr)
         as [(r1 & l1 & (r2 & l2 & heq))| HypTr''].
         +++ destruct (eq_spec (f s') r1 τ) as (v & hlv & heqv).
             exists r. split; eauto with mdb. now symmetry.
             destruct (IHs' _ h1 h2 hlv) as [happy' | Hyp].
             ++++ exfalso. 
                  assert (¬ attaboy r2) as not_happy''.
                  eapply unattaboy_preserved_by_lts_non_blocking_action; eauto.
                  assert (¬ attaboy v) as not_happy'.
                  eapply unattaboy_preserved_by_eq; eauto.
                  etrans. eapply heqv. now symmetry. 
                  contradiction.
             ++++ right. destruct Hyp 
                  as (μ & s1 & s2 & s3 & eq_trace & equiv & hi & his1 & his2). subst.
                  exists μ, (μ' :: s1), s2, s3. repeat split; eauto.
                        repeat split; eauto.
                        ++++++ edestruct (gen_spec_mu_lts_co μ') as (w & hlw & heqw).
                               eapply lts_oba_non_blocking_action_deter_inv. eassumption.
                               eassumption. eassumption.
                               etrans. eassumption.
                               etrans. symmetry. eapply heqv.
                               etrans. eassumption.
                               now symmetry.
                        ++++++ eapply Forall_cons; split; eauto. exists (co_of μ'). split.
                               exact nb. eapply co_inter.
         +++ destruct HypTr'' as (μ & duo & HypTr').
             assert (μ' = μ) as eq. eapply co_inter_spec1. exact duo.
             subst.
             assert (neq : μ <> co_of μ). intro eq_imp. rewrite eq_imp in not_nb.
             contradiction.
             destruct HypTr' as (q' & l' & heq).
             edestruct (lts_oba_non_blocking_action_delay nb hlr l')
           as (v & hlv & (t & l4 & heq4)).
             edestruct (lts_oba_non_blocking_action_confluence nb neq hlr hlv)
           as (r' & l3 & (t' & l4' & heq4')).
             destruct (eq_spec (f s') r' (ActExt $ μ)) as (t0 & hlt0 & heqt0).
             exists r. split. now symmetry. eassumption.
             destruct (inversion_gen_mu _ _ _ h2 hlt0)
              as [happy | (s1 & s2 & μ' & eq1 & eq_trace & equiv & his)]. 
             ++++ assert (t0 ⋍ q) as equiv.
                  etrans. eauto.
                  transitivity t'. now symmetry.
                  symmetry. transitivity t.
                  transitivity q'; now symmetry.
                  eapply lts_oba_non_blocking_action_deter; eauto.
                  left. eapply attaboy_preserved_by_eq; eauto.
             ++++ subst.
                  assert (μ' = co_of (co_of μ')) as eq. eapply co_co_is_id.
                  right. exists (co_of μ'), ε, s1, s2. repeat split; simpl; subst; eauto.
                  +++++ symmetry. symmetry in eq. rewrite eq at 1. eauto.
                  +++++ etrans. symmetry. eassumption.
                        etrans. symmetry. eassumption.
                        symmetry.
                        etrans. symmetry. eassumption.
                        etrans. eapply heqt0.
                        etrans. symmetry. eapply heq4'.
                        eapply lts_oba_non_blocking_action_deter; eassumption.
                  +++++ exists (co_of (co_of μ')). split; eauto.
    + left. eapply gen_spec_co_not_nb_lts_tau_attaboy. exact not_nb. exact HypTr.
Qed.

Lemma inversion_gen_tau_gen_conv `{
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec_conv co_of f} 
  s q :
  f s ⟶ q ->
  attaboy q \/
  ∃ μ s1 s2 s3,
  s = s1 ++ [μ] ++ s2 ++ [co_of μ] ++ s3
  /\ q ⋍ f (s1 ++ s2 ++ s3)
  /\ exist_co_nba μ
  /\ Forall exist_co_nba s1 
  /\ Forall exist_co_nba s2.
Proof.
  intros.
  eapply inversion_gen_tau; eauto.
  + right. eapply gen_spec_conv_nil_lts_tau_attaboy.
  + intro μ. left. eapply gen_spec_conv_nil_refuses_mu.
Qed.

Lemma inversion_gen_tau_gen_acc `{CC : Countable PreA} `{
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec_acc PreA co_of f Γ}
  s O q :
  f O s ⟶ q ->
  attaboy q \/ (∃ μ s1 s2 s3, s = s1 ++ [μ] ++ s2 ++ [co_of μ] ++ s3
                          /\ q ⋍ f O (s1 ++ s2 ++ s3)
                          /\ exist_co_nba μ
                          /\ Forall exist_co_nba s1 
                          /\ Forall exist_co_nba s2).
Proof.
  intros.
  eapply inversion_gen_tau; eauto.
  + left. eapply gen_spec_acc_nil_refuses_tau; eauto.
  + intro μ. destruct (decide (non_blocking μ)) as [nb | not_nb]. 
    ++ left. eapply gen_spec_acc_nil_refuses_nb; eauto.
    ++ right. intro e. 
       eapply gen_spec_acc_nil_lts_not_nb_attaboy ; eauto.
Qed.

(** Converse implication of the first requirement. *)

Lemma must_if_cnv `{
  @gLtsObaFW P A H gLtsP gLtsEqP V,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Testing_Predicate E A attaboy,
  !gen_spec_conv co_of gen_conv} 

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  s (p : P) :
  p ⇓ s -> must p (gen_conv s).
Proof.
  revert p.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  intros p hcnv.
  induction (cnv_terminate p s hcnv) as [p hp IHtp].
  apply m_step.
  + eapply gen_spec_unattaboy.
  + edestruct gen_conv_always_reduces. exists (p ▷ x). eapply ParRight; eauto.
  + intros p' l. eapply IHtp; [|eapply cnv_preserved_by_lts_tau]; eauto.
  + intros e' l.
    destruct (inversion_gen_tau_gen_conv s e' l)
      as [hu | (ν & s1 & s2 & s3 & eq__s & sc & i0 & i1 & i2)]; eauto with mdb.
    eapply must_eq_client. symmetry. eassumption.
    eapply Hlength.
    ++ subst. rewrite 6 length_app. simpl. lia.
    ++ inversion i0 as (x & nb & duo).
       assert (x = co ν). eapply unique_nb; eauto. subst.
       assert (co_of ν = co ν) as eq. eapply co_of_is_co_nb; eauto. 
       rewrite<- eq in duo, nb. eapply cnv_annhil; eauto.
  + intros p' e' ν' ν inter hlp hle.
    destruct (inversion_gen_mu_gen_conv s ν e' hle)
      as [hg | (s1 & s2 & ν'' & heq & sc & eq & his)]; eauto with mdb.
    rewrite heq in hle. subst. 
    assert (ν'' = ν'). eapply co_inter_spec1; eauto. subst.
    dependent induction s1.
    ++ simpl in *.
       eapply must_eq_client. symmetry. eassumption.
       eapply Hlength; subst; eauto with mdb.
       eapply cnv_preserved_by_wt_act; eauto.
       eapply lts_to_wt; eauto.
    ++ destruct (decide (non_blocking ν')) as [nb' | not_nb'].
       +++ eapply (cnv_drop_action_in_the_middle p (a :: s1) s2) in hlp; subst; eauto with mdb.
       eapply must_eq_client. symmetry. eassumption.
       eapply Hlength; subst; eauto with mdb.
       rewrite 2 length_app. simpl. lia.
       +++ eapply (cnv_drop_action_in_the_middle p (a :: s1) s2) in hlp; subst; eauto with mdb.
           eapply must_eq_client. symmetry. eassumption.
           eapply Hlength; subst; eauto with mdb.
           rewrite 2 length_app. simpl. lia.
Qed.

Lemma must_iff_cnv `{
  @gLtsObaFW P A H gLtsP gLtsEqP V,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Testing_Predicate E A attaboy, 
  !gen_spec_conv co_of gen_conv}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) s : must p (gen_conv s) <-> p ⇓ s.
Proof. split; [eapply cnv_if_must | eapply must_if_cnv]; eauto. Qed.

Lemma completeness1 `{
    @gLtsObaFW P A H gLtsP gLtsEqP V,
    @gLtsObaFW Q A H gLtsQ gLtsEqQ T,
    @gLtsObaFB E A H gLtsE gLtsEqE W, !Testing_Predicate E A attaboy,
    ! gen_spec_conv co_of gen_conv}

    `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}
    `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  (p : P) (q : Q) : p ⊑ q -> p ≼₁ q.
Proof. intros hleq s hcnv. now eapply must_iff_cnv, hleq, must_iff_cnv. Qed.

Lemma exists_forall_in {B} (ps : list B) (P : B -> Prop) (Q : B -> Prop)
  (h : forall p, p ∈ ps -> P p \/ Q p) : Exists P ps \/ Forall Q ps.
Proof.
  induction ps as [|p ?]. eauto.
  destruct IHps; destruct (h p); eauto; set_solver.
Qed.

Lemma exists_forall_in_gset `{Countable A} (ps : gset A) (P : A -> Prop) (Q : A -> Prop)
  (h : forall p, p ∈ ps -> P p \/ Q p) : (exists p, p ∈ ps /\ P p)\/ (forall p, p ∈ ps -> Q p).
Proof.
  induction ps using set_ind_L. set_solver.
  destruct IHps; destruct (h x); eauto; set_solver.
Qed.

Lemma wt_acceptance_set_subseteq
  `{gLtsP : @gLts P A H, !FiniteImagegLts P A, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  μ s p q hacnv1 hacnv2 :
  p ⟹{μ} q ->
  map pre_co_actions_of (elements (wt_refuses_set q s hacnv1)) ⊆
    map pre_co_actions_of (elements (wt_refuses_set p (μ :: s) hacnv2)).
Proof.
  intros.
  intros a in__a.
  assert (wt_refuses_set q s hacnv1 ⊆ wt_refuses_set p (μ :: s) hacnv2).
  intros t in__t.
  eapply wt_refuses_set_spec2.
  eapply wt_refuses_set_spec1 in in__t.
  destruct in__t. split; eauto with mdb.
  eapply wt_push_left; eauto.
  set_solver.
Qed.

Lemma lts_tau_acceptance_set_subseteq
  `{gLtsP : @gLts P A H, !FiniteImagegLts P A, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  s p q hacnv1 hacnv2 :
  p ⟶ q ->
  map pre_co_actions_of (elements $ wt_refuses_set q s hacnv1) ⊆
    map pre_co_actions_of (elements $ wt_refuses_set p s hacnv2).
Proof.
  intros.
  intros a in__a.
  assert (wt_refuses_set q s hacnv1 ⊆ wt_refuses_set p s hacnv2).
  { intros t in__t. eapply wt_refuses_set_spec2.
    eapply wt_refuses_set_spec1 in in__t.
    destruct in__t. split; eauto with mdb. }
  set_solver.
Qed.

Definition oas 
  `{gLtsP : @gLts P A H, FiniteImagegLts P A, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  (p : P) (s : list A) (hcnv : p ⇓ s) : gset PreA:=
  let ps : list P := elements (wt_refuses_set p s hcnv) in
  ⋃ map pre_co_actions_of ps.

Lemma union_wt_acceptance_set_subseteq
  `{gLtsP : @gLts P A H, !FiniteImagegLts P A, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  μ s p q h1 h2 :
  p ⟹{μ} q -> oas q s h1 ⊆ oas p (μ :: s) h2.
Proof.
  intros hw a (O & mem1 & mem2)%elem_of_union_list.
  eapply elem_of_union_list.
  exists O. split; eauto. eapply wt_acceptance_set_subseteq; eauto.
Qed.

Lemma union_acceptance_set_lts_tau_subseteq
  `{gLtsP : @gLts P A H, !FiniteImagegLts P A, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  s p q h1 h2 :
  p ⟶ q -> oas q s h1 ⊆ oas p s h2.
Proof.
  intros l a (L & mem1 & mem2)%elem_of_union_list.
  eapply elem_of_union_list.
  exists L. split; eauto.
  eapply lts_tau_acceptance_set_subseteq; eauto.
Qed.

Lemma aft_not_nb_co_of_must_gen_acc `{CC : Countable PreA} `{
  @gLtsOba P A H gLtsP gLtsEqP,
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec_acc PreA co_of gen_acc Γ}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) μ s L :
  p ⤓ -> ¬ non_blocking (co_of μ) -> (forall q, p ⟹{μ} q -> must q (gen_acc L s)) 
              -> must p (gen_acc L (μ :: s) : E).
Proof.
  intro tp. revert L μ s. induction tp.
  intros L μ s not_nb hmq.
  eapply m_step.
  - eapply gen_spec_unattaboy.
  - edestruct (@gen_spec_co_not_nb_lts_tau_ex E A); eauto with mdb.
    now destruct gen_spec_acc0. exists (p ▷ x). eapply ParRight; eauto.
  - intros. eapply H4. exact H5. eassumption. eauto with mdb.
  - intros e' l. eapply m_now.
    apply (gen_spec_co_not_nb_lts_tau_attaboy μ s e'). eassumption. eassumption.
  - intros p' e' μ' μ'' inter l0 l1.
    destruct (decide (μ'' = co_of μ)) as [eq | neq].
    + subst. eapply gen_spec_mu_lts_not_nb_determinacy in not_nb as h1; eauto. subst.
      eapply must_eq_client. symmetry; eauto.
      eapply hmq.
      eapply co_inter_spec1 in inter; eauto. subst. eauto with mdb.
    + eapply m_now. eapply gen_spec_mu_lts_not_nb_side_effect;eauto. Unshelve. eauto.
Qed.

Lemma gen_acc_tau_ex `{CC : Countable PreA}`{
  @gLtsObaFB E A H gLtsE LtsEqE LtsOBAE, !Testing_Predicate E A attaboy, !gen_spec_acc PreA co_of f Γ} 
  s1 s2 s3 μ L :
  exist_co_nba μ -> Forall exist_co_nba s1 -> Forall exist_co_nba s2 ->
  f L (s1 ++ [μ] ++ s2 ++ [co_of μ] ++ s3) ⟶⋍ f L (s1 ++ s2 ++ s3).
Proof.
  intros co_and_nb Hyp Hyp'.
  assert (f L (s1 ++ [μ] ++ s2 ++ [co_of μ] ++ s3) ⟶⋍[co_of μ]
            f L (s1 ++ s2 ++ [co_of μ] ++ s3)) as (e1 & l1 & heq1).
  eapply (@f_gen_lts_mu_in_the_middle E A _ _ _ _ _ _ co_of (f L) _
            s1 (s2 ++ [co_of μ] ++ s3) μ); simpl in *; eauto. (* 3 *)
  assert (f L (s1 ++ s2 ++ [co_of μ] ++ s3) ⟶⋍[co_of (co_of μ)]
            f L ((s1 ++ s2) ++ s3)) as (e2 & l2 & heq2).
  replace (s1 ++ s2 ++ [co_of μ] ++ s3) with ((s1 ++ s2) ++ [co_of μ] ++ s3).
  eapply (@f_gen_lts_mu_in_the_middle E A _ _ _ _ _ _ co_of (f L) _
            (s1 ++ s2) s3 (co_of μ)); simpl in *; eauto.
  unfold exist_co_nba. eapply Forall_app; eauto.
  now rewrite <- app_assoc.
  assert (μ =co_of (co_of μ)) as eq. eapply co_co_is_id; eauto.
  rewrite <-eq in l2.
  destruct co_and_nb as (a' & nb & duo). 
  assert (a' = co μ). eapply unique_nb; eauto. subst. 
  assert (co_of μ = co μ) as eq'. eapply co_of_is_co_nb; eauto.
  rewrite<- eq' in nb, duo. simpl in *.
  edestruct (eq_spec e1 e2) as (e' & l' & heq'). eauto.
  destruct (lts_oba_fb_feedback nb duo l1 l') as (t & lt & heqt); eauto.
  exists t. split; eauto.
  rewrite <- app_assoc in heq2.
  transitivity e'. eauto.
  transitivity e2; eauto. Unshelve. eauto. eauto.
Qed.

Lemma must_f_gen_a_subseteq_non_blocking `{CC : Countable PreA} `{
  @gLtsObaFB E A H gLtsE gLtsEqE W, AbE : @AbsAction A H E FinA gLtsE Φ, 
  !Testing_Predicate E A attaboy, !gen_spec_acc PreA co_of gen_acc Γ} 
  s e η L1 :
  non_blocking η -> gen_acc L1 s ⟶[η] e 
    -> forall L2, L1 ⊆ L2
      -> exists t, gen_acc L2 s ⟶[η] t.
Proof.
  revert e L1.
  induction s as [|μ s']; intros e L1 nb l L2 hsub.
  + exfalso. eapply lts_refuses_spec2, gen_spec_acc_nil_refuses_nb; eauto.
  + destruct (decide (non_blocking μ)) as [nb' | not_nb'].
    ++ edestruct
         (@gen_spec_mu_lts_co E A _ _ _ _ _  co_of (gen_acc L2) _ μ s')
         as (r' & hl' & heqr').
       assert (¬ non_blocking (co_of μ)) as not_nb. 
       eapply dual_blocks; eauto.
       assert (parallel_inter (co_of μ) μ). symmetry. 
       inversion gen_spec_acc0; subst. destruct (gen_acc_spec_gen_spec0 L2).
       eapply co_inter0. eauto.
       assert (¬ non_blocking η) as imp.
       { eapply side_effect_by_blocking_action; eauto. } 
       contradiction.
    ++ edestruct
        (@gen_spec_mu_lts_co E A _ _ _ _ _ co_of (gen_acc L1) _ μ s')
        as (e1 & hle1 & heqe1). (* simpl in hle1. *)
       edestruct
         (@gen_spec_mu_lts_co E A _ _ _ _ _ co_of (gen_acc L2) _ μ s')
         as (e2 & hle2 & heqe2). (* simpl in hle2. *)
       destruct (decide (non_blocking (co_of μ))) as [nb'' | not_nb''].
       +++ destruct (decide (η = co_of μ)) as [eq | not_eq]. 
           ++++ subst; eauto.
           ++++ destruct (lts_oba_non_blocking_action_confluence nb'' not_eq hle1 l) as
            (r1 & l1 & r2 & l2 & heq).
           edestruct (eq_spec (gen_acc L1 s') r1) as (e' & hle' & heqe').
           symmetry in heqe1. eauto.
           eapply IHs' in hle' as (t & hlt); eauto.
           edestruct (eq_spec e2 t) as (e2' & hle2' & heqe2'). eauto.
           edestruct (lts_oba_non_blocking_action_delay nb'' hle2 hle2') as (v & l3 & l4).
           eauto with mdb.
       +++ assert (¬ non_blocking η) as imp.
           { eapply side_effect_by_blocking_action; eauto. }
           contradiction.
Qed.

(* Lemma must_f_gen_a_subseteq_not_non_blocking {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA PreA_eq PreA_countable 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA PreA_eq PreA_countable 𝝳 gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Testing_Predicate E A attaboy, !gen_spec_acc P Q co_of gen_acc} 
  s e μ' L1 :
  ¬ non_blocking μ' -> gen_acc L1 s ⟶[μ'] e
    -> forall L2, L1 ⊆ L2 
      -> (exists t, gen_acc L2 s ⟶[μ'] t) \/ (∃ e', gen_acc L2 s ⟶ e').
Proof.
  revert e L1.
  induction s as [|μ s']; intros e L1 not_nb l L2 hsub.
  + assert ( (*∃ η : A, μ' = co_of η ∧ *) 𝝳 μ' ∈ L1) as (* (  μ'' & eq & *) In (* ) *); subst.
    { eapply (@gen_spec_acc_nil_mu_inv P Q); eauto. }
    eapply hsub in In. eapply (@gen_spec_acc_nil_mem_lts_inp P Q) in In as (r & μ & HypTr & eq); eauto.
    admit.
  + destruct (decide (non_blocking (co_of μ))) as [nb' | not_nb'].
    ++ edestruct
        (@gen_spec_mu_lts_co E A _ _ _ _ _ co_of (gen_acc L1) _ μ s')
        as (r & hl & heqr).
       assert (not_eq :  μ' ≠ (co_of μ)). { intro impossible. subst. contradiction. }
       destruct (lts_oba_non_blocking_action_confluence nb' not_eq hl l) as
         (r1 & l1 & r2 & l2 & heq).
       edestruct (eq_spec (gen_acc L1 s') r1) as (e' & hle' & heqe').
       symmetry in heqr. eauto.
       eapply IHs' in hle' as [(t & hlt_mu) | (t & hlt_tau)]; eauto.
       +++ edestruct
         (@gen_spec_mu_lts_co E A _ _ _ _ _ co_of (gen_acc L2) _ μ s')
         as (r' & hl' & heqr'). simpl in hl'.
           edestruct (eq_spec r' t) as (e2 & hle2 & heqe2). eauto.
           edestruct (lts_oba_non_blocking_action_delay nb' hl' hle2) as (v & l3 & l4).
           eauto with mdb.
       +++ right. assert (gen_acc L2 (μ :: s') ⟶⋍[co_of μ] gen_acc L2 s') as (r' & hl' & heqr').
           apply gen_spec_mu_lts_co.
           edestruct (eq_spec r' t) as (e2 & hle2 & heqe2); eauto.
           edestruct (lts_oba_non_blocking_action_delay nb' hl' hle2) as (v & l3 & l4); eauto.
    ++ right. eapply gen_spec_co_not_nb_lts_tau_ex; eauto.
Admitted.

(* Lemma must_f_gen_a_subseteq_not_non_blocking {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA PreA_eq PreA_countable 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA PreA_eq PreA_countable 𝝳 gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Testing_Predicate E A attaboy, !gen_spec_acc P Q co_of gen_acc} 
  s e μ' L1 :
  ¬ non_blocking μ' -> gen_acc L1 s ⟶[μ'] e
    -> forall L2, L1 ⊆ L2 
      -> (exists t, gen_acc L2 s ⟶[μ'] t) \/ (∃ e', gen_acc L2 s ⟶ e').
Proof.
  revert e L1.
  induction s as [|μ s']; intros e L1 not_nb l L2 hsub.
  + assert ( (*∃ η : A, μ' = co_of η ∧ *) 𝝳 μ' ∈ L1) as (* (  μ'' & eq & *) In (* ) *); subst.
    { eapply (@gen_spec_acc_nil_mu_inv P Q); eauto. }
    eapply hsub in In. eapply (@gen_spec_acc_nil_mem_lts_inp P Q) in In as (r & μ & HypTr & eq); eauto.
    admit.
  + destruct (decide (non_blocking (co_of μ))) as [nb' | not_nb'].
    ++ edestruct
        (@gen_spec_mu_lts_co E A _ _ _ _ _ co_of (gen_acc L1) _ μ s')
        as (r & hl & heqr).
       assert (not_eq :  μ' ≠ (co_of μ)). { intro impossible. subst. contradiction. }
       destruct (lts_oba_non_blocking_action_confluence nb' not_eq hl l) as
         (r1 & l1 & r2 & l2 & heq).
       edestruct (eq_spec (gen_acc L1 s') r1) as (e' & hle' & heqe').
       symmetry in heqr. eauto.
       eapply IHs' in hle' as [(t & hlt_mu) | (t & hlt_tau)]; eauto.
       +++ edestruct
         (@gen_spec_mu_lts_co E A _ _ _ _ _ co_of (gen_acc L2) _ μ s')
         as (r' & hl' & heqr'). simpl in hl'.
           edestruct (eq_spec r' t) as (e2 & hle2 & heqe2). eauto.
           edestruct (lts_oba_non_blocking_action_delay nb' hl' hle2) as (v & l3 & l4).
           eauto with mdb.
       +++ right. assert (gen_acc L2 (μ :: s') ⟶⋍[co_of μ] gen_acc L2 s') as (r' & hl' & heqr').
           apply gen_spec_mu_lts_co.
           edestruct (eq_spec r' t) as (e2 & hle2 & heqe2); eauto.
           edestruct (lts_oba_non_blocking_action_delay nb' hl' hle2) as (v & l3 & l4); eauto.
    ++ right. eapply gen_spec_co_not_nb_lts_tau_ex; eauto.
Admitted. *)*)

(* Lemma must_f_gen_a_subseteq_tau {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA PreA_eq PreA_countable 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA PreA_eq PreA_countable 𝝳 gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Testing_Predicate E A attaboy, !gen_spec_acc P Q co_of gen_acc}
  s e L1 : 
  gen_acc L1 s ⟶ e 
    -> forall L2, L1 ⊆ L2
      -> exists t, gen_acc L2 s ⟶ t.
Proof.
  revert e L1.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  intros e L1 l (* not_happy *) L2 hsub. destruct s.
  + exfalso. eapply lts_refuses_spec2, (@gen_spec_acc_nil_refuses_tau P Q); eauto.
  + destruct (decide (non_blocking (co_of a))) as [nb | not_nb].
    ++ assert (gen_acc L1 (a :: s) ⟶⋍[co_of a] gen_acc L1 s) as (r & hl & heqr).
       apply gen_spec_mu_lts_co.
       destruct (lts_oba_non_blocking_action_tau nb hl l) 
        as [(r1 & l1 & (r2 & l2 & heq))| (μ' & duo & (r' & hl' & heq'))].
       +++ edestruct (eq_spec (gen_acc L1 s) r1) as (e' & hle' & heqe').
           symmetry in heqr. eauto.
           eapply Hlength in hle' as (t & hlt).
           assert (gen_acc L2 (a :: s) ⟶⋍[co_of a] gen_acc L2 s) as (r' & hl' & heqr').
           apply gen_spec_mu_lts_co.
           edestruct (eq_spec r' t) as (e2 & hle2 & heqe2). eauto.
           edestruct (lts_oba_non_blocking_action_delay nb hl' hle2) as (v & l3 & l4); eauto.
           eauto with mdb.
           eassumption.
       +++ edestruct (eq_spec (gen_acc L1 s) r') as (t & hlt & heqt).
           symmetry in heqr. eauto.
           assert (¬ non_blocking μ') as not_nb.
           eapply dual_blocks; eauto.
           assert (a = μ').
           { eapply co_inter_spec1;eauto. } subst.
           (* edestruct (must_f_gen_a_subseteq_not_non_blocking s t μ' L1 not_nb hlt L2 hsub) as [(x & tr)| (e' & tr)].
           ++++ assert (gen_acc L2 (μ' :: s) ⟶⋍[co_of μ'] gen_acc L2 s) as (u & hlu & hequ).
                apply gen_spec_mu_lts_co.
                edestruct (eq_spec u x) as (t' & hlt' & heqt'). eauto.
                edestruct (lts_oba_fb_feedback nb duo hlu hlt'); eauto.
                firstorder.
           ++++ assert (gen_acc L2 (μ' :: s) ⟶⋍[co_of μ'] gen_acc L2 s) as (u & hlu & hequ).
                apply gen_spec_mu_lts_co.
                edestruct (eq_spec u e') as (t' & hlt' & heqt'). eauto.
                edestruct (lts_oba_non_blocking_action_delay nb hlu hlt') 
                    as (e'' & tr'' & e''' & tr''' & equiv) ; eauto.  *) admit.
    ++ eapply gen_spec_co_not_nb_lts_tau_ex. exact not_nb.
    Unshelve. eauto.
Admitted. *)

Lemma must_f_gen_a_subseteq_nil {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, AbE : @AbsAction A H E FinA gLtsE Φ,
  !Testing_Predicate E A attaboy, !gen_spec_acc PreA co_of gen_acc (fun x => 𝝳 (Φ x))}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) L1 : 
  must p (gen_acc L1 ε) 
    -> forall L2, L1 ⊆ L2 
      -> must p (gen_acc L2 ε).
Proof.
  intros hm.
  assert (hpt : p ⤓)
    by now (eapply must_terminate_unattaboy , gen_spec_unattaboy; eauto).
  induction hpt. dependent induction hm; intros L2 hsub.
  - assert (¬ attaboy (gen_acc L1 ε)).
    { now eapply gen_spec_unattaboy. }
    contradiction.
  - eapply m_step; eauto with mdb.
    + eapply gen_spec_unattaboy.
    + destruct ex as ((p' & e') & l').
      inversion l'; subst.
      +++ exists (p' ▷ (gen_acc L2 ε)). eapply ParLeft; eauto.
      +++ exfalso. assert ({q : E | gen_acc L1 ε ⟶ q}) as impossible.
          eauto.
          eapply lts_refuses_spec2 in impossible.
          assert (gen_acc L1 ε ↛). eapply gen_spec_acc_nil_refuses_tau; eauto.
          contradiction.
      +++ destruct (decide (non_blocking μ2)) as [nb2 | not_nb2].
          ++++ exfalso.
               assert ({q : E | gen_acc L1 ε ⟶[μ2] q}) as impossible. eauto.
               eapply lts_refuses_spec2 in impossible. 
               assert (gen_acc L1 ε ↛[μ2]). eapply gen_spec_acc_nil_refuses_nb; eauto.
               contradiction.
          ++++ assert (μ2 ∈ co_actions_of p) as co_set.
               { exists μ1. repeat split; eauto. eapply lts_refuses_spec2; eauto.
                 symmetry in eq; eauto. }
               eapply preactions_of_fin_test_spec1 in co_set.
               eapply preactions_of_spec1 in co_set.
               eapply gen_spec_acc_nil_mu_inv in l2 as mem; eauto.
               eapply hsub in mem.
               eapply gen_spec_acc_nil_mem_lts_inp in mem as (r & μ'2 & Tr' & eq'); eauto.
               rewrite<- eq' in co_set.
               eapply preactions_of_spec2 in co_set; eauto.
               eapply preactions_of_fin_test_spec2 in co_set as (μ'' & co_set & eq'').
               destruct co_set as (μ'1 & Tr & duo & b).
               assert (blocking μ'2).
               { intro imp. eapply gen_spec_acc_nil_refuses_nb in imp. 
                 eapply (@lts_refuses_spec2 E). exists r. exact Tr'. eauto. }
               assert (¬ gen_acc L2 ε ↛[μ'']) as Tr''.
               { eapply (abstraction_test_spec μ'2 μ'' (gen_acc L2 ε)) in eq''; eauto.
                 eapply lts_refuses_spec2; eauto. }
               eapply lts_refuses_spec1 in Tr'' as (e'' & Tr'').
               eapply lts_refuses_spec1 in Tr as (p'' & Tr).
               exists (p'', e''). eapply ParSync. symmetry. exact duo. exact Tr. exact Tr''.
    + intros e l.
      exfalso. 
      assert ({q : E | gen_acc L2 ε ⟶ q}) as impossible. eauto.
      eapply lts_refuses_spec2 in impossible. 
      assert (gen_acc L2 ε ↛). eapply gen_spec_acc_nil_refuses_tau; eauto.
      contradiction.
    + intros p' e' μ μ' inter l2 l1.
      destruct (decide (non_blocking μ')) as [nb | not_nb].
      ++ exfalso. 
         assert ({q : E | gen_acc L2 ε ⟶[μ'] q}) as impossible. eauto.
         eapply lts_refuses_spec2 in impossible. 
         assert (gen_acc L2 ε ↛[μ']). eapply gen_spec_acc_nil_refuses_nb; eauto.
         contradiction.
      ++ eapply (@gen_spec_acc_nil_lts_not_nb_attaboy 
            PreA PreA_eq PreA_countable E A H gLtsE gLtsEqE
                  attaboy Testing_Predicate0 co_of gen_acc (fun x => 𝝳 (Φ x))) in l1;eauto.
         eapply m_now; eauto.
Qed.

Lemma must_f_gen_a_subseteq {P Q : Type} `{
  @gLtsObaFW P A H gLtsP gLtsEqP V, PreAP : @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ T, PreAQ: @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, @AbsAction A H E FinA gLtsE Φ, !Testing_Predicate E A attaboy,
  !gen_spec_acc PreA co_of gen_acc (fun x => (𝝳  (Φ x)))}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  s (p : P) L1 :

  must p (gen_acc L1 s) 
    -> forall L2, L1 ⊆ L2
      -> must p (gen_acc L2 s).
Proof.
  revert p L1.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros p L1 hm L2 hsub; subst.
  - eapply must_f_gen_a_subseteq_nil; eauto.
  - assert (htp : p ⤓) by (eapply must_terminate_unattaboy, gen_spec_unattaboy; eauto).
    induction htp.
    inversion hm.
    * now eapply gen_spec_unattaboy in H7.
    * eapply m_step; eauto with mdb.
      + eapply gen_spec_unattaboy.
      + destruct (decide (non_blocking (co_of ν))) as [nb | not_nb].
        ++ edestruct (lts_oba_fw_forward p (co_of ν) ν) as (p' & Hyp').
           assert (p ⟶[ν] p').
           { eapply Hyp'; eauto. eapply (co_inter ν). }
           assert (gen_acc L2 (ν :: s') ⟶⋍[co_of ν] gen_acc L2 s') as (t' & tr' & eq').
           { eapply gen_spec_mu_lts_co. }
           exists (p' , t'). eapply ParSync; eauto. eapply (co_inter ν).
        ++ assert (∃ e', gen_acc L2 (ν :: s') ⟶ e') as (e' & tr').
           { eapply gen_spec_co_not_nb_lts_tau_ex. eauto. }
           exists (p , e'). eapply ParRight. exact tr'.
      + intros e' l.
        edestruct @inversion_gen_tau_gen_acc as [|Hyp]; eauto with mdb.
        destruct Hyp as (μ & s1 & s2 & s3 & heqs & sc & himu & his1 & his2).
        eapply (must_eq_client p (gen_acc L2 (s1 ++ s2 ++ s3))). now symmetry.
        edestruct (@gen_acc_tau_ex _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1 s2 s3 μ L1) as (t & hlt & heqt); eauto.
        eapply Hlength; eauto.
        ++ rewrite heqs, 6 length_app. simpl. lia.
        ++ eapply must_eq_client. eapply heqt. eapply et. now rewrite heqs.
      + intros p' e' μ μ' inter l1 l2.
        edestruct @inversion_gen_mu_gen_acc as [|Hyp]; eauto with mdb.
        destruct Hyp as (s1 & s2 & μ''' & heqs & heq & eq & his1). subst.
        eapply must_eq_client. symmetry. eassumption.
        edestruct @f_gen_lts_mu_in_the_middle as (t & l & heq'); eauto.
        now destruct gen_spec_acc0.
        eapply Hlength. rewrite heqs.
        rewrite 2 length_app. simpl. lia.
        eapply must_eq_client. eapply heq'.
        eapply com; eauto. rewrite heqs. eassumption.
        eassumption. Unshelve. eauto. eauto.
Qed.

Lemma must_gen_acc_refuses {P Q : Type} `{
  @gLtsOba P A H gLtsP gLtsEqP, @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  @gLtsOba Q A H gLtsQ gLtsEqQ, @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @gLtsOba E A H gLtsE gLtsEqE, @AbsAction A H E FinA gLtsE Φ, !Testing_Predicate E A attaboy, 
  !gen_spec_acc PreA co_of gen_acc (fun x => (𝝳  (Φ x)))}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (q : Q): 

  p ↛ (* -> *) (* ¬  *) (* (∃ x, x ∈ lts_acc_set_of p ∖ O) *)
      -> must p (gen_acc ((pre_co_actions_of p) ∖ (pre_co_actions_of q)) ε)
          \/ (pre_co_actions_of p ⊆ pre_co_actions_of q).
Proof.
  intros.
  remember ((pre_co_actions_of p) ∖ (pre_co_actions_of q)) as D.
  destruct D as [|a D'] using set_ind_L.
  + right. set_solver.
  + left.
      eapply m_step.
      ++ now eapply gen_spec_unattaboy.
      ++ assert (a ∈ pre_co_actions_of p ∖ pre_co_actions_of q) as mem'.
         { set_solver. }
         assert (a ∈ pre_co_actions_of p) as co_set. 
         { eauto. eapply elem_of_difference; eauto. }
         eapply gen_spec_acc_nil_mem_lts_inp in mem' as (r & μ & Tr & eq); eauto.
         subst. eapply preactions_of_spec2 in co_set.
         eapply preactions_of_fin_test_spec2 in co_set as (μ'' & co_set & eq). 
         destruct co_set as (μ' & Tr' & duo & b).
         assert (blocking μ).
         { intro imp. eapply gen_spec_acc_nil_refuses_nb in imp. 
           eapply (@lts_refuses_spec2 E). exists r. exact Tr. eauto. }
         assert (¬ (gen_acc (pre_co_actions_of p ∖ pre_co_actions_of q) ε) ↛[μ'']) as Tr''.
         { eapply abstraction_test_spec; eauto. eapply lts_refuses_spec2; eauto. }
         rewrite<- HeqD in Tr''.
         eapply lts_refuses_spec1 in Tr'' as (e'' & Tr'').
         eapply lts_refuses_spec1 in Tr' as (p'' & Tr').
         exists (p'' , e''). symmetry in duo. eapply ParSync; eauto. eauto.
      ++ intros p' l'. exfalso. eapply (lts_refuses_spec2 p); eauto with mdb.
      ++ intros e' l'. exfalso.
         assert (¬ gen_acc (pre_co_actions_of p ∖ pre_co_actions_of q) ε ↛ ).
         { rewrite<- HeqD. eapply lts_refuses_spec2; eauto. }
         assert (gen_acc (pre_co_actions_of p ∖ pre_co_actions_of q) ε ↛).
         { rewrite<- HeqD. eapply gen_spec_acc_nil_refuses_tau ; eauto. }
         contradiction.
      ++ intros p'' e'' μ' μ inter l'1 l'0.
         destruct (decide (non_blocking μ)) as [nb' | not_nb'].
         ++++++ exfalso.
                eapply (@lts_refuses_spec2 E); eauto with mdb.
                eapply gen_spec_acc_nil_refuses_nb ; eauto.
         ++++++ eapply gen_spec_acc_nil_lts_not_nb_attaboy in l'0. 
                eapply m_now.  exact l'0. eauto.
Qed.

(* Lemma must_gen_acc_refuses_inv' {P Q : Type} `{
  LtsP : @gLts P A H,
  LtsQ : @gLts Q A H,
  @gLtsOba P A H gLtsP gLtsEqP,
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec_acc P Q co_of gen_acc}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) O : 

  lts_acc_set_of p ⊆ O -> ¬ (∃ x, x ∈ lts_acc_set_of p ∖ O) .
Proof.
  intros imp. intros (x & Hyp). destruct Hyp.
  eapply imp in H3. contradiction.
Qed. *)

(* Lemma must_gen_acc_refuses_inv'' {P Q : Type} `{
  gLtsP : @gLts P A H,
  gLtsQ : @gLts Q A H,
  @gLtsOba P A H gLtsP gLtsEqP, 
  @gLtsOba E A H gLtsE gLtsEqE, !Testing_Predicate E A attaboy, !gen_spec_acc P Q co_of gen_acc}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) O : 

  (∃ x, x ∈ lts_acc_set_of p ∖ O) -> ¬ lts_acc_set_of p ⊆ O.
Proof.
  intros imp. intro imp'. eapply (@must_gen_acc_refuses_inv' P Q) in imp'; eauto.
Qed.
 *)

Lemma must_gen_a_with_nil {P Q : Type} `{
  gLtsP : @gLts P A H,
  gLtsQ : @gLts Q A H,
  @gLtsObaFW P A H gLtsP gLtsEqP V, !FiniteImagegLts P A, @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ T, !FiniteImagegLts Q A, @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, @AbsAction A H E FinA gLtsE Φ, !Testing_Predicate E A attaboy, !gen_spec_acc PreA co_of gen_acc (fun x => (𝝳  (Φ x)))}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (hcnv : p ⇓ ε) (q : Q):

  (exists p', p ⟹ p' /\ lts_refuses p' τ /\ pre_co_actions_of p' ⊆ pre_co_actions_of q)
  \/ must p (gen_acc ((oas p ε hcnv) ∖ (pre_co_actions_of q)) ε).
Proof.
  induction (cnv_terminate p ε hcnv) as (p, hpt, ihhp).
  destruct (decide (lts_refuses p τ)) as [st | (p'' & l)%lts_refuses_spec1].
  + destruct (must_gen_acc_refuses p q st) as [Hyp | Hyp].
    ++ right. unfold oas.
       rewrite wt_refuses_set_refuses_singleton, elements_singleton; eauto.
       simpl. rewrite union_empty_r_L. set_solver.
    ++ left. exists p. split; eauto. constructor.
  + assert (∀ q0 : P,
         q0 ∈ lts_tau_set p
         → (∃ p' : P, q0 ⟹ p' ∧ p' ↛ ∧ pre_co_actions_of p' ⊆ pre_co_actions_of  q)
             ∨ (exists h, must q0 (gen_acc ((oas q0 ε h) ∖ (pre_co_actions_of q)) ε))) as Hyp.
  ++ intros q' l'%lts_tau_set_spec.
     destruct (hpt q' l') as (hq).
     assert (q' ⇓ ε) as cnv_nil'.
     eapply (cnv_nil q' (tstep q' hq)).
     edestruct (ihhp q' l') as [hl | hr].
     +++ now left.
     +++ right. exists (cnv_nil _ (tstep q' hq)). eauto.
    ++ destruct (@exists_forall_in P (lts_tau_set p) _ _ Hyp) as [Hyp' | Hyp'].
       +++ eapply Exists_exists in Hyp' as (t & l'%lts_tau_set_spec & t' & w & st & sub).
           left. exists t'. eauto with mdb.
       +++ right. eapply m_step.
           ++++ eapply gen_spec_unattaboy.
           ++++ exists (p'' ▷ gen_acc ((oas p ε hcnv) ∖ (pre_co_actions_of q)) ε). eapply ParLeft; eauto.
           ++++ intros p0 l0%lts_tau_set_spec.
                eapply Forall_forall in Hyp' as (h0 & hm).
                eapply must_f_gen_a_subseteq; eauto.
                eapply difference_mono_r.
                eapply union_acceptance_set_lts_tau_subseteq. 
                eapply lts_tau_set_spec. exact l0.
                eauto.
           ++++ intros e' l'. exfalso.
                eapply (@lts_refuses_spec2 E). eauto. eapply gen_spec_acc_nil_refuses_tau; eauto.
           ++++ intros p0 e0 μ' μ inter lp le.
                destruct (decide (non_blocking μ)) as [nb | not_nb].
                +++++ exfalso.
                      assert ({q' : E | gen_acc ((oas p ε hcnv) ∖ (pre_co_actions_of q)) ε ⟶[μ] q'}).
                      { eauto. } eapply (lts_refuses_spec2); eauto. 
                      eapply gen_spec_acc_nil_refuses_nb; eauto.
                +++++ eapply m_now. eapply gen_spec_acc_nil_lts_not_nb_attaboy; eauto.
Qed.

Lemma must_gen_a_with_s {P Q : Type} `{
  @gLtsObaFW P A H gLtsP gLtsEqP V, !FiniteImagegLts P A, @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ T, !FiniteImagegLts Q A, @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, @AbsAction A H E FinA gLtsE Φ, !Testing_Predicate E A attaboy, !gen_spec_acc PreA co_of gen_acc (fun x => (𝝳  (Φ x)))} 

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  s (p : P) (hcnv : p ⇓ s) (q : Q):

  (exists p', p ⟹[s] p' /\ lts_refuses p' τ /\ pre_co_actions_of p' ⊆ pre_co_actions_of q) 
      \/ must p (gen_acc ((oas p s hcnv) ∖ (pre_co_actions_of q)) s).
Proof.
  revert p hcnv q.
  induction s as [|μ s'].
  - intros. eapply must_gen_a_with_nil.
  - intros p hcnv q.
    set (ps := wt_set_mu p μ s' hcnv).
    inversion hcnv as [| ? ? ? conv Hyp_conv]; subst.
    assert (hcnv0 : forall p', p' ∈ ps -> p' ⇓ s') by (intros ? mem%wt_set_mu_spec1; eauto).
    assert (he : ∀ p', p' ∈ ps ->
     ((exists pr p0, p0 ∈ wt_refuses_set p' s' pr ∧ pre_co_actions_of p0 ⊆ pre_co_actions_of q) 
             \/ (exists h, must p' (gen_acc ((oas p' s' h) ∖ (pre_co_actions_of q)) s')))).
    + intros p' mem.
      destruct (IHs' p' (hcnv0 _ mem) q) as [(r & w & st & sub)| hm].
      ++ left. eapply wt_set_mu_spec1 in mem.
         exists (Hyp_conv _ mem), r. split; [eapply wt_refuses_set_spec2 |]; eauto.
      ++ right. eauto.
    + destruct (exists_forall_in_gset ps _ _ he) as [Hyp | Hyp].
      ++ left. destruct Hyp
          as (p1 & ?%wt_set_mu_spec1 & ? & r & (? & ?)%wt_refuses_set_spec1 & ?).
         exists r. repeat split; eauto. eapply wt_push_left; eauto.
      ++ right. 
         assert (parallel_inter μ (co_of μ)) as inter.
         eapply co_inter; eauto. 
         destruct (decide (non_blocking (co_of μ))) as [nb | not_nb]. 
         inversion hcnv; subst.
         +++ destruct (lts_oba_fw_forward p (co_of μ) μ) as (p' & l0 & l1); eauto.
             assert (gen_acc ((oas p (μ :: s') hcnv) ∖ (pre_co_actions_of q)) (μ :: s')
                   ⟶⋍[co_of $ μ] gen_acc ((oas p (μ :: s') hcnv) ∖ (pre_co_actions_of q)) s')
            as (e' & hle' & heqe') by eapply gen_spec_mu_lts_co.
             eapply must_non_blocking_action_swap_l_fw; eauto.
             eapply (must_eq_client _ _ _ (symmetry heqe')).
             edestruct (Hyp p') as (? & hm).
             eapply wt_set_mu_spec2; eauto with mdb.
             assert (oas p' s' x ∖ pre_co_actions_of q ⊆ oas p (μ :: s') hcnv ∖ pre_co_actions_of q).
             eapply difference_mono_r.
             eapply union_wt_acceptance_set_subseteq; eauto with mdb.
             eapply must_f_gen_a_subseteq; eauto.
         +++ eapply aft_not_nb_co_of_must_gen_acc; eauto.
             intros p' hw.
             edestruct (Hyp p') as (? & hm).
             eapply wt_set_mu_spec2; eauto.
             assert ((oas p' s' x ∖ pre_co_actions_of q) ⊆ oas p (μ :: s') hcnv ∖ pre_co_actions_of q).
             eapply difference_mono_r. 
             eapply union_wt_acceptance_set_subseteq; eauto with mdb.
             eapply must_f_gen_a_subseteq; eauto. Unshelve. exact (⋃ map pre_co_actions_of (elements ps) ∖ (pre_co_actions_of q)).
Qed.

Lemma not_must_gen_a_without_required_acc_set {(* P *) Q : Type} `{
  gLtsP : @gLts P A H, @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ V, @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, @AbsAction A H E FinA gLtsE Φ,!Testing_Predicate E A attaboy, !gen_spec_acc PreA co_of gen_acc (fun x => (𝝳  (Φ x)))} 

  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  (q q' : Q) s (L : list P) :

  q ⟹[s] q' -> q' ↛ -> ¬ must q (gen_acc ((⋃ map pre_co_actions_of L) ∖ (pre_co_actions_of q')) s).
Proof.
  intros wt hst.
  dependent induction wt; intros hm. rename p into q.
  - inversion hm as [happy | ]; subst.
    ++ contradict happy. eapply gen_spec_unattaboy.
    ++ destruct ex as (t & l). inversion l; subst.
       +++ eapply (lts_refuses_spec2 q τ); eauto with mdb.
       +++ eapply lts_refuses_spec2, gen_spec_acc_nil_refuses_tau; eauto.
       +++ destruct (decide (non_blocking μ2)) as [nb2 | not_nb2].
           ++++ exfalso. eapply lts_refuses_spec2.
                eauto. eapply gen_spec_acc_nil_refuses_nb ;eauto. 
           ++++ eapply gen_spec_acc_nil_mu_inv in l2 as mem; eauto.
                assert (𝝳 (Φ μ2) ∉ pre_co_actions_of q) as not_in_mem.
                { set_solver. }
                assert (𝝳 (Φ μ2) ∈ pre_co_actions_of q) as in_mem.
                { eapply preactions_of_spec1. eapply preactions_of_fin_test_spec1. exists μ1. repeat split; eauto.
                eapply lts_refuses_spec2; eauto. symmetry in eq; eauto. }
                contradiction.
  - eapply (IHwt hst), (must_preserved_by_lts_tau_srv p q _ hm l).
  - eapply (IHwt hst).
    assert (gen_acc ((⋃ map pre_co_actions_of L) ∖ (pre_co_actions_of t)) (μ :: s) ⟶⋍[co_of μ]
              gen_acc ((⋃ map pre_co_actions_of L) ∖ (pre_co_actions_of t)) s) as (e' & hle' & heqe')
    by eapply gen_spec_mu_lts_co.
    eapply must_eq_client; eauto.
    inversion hm as [happy |]; subst.
    + now eapply gen_spec_unattaboy in happy.
    + assert (parallel_inter μ (co_of μ)) as inter. eapply co_inter; eauto.
      eauto. Unshelve.  exact (⋃ map pre_co_actions_of L).
Qed.

Lemma completeness2 {P Q : Type} `{
  @gLtsObaFW P A H gLtsP gLtsEqP VP, !FiniteImagegLts P A, @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ VQ, !FiniteImagegLts Q A, @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE VE, 
  @AbsAction A H E FinA gLtsE Φ, !Testing_Predicate E A attaboy, !gen_spec_acc PreA co_of gen_acc (fun x => (𝝳  (Φ x)))}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  (p : P) (q : Q) : p ⊑ q -> p ≼₂ q.
Proof.
  intros hpre s q' hacnv w st.
  destruct (must_gen_a_with_s s p hacnv q') as [|hm].
  + eauto.
  + eapply hpre in hm. contradict hm.
    eapply not_must_gen_a_without_required_acc_set; set_solver.
Qed.

Lemma completeness_fw {P Q : Type} `{
  @gLtsObaFW P A H gLtsP gLtsEqP VP, !FiniteImagegLts P A, @PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ VQ, !FiniteImagegLts Q A, @PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE VE, !FiniteImagegLts E A,
  @AbsAction A H E FinA gLtsE Φ, !Testing_Predicate E A attaboy, !gen_spec_conv co_of gen_conv, !gen_spec_acc PreA co_f gen_acc (fun x => (𝝳  (Φ x)))}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  (p : P) (q : Q) : p ⊑ q -> p ≼ q.
Proof. intros. split. now apply completeness1. now apply completeness2. Qed.

(* From stdpp Require Import gmultiset.

#[global] Program Instance PreActionForFW 
  `{@PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts} 
  : @PreExtAction A H (P * mb A) FinA PreA PreA_eq PreA_countable 𝝳 Φ (FW_gLts gLtsP) := 
  {| pre_co_actions_of p := pre_co_actions_of p.1 ∪ dom (gmultiset_map (fun x => 𝝳 (Φ (co x))) p.2); 
     pre_co_actions_of_fin p := 
     fun pre_μ => ∃ μ', μ' ∈ co_actions_of p /\ pre_μ = (Φ μ'); |}.
Next Obligation.
  intros. exists μ. repeat split; eauto.
Qed.
Next Obligation.
  intros. destruct H2 as (μ' & mem & eq). exists μ'. repeat split; eauto.
Qed.
Next Obligation.
 intros. split.
 - intro mem. destruct p as (p , m). destruct mem as (μ' & mem & eq).
   destruct mem as (μ'' & tr & duo & b). eapply lts_refuses_spec1 in tr as ((p',m') & tr).
   inversion tr; subst.
   + eapply elem_of_union_l. simpl. eapply preactions_of_spec.
     eapply preactions_of_fin_test_spec1. exists μ''. repeat split; eauto.
     eapply lts_refuses_spec2; eauto.
   + destruct (decide (non_blocking μ'')) as [nb | not_nb].
     * assert (non_blocking μ''); eauto. eapply (non_blocking_action_in_ms m μ'' m') in nb; eauto. subst.
       eapply elem_of_union_r. eapply gmultiset_elem_of_dom. simpl.
       assert (gmultiset_map (λ x : A, 𝝳 (Φ (co x))) ({[+ μ'' +]} ⊎ m') = 
        gmultiset_map (λ x : A, 𝝳 (Φ (co x))) {[+ μ'' +]} ⊎ gmultiset_map (λ x : A, 𝝳 (Φ (co x))) m') as eq.
       by eapply gmultiset_map_disj_union.
       rewrite eq. rewrite gmultiset_map_singleton.
       assert (μ'' = (co μ')). { eapply unique_nb; eauto. } subst.
       assert ((co (co μ')) = μ') as eq'. { admit. } rewrite eq'. multiset_solver. 
     * assert (¬ non_blocking μ''); eauto.
       eapply blocking_action_in_ms in not_nb as (eq & duo' & nb); eauto. subst.
       symmetry in duo. eapply (nb_not_nb (co μ'') μ') in nb ;eauto. contradiction.
 - intro mem. destruct p as (p , m). eapply elem_of_union in mem. destruct mem as [p_co_act | multiset_co_act].
   + simpl in p_co_act. eapply preactions_of_spec in p_co_act.
     eapply preactions_of_fin_test_spec2 in p_co_act as (μ' & mem & eq). simpl.
     subst. exists μ'. destruct mem as (μ'' & tr & duo & b).
     repeat split; eauto. exists μ''. repeat split; eauto. eapply lts_refuses_spec2.
     eapply lts_refuses_spec1 in tr as (p' & tr). exists (p' ▷ m).
     eapply ParLeft. exact tr.
   + eapply gmultiset_elem_of_dom in multiset_co_act. simpl in *.
     admit.
Admitted. *)

Lemma completeness {P Q : Type} `{
  @gLtsObaFB P A H gLtsP gLtsEqP VP, !FiniteImagegLts P A,
  @gLtsObaFB Q A H gLtsQ gLtsEqQ VQ, !FiniteImagegLts Q A,
  @gLtsObaFB E A H gLtsE gLtsEqE VE, !FiniteImagegLts E A, @AbsAction A H E FinA gLtsE Φ, !Testing_Predicate E A attaboy}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  (* `{@PreExtAction A H P FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  `{@PreExtAction A H Q FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ}
 *)
  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) E A parallel_inter H (FW_gLts gLtsP) gLtsE}

  `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}
  `{@Prop_of_Inter (Q * mb A) E A parallel_inter H (FW_gLts gLtsQ) gLtsE}

  `{@PreExtAction A H (P * mb A) FinA PreA PreA_eq PreA_countable 𝝳 Φ (FW_gLts gLtsP)}
  `{@PreExtAction A H (Q * mb A) FinA PreA PreA_eq PreA_countable 𝝳 Φ (FW_gLts gLtsQ)}

  `{!gen_spec_conv co_of gen_conv, !gen_spec_acc PreA co_of gen_acc (fun x => (𝝳  (Φ x)))}

  (p : P) (q : Q) : (ctx_pre p q) -> p ▷ ∅ ≼ q ▷ ∅.
Proof.
  intros hctx.
  eapply (@completeness_fw (P * mb A) (Q * mb A)); eauto.
  exact FW_gLtsObaFW. exact gLtsMBFinite. exact FW_gLtsObaFW. exact gLtsMBFinite.
  now rewrite <- Lift.lift_fw_ctx_pre.
Qed.