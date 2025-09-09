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
       Must Lift Subset_Act Convergence Termination.
From Must Require Import ActTau.

(** Test generators specification. **)

Class gen_spec (* {E A : Type} *)
  `{gLts E A, !gLtsEq E A, !Good E A good}
  (co_of : A -> A) (gen : list A -> E) := {
            co_inter μ : parallel_inter μ (co_of μ);
                (* co_of μ interract with μ *)
            co_inter_spec1 μ μ': 
                parallel_inter μ' (co_of μ)
                          -> μ = μ';
                (* co_of μ interract only with μ *)
    (* 1 *) gen_spec_ungood : 
              forall s, ¬ good (gen s) ;
    (* 2 *) gen_spec_mu_lts_co μ1 (* μ2 *) s :
              gen (μ1 :: s) ⟶⋍[co_of μ1] gen s;
    (* 3 *) gen_spec_co_not_nb_lts_tau_ex μ s : 
              ¬ non_blocking (co_of μ) ->
              ∃ e', gen (μ :: s) ⟶ e';
    (* 4 *) gen_spec_co_not_nb_lts_tau_good μ s e : 
              ¬ non_blocking (co_of μ) ->
              gen (μ :: s) ⟶ e -> good e;
    (* 5 *) gen_spec_mu_lts_not_nb_determinacy {μ s e}:
               ¬ non_blocking (co_of μ) ->
              gen (μ :: s) ⟶[co_of μ] e -> e ⋍ gen s;

    (* 6 *) gen_spec_mu_lts_not_nb_side_effect {e μ μ' s} :
              ¬ non_blocking (co_of μ) ->
              gen (μ :: s) ⟶[μ'] e -> μ' ≠ co_of μ -> good e ;
  }.

Lemma co_of_inj `{
  gLts E A, !gLtsEq E A, !Good E A good, !gen_spec co_of f}
  μ μ' :
  co_of μ = co_of μ' -> μ = μ'.
Proof.
  intro eq. 
  assert (parallel_inter μ' (co_of μ)) as inter. rewrite eq.
  eapply co_inter. eapply co_inter_spec1. exact inter.
Qed.

Lemma co_co_is_id `{
  gLts E A, !gLtsEq E A, !Good E A good, !gen_spec co_of f} 
  μ :
  μ = co_of (co_of μ).
Proof.
  assert (parallel_inter (co_of (co_of μ)) (co_of μ)) as inter.
  symmetry. eapply co_inter.
  eapply co_inter_spec1. exact inter.
Qed.

Lemma co_is_co_of_nb `{
  gLts E A, !gLtsEq E A, !Good E A good, !gen_spec co_of f} 
  μ :
  non_blocking (co_of μ) -> co_of μ = co μ.
Proof.
  intro nb. assert (parallel_inter μ (co_of μ)) as inter.
  eapply co_inter. 
  eapply unique_nb; eauto.
Qed.

Lemma co_of_is_co_nb `{
  gLts E A, !gLtsEq E A, !Good E A good, !gen_spec co_of f} 
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
  gLtsOba E A, !Good E A good, !gen_spec co_of f} 
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
  `{gLts E A, ! gLtsEq E A, !Good E A good}
  (co_of : A -> A) (gen_conv : list A -> E) := {
    gen_conv_spec_gen_spec : gen_spec co_of gen_conv ;
    (* c1 *) gen_spec_conv_nil_refuses_mu μ : gen_conv ε ↛[μ] ;
    (* c2 *) gen_spec_conv_nil_lts_tau_ex : ∃ e', gen_conv ε ⟶ e';
    (* c2 *) gen_spec_conv_nil_lts_tau_good e : gen_conv ε ⟶ e -> good e;
  }.

#[global] Existing Instance gen_conv_spec_gen_spec.

Definition union_of_actions_without `{gLts P A} `{gLts Q A}
  (p_L : list P * Q) := ⋃ map lts_acc_set_of p_L.1 ∖ (lts_acc_set_of p_L.2).

Class gen_spec_acc
  (* ! FiniteImagegLts P A *)
  (P : Type) (Q : Type)
  `{LtsP : @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP}
  `{LtsQ : @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ}
  `{@gLts E A H, ! gLtsEq E A, !Good E A good}
  (co_of : A -> A) (gen_acc : list PreA -> list A -> E) 

    := {
    gen_acc_spec_gen_spec (L : list PreA) : gen_spec co_of (gen_acc L) ;
    (* t1 *) gen_spec_acc_nil_refuses_tau (L : list PreA) : 
                gen_acc L ε ↛ ; 
    (* t2 *) gen_spec_acc_nil_refuses_nb (L : list PreA) η : 
                non_blocking η -> gen_acc L ε ↛[η] ;
  (* t3-> *) gen_spec_acc_nil_mu_inv (L : list PreA) μ e : 
                ¬ non_blocking μ -> gen_acc L ε ⟶[μ] e
                    -> (exists η, (* μ = co_of η /\ *) (𝝳 η) ∈ L) ;
  (* t3<- *) gen_spec_acc_nil_mem_lts_inp (L : list PreA) η : 
                (𝝳 η) ∈ L -> ∃ r, gen_acc L ε ⟶[co_of η] r ;
                (* ∃ r μ, gen_acc O ε ⟶[co_of η] r /\ μ = co_of η *)
    (* t4 *) gen_spec_acc_nil_lts_not_nb_good μ e' (L : list PreA) : 
                ¬ non_blocking μ -> gen_acc L ε ⟶[μ] e' -> good e' ;
  }.

#[global] Existing Instance gen_acc_spec_gen_spec.

Lemma co_inter' {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  @gLts E A H, ! gLtsEq E A, !Good E A good, !gen_spec_acc P Q co_of gen_acc}
  `{L : list PreA}
  μ :
  parallel_inter μ (co_of μ).
Proof.
  eapply co_inter. Unshelve. eauto.
Qed.

Lemma co_inter_spec1' {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  @gLts E A H, ! gLtsEq E A, !Good E A good, !gen_spec_acc P Q co_of gen_acc}
  `{L : list PreA}
  μ μ' :
  parallel_inter μ' (co_of μ)
                          -> μ = μ'.
Proof.
  eapply co_inter_spec1. Unshelve. eauto.
Qed.

Lemma co_of_inj' {P Q : Type}  `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  @gLts E A H, ! gLtsEq E A, !Good E A good, !gen_spec_acc P Q co_of gen_acc}
  `{L : list PreA}
  μ μ' :
  co_of μ = co_of μ' -> μ = μ'.
Proof.
  eapply co_of_inj. Unshelve. eauto.
Qed.

Lemma co_co_is_id' {P Q : Type}  `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  @gLts E A H, ! gLtsEq E A, !Good E A good, !gen_spec_acc P Q co_of gen_acc}
  `{L : list PreA}
  μ :
  μ = co_of (co_of μ).
Proof.
  eapply co_co_is_id. Unshelve. eauto.
Qed.

Lemma co_is_co_of_nb' {P Q : Type}  `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  @gLts E A H, ! gLtsEq E A, !Good E A good, !gen_spec_acc P Q co_of gen_acc }
  `{L : list PreA}
  μ :
  non_blocking (co_of μ) -> co_of μ = co μ.
Proof.
  eapply co_is_co_of_nb. Unshelve. eauto.
Qed.

Lemma co_of_is_co_nb' {P Q : Type}  `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  @gLts E A H, ! gLtsEq E A, !Good E A good, !gen_spec_acc P Q co_of gen_acc }
  `{L : list PreA}
  μ :
  non_blocking (co μ) -> dual (co μ) μ -> co_of μ = co μ.
Proof.
  eapply co_of_is_co_nb. Unshelve. eauto.
Qed.

(* Facts about test generators. *)

Lemma gen_conv_always_reduces `{
  gLtsOba E A, !Good E A good, !gen_spec_conv co_of gen_conv} s :
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
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good, !gen_spec_conv co_of gen_conv}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) : 
  p ⤓ -> must p (gen_conv ε).
Proof.
  intros ht.
  induction ht.
  eapply m_step; eauto with mdb.
  - eapply gen_spec_ungood.
  - destruct gen_spec_conv_nil_lts_tau_ex as (e' & l); eauto with mdb.
    exists (p ▷ e'). eapply ParRight; eauto.
  - intros e' l. eapply gen_spec_conv_nil_lts_tau_good in l. eauto with mdb.
  - intros p0 e0 μ μ' inter l1 l2.
    exfalso. eapply lts_refuses_spec2.
    exists e0. eassumption. eapply gen_spec_conv_nil_refuses_mu.
Qed.

Lemma must_gen_conv_wta_mu `{
  gLtsP : gLts P A, 
  gLtsE : ! gLts E A, ! gLtsEq E A, !Good E A good, ! gen_spec_conv co_of gen_conv}

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
    eapply must_preserved_by_synch_if_notgood; eauto with mdb.
    eapply gen_spec_ungood. eapply co_inter.
Qed.

(** First implication of the first requirement. *)

Lemma cnv_if_must `{
  gLtsP : gLts P A, 
  gLtsE : !gLts E A, !gLtsEq E A, !Good E A good, !gen_spec_conv co_of gen_conv}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  s (p : P) : 
  must p (gen_conv s) -> p ⇓ s.
Proof.
  revert p.
  induction s as [|μ s']; intros p hm.
  - eapply cnv_nil.
    eapply (must_terminate_ungood _ _ hm), gen_spec_ungood.
  - eapply cnv_act.
    + eapply (must_terminate_ungood _ _ hm), gen_spec_ungood.
    + intros q w. eapply IHs', must_gen_conv_wta_mu; eauto.
Qed.

Lemma f_gen_lts_mu_in_the_middle `{
  gLtsOba P A, !Good P A good, !gen_spec co_of f} 
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
  gLtsOba P A, !Good P A good, !gen_spec co_of f} 
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
  gLtsOba P A, !Good P A good, !gen_spec co_of f} 
  s μ μ' e:
  ¬ non_blocking (co_of μ) -> f (μ :: s) ⟶[μ'] e -> ¬ non_blocking μ'.
Proof.
  intros not_nb HypTr.
  intro nb. destruct (decide (μ' = co_of μ)) as [eq | neq].
  + subst ;eauto.
  + assert (good e).
    { eapply gen_spec_mu_lts_not_nb_side_effect; eauto. }
    assert (good (f (μ :: s))).
    { eapply good_preserved_by_lts_non_blocking_action_converse; eauto. }
    assert (¬ good (f (μ :: s))).
    { eapply gen_spec_ungood; eauto. }
    contradiction.
Qed.

Lemma f_gen_lts_mu_in_the_middle_not_nb_or_neq `{
  gLtsOba P A, !Good P A good, !gen_spec co_of f} 
  s1 s2 μ μ' e:
  Forall exist_co_nba s1 -> ¬ non_blocking (co_of μ) -> μ' ≠ co_of μ -> ¬ non_blocking μ'
    -> f (s1 ++ μ :: s2) ⟶[μ'] e -> good e.
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
      assert (good t') as happy.
      { eapply IHs' ;eauto. }
      eapply good_preserved_by_lts_non_blocking_action_converse; eauto.
     eapply good_preserved_by_eq; eauto. etransitivity ;eauto. now symmetry.
Qed.

Lemma inversion_gen_mu_not_nb `{
  M1 : gLtsOba E A, !Good E A good, !gen_spec co_of f} 
  s μ' p :
  (forall μ, f ε ↛[μ] \/ (forall e, f ε ⟶[μ] e -> good e)) ->
  f s ⟶[μ'] p ->
  ¬ non_blocking μ' -> 
  good p \/
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
  - edestruct (h μ) as [refuses_f | f_to_good].
    + now eapply lts_refuses_spec2 in refuses_f; eauto.
    + left. eapply f_to_good. eauto.
  - destruct (decide (non_blocking (co_of ν))) as [nb' | not_nb'].
    + assert (f (ν :: s') ⟶⋍[co_of ν] f s') as (v & hlv & eqv).
      eapply gen_spec_mu_lts_co. assert (μ <> (co_of ν)) as not_eq.
      eapply BlockingAction_are_not_non_blocking; eauto.
      destruct (lts_oba_non_blocking_action_confluence nb' not_eq hlv l)
           as (t' & l2 & (t & l1 & heq)).
      destruct (eq_spec (f s') t' (ActExt μ)) as (v' & hlv' & heqv').
      exists v. split. symmetry; eauto. exact l2.
      destruct (decide (good v')) as [happy' | not_happy'].
      ++ left. eapply good_preserved_by_lts_non_blocking_action_converse; eauto.
         eapply good_preserved_by_eq; eauto. etransitivity; eauto. symmetry. eauto.
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
  M1 : gLtsOba E A, !Good E A good, !gen_spec co_of f} 
  s μ p :
  (forall μ, f ε ↛[μ] \/ (forall e, f ε ⟶[μ] e -> good e)) ->
  f s ⟶[μ] p ->
  non_blocking μ -> 
  good p \/
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
  - edestruct (h μ); eauto. now eapply lts_refuses_spec2 in H0; eauto.
  - (* destruct (decide (non_blocking ν)) as [nb'| not_nb']. *)
    + edestruct (gen_spec_mu_lts_co ν s') as (r & hlr & heqr).
      destruct (decide (co_of ν = μ)) as [eq | not_eq].
      ++ right. subst. exists ε, s', ν. repeat split; simpl; eauto with mdb.
         transitivity r; eauto. eapply (lts_oba_non_blocking_action_deter nb l hlr); eauto.
      ++ destruct (lts_oba_non_blocking_action_confluence nb not_eq l hlr )
           as (t' & l2 & (t & l1 & heq)).
         destruct (eq_spec (f s') t (ActExt $ μ)) as (v & hlv & heqv).
         exists r. split; eauto with mdb. now symmetry.
         destruct (decide (good v)) as [happy' | not_happy'].
         +++ exfalso. assert (good (f s')). 
             eapply good_preserved_by_lts_non_blocking_action_converse; eauto.
             assert (¬ good (f s')). eapply gen_spec_ungood. contradiction.
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
            ++++ subst. assert (good p).
                 { eapply gen_spec_mu_lts_not_nb_side_effect; eauto. } eauto. 
Qed.

Lemma inversion_gen_mu `{
  M1 : gLtsOba E A, !Good E A good, !gen_spec co_of f} 
  s μ p :
  (forall μ, f ε ↛[μ] \/ (forall e, f ε ⟶[μ] e -> good e)) ->
  f s ⟶[μ] p ->
  good p \/
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
  M1 : gLtsOba E A, !Good E A good, !gen_spec_conv co_of f}
  s μ p :
  f s ⟶[μ] p ->
  good p \/ 
  ∃ s1 s2 μ', s = s1 ++ μ' :: s2 
  /\ p ⋍ f (s1 ++ s2)
  /\ μ = co_of μ'
  /\ Forall exist_co_nba s1.
Proof.
  intros. eapply inversion_gen_mu; eauto.
  left. eapply gen_spec_conv_nil_refuses_mu; eauto.
Qed.

Lemma inversion_gen_mu_gen_acc {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  M1 : @gLtsOba E A H gLtsE gLtsEqE, !Good E A good, !gen_spec_acc P Q co_of f} 
  s μ (p : E) (O : list PreA) :
  f O s ⟶[μ] p ->
  good p \/ 
  ∃ s1 s2 μ', s = s1 ++ μ' :: s2 
  /\ p ⋍ f O (s1 ++ s2)
  /\ μ = co_of μ'
  /\ Forall exist_co_nba s1.
Proof.
  eapply inversion_gen_mu; eauto. intros μ'.
  destruct (decide (non_blocking μ')) as [nb' | not_nb'].
       +++ left. eapply (@gen_spec_acc_nil_refuses_nb P Q); eauto.
       +++ right. intro e. eapply (@gen_spec_acc_nil_lts_not_nb_good P Q); eauto.
Qed.

Lemma inversion_gen_tau `{
  M1 : gLtsOba E A, !Good E A good, !gen_spec co_of f}
  s q :
  (f ε ↛ \/ (forall e, f ε ⟶ e -> good e)) ->
  (forall μ, f ε ↛[μ] \/ (forall e, f ε ⟶[μ] e -> good e)) ->
  f s ⟶ q ->
  good q \/
  ∃ μ s1 s2 s3, 
  s = s1 ++ [μ] ++ s2 ++ [co_of μ] ++ s3
  /\ q ⋍ f (s1 ++ s2 ++ s3)
  /\ exist_co_nba μ
  /\ Forall exist_co_nba s1 
  /\ Forall exist_co_nba s2.
Proof.
  revert q. induction s as [|μ' s']; intros q h1 h2 HypTr.
  - destruct h1 as [refuses_f | f_to_good].
    + eauto. now eapply lts_refuses_spec2 in refuses_f ; eauto.
    + eauto. 
  - destruct (decide (non_blocking (co_of μ'))) as [nb | not_nb].
    + destruct (decide (good q)) as [happy | not_happy].
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
                  assert (¬ good r2) as not_happy''.
                  eapply ungood_preserved_by_lts_non_blocking_action; eauto.
                  assert (¬ good v) as not_happy'.
                  eapply ungood_preserved_by_eq; eauto.
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
                  left. eapply good_preserved_by_eq; eauto.
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
    + left. eapply gen_spec_co_not_nb_lts_tau_good. exact not_nb. exact HypTr.
Qed.

Lemma inversion_gen_tau_gen_conv `{
  M1 : gLtsOba E A, !Good E A good, !gen_spec_conv co_of f} 
  s q :
  f s ⟶ q ->
  good q \/
  ∃ μ s1 s2 s3,
  s = s1 ++ [μ] ++ s2 ++ [co_of μ] ++ s3
  /\ q ⋍ f (s1 ++ s2 ++ s3)
  /\ exist_co_nba μ
  /\ Forall exist_co_nba s1 
  /\ Forall exist_co_nba s2.
Proof.
  intros.
  eapply inversion_gen_tau; eauto.
  + right. eapply gen_spec_conv_nil_lts_tau_good.
  + intro μ. left. eapply gen_spec_conv_nil_refuses_mu.
Qed.

Lemma inversion_gen_tau_gen_acc {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  M1 : @gLtsOba E A H LtsE LtsEqE, !Good E A good, !gen_spec_acc P Q co_of f}
  s O q :
  f O s ⟶ q ->
  good q \/ (∃ μ s1 s2 s3, s = s1 ++ [μ] ++ s2 ++ [co_of μ] ++ s3
                          /\ q ⋍ f O (s1 ++ s2 ++ s3)
                          /\ exist_co_nba μ
                          /\ Forall exist_co_nba s1 
                          /\ Forall exist_co_nba s2).
Proof.
  intros.
  eapply inversion_gen_tau; eauto.
  + left. eapply (@gen_spec_acc_nil_refuses_tau P Q); eauto.
  + intro μ. destruct (decide (non_blocking μ)) as [nb | not_nb]. 
    ++ left. eapply (@gen_spec_acc_nil_refuses_nb P Q); eauto.
    ++ right. intro e. 
       eapply (@gen_spec_acc_nil_lts_not_nb_good P Q); eauto.
Qed.

(** Converse implication of the first requirement. *)

Lemma must_if_cnv `{
  @gLtsObaFW P A H gLtsP gLtsEqP V,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Good E A good,
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
  + eapply gen_spec_ungood.
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
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Good E A good, 
  !gen_spec_conv co_of gen_conv}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) s : must p (gen_conv s) <-> p ⇓ s.
Proof. split; [eapply cnv_if_must | eapply must_if_cnv]; eauto. Qed.

Lemma completeness1 `{
    @gLtsObaFW P A H gLtsP gLtsEqP V,
    @gLtsObaFW Q A H gLtsQ gLtsEqQ T,
    @gLtsObaFB E A H gLtsE gLtsEqE W, !Good E A good,
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
  `{FiniteImagegLts P A} μ s p q hacnv1 hacnv2 :
  p ⟹{μ} q ->
  map lts_acc_set_of (elements (wt_refuses_set q s hacnv1)) ⊆
    map lts_acc_set_of (elements (wt_refuses_set p (μ :: s) hacnv2)).
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

Lemma lts_tau_acceptance_set_subseteq `{FiniteImagegLts P A} s p q hacnv1 hacnv2 :
  p ⟶ q ->
  map lts_acc_set_of (elements $ wt_refuses_set q s hacnv1) ⊆
    map lts_acc_set_of (elements $ wt_refuses_set p s hacnv2).
Proof.
  intros.
  intros a in__a.
  assert (wt_refuses_set q s hacnv1 ⊆ wt_refuses_set p s hacnv2).
  intros t in__t.
  eapply wt_refuses_set_spec2.
  eapply wt_refuses_set_spec1 in in__t.
  destruct in__t. split; eauto with mdb.
  set_solver.
Qed.

Definition oas `{FiniteImagegLts P A} (p : P) (s : list A) (hcnv : p ⇓ s) : A -> Prop :=
  let ps : list P := elements (wt_refuses_set p s hcnv) in
  ⋃ map lts_acc_set_of ps.

Lemma union_wt_acceptance_set_subseteq `{FiniteImagegLts P A} μ s p q h1 h2 :
    p ⟹{μ} q -> oas q s h1 ⊆ oas p (μ :: s) h2.
Proof.
  intros hw a (O & mem1 & mem2)%elem_of_union_list.
  eapply elem_of_union_list.
  exists O. split; eauto. eapply wt_acceptance_set_subseteq; eauto.
Qed.

Lemma union_acceptance_set_lts_tau_subseteq `{FiniteImagegLts P A} s p q h1 h2 :
  p ⟶ q -> oas q s h1 ⊆ oas p s h2.
Proof.
  intros l a (L & mem1 & mem2)%elem_of_union_list.
  eapply elem_of_union_list.
  exists L. split; eauto. eapply lts_tau_acceptance_set_subseteq; eauto.
Qed.

Lemma aft_not_nb_co_of_must_gen_acc {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  @gLtsOba P A H gLtsP gLtsEqP,
  @gLtsOba E A H gLtsE gLtsEqE, !Good E A good, !gen_spec_acc P Q co_of gen_acc }

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) μ s L :
  p ⤓ -> ¬ non_blocking (co_of μ) -> (forall q, p ⟹{μ} q -> must q (gen_acc L s)) 
              -> must p (gen_acc L (μ :: s) : E).
Proof.
  intro tp. revert L μ s. induction tp.
  intros L μ s not_nb hmq.
  eapply m_step.
  - eapply gen_spec_ungood.
  - edestruct (@gen_spec_co_not_nb_lts_tau_ex E A); eauto with mdb.
    now destruct gen_spec_acc0. exists (p ▷ x). eapply ParRight; eauto.
  - intros. eapply H4. exact H5. eassumption. eauto with mdb.
  - intros e' l. eapply m_now.
    apply (gen_spec_co_not_nb_lts_tau_good μ s e'). eassumption. eassumption.
  - intros p' e' μ' μ'' inter l0 l1.
    destruct (decide (μ'' = co_of μ)) as [eq | neq].
    + subst. eapply gen_spec_mu_lts_not_nb_determinacy in not_nb as h1; eauto. subst.
      eapply must_eq_client. symmetry; eauto.
      eapply hmq.
      eapply @co_inter_spec1' in inter; eauto. subst. eauto with mdb.
    + eapply m_now. eapply gen_spec_mu_lts_not_nb_side_effect; eauto.
Qed.

Lemma gen_acc_tau_ex {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  M1 : @gLtsObaFB E A H LtsE LtsEqE LtsOBAE, !Good E A good, !gen_spec_acc P Q co_of f} 
  s1 s2 s3 μ L :
  exist_co_nba μ -> Forall exist_co_nba s1 -> Forall exist_co_nba s2 ->
  f L (s1 ++ [μ] ++ s2 ++ [co_of μ] ++ s3) ⟶⋍ f L (s1 ++ s2 ++ s3).
Proof.
  intros co_and_nb Hyp Hyp'.
  assert (f L (s1 ++ [μ] ++ s2 ++ [co_of μ] ++ s3) ⟶⋍[co_of μ]
            f L (s1 ++ s2 ++ [co_of μ] ++ s3)) as (e1 & l1 & heq1).
  eapply (@f_gen_lts_mu_in_the_middle E A _ _ _ _ _ _  co_of (f L) _
            s1 (s2 ++ [co_of μ] ++ s3) μ); simpl in *; eauto. (* 3 *)
  assert (f L (s1 ++ s2 ++ [co_of μ] ++ s3) ⟶⋍[co_of (co_of μ)]
            f L ((s1 ++ s2) ++ s3)) as (e2 & l2 & heq2).
  replace (s1 ++ s2 ++ [co_of μ] ++ s3) with ((s1 ++ s2) ++ [co_of μ] ++ s3).
  eapply (@f_gen_lts_mu_in_the_middle E A _ _ _ _ _ _ co_of (f L) _
            (s1 ++ s2) s3 (co_of μ)); simpl in *; eauto.
  unfold exist_co_nba. eapply Forall_app; eauto.
  now rewrite <- app_assoc.
  assert (μ =co_of (co_of μ)) as eq. eapply (@co_co_is_id' P Q); eauto.
  rewrite <-eq in l2.
  destruct co_and_nb as (a' & nb & duo). 
  assert (a' = co μ). eapply unique_nb; eauto. subst. 
  assert (co_of μ = co μ) as eq'. eapply (@co_of_is_co_nb' P Q); eauto.
  rewrite<- eq' in nb, duo.
  (* subst.  *)simpl in *.
  edestruct (eq_spec e1 e2) as (e' & l' & heq'). eauto.
  destruct (lts_oba_fb_feedback nb duo l1 l') as (t & lt & heqt); eauto.
  exists t. split; eauto.
  rewrite <- app_assoc in heq2.
  transitivity e'. eauto.
  transitivity e2; eauto.
Qed.

Lemma must_f_gen_a_subseteq_non_blocking {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Good E A good, !gen_spec_acc P Q co_of gen_acc} 
  s e η L1 :
  non_blocking η -> gen_acc L1 s ⟶[η] e 
    -> forall L2, L1 ⊆ L2
      -> exists t, gen_acc L2 s ⟶[η] t.
Proof.
  revert e L1.
  induction s as [|μ s']; intros e L1 nb l L2 hsub.
  + exfalso. eapply lts_refuses_spec2, (@gen_spec_acc_nil_refuses_nb P Q); eauto.
  + destruct (decide (non_blocking μ)) as [nb' | not_nb'].
    ++ edestruct
         (@gen_spec_mu_lts_co E A _ _ _ _ _ co_of (gen_acc L2) _ μ s')
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
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Good E A good, !gen_spec_acc P Q co_of gen_acc} 
  s e μ' L1 :
  ¬ non_blocking μ' -> gen_acc L1 s ⟶[μ'] e
    -> forall L2, L1 ⊆ L2 
      -> (exists t, gen_acc L2 s ⟶[μ'] t) \/ (∃ e', gen_acc L2 s ⟶ e').
Proof.
  revert e L1.
  induction s as [|μ s']; intros e L1 not_nb l L2 hsub.
  + assert (∃ η : A, (* μ' = co_of η ∧ *) 𝝳 η ∈ L1) as (μ'' (* & eq *) & In).
    eapply (@gen_spec_acc_nil_mu_inv P Q); eauto. (* subst. *)
    eapply hsub in In. eapply (@gen_spec_acc_nil_mem_lts_inp P Q) in In as (r & HypTr); eauto.
    eauto. admit.
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
Admitted. *)

(* Lemma must_f_gen_a_subseteq_tau {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Good E A good, !gen_spec_acc P Q co_of gen_acc}
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

(* Lemma must_f_gen_a_subseteq_nil {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Good E A good, !gen_spec_acc P Q co_of gen_acc}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) L1 : 
  must p (gen_acc L1 ε) 
    -> forall L2, L1 ⊆ L2 
      -> must p (gen_acc L2 ε).
Proof.
  intros hm.
  assert (hpt : p ⤓)
    by now (eapply must_terminate_ungood , gen_spec_ungood; eauto).
  induction hpt. dependent induction hm; intros L2 hsub.
  - assert (¬ good (gen_acc L1 ε)).
    { now eapply gen_spec_ungood. }
    contradiction.
  - eapply m_step; eauto with mdb.
    + eapply gen_spec_ungood.
    + destruct ex as ((p' & e') & l').
      inversion l'; subst.
      +++ exists (p' ▷ (gen_acc L2 ε)). eapply ParLeft; eauto.
      +++ exfalso. assert ({q : E | gen_acc L1 ε ⟶ q}) as impossible.
          eauto.
          eapply lts_refuses_spec2 in impossible.
          assert (gen_acc L1 ε ↛). eapply (@gen_spec_acc_nil_refuses_tau P Q); eauto.
          contradiction.
      +++ destruct (decide (non_blocking μ1)) as [nb1 | not_nb1]; 
          destruct (decide (non_blocking μ2)) as [nb2 | not_nb2].
          ++++ contradict nb1.
               eapply dual_blocks; eauto.
          ++++ assert (∃ η : A, (* μ2 = co_of η ∧ *) 𝝳 η ∈ L1) 
               as (μ'' (* & eq' *) & In).
               eapply (@gen_spec_acc_nil_mu_inv P Q); eauto. subst.
               eapply hsub in In. eapply (@gen_spec_acc_nil_mem_lts_inp P Q) in In 
                as (e & l); eauto.
               exists (p' ▷ e). eapply ParSync; eauto. admit.
          ++++ exfalso.
               assert ({q : E | gen_acc L1 ε ⟶[μ2] q}) as impossible. eauto.
               eapply lts_refuses_spec2 in impossible. 
               assert (gen_acc L1 ε ↛[μ2]). eapply (@gen_spec_acc_nil_refuses_nb P Q); eauto.
               contradiction.
          ++++ assert (∃ η : A, (* μ2 = co_of η ∧ *) 𝝳 η ∈ L1) as (μ'' (* & eq' *) & In).
               eapply (@gen_spec_acc_nil_mu_inv P Q); eauto. subst.
               eapply hsub in In. eapply (@gen_spec_acc_nil_mem_lts_inp P Q) in In 
                as (e & l); eauto. exists (p' ▷ e). eapply ParSync; eauto. admit.
    + intros e l.
      exfalso. 
      assert ({q : E | gen_acc L2 ε ⟶ q}) as impossible. eauto.
      eapply lts_refuses_spec2 in impossible. 
      assert (gen_acc L2 ε ↛). eapply (@gen_spec_acc_nil_refuses_tau P Q); eauto.
      contradiction.
    + intros p' e' μ μ' inter l2 l1.
      destruct (decide (non_blocking μ')) as [nb | not_nb].
      ++ exfalso. 
         assert ({q : E | gen_acc L2 ε ⟶[μ'] q}) as impossible. eauto.
         eapply lts_refuses_spec2 in impossible. 
         assert (gen_acc L2 ε ↛[μ']). eapply (@gen_spec_acc_nil_refuses_nb P Q); eauto.
         contradiction.
      ++ eapply (@gen_spec_acc_nil_lts_not_nb_good P Q) in l1;eauto. admit.
Admitted. *)

(* Lemma must_f_gen_a_subseteq {P Q : Type} `{
  gLtsP: @gLts P A H, PreAP : @PreExtAction A H P PreA 𝝳 gLtsP,
  gLtsQ: @gLts Q A H, PreAQ : @PreExtAction A H Q PreA 𝝳 gLtsQ,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Good E A good,
  !gen_spec_acc P Q co_of gen_acc}

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
  - (* eapply must_f_gen_a_subseteq_nil; eauto. *) admit.
  - assert (htp : p ⤓) by (eapply must_terminate_ungood, gen_spec_ungood; eauto).
    induction htp.
    inversion hm. now eapply gen_spec_ungood in H4.
    eapply m_step; eauto with mdb.
    + eapply gen_spec_ungood.
    + destruct ex as (t & l). inversion l; subst; eauto with mdb.
      ++ exists (a2 ▷ gen_acc L2 (ν :: s')). eapply ParLeft; eauto.
      ++ (* eapply must_f_gen_a_subseteq_tau in l0 as (e & hle).
         exists (p ▷ e). eapply ParRight; eauto. eauto. *) admit.
      ++ destruct (decide (non_blocking μ1)) as [nb1 | not_nb1]; 
         destruct (decide (non_blocking μ2)) as [nb2 | not_nb2].
         +++ contradict nb1. 
             eapply dual_blocks; eauto.
         +++ (* eapply must_f_gen_a_subseteq_not_non_blocking in l2 as [(t & hl_mu) | (t & hl_tau)]; eauto with mdb.
             ++++ exists (a2 ▷ t). eapply ParSync; eauto.
             ++++ exists (p ▷ t). eapply ParRight; eauto. *) admit.
         +++ eapply (@must_f_gen_a_subseteq_non_blocking P Q) in l2 as (t & hl); eauto with mdb.
             exists (a2 ▷ t). eapply ParSync; eauto.
         +++ (* eapply must_f_gen_a_subseteq_not_non_blocking in l2 as [(t & hl_mu) | (t & hl_tau)]; eauto with mdb.
             ++++ exists (a2 ▷ t). eapply ParSync; eauto.
             ++++ exists (p ▷ t). eapply ParRight; eauto. *) admit.
    + intros e' l.
      edestruct @inversion_gen_tau_gen_acc as [|Hyp]; eauto with mdb.
      destruct Hyp as (μ & s1 & s2 & s3 & heqs & sc & himu & his1 & his2).
      eapply (must_eq_client p (gen_acc L2 (s1 ++ s2 ++ s3))). now symmetry.
      (* edestruct (gen_acc_tau_ex s1 s2 s3 μ L1) as (t & hlt & heqt); eauto.
      eapply Hlength; eauto.
      ++ rewrite heqs, 6 length_app. simpl. lia.
      ++ eapply must_eq_client. eapply heqt. eapply et. now rewrite heqs. *) admit.
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
      eassumption.
Admitted. *)

Lemma must_gen_acc_refuses {P Q : Type} `{
  @gLtsOba P A H gLtsP gLtsEqP,
  @gLtsOba Q A H gLtsQ gLtsEqQ,
  @gLtsOba E A H gLtsE gLtsEqE, !Good E A good, !gen_spec_acc P Q co_of gen_acc}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (q : Q): 

  p ↛ (* -> *) (* ¬  *) (* (∃ x, x ∈ lts_acc_set_of p ∖ O) *)
      -> must p (gen_acc ([p] , q) ε) \/ (lts_acc_set_of p ⊆ lts_acc_set_of q).
Proof.
  intros refuses.
  ++ destruct (decide (lts_refuses (p , (gen_acc ([p] ▷ q) ε)) τ)) as [stable | not_stable].
       +++ right.
           intro a'. intro Hyp.
           destruct (decide (a' ∈ lts_acc_set_of q)).
           ++++ eauto.
           ++++ exfalso. assert (a' ∈ union_of_actions_without ([p] ▷ q)) as mem.
                unfold union_of_actions_without. simpl. split; eauto. left; eauto.
                eapply gen_spec_acc_nil_mem_lts_inp in mem as (e & Tr').
                assert (¬ (p ▷ gen_acc ([p] ▷ q) ε) ↛). eapply lts_refuses_spec2.
                eapply lts_refuses_spec1 in Hyp as (p' & Tr).
                assert (parallel_inter a' (co_of a')). eapply co_inter; eauto.
                exists (p', e). eapply ParSync; eauto. contradiction.
      +++ eapply lts_refuses_spec1 in not_stable as ((p' , e') & Trr).
          inversion Trr; subst.
          ++++ assert (¬ p ↛ ). eapply lts_refuses_spec2; eauto. contradiction.
          ++++ assert (¬ gen_acc ([p'] ▷ q) ε ↛ ). eapply lts_refuses_spec2; eauto.
               assert (gen_acc ([p'] ▷ q) ε ↛). eapply gen_spec_acc_nil_refuses_tau.
               contradiction.
          ++++ assert (¬ non_blocking μ2) as not_nb.
               intro nb.
               eapply @gen_spec_acc_nil_refuses_nb in nb; eauto.
               instantiate (1 := ([p] ▷ q)) in nb.
               assert (¬ gen_acc ([p] ▷ q) ε ↛[μ2]). eapply lts_refuses_spec2; eauto.
               contradiction.
               assert (l'2 : gen_acc ([p] ▷ q) ε ⟶[μ2] e'). eauto.
               eapply gen_spec_acc_nil_mu_inv in l2 as (μ' & eq' & mem); eauto; subst.
               eapply co_inter_spec1 in eq as eq'. subst.
               left. eapply m_step.
               +++++ now eapply gen_spec_ungood.
               +++++ exists (p' , e').
                     eapply ParSync; eauto.
               +++++ intros p'' l'. exfalso. eapply (@lts_refuses_spec2 P); eauto with mdb.
               +++++ intros e'' l'. exfalso.
                     eapply (@lts_refuses_spec2 E A _ _ (gen_acc ([p] , q) ε) τ); eauto with mdb.
                     eapply gen_spec_acc_nil_refuses_tau.
               +++++ intros p'' e'' μ' μ inter l'1 l'0.
                     destruct (decide (non_blocking μ)) as [nb' | not_nb'].
                     ++++++ exfalso.
                            eapply (@lts_refuses_spec2 E); eauto with mdb.
                            eapply gen_spec_acc_nil_refuses_nb; eauto.
                     ++++++ eapply gen_spec_acc_nil_lts_not_nb_good in l'0; eauto. eauto with mdb.
        Unshelve. exact ([p] , q). exact ([p] , q).
Qed.

Lemma must_gen_acc_refuses_inv' {P Q : Type} `{
  LtsP : @gLts P A H,
  LtsQ : @gLts Q A H,
  @gLtsOba P A H gLtsP gLtsEqP,
  @gLtsOba E A H gLtsE gLtsEqE, !Good E A good, !gen_spec_acc P Q co_of gen_acc}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) O : 

  lts_acc_set_of p ⊆ O -> ¬ (∃ x, x ∈ lts_acc_set_of p ∖ O) .
Proof.
  intros imp. intros (x & Hyp). destruct Hyp.
  eapply imp in H3. contradiction.
Qed.

Lemma must_gen_acc_refuses_inv'' {P Q : Type} `{
  gLtsP : @gLts P A H,
  gLtsQ : @gLts Q A H,
  @gLtsOba P A H gLtsP gLtsEqP, 
  @gLtsOba E A H gLtsE gLtsEqE, !Good E A good, !gen_spec_acc P Q co_of gen_acc}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) O : 

  (∃ x, x ∈ lts_acc_set_of p ∖ O) -> ¬ lts_acc_set_of p ⊆ O.
Proof.
  intros imp. intro imp'. eapply (@must_gen_acc_refuses_inv' P Q) in imp'; eauto.
Qed.

Lemma must_gen_a_with_nil {P Q : Type} `{
  gLtsP : @gLts P A H,
  gLtsQ : @gLts Q A H,
  @gLtsObaFW P A H gLtsP gLtsEqP V, !FiniteImagegLts P A,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ T, !FiniteImagegLts Q A,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Good E A good, !gen_spec_acc P Q co_of gen_acc}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  (p : P) (hcnv : p ⇓ ε) (q : Q):

  (exists p', p ⟹ p' /\ lts_refuses p' τ /\ lts_acc_set_of p' ⊆ lts_acc_set_of q)
  \/ must p (gen_acc (elements (wt_refuses_set p ε hcnv) , q) ε).
Proof.
  induction (cnv_terminate p ε hcnv) as (p, hpt, ihhp).
  destruct (decide (lts_refuses p τ)) as [st | (p'' & l)%lts_refuses_spec1].
  + destruct (must_gen_acc_refuses p q st) as [Hyp | Hyp].
    ++ right. eauto. unfold oas.
       rewrite wt_refuses_set_refuses_singleton, elements_singleton; eauto.
    ++ left. exists p. split; eauto. constructor.
  + assert (∀ q0 : P,
         q0 ∈ lts_tau_set p
         → (∃ p' : P, q0 ⟹ p' ∧ p' ↛ ∧ lts_acc_set_of p' ⊆ lts_acc_set_of q)
             ∨ (exists h, must q0 (gen_acc (elements (wt_refuses_set q0 ε h) , q) ε))) as Hyp.
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
           ++++ eapply gen_spec_ungood.
           ++++ exists (p'' ▷ gen_acc (elements (wt_refuses_set p ε hcnv) ▷ q) ε). eapply ParLeft; eauto.
           ++++ intros p0 l0%lts_tau_set_spec.
                eapply Forall_forall in Hyp' as (h0 & hm).
                eapply must_f_gen_a_subseteq; eauto.
                eapply difference_mono_r.
                eapply union_acceptance_set_lts_tau_subseteq. 
                eapply lts_tau_set_spec. exact l0.
                eauto.
           ++++ intros e' l'. exfalso.
                eapply (@lts_refuses_spec2 E). eauto. eapply gen_spec_acc_nil_refuses_tau.
           ++++ intros p0 e0 μ' μ inter lp le.
                destruct (decide (non_blocking μ)) as [nb | not_nb].
                +++++ exfalso. 
                      assert ({q' : E | gen_acc (elements (wt_refuses_set p ε hcnv) , q) ε ⟶[μ] q'}).
                      eauto. eapply (lts_refuses_spec2); eauto. 
                      eapply gen_spec_acc_nil_refuses_nb; auto.
                +++++ eapply m_now. eapply (@gen_spec_acc_nil_lts_not_nb_good P Q); eauto.
Qed.

Lemma must_gen_a_with_s {P Q : Type} `{
  @gLtsObaFW P A H gLtsP gLtsEqP V, !FiniteImagegLts P A,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ T, !FiniteImagegLts Q A,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Good E A good, !gen_spec_acc P Q co_of gen_acc} 

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}

  s (p : P) (hcnv : p ⇓ s) (q : Q):

  (exists p', p ⟹[s] p' /\ lts_refuses p' τ /\ lts_acc_set_of p' ⊆ lts_acc_set_of q) 
      \/ must p (gen_acc (elements (wt_refuses_set p s hcnv) , q) s).
Proof.
  revert p hcnv q.
  induction s as [|μ s'].
  - intros. eapply must_gen_a_with_nil.
  - intros p hcnv q.
    set (ps := wt_set_mu p μ s' hcnv).
    inversion hcnv as [| ? ? ? conv Hyp_conv]; subst.
    assert (hcnv0 : forall p', p' ∈ ps -> p' ⇓ s') by (intros ? mem%wt_set_mu_spec1; eauto).
    assert (he : ∀ p', p' ∈ ps ->
     ((exists pr p0, p0 ∈ wt_refuses_set p' s' pr ∧ lts_acc_set_of p0 ⊆ lts_acc_set_of q) 
             \/ (exists h, must p' (gen_acc (elements (wt_refuses_set p' s' h) , q) s')))).
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
         eapply (@co_inter' P Q); eauto. exact (elements ps , q).
         destruct (decide (non_blocking (co_of μ))) as [nb | not_nb]. 
         inversion hcnv; subst.
         +++ destruct (lts_oba_fw_forward p (co_of μ) μ) as (p' & l0 & l1); eauto.
             assert (gen_acc (elements (wt_refuses_set p (μ :: s') hcnv) , q) (μ :: s')
                   ⟶⋍[co_of $ μ] gen_acc (elements (wt_refuses_set p (μ :: s') hcnv) , q) s')
            as (e' & hle' & heqe') by eapply gen_spec_mu_lts_co.
             eapply must_non_blocking_action_swap_l_fw; eauto.
             eapply (must_eq_client _ _ _ (symmetry heqe')).
             edestruct (Hyp p') as (? & hm).
             eapply wt_set_mu_spec2; eauto with mdb.
             assert (oas p' s' x ∖ lts_acc_set_of q ⊆ oas p (μ :: s') hcnv ∖ lts_acc_set_of q).
             eapply difference_mono_r.
             eapply union_wt_acceptance_set_subseteq; eauto with mdb.
             eapply must_f_gen_a_subseteq; eauto.
         +++ eapply aft_not_nb_co_of_must_gen_acc; eauto.
             intros p' hw.
             edestruct (Hyp p') as (? & hm).
             eapply wt_set_mu_spec2; eauto.
             assert ((oas p' s' x ∖ lts_acc_set_of q) ⊆ oas p (μ :: s') hcnv ∖ lts_acc_set_of q).
             eapply difference_mono_r. 
             eapply union_wt_acceptance_set_subseteq; eauto with mdb.
             eapply must_f_gen_a_subseteq; eauto.
Qed.

Lemma not_must_gen_a_without_required_acc_set {P Q : Type} `{
  gLtsP : @gLts P A H,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ V,
  @gLtsObaFB E A H gLtsE gLtsEqE W, !Good E A good, !gen_spec_acc P Q co_of gen_acc} 

  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  (q q' : Q) s (L : list P) :

  q ⟹[s] q' -> q' ↛ -> ¬ must q (gen_acc (L , q') s).
Proof.
  intros wt hst.
  dependent induction wt; intros hm. rename p into q.
  - inversion hm as [happy | ]; subst.
    ++ contradict happy. eapply gen_spec_ungood.
    ++ destruct ex as (t & l). inversion l; subst.
       +++ eapply (lts_refuses_spec2 q τ); eauto with mdb.
       +++ eapply lts_refuses_spec2, (@gen_spec_acc_nil_refuses_tau P Q); eauto.
       +++ destruct (decide (non_blocking μ1)) as [nb1 | not_nb1]; 
           destruct (decide (non_blocking μ2)) as [nb2 | not_nb2].
           ++++ contradict nb1. 
                eapply dual_blocks; eauto.
           ++++ eapply gen_spec_acc_nil_mu_inv in l2 as (μ' & eq' & In); eauto. subst.
                assert (μ' = μ1). eapply (@co_inter_spec1' P Q);eauto. subst.
                assert (lts_acc_set_of q μ1) as not_refuses.
                assert ({q' : Q | q ⟶[μ1] q'}) as Hyp. eauto. 
                eapply lts_refuses_spec2 in Hyp.
                intro refuses. contradiction.
                destruct In; simpl in *.
                contradiction.
           ++++ eapply lts_refuses_spec2, (@gen_spec_acc_nil_refuses_nb P Q); eauto.
           ++++ eapply gen_spec_acc_nil_mu_inv in l2 as (μ' & eq' & In); eauto. subst.
                assert (μ' = μ1). eapply (@co_inter_spec1' P Q); eauto. subst.
                assert (lts_acc_set_of q μ1) as not_refuses.
                assert ({q' : Q | q ⟶[μ1] q'}) as Hyp. eauto. 
                eapply lts_refuses_spec2 in Hyp.
                intro refuses. contradiction.
                destruct In.
                contradiction.
  - eapply (IHwt hst), (must_preserved_by_lts_tau_srv p q _ hm l).
  - eapply (IHwt hst).
    assert (gen_acc (L , t) (μ :: s) ⟶⋍[co_of μ]
              gen_acc (L , t) s) as (e' & hle' & heqe')
    by eapply gen_spec_mu_lts_co.
    eapply must_eq_client; eauto.
    inversion hm as [happy |]; subst.
    + now eapply gen_spec_ungood in happy.
    + assert (parallel_inter μ (co_of μ)) as inter. eapply (@co_inter' P Q); eauto. eauto.
Qed.

Lemma completeness2 {P Q : Type} `{
  @gLtsObaFW P A H gLtsP gLtsEqP VP, !FiniteImagegLts P A,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ VQ, !FiniteImagegLts Q A,
  @gLtsObaFB E A H gLtsE gLtsEqE VE, 
  !Good E A good, !gen_spec_acc P Q co_of gen_acc}

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
  @gLtsObaFW P A H gLtsP gLtsEqP VP, !FiniteImagegLts P A,
  @gLtsObaFW Q A H gLtsQ gLtsEqQ VQ, !FiniteImagegLts Q A, 
  @gLtsObaFB E A H gLtsE gLtsEqE VE, !FiniteImagegLts E A, 
  !Good E A good, !gen_spec_conv co_of gen_conv, !gen_spec_acc P Q co_f gen_acc}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  (p : P) (q : Q) : p ⊑ q -> p ≼ q.
Proof. intros. split. now apply completeness1. now apply completeness2. Qed.

Lemma completeness {P Q : Type} `{
  @gLtsObaFB P A H gLtsP gLtsEqP VP, !FiniteImagegLts P A,
  @gLtsObaFB Q A H gLtsQ gLtsEqQ VQ, !FiniteImagegLts Q A,
  @gLtsObaFB E A H gLtsE gLtsEqE VE, !FiniteImagegLts E A, !Good E A good}

  `{@Prop_of_Inter P E A parallel_inter H gLtsP gLtsE}
  `{@Prop_of_Inter Q E A parallel_inter H gLtsQ gLtsE}

  `{@Prop_of_Inter P (mb A) A fw_inter H gLtsP MbgLts}
  `{@Prop_of_Inter (P * mb A) E A parallel_inter H (FW_gLts gLtsP) gLtsE}

  `{@Prop_of_Inter Q (mb A) A fw_inter H gLtsQ MbgLts}
  `{@Prop_of_Inter (Q * mb A) E A parallel_inter H (FW_gLts gLtsQ) gLtsE}

  `{!gen_spec_conv co_of gen_conv, !gen_spec_acc (P * mb A) (Q * mb A) co_of gen_acc}

  (p : P) (q : Q) : p ⊑ q -> p ▷ ∅ ≼ q ▷ ∅.
Proof.
  intros hctx.
  eapply (@completeness_fw (P * mb A) (Q * mb A)); eauto.
  exact FW_gLtsObaFW. exact gLtsMBFinite. exact FW_gLtsObaFW. exact gLtsMBFinite.
  now rewrite <- Lift.lift_fw_ctx_pre.
Qed.