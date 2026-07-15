(*
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

From Stdlib Require ssreflect Setoid.
From Stdlib Require Import Unicode.Utf8 List.
From Stdlib.Program Require Import Wf Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.

From stdpp Require Import sets base countable finite gmap list finite
                          decidable finite gmap.
From stdpp Require gmultiset.
From TestingTheory Require Import gLts Bisimulation Lts_OBA
  WeakTransitions Lts_OBA_FB Lts_FW FiniteImageLTS
  InteractionBetweenLts MultisetLTSConstruction
  ParallelLTSConstruction ForwarderConstruction
  Must Lift Subset_Act Convergence Termination
  Testing_Predicate DefinitionAS ActTau Lts_Finite_Output_Chain Subset_Act
  coWeakTransition coConvergence coFiniteImage DefinitionASco.

Import ListNotations.

(** * Completeness for the co-acceptance-set preorder

    This file mirrors [Completeness.v] (the plain acceptance-set preorder)
    for the "co" preorder defined in [DefinitionASco.v], which is stated
    directly in terms of the relational duals [cocnv]/[cowt] ([⇓ᶜᵒ]/[⟹ᶜᵒ])
    from [coConvergence.v]/[coWeakTransition.v], instead of testing a
    [map co]-translated trace ([coₜ]) as the original file does.

    All of the test-generator machinery ([test_spec], [test_convergence_spec],
    [test_co_acceptance_set_spec]) and every lemma about it that only talks
    about [T]/[A] (never about [P]'s own convergence/weak-transition
    structure) is copied below, verbatim, from [Completeness.v] — this file
    is kept independent of it on purpose (no [Require Import Completeness]),
    so it does not need the map-[coₜ]-based [cnv_if_must]/[must_if_cnv]/
    [completeness1]/[wt_acceptance_set_subseteq]/[oas]/etc. that file also
    defines but this one has no use for. Only the lemmas that relate [P]/[Q]
    to the tests via [⇓]/[⟹] are re-derived (not copied) here against
    [⇓ᶜᵒ]/[⟹ᶜᵒ]. *)

(** ** Axioms for completeness (copied from [Completeness.v], unchanged) *)
(** *** Common axioms for the generation of tests **)

(* TODO : move in Helpers *)
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

(** *** Common axioms for the generation of tests **)
Class test_spec (* {E A : Type} *)
  `{gLtsT : @gLtsEq T A H, !Testing_Predicate outcome _}
  (gen : list A -> T) := {
    (* 1 *) test_ungood :
              forall s, ¬ outcome (gen s) ;
    (* 2 *) test_next_step μ s :
              gen (μ :: s) ⟶⋍[μ] gen s;
    (* 3 *) test_tau_transition β s :
              blocking β ->
              ∃ t, gen (β :: s) ⟶ t;
    (* 4 *) test_reset_tau_path β s t :
              blocking β ->
              gen (β :: s) ⟶ t -> outcome t;
    (* 5 *) test_follows_trace_determinacy {β s t}:
              blocking β ->
              gen (β :: s) ⟶[β] t -> t ⋍ gen s;
    (* 6 *) test_side_effect_by_construction {t β μ s} :
              blocking β ->
              gen (β :: s) ⟶[μ] t -> μ ≠ β -> outcome t ;
  }.

(** *** Axioms for tests on convergence *)
Class test_convergence_spec
  `{@gLtsEq T A H, !Testing_Predicate outcome _}
  (tconv : list A -> T) := {
    tconv_test_spec : test_spec tconv ;
    (* c1 *) tconv_does_no_external_action μ : tconv ε ↛[μ] ;
    (* c2 *) tconv_can_compute : ∃ e', tconv ε ⟶ e';
    (* c3 *) tconv_computes_to_good e : tconv ε ⟶ e -> outcome e;
  }.

#[global] Existing Instance tconv_test_spec.

(** *** Axioms for the tests on co-acceptance sets *)
Class test_co_acceptance_set_spec (PreAct : Type) `{CC : Countable PreAct}
  `{@gLtsEq T A H, !Testing_Predicate outcome _}
  (ta : gset PreAct -> list A -> T) (Γ : A -> PreAct)
    := {
    ta_test_spec (E : gset PreAct) : test_spec (ta E) ;
    (* t1 *) ta_does_no_tau (E : gset PreAct) :
                ta E ε ↛ ;
    (* t2 *) ta_does_no_non_blocking_actions (E : gset PreAct) η :
                non_blocking η -> ta E ε ↛[η] ;
  (* t4-> *) ta_actions_are_in_its_gamma_set (E : gset PreAct) β e :
                blocking β -> ta E ε ⟶[β] e
                    -> (Γ β) ∈ E ;
  (* t4<- *) ta_has_a_representative_transition_for_its_gamma_set (E : gset PreAct) pβ :
                pβ ∈ E ->
                ∃ r β, ta E ε ⟶[β] r /\ (Γ β = pβ);
    (* t3 *) ta_transition_to_good β e' (E : gset PreAct) :
                blocking β -> ta E ε ⟶[β] e' -> outcome e' ;
  }.

#[global] Existing Instance ta_test_spec.

(** *** Facts about test generators *)
Lemma tconv_always_reduces `{
  gLtsOba T , !Testing_Predicate outcome _, !test_convergence_spec tconv} s :
  ∃ t, tconv s ⟶ t.
Proof.
  induction s as [|μ s'].
  - eapply tconv_can_compute.
  - destruct (decide (non_blocking μ)) as [nb | not_nb].
    + destruct IHs' as (e & l).
      destruct (test_next_step μ s') as (e' & hl' & heq).
      destruct (eq_spec e' e τ) as (e0 & hl0 & heqe0). eauto with mdb.
      destruct (nb_delay nb hl' hl0)
        as (r & l1 & l2); eauto.
    + eapply test_tau_transition. exact not_nb.
Qed.

Lemma f_gen_lts_mu_in_the_middle `{
  gLtsT : gLtsOba T, !Testing_Predicate outcome _, !test_spec f}
  s1 s2 μ:
  Forall non_blocking s1
    -> f (s1 ++ μ :: s2) ⟶⋍[μ] f (s1 ++ s2).
Proof.
  revert s2 μ.
  induction s1 as [|ν s']; intros s2 μ his ; simpl in *.
  - eapply (test_next_step μ).
  - inversion his as [| ? ? nb his']; subst.
    destruct (IHs' s2 μ his') as (r & hlr & heqr).
    edestruct (test_next_step ν (s' ++ μ :: s2))
      as (t & hlt & heqt).
    edestruct (eq_spec t r) as (u & hlu & hequ).
    { eauto with mdb. }
    destruct (nb_delay nb hlt hlu)
      as (v & l1 & (t' & l2 & heq')).
    exists v. split. eassumption.
    destruct (test_next_step ν (s' ++ s2)) as (w & hlw & heqw).
    eapply backwards_nb_determinacy; try eassumption.
    etrans. eauto. etrans. eauto. etrans. eauto. now symmetry.
Qed.

Lemma f_gen_lts_mu_in_the_middle' `{
  gLtsT : gLtsOba T, !Testing_Predicate outcome _, !test_spec f}
  s1 s2 μ t:
  Forall non_blocking s1
    -> f (s1 ++ μ :: s2) ⟶⋍[μ] t -> t ⋍ f (s1 ++ s2).
Proof.
  revert s2 μ t.
  induction s1 as [|ν s']; intros s2 μ t his HypTr; simpl in *.
  - destruct (decide (non_blocking μ)) as [nb | not_nb].
    + assert (f (ε ++ μ :: s2) ⟶⋍[μ] f (ε ++ s2)) as HypTr'.
      { eapply f_gen_lts_mu_in_the_middle. eauto. }
      destruct HypTr as (e & HypTr & equiv).
      destruct HypTr' as (e' & HypTr' & equiv'); simpl in *.
      assert (e ⋍ e').
      { eapply nb_determinacy; eauto. }
      etransitivity. symmetry. exact equiv. etransitivity; eauto.
    + destruct HypTr as (e & HypTr & equiv).
      assert (e ⋍ f s2) as equiv'.
      { eapply test_follows_trace_determinacy; eauto. }
      etransitivity. symmetry. exact equiv. eauto.
  - inversion his; subst.
    destruct (decide (non_blocking μ)) as [nb | not_nb].
    + assert (f ((ν :: s') ++ μ :: s2) ⟶⋍[μ] f ((ν :: s') ++ s2)) as HypTr'.
      { eapply f_gen_lts_mu_in_the_middle. eauto. }
      destruct HypTr as (e & HypTr & equiv).
      destruct HypTr' as (e' & HypTr' & equiv').
      assert (e ⋍ e').
      { eapply nb_determinacy; eauto. }
      etransitivity. symmetry. exact equiv. etransitivity; eauto.
    + destruct HypTr as (e & HypTr & equiv).
      destruct (decide (non_blocking ν)) as [nb' | not_nb'].
      ++ assert (f (ν :: s' ++ μ :: s2) ⟶⋍[ν] f (s' ++ μ :: s2)) as HypTr'.
         { eapply test_next_step. }
         destruct HypTr' as (e' & HypTr' & equiv').
         assert (μ <> ν) as not_eq.
         { intro imp. rewrite imp in not_nb. contradiction. }
         destruct (nb_confluence nb' not_eq HypTr' HypTr )
           as (t' & l2 & (t'' & l1 & heq)).
         assert (f (s' ++ μ :: s2) ⟶⋍[μ] f (s' ++ s2)) as HypTr''.
         { eapply f_gen_lts_mu_in_the_middle; eauto. }
         edestruct (eq_spec (f (s' ++ μ :: s2)) t' (ActExt μ))
          as (v & hlv & heqv).
         exists e'. split; eauto. symmetry; eauto.
         assert (t' ⋍ (f (s' ++ s2))) as heq'.
         { eapply IHs'; eauto. exists v. split; eauto. }
         assert (f (ν :: s' ++ s2) ⟶⋍[ν] f (s' ++ s2)) as (v' & hlv' & heqv').
         { eapply test_next_step. }
         assert (e ⋍ f (ν :: s' ++ s2)) as final.
         { eapply backwards_nb_determinacy; eauto.
         etransitivity. exact heq. etransitivity. exact heq'. symmetry; eauto. }
         etransitivity. symmetry. exact equiv. eauto.
      ++ inversion his; subst.
         contradiction.
Qed.

Lemma inversion_test_b_external_action `{
  gLtsT : gLtsOba T, !Testing_Predicate outcome _, !test_spec f}
  s β' t :
  (forall μ, f ε ↛[μ] \/ (forall t, f ε ⟶[μ] t -> outcome t)) ->
  f s ⟶[β'] t ->
  blocking β' ->
  outcome t \/
  ∃  s1 s2 β, s = s1 ++ β :: s2
  /\ t ⋍ f (s1 ++ s2)
  /\ β' = β
  /\ Forall non_blocking s1.
Proof.
  revert β' t.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros μ t h l not_nb.
  - edestruct (h μ) as [refuses_f | f_to_outcome].
    + now eapply lts_refuses_spec2 in refuses_f; eauto.
    + left. eapply f_to_outcome. eauto.
  - destruct (decide (non_blocking ν)) as [nb | b].
    + assert (f (ν :: s') ⟶⋍[ν] f s') as (v & hlv & eqv).
      { eapply test_next_step. }
      assert (μ <> ν) as not_eq.
      { intro. subst. contradiction. }
      destruct (nb_confluence nb not_eq hlv l)
           as (t' & l2 & (t'' & l1 & heq)).
      destruct (eq_spec (f s') t' (ActExt μ)) as (v' & hlv' & heqv').
      { exists v. split. symmetry; eauto. exact l2. }
      destruct (decide (outcome v')) as [happy' | not_happy'].
      ++ left. eapply outcome_preserved_by_lts_non_blocking_action_converse; eauto.
         eapply outcome_preserved_by_eq; eauto. etransitivity; eauto. symmetry. eauto.
      ++ edestruct (Hlength s') as [happy | (s1 & s2 & μ' & eq & equiv & eq_action & his)]; eauto.
         +++ contradiction.
         +++ right. subst.
             assert (t ⋍ f ((ν :: s1) ++ s2)).
             { eapply f_gen_lts_mu_in_the_middle'. constructor; eauto.
               exists t. split; eauto. reflexivity. }
             exists (ν :: s1). exists s2. exists μ'.
             split. eauto. repeat split; eauto.
    + destruct (decide (μ = ν)) as [eq | neq].
      ++ right. subst.
         exists ε, s', ν. simpl. repeat split; simpl; eauto with mdb.
         repeat split;eauto. intros. eapply test_follows_trace_determinacy; eauto.
      ++ left. eapply test_side_effect_by_construction; eauto.
Qed.

Lemma inversion_test_nb_external_action `{
  gLtsT : gLtsOba T, !Testing_Predicate outcome _, !test_spec f}
  s η' t :
  (forall μ, f ε ↛[μ] \/ (forall t, f ε ⟶[μ] t -> outcome t)) ->
  f s ⟶[η'] t ->
  non_blocking η' ->
  outcome t \/
  ∃ s1 s2 η, s = s1 ++ η :: s2
  /\ t ⋍ f (s1 ++ s2)
  /\ η' = η
  /\ Forall non_blocking s1.
Proof.
  revert η' t.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros η t h l nb.
  - edestruct (h η) as [Tr|]; eauto. now eapply lts_refuses_spec2 in Tr; eauto.
  - edestruct (test_next_step ν s') as (r & hlr & heqr).
    destruct (decide (ν = η)) as [eq | not_eq].
    + right. subst. exists ε, s', η. repeat split; simpl; eauto with mdb.
      transitivity r; eauto. eapply (nb_determinacy nb l hlr); eauto.
    + destruct (nb_confluence nb not_eq l hlr )
        as (t' & l2 & (t'' & l1 & heq)).
      destruct (eq_spec (f s') t'' (ActExt $ η)) as (v & hlv & heqv).
      { exists r. split; eauto with mdb. now symmetry. }
      destruct (decide (outcome v)) as [happy' | not_happy'].
      * exfalso. assert (outcome (f s')).
        { eapply outcome_preserved_by_lts_non_blocking_action_converse; eauto. }
        assert (¬ outcome (f s')).
        { eapply test_ungood. }
        contradiction.
      * edestruct (Hlength s' ltac:(eauto) η v h hlv nb)
             as [happy' | (s1' & s2' & μ' & eq0 & eq1 & eq2 & eq3)]; try contradiction.
        destruct (decide (non_blocking ν)) as [nb' | not_nb'].
        -- right. subst.
           assert (Forall non_blocking (ν :: s1')) as Hyp.
           { constructor; eauto. }
           exists (ν :: s1'), s2', μ'. repeat split; eauto.
           edestruct (f_gen_lts_mu_in_the_middle (ν :: s1') s2' ν)
            as (r' & hlr' & heqr'); eauto.
           edestruct (test_next_step ν (s1' ++ s2'))
            as (w & hlw & heqw).
           eapply backwards_nb_determinacy; try eassumption.
           transitivity t''. symmetry. eassumption.
           transitivity v. now symmetry.
           transitivity (f (s1' ++ s2')). eassumption. now symmetry.
        -- subst. assert (outcome t).
           { eapply test_side_effect_by_construction; eauto. } eauto.
Qed.

Lemma inversion_test_external_action `{
  gLtsT : gLtsOba T, !Testing_Predicate outcome _, !test_spec f}
  s η' t :
  (forall μ, f ε ↛[μ] \/ (forall t, f ε ⟶[μ] t -> outcome t)) ->
  f s ⟶[η'] t ->
  outcome t \/
  ∃ s1 s2 η, s = s1 ++ η :: s2
  /\ t ⋍ f (s1 ++ s2)
  /\ η' = η
  /\ Forall non_blocking s1.
Proof.
  intros. destruct (decide (non_blocking η')) as [nb | not_nb].
  + eapply inversion_test_nb_external_action; eauto.
  + eapply inversion_test_b_external_action; eauto.
Qed.

Lemma inversion_tconv_external_action `{
  gLtsT : gLtsOba T, !Testing_Predicate outcome _, !test_convergence_spec f}
  s μ' t :
  f s ⟶[μ'] t ->
  outcome t \/
  ∃ s1 s2 μ, s = s1 ++ μ :: s2
  /\ t ⋍ f (s1 ++ s2)
  /\ μ' = μ
  /\ Forall non_blocking s1.
Proof.
  intros. eapply inversion_test_external_action; eauto.
  left. eapply tconv_does_no_external_action; eauto.
Qed.

Lemma inversion_ta_external_action `{CC: Countable PreAct} `{
  gLtsT : gLtsOba T,
  !Testing_Predicate outcome _, !test_co_acceptance_set_spec PreAct f Γ}
  s μ' (t : T) (O : gset PreAct) :
  f O s ⟶[μ'] t ->
  outcome t \/
  ∃ s1 s2 μ, s = s1 ++ μ :: s2
  /\ t ⋍ f O (s1 ++ s2)
  /\ μ' = μ
  /\ Forall non_blocking s1.
Proof.
  eapply inversion_test_external_action; eauto. intros μ.
  destruct (decide (non_blocking μ)) as [nb' | not_nb'].
       +++ left. eapply ta_does_no_non_blocking_actions; eauto.
       +++ right. intro e. eapply ta_transition_to_good; eauto.
Qed.

Lemma inversion_test_tau_action `{
  gLtsT : gLtsOba T, !Testing_Predicate outcome _, !test_spec f}
  s t :
  (f ε ↛ \/ (forall t, f ε ⟶ t -> outcome t)) ->
  (forall μ, f ε ↛[μ] \/ (forall t, f ε ⟶[μ] t -> outcome t)) ->
  f s ⟶ t ->
  outcome t \/
  ∃ η μ s1 s2 s3,
  s = s1 ++ [η] ++ s2 ++ [μ] ++ s3
  /\ t ⋍ f (s1 ++ s2 ++ s3)
  /\ non_blocking η
  /\ Forall non_blocking s1
  /\ Forall non_blocking s2
  /\ dual μ η.
Proof.
  revert t. induction s as [|μ' s']; intros t h1 h2 HypTr.
  - destruct h1 as [refuses_f | f_to_outcome].
    + eauto. now eapply lts_refuses_spec2 in refuses_f ; eauto.
    + eauto.
  - destruct (decide (non_blocking μ')) as [nb | not_nb].
    + destruct (decide (outcome t)) as [happy | not_happy].
      ++ left. exact happy.
      ++ edestruct (test_next_step μ' s') as (r & hlr & heqr).
         destruct (nb_tau nb hlr HypTr)
         as [(r1 & l1 & (r2 & l2 & heq))| HypTr''].
         +++ destruct (eq_spec (f s') r1 τ) as (v & hlv & heqv).
             exists r. split; eauto with mdb. now symmetry.
             destruct (IHs' _ h1 h2 hlv) as [happy' | Hyp].
             ++++ exfalso.
                  assert (¬ outcome r2) as not_happy''.
                  { eapply unoutcome_preserved_by_lts_non_blocking_action; eauto. }
                  assert (¬ outcome v) as not_happy'.
                  { eapply unoutcome_preserved_by_eq; eauto.
                    etrans. eapply heqv. now symmetry. }
                  contradiction.
             ++++ right. destruct Hyp
                  as (η & μ & s1 & s2 & s3 & eq_trace & equiv & hi & his1 & his2 & duo). subst.
                  exists η, μ, (μ' :: s1), s2, s3. repeat split; eauto.
                  repeat split; eauto.
                  edestruct (test_next_step μ') as (w & hlw & heqw).
                  eapply backwards_nb_determinacy. exact nb.
                  eassumption. eassumption.
                  etrans. eassumption.
                  etrans. symmetry. eapply heqv.
                  etrans. eassumption.
                  now symmetry.
         +++ destruct HypTr'' as (μ & duo & HypTr').
             destruct HypTr' as (r'' & HypTr'' & equiv'').
             destruct (eq_spec (f s') r'' (ActExt $ μ)) as (t0 & hlt0 & heqt0).
             { exists r. split; eauto. now symmetry. }
             assert (f s' ⟶[μ] t0) as Hyp; eauto.
             eapply inversion_test_external_action in Hyp; eauto.
             destruct Hyp as [good | continue].
             ++++ assert (t0 ⋍ t) as equiv.
                  { etrans. eauto. now symmetry. }
                  eapply outcome_preserved_by_eq in equiv; eauto.
             ++++ destruct continue as
                    (s1 & s2 & μ'' & eq1 & eq_trace & equiv & his); subst.
                  right. exists μ' ,μ'', ε, s1, s2. repeat split; simpl; subst; eauto.
                  symmetry. etrans; eauto. symmetry in heqt0. symmetry; etrans ; eauto.
    + left. eapply test_reset_tau_path. exact not_nb. exact HypTr.
Qed.

Lemma inversion_tconv_tau_action `{
  gLtsT : gLtsOba T, !Testing_Predicate outcome _, !test_convergence_spec f}
  s t :
  f s ⟶ t ->
  outcome t \/
  ∃ η μ' s1 s2 s3,
  s = s1 ++ [η] ++ s2 ++ [μ'] ++ s3
  /\ t ⋍ f (s1 ++ s2 ++ s3)
  /\ non_blocking η
  /\ Forall non_blocking s1
  /\ Forall non_blocking s2
  /\ dual μ' η.
Proof.
  intros.
  eapply inversion_test_tau_action; eauto.
  + right. eapply tconv_computes_to_good.
  + intro μ. left. eapply tconv_does_no_external_action.
Qed.

Lemma inversion_ta_tau_action `{CC : Countable PreAct} `{
  gLtsT : gLtsOba T,
  !Testing_Predicate outcome _, !test_co_acceptance_set_spec PreAct f Γ}
  s O t :
  f O s ⟶ t ->
  outcome t \/ (∃ η μ s1 s2 s3, s = s1 ++ [η] ++ s2 ++ [μ] ++ s3
                          /\ t ⋍ f O (s1 ++ s2 ++ s3)
                          /\ non_blocking η
                          /\ Forall non_blocking s1
                          /\ Forall non_blocking s2
                          /\ dual μ η).
Proof.
  intros.
  eapply inversion_test_tau_action; eauto.
  + left. eapply ta_does_no_tau; eauto.
  + intro μ. destruct (decide (non_blocking μ)) as [nb | not_nb].
    ++ left. eapply ta_does_no_non_blocking_actions; eauto.
    ++ right. intro e.
       eapply ta_transition_to_good ; eauto.
Qed.

Lemma after_blocking_co_of_must_tacc `{CC : Countable PreAct} `{
  @gLtsEq P A H,
  @gLtsOba T A H gLtsEqT, !Testing_Predicate outcome _,
  !test_co_acceptance_set_spec PreAct ta Γ}

  `{!Prop_of_Inter P T A dual}

  (p : P) β s E :
  p ⤓ -> blocking β -> (forall q μ', dual μ' β -> p ⟹{μ'} q -> q must_pass (ta E s))
              -> p must_pass (ta E (β :: s) : T).
Proof.
  intro tp. revert E β s. induction tp.
  intros E β s b hmq.
  eapply m_step.
  - eapply test_ungood.
  - edestruct (@test_tau_transition T A); eauto with mdb.
    now destruct test_co_acceptance_set_spec0. exists (p ▷ x). eapply ParRight; eauto.
  - intros p' Tr_p. eapply H3. exact Tr_p. eassumption. eauto with mdb.
  - intros e' l. eapply m_now.
    apply (test_reset_tau_path β s e'). eassumption. eassumption.
  - intros p' e' μ' μ'' inter l0 l1.
    destruct (decide (μ'' = β)) as [eq | neq].
    + subst. eapply test_follows_trace_determinacy in b as h1; eauto.
      eapply must_eq_client. symmetry; eauto.
      eapply hmq. eauto with mdb. eauto with mdb.
    + eapply m_now. eapply test_side_effect_by_construction ;eauto.
Qed.

Lemma ta_tau_ex `{CC : Countable PreAct}`{
  @gLtsObaFB T A H gLtsEqT gLtsObaT, !Testing_Predicate outcome _,
  !test_co_acceptance_set_spec PreAct f Γ}
  s1 s2 s3 η μ E :
  non_blocking η -> Forall non_blocking s1 -> Forall non_blocking s2 -> dual μ η ->
  f E (s1 ++ [η] ++ s2 ++ [μ] ++ s3) ⟶⋍ f E (s1 ++ s2 ++ s3).
Proof.
  intros nb Hyp Hyp' duo.
  assert (f E (s1 ++ [η] ++ s2 ++ [μ] ++ s3) ⟶⋍[η]
            f E (s1 ++ s2 ++ [μ] ++ s3)) as (e1 & l1 & heq1).
  { eapply (@f_gen_lts_mu_in_the_middle T A _ _ _ _ _ (f E) _
            s1 (s2 ++ [μ] ++ s3) η); simpl in *; eauto. }
  assert (f E (s1 ++ s2 ++ [μ] ++ s3) ⟶⋍[μ]
            f E ((s1 ++ s2) ++ s3)) as (e2 & l2 & heq2).
  { replace (s1 ++ s2 ++ [μ] ++ s3) with ((s1 ++ s2) ++ [μ] ++ s3).
    eapply (@f_gen_lts_mu_in_the_middle T A _ _ _ _ _ (f E) _
            (s1 ++ s2) s3 μ); simpl in *; eauto.
    eapply Forall_app. split; eauto. now rewrite <- app_assoc. }
  simpl in *. edestruct (eq_spec e1 e2) as (e' & l' & heq'). eauto.
  destruct (feedback nb duo l1 l') as (t & lt & heqt); eauto.
  exists t. split; eauto.
  rewrite <- app_assoc in heq2.
  transitivity e'. eauto.
  transitivity e2; eauto.
Qed.

Lemma must_ta_monotonicity_nil {P : Type} `{CC : Countable PreAct} `{
  gLtsP : @gLts P A H,
  @gLtsObaFB T A H gLtsEqT gLtsObaT,
  AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳 _ _ , !Testing_Predicate outcome _,
  !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳 (Φ x)))}

  `{!Prop_of_Inter P T A dual}

  (p : P) E1 :
  p must_pass (ta E1 ε)
    -> forall E2, E1 ⊆ E2
      -> p must_pass (ta E2 ε).
Proof.
  intros hm.
  assert (hpt : p ⤓)
    by now (eapply must_terminate_unoutcome , test_ungood; eauto).
  induction hpt. dependent induction hm; intros E2 hsub.
  - assert (¬ outcome (ta E1 ε)).
    { now eapply test_ungood. }
    contradiction.
  - eapply m_step; eauto with mdb.
    + eapply test_ungood.
    + destruct ex as ((p' & e') & l').
      inversion l'; subst.
      +++ exists (p' ▷ (ta E2 ε)). eapply ParLeft; eauto.
      +++ exfalso. assert ({q : T | ta E1 ε ⟶ q}) as impossible.
          eauto.
          eapply lts_refuses_spec2 in impossible.
          assert (ta E1 ε ↛). { eapply ta_does_no_tau; eauto. }
          contradiction.
      +++ destruct (decide (non_blocking μ2)) as [nb2 | not_nb2].
          ++++ exfalso.
               assert ({q : T | ta E1 ε ⟶[μ2] q}) as impossible; eauto.
               eapply lts_refuses_spec2 in impossible.
               assert (ta E1 ε ↛[μ2]).
               { eapply ta_does_no_non_blocking_actions; eauto. }
               contradiction.
          ++++ assert (μ2 ∈ coR p) as co_set.
               { exists μ1. repeat split; eauto. eapply lts_refuses_spec2; eauto. }
               eapply (map_gamma_of_action (𝝳 ∘ Φ)) in co_set.
               eapply ta_actions_are_in_its_gamma_set in l2 as mem; eauto.
               eapply hsub in mem.
               eapply ta_has_a_representative_transition_for_its_gamma_set in mem as (r & μ'2 & Tr' & eq'); eauto.
               simpl in co_set. rewrite<- eq' in co_set.
               destruct co_set as (μ'1 & mem & eq''). eapply (map_gamma_of_action Φ) in mem as mem_map.
               simpl in eq''. symmetry in eq''.
               (* The next line uses a property of delta *)
               eapply (abstraction_prog_spec p μ'1) in eq'' as mem_map_phi; eauto.
               destruct mem_map_phi as (μ'' & co_set & eq''').
               destruct co_set as (μ''1 & Tr & duo & b).
               assert (blocking μ'2).
               { intro imp. eapply ta_does_no_non_blocking_actions in imp.
                 eapply (@lts_refuses_spec2 T). exists r. exact Tr'. eauto. }
               assert (¬ ta E2 ε ↛[μ'']) as Tr''.
               (* The next line uses a property of phi *)
               { eapply (abstraction_test_spec (ta E2 ε) μ'2 μ'' ) in eq'''; eauto.
                 eapply lts_refuses_spec2; eauto. }
               eapply lts_refuses_spec1 in Tr'' as (e'' & Tr'').
               eapply lts_refuses_spec1 in Tr as (p'' & Tr).
               exists (p'', e''). eapply ParSync. exact duo. exact Tr. exact Tr''.
               destruct mem as (μ & Tr & duo & b). eauto.
               intro imp. eapply ta_does_no_non_blocking_actions in imp.
               eapply (@lts_refuses_spec2 T). exists r. exact Tr'. eauto.
    + intros e l.
      exfalso.
      assert ({q : T | ta E2 ε ⟶ q}) as impossible. eauto.
      eapply lts_refuses_spec2 in impossible.
      assert (ta E2 ε ↛). eapply ta_does_no_tau; eauto.
      contradiction.
    + intros p' e' μ μ' inter l2 l1.
      destruct (decide (non_blocking μ')) as [nb | not_nb].
      ++ exfalso.
         assert ({q : T | ta E2 ε ⟶[μ'] q}) as impossible. eauto.
         eapply lts_refuses_spec2 in impossible.
         assert (ta E2 ε ↛[μ']). eapply ta_does_no_non_blocking_actions; eauto.
         contradiction.
      ++ eapply (@ta_transition_to_good
            PreAct _ _ T A H gLtsEqT
                  outcome Testing_Predicate0 ta (fun x => 𝝳 (Φ x))) in l1;eauto.
         eapply m_now; eauto.
Qed.

Lemma must_ta_monotonicity {P : Type} `{CC : Countable PreAct} `{
  @gLtsObaFW P A H gLtsEqP gLtsObaP,
  @gLtsObaFB T A H gLtsEqT gLtsObaT,
  AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳 _ _ , !Testing_Predicate outcome _,
  !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳 (Φ x)))}

  `{!Prop_of_Inter P T A dual}

  s (p : P) E1 :
  p must_pass (ta E1 s)
    -> forall E2, E1 ⊆ E2
      -> p must_pass (ta E2 s).
Proof.
  revert p E1.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros p E1 hm E2 hsub; subst.
  - eapply must_ta_monotonicity_nil; eauto.
  - assert (htp : p ⤓) by (eapply must_terminate_unoutcome, test_ungood; eauto).
    induction htp.
    inversion hm.
    * now eapply test_ungood in H4.
    * eapply m_step; eauto with mdb.
      + eapply test_ungood.
      + destruct (decide (non_blocking ν)) as [nb | not_nb].
        ++ edestruct (boomerang p ν (co ν)) as (p' & Hyp').
           assert (p ⟶[(co ν)] p').
           { eapply Hyp'; eauto. destruct (exists_dual ν) as (x & duo).
             symmetry. eauto. }
           assert (ta E2 (ν :: s') ⟶⋍[ν] ta E2 s') as (t' & tr' & eq').
           { eapply test_next_step. }
           exists (p' , t'). eapply ParSync; eauto.
           destruct (exists_dual ν) as (x & duo). symmetry. eauto.
        ++ assert (∃ e', ta E2 (ν :: s') ⟶ e') as (e' & tr').
           { eapply test_tau_transition. eauto. }
           exists (p , e'). eapply ParRight. exact tr'.
      + intros e' l.
        edestruct @inversion_ta_tau_action as [|Hyp]; eauto with mdb.
        destruct Hyp as (η & μ & s1 & s2 & s3 & heqs & sc & himu & his1 & his2 & duo).
        eapply (must_eq_client p (ta E2 (s1 ++ s2 ++ s3))). now symmetry.
        edestruct (@ta_tau_ex _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1 s2 s3 η μ E1) as (t & hlt & heqt); eauto.
        eapply Hlength; eauto.
        ++ rewrite heqs, 6 length_app. simpl. lia.
        ++ eapply must_eq_client. eapply heqt. eapply et. now rewrite heqs.
      + intros p' e' μ μ' inter l1 l2.
        edestruct @inversion_ta_external_action as [|Hyp]; eauto with mdb.
        destruct Hyp as (s1 & s2 & μ''' & heqs & heq & eq & his1). subst.
        eapply must_eq_client. symmetry. eassumption.
        edestruct @f_gen_lts_mu_in_the_middle as (t & l & heq'); eauto.
        now destruct test_co_acceptance_set_spec0.
        eapply Hlength. rewrite heqs.
        rewrite 2 length_app. simpl. lia.
        eapply must_eq_client. eapply heq'.
        eapply com; eauto. rewrite heqs. eassumption.
        eassumption.
Qed.

Lemma stable_process_must_ta_or_empty_pre_action_set {P : Type} `{CC : Countable PreAct} `{
  @gLtsOba P A H gLtsEqP,
  @gLtsOba T A H gLtsEqT}

  `{FiniteAbs : @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ _ _ _}

  `{!Testing_Predicate outcome _,
  !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳 (Φ x)))}

  `{!Prop_of_Inter P T A dual}

  (p : P) (E : gset PreAct):

  p ↛
  -> p must_pass (ta ((coR_abs p) ∖ E) ε)
          \/ (coR_abs p ⊆ E).
Proof.
  intros.
  (* Finite set hypothesis for (delta o phi) set*)
  remember ((coR_abs p) ∖ E) as D.
  destruct D as [|a D'] using set_ind_L.
  + right. set_solver.
  + left.
      eapply m_step.
      ++ now eapply test_ungood.
      ++ assert (a ∈ coR_abs p ∖ E) as mem'.
         { set_solver. }
         assert (a ∈ coR_abs p) as co_set.
         { eauto. eapply elem_of_difference; eauto. }
         eapply ta_has_a_representative_transition_for_its_gamma_set in mem' as (r & μ & Tr & eq); eauto.
         subst. eapply coR_abs_spec1 in co_set.
         destruct co_set as (μ'' & co_set & eq).
         assert ((Φ μ) ∈ ⌈ Φ ⌉ (coR p)) as mem.
         { symmetry in eq; eapply abstraction_prog_spec; eauto.
           destruct co_set as (μ' & Tr' & duo & nb). exact nb.
           intro imp. eapply ta_does_no_non_blocking_actions in imp.
           eapply (@lts_refuses_spec2 T). exists r. exact Tr. eauto.
           eapply map_gamma_of_action. eauto. }
         destruct mem as (μ' & Tr' & eq').
         assert (blocking μ).
         { intro imp. eapply ta_does_no_non_blocking_actions in imp.
           eapply (@lts_refuses_spec2 T). exists r. exact Tr. eauto. }
         assert (¬ (ta (coR_abs p ∖ E) ε) ↛[μ']) as Tr''.
         { eapply abstraction_test_spec in eq' ; eauto. destruct Tr' as (Tr'' & duo'' & b'' & bbbb).
           eauto. eapply lts_refuses_spec2; eauto. }
         rewrite<- HeqD in Tr''.
         eapply lts_refuses_spec1 in Tr'' as (e'' & Tr'').
         destruct Tr' as (μ''' & Tr' & duo & b).
         eapply lts_refuses_spec1 in Tr' as (p'' & Tr').
         exists (p'' , e''). eapply ParSync; eauto.
      ++ intros p' l'. exfalso. eapply (lts_refuses_spec2 p); eauto with mdb.
      ++ intros e' l'. exfalso.
         assert (¬ ta (coR_abs p ∖ E) ε ↛ ).
         { rewrite<- HeqD. eapply lts_refuses_spec2; eauto. }
         assert (ta (coR_abs p ∖ E) ε ↛).
         { rewrite<- HeqD. eapply ta_does_no_tau ; eauto. }
         contradiction.
      ++ intros p'' e'' μ' μ inter l'1 l'0.
         destruct (decide (non_blocking μ)) as [nb' | not_nb'].
         ++++++ exfalso.
                eapply (@lts_refuses_spec2 T); eauto with mdb.
                eapply ta_does_no_non_blocking_actions ; eauto.
         ++++++ eapply ta_transition_to_good in l'0.
                eapply m_now. exact l'0. eauto.
Qed.

(** ** Completeness for co-acceptance sets

    Everything below relates [P]'s own [⇓ᶜᵒ]/[⟹ᶜᵒ] to the tests above, and is
    genuinely re-derived (not copied) against [cocnv]/[cowt]. *)

Lemma must_tconv_cowt_mu `{
  gLtsP : @gLts P A H,
  gLtsT : ! gLtsEq T H,
  !Testing_Predicate outcome _, ! test_convergence_spec tconv}

  `{!Prop_of_Inter P T A dual}

  μ s (p q : P):
  p must_pass (tconv (μ :: s)) ->
    p ⟹ᶜᵒ{μ} q -> q must_pass (tconv s).
Proof.
  intros hm w.
  dependent induction w.
  + eapply IHw; eauto with mdb.
    eapply must_preserved_by_lts_tau_srv; eauto.
  + edestruct test_next_step as (t' & hlt' & heqt').
    eapply (must_eq_client _ _ _ heqt').
    eapply (must_preserved_by_weak_nil_srv q t); eauto.
    eapply must_preserved_by_synch_if_notoutcome; eauto with mdb.
    eapply test_ungood.
    eapply cowt_iff_wt_nil.
    exact w.
Qed.

Lemma cocnv_if_must `{
  gLtsP : @gLts P A H,
  gLtsT : !gLtsEq T H, !Testing_Predicate outcome _, !test_convergence_spec tconv}
  `{!Prop_of_Inter P T A dual}
  s (p : P) :
  p must_pass (tconv s) -> p ⇓ᶜᵒ s.
Proof.
  revert p.
  induction s as [|μ s']; intros p hm.
  - eapply cocnv_nil.
    eapply (must_terminate_unoutcome _ _ hm), test_ungood.
  - eapply cocnv_act.
    + eapply (must_terminate_unoutcome _ _ hm), test_ungood.
    + intros q w.
      eapply IHs', must_tconv_cowt_mu; eauto.
Qed.

Lemma must_if_cocnv `{
  @gLtsObaFW P A H gLtsEqP gLtsObaP,
  @gLtsObaFB T A H gLtsEqT gLtsObaT, !Testing_Predicate outcome _, !test_convergence_spec tconv}

  `{!Prop_of_Inter P T A dual}

  s (p : P) :
  p ⇓ᶜᵒ s -> p must_pass (tconv s).
Proof.
  revert p.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  intros p hcocnv.
  induction (cocnv_terminate p s hcocnv) as [p hp IHtp].
  apply m_step.
  + eapply test_ungood.
  + edestruct tconv_always_reduces. exists (p ▷ x). eapply ParRight; eauto.
  + intros p' l. eapply IHtp; [|eapply cocnv_preserved_by_lts_tau]; eauto.
  + intros e' l.
    destruct (inversion_tconv_tau_action s e' l)
      as [hu | (η & μ & s1 & s2 & s3 & eq__s & sc & i0 & i1 & i2 & duo)]; eauto with mdb.
    eapply must_eq_client. symmetry. eassumption.
    subst.
    eapply Hlength.
    * rewrite 6 length_app. simpl. lia.
    * eapply cocnv_annhil; eauto.
  + intros p' e' ν' ν inter hlp hle.
    destruct (inversion_tconv_external_action s ν e' hle)
      as [hg | (s1 & s2 & ν'' & heq & sc & eq & his)]; eauto with mdb.
    subst.
    eapply must_eq_client. symmetry. eassumption.
    eapply Hlength.
    * rewrite length_app. simpl. rewrite length_app. simpl. lia.
    * eapply cocnv_drop_action_in_the_middle; eauto.
Qed.

Lemma must_iff_cocnv `{
  @gLtsObaFW P A H gLtsEqP gLtsObaP,
  @gLtsObaFB T A H gLtsEqT gLtsObaT, !Testing_Predicate outcome _,
  !test_convergence_spec tconv}

  `{!Prop_of_Inter P T A dual}

  (p : P) s : p must_pass (tconv s) <-> p ⇓ᶜᵒ s.
Proof. split; [eapply cocnv_if_must | eapply must_if_cocnv]; eauto. Qed.

Lemma completeness1_co `{
    @gLtsObaFW P A H gLtsEqP gLtsObaP,
    @gLtsObaFW Q A H gLtsEqQ gLtsObaQ,
    @gLtsObaFB T A H gLtsEqT gLtsObaT, !Testing_Predicate outcome _,
    ! test_convergence_spec tconv}

    `{!Prop_of_Inter P T A dual}
    `{!Prop_of_Inter Q T A dual}

  (p : P) (q : Q) : p ⊑ₘᵤₛₜᵢ q -> p ₁≼꜀ₒ₋ₐₛ q.
Proof. intros hleq s hcnv. now eapply must_iff_cocnv, hleq, must_iff_cocnv. Qed.

(** ** Completeness for co-acceptance sets

    [must_ta_monotonicity_nil], [must_ta_monotonicity] and
    [stable_process_must_ta_or_empty_pre_action_set] are reused unchanged
    from [Completeness.v]: their statements only ever mention [P]'s plain
    single-step [⟶]/[coR] or the test-side trace [s]/[E] — never [P]'s own
    [⇓]/[⟹] — so nothing about them is specific to the map-[coₜ] vs.
    relational-[cowt] choice. Only the lemmas built on [wt_refuses_set]
    (which packages [P]'s own [⇓]/[⟹]) need a [cowt_refuses_set] replacement,
    below. *)

Lemma after_blocking_co_of_must_tacc_co `{CC : Countable PreAct} `{
  @gLtsEq P A H,
  @gLtsOba T A H gLtsEqT, !Testing_Predicate outcome _,
  !test_co_acceptance_set_spec PreAct ta Γ}

  `{!Prop_of_Inter P T A dual}

  (p : P) β s E :
  p ⤓ -> blocking β -> (forall q, p ⟹ᶜᵒ{β} q -> q must_pass (ta E s))
              -> p must_pass (ta E (β :: s) : T).
Proof.
  intros hp hb hq.
  eapply after_blocking_co_of_must_tacc; eauto.
  intros q μ' duo w.
  eapply hq. eapply wt_to_cowt_dual with (s' := [μ']); eauto.
  constructor; [symmetry; exact duo | constructor].
Qed.

Lemma cowt_acceptance_set_subseteq `{CC : Countable PreAct} `{
  gLtsP : @gLts P A H, !coFiniteImagegLts P A,
  FiniteAbs : @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 gLtsP gLtsT _ _}
  μ s p q hacnv1 hacnv2 :
  p ⟹ᶜᵒ{μ} q ->
  map (coR_abs) (elements (cowt_refuses_set q s hacnv1)) ⊆
    map (coR_abs) (elements (cowt_refuses_set p (μ :: s) hacnv2)).
Proof.
  intros.
  intros a in__a.
  assert (cowt_refuses_set q s hacnv1 ⊆ cowt_refuses_set p (μ :: s) hacnv2).
  intros t in__t.
  eapply cowt_refuses_set_spec2.
  eapply cowt_refuses_set_spec1 in in__t.
  destruct in__t. split; eauto with mdb.
  eapply cowt_push_left; eauto.
  set_solver.
Qed.

Lemma lts_tau_cowt_acceptance_set_subseteq `{CC : Countable PreAct} `{
  gLtsP : @gLts P A H, !coFiniteImagegLts P A,
  FiniteAbs : @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 gLtsP gLtsT _ _}
  s p q hacnv1 hacnv2 :
  p ⟶ q ->
  map coR_abs  (elements $ cowt_refuses_set q s hacnv1) ⊆
    map coR_abs (elements $ cowt_refuses_set p s hacnv2).
Proof.
  intros.
  intros a in__a.
  assert (cowt_refuses_set q s hacnv1 ⊆ cowt_refuses_set p s hacnv2).
  { intros t in__t. eapply cowt_refuses_set_spec2.
    eapply cowt_refuses_set_spec1 in in__t.
    destruct in__t. split; eauto with mdb. }
  set_solver.
Qed.

Definition cooas `{CC : Countable PreAct}  `{
  gLtsP : @gLts P A H, !coFiniteImagegLts P A,
  FiniteAbs : @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 gLtsP gLtsT _ _}
  (p : P) (s : list A) (hcocnv : p ⇓ᶜᵒ s) : gset PreAct :=
  let ps : list P := elements (cowt_refuses_set p s hcocnv) in
  ⋃ map coR_abs ps.

Lemma union_cowt_acceptance_set_subseteq `{CC : Countable PreAct}  `{
  gLtsP : @gLts P A H, !coFiniteImagegLts P A,
  FiniteAbs : @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 gLtsP gLtsT _ _}
  μ s p q h1 h2 :
  p ⟹ᶜᵒ{μ} q -> cooas q s h1 ⊆ cooas p (μ :: s) h2.
Proof.
  intros hw a (O & mem1 & mem2)%elem_of_union_list.
  eapply elem_of_union_list.
  exists O. split; eauto. eapply cowt_acceptance_set_subseteq; eauto.
Qed.

Lemma union_acceptance_set_lts_tau_cowt_subseteq `{CC : Countable PreAct} `{
  gLtsP : @gLts P A H, !coFiniteImagegLts P A,
  FiniteAbs : @FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 gLtsP gLtsT _ _}
  s p q h1 h2 :
  p ⟶ q -> cooas q s h1 ⊆ cooas p s h2.
Proof.
  intros l a (L & mem1 & mem2)%elem_of_union_list.
  eapply elem_of_union_list.
  exists L. split; eauto.
  eapply lts_tau_cowt_acceptance_set_subseteq; eauto.
Qed.

Lemma must_ta_or_empty_pre_action_set_for_empty_trace_co `{CC : Countable PreAct} {P : Type} `{
  @gLtsObaFW P A H gLtsEqP gLtsObaP, !coFiniteImagegLts P A,
  @gLtsObaFB T A H gLtsEqT gLtsObaT, FiniteAbs :@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ _ _ _ ,
  !Testing_Predicate outcome _,
  !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳  (Φ x)))}

  `{!Prop_of_Inter P T A dual}

  (p : P) (hcocnv : p ⇓ᶜᵒ ε) (E : gset PreAct):

  (exists p', p ⟹ p' /\ lts_refuses p' τ /\ coR_abs p' ⊆ E)
  \/ p must_pass (ta ((cooas p ε hcocnv) ∖ E) ε).
Proof.
  induction (cocnv_terminate p ε hcocnv) as (p, hpt, ihhp).
  destruct (decide (lts_refuses p τ)) as [st | (p'' & l)%lts_refuses_spec1].
  + destruct (stable_process_must_ta_or_empty_pre_action_set p E st) as [Hyp | Hyp].
    ++ right. assert (cooas p ε hcocnv = coR_abs p) as eq.
       { unfold cooas. rewrite cowt_refuses_set_refuses_singleton, elements_singleton; eauto.
         simpl. now rewrite union_empty_r_L. } rewrite eq.
       exact Hyp.
    ++ left. exists p. split; eauto. constructor.
  + assert (∀ q0 : P,
         q0 ∈ cowt_tau_set p
         → (∃ p' : P, q0 ⟹ p' ∧ p' ↛ ∧ coR_abs p' ⊆ E)
             ∨ (∃ h, must q0 (ta ((cooas q0 ε h) ∖ E) ε))) as Hyp.
    { intros q' l'%cowt_tau_set_spec. destruct (hpt q' l') as (hq).
      assert (q' ⇓ᶜᵒ ε) as cocnv_nil' by (eapply (cocnv_nil q' (tstep q' hq))).
      edestruct (ihhp q' l') as [hl | hr].
      * now left.
      * right. exists (cocnv_nil _ (tstep q' hq)). eauto. }
    destruct (@exists_forall_in P (cowt_tau_set p) _ _ Hyp) as [Hyp' | Hyp'].
    - eapply Exists_exists in Hyp' as (t & l'%cowt_tau_set_spec & t' & w & st & sub).
        left. exists t'. eauto with mdb.
    - right. eapply m_step.
      * eapply test_ungood.
      * exists (p'' ▷ ta ((cooas p ε hcocnv) ∖ E) ε). eapply ParLeft; eauto.
      * intros p0 l0%cowt_tau_set_spec.
        eapply Forall_forall in Hyp' as (h0 & hm); eauto.
        eapply must_ta_monotonicity; eauto.
        eapply difference_mono_r. eapply union_acceptance_set_lts_tau_cowt_subseteq.
        eapply cowt_tau_set_spec. exact l0.
      * intros e' l'. exfalso.
             eapply (@lts_refuses_spec2 T). eauto. eapply ta_does_no_tau; eauto.
      * intros p0 e0 μ' μ inter lp le.
             destruct (decide (non_blocking μ)) as [nb | not_nb].
        ++ exfalso.
           assert ({q' : T | ta ((cooas p ε hcocnv) ∖ E) ε ⟶[μ] q'}).
           { eauto. } eapply (@lts_refuses_spec2 T); eauto.
           eapply ta_does_no_non_blocking_actions; eauto.
        ++ eapply m_now. eapply ta_transition_to_good; eauto.
Qed.

Lemma must_ta_or_empty_pre_action_set_for_all_trace_co {P : Type} `{CC : Countable PreAct} `{
  @gLtsObaFW P A H gLtsEqP gLtsObaP, !coFiniteImagegLts P A,
  @gLtsObaFB T A H gLtsEqT gLtsObaT, FiniteAbs :@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ _ _ _ ,
  !Testing_Predicate outcome _, !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳 (Φ x)))}

  `{!Prop_of_Inter P T A dual}

  s (p : P) (hcocnv : p ⇓ᶜᵒ s) (E : gset PreAct):

  (exists p', p ⟹ᶜᵒ[s] p' /\ lts_refuses p' τ /\ coR_abs p' ⊆ E)
      \/ p must_pass (ta ((cooas p s hcocnv) ∖ E) s).
Proof.
  revert p hcocnv E.
  induction s as [|μ s'].
  - intros. destruct (must_ta_or_empty_pre_action_set_for_empty_trace_co p hcocnv E) as [(p'&w&st&sub)|hm].
    + left. exists p'. repeat split; eauto. eapply cowt_iff_wt_nil. exact w.
    + right. exact hm.
  - intros p hcocnv E.
    set (ps := cowt_set_mu p μ s' hcocnv).
    inversion hcocnv as [| ? ? ? conv Hyp_conv]; subst.
    assert (hcocnv0 : forall p', p' ∈ ps -> p' ⇓ᶜᵒ s') by (intros ? mem%cowt_set_mu_spec1; eauto).
    assert (he : ∀ p', p' ∈ ps ->
     ((exists pr p0, p0 ∈ cowt_refuses_set p' s' pr ∧ coR_abs p0 ⊆ E)
             \/ (exists h, must p' (ta ((cooas p' s' h) ∖ E) s')))).
    { intros p' mem. destruct (IHs' p' (hcocnv0 _ mem) E) as [(r & w & st & sub)| hm].
      * left. eapply cowt_set_mu_spec1 in mem.
        exists (Hyp_conv _ mem), r. split; [eapply cowt_refuses_set_spec2 |]; eauto.
      * right. eauto. }
    destruct (exists_forall_in_gset ps _ _ he) as [Hyp | Hyp].
    + left. destruct Hyp
          as (p1 & ?%cowt_set_mu_spec1 & ? & r & (? & ?)%cowt_refuses_set_spec1 & ?).
      exists r. repeat split; eauto. eapply cowt_push_left; eauto.
    + right.
      destruct (decide (non_blocking μ)) as [nb | b].
      +++ destruct (boomerang p μ (co μ)) as (p' & Hb).
          destruct (Hb nb (symmetry (proj2_sig (exists_dual μ)))) as (l0 & l1).
          assert (ta ((cooas p (μ :: s') hcocnv) ∖ E) (μ :: s')
                   ⟶⋍[μ] ta ((cooas p (μ :: s') hcocnv) ∖ E) s')
            as (e' & hle' & heqe') by eapply test_next_step.
          eapply must_non_blocking_action_swap_l_fw; eauto.
          eapply (must_eq_client _ _ _ (symmetry heqe')).
          edestruct (Hyp p') as (? & hm).
          { eapply cowt_set_mu_spec2. eapply lts_to_cowt.
            symmetry. exact (proj2_sig (exists_dual μ)). exact l0. }
          assert (cooas p' s' x ∖ E ⊆ cooas p (μ :: s') hcocnv ∖ E).
          { eapply difference_mono_r. eapply union_cowt_acceptance_set_subseteq; eauto.
            eapply lts_to_cowt. symmetry. exact (proj2_sig (exists_dual μ)). exact l0. }
          eapply must_ta_monotonicity; eauto.
      +++ eapply after_blocking_co_of_must_tacc_co; eauto.
          intros p' w.
          edestruct (Hyp p') as (? & hm).
          { eapply cowt_set_mu_spec2; eauto. }
          assert ((cooas p' s' x ∖ E) ⊆ cooas p (μ :: s') hcocnv ∖ E).
          { eapply difference_mono_r. eapply union_cowt_acceptance_set_subseteq; eauto. }
          eapply must_ta_monotonicity; eauto.
Qed.

Lemma not_must_ta_without_required_acc_set_co {Q : Type} `{CC : Countable PreAct} `{
  @gLtsObaFW Q A H gLtsEqQ gLtsObaQ,
  @gLtsObaFB T A H gLtsEqT gLtsObaT, FiniteAbs :@FinitaryAbsAction Q T FinA PreAct A H Φ 𝝳 _ _ _ _ ,
  !Testing_Predicate outcome _,
  !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳  (Φ x)))}

  `{!Prop_of_Inter Q T A dual}

  (q q' : Q) s (E : gset PreAct) :

  q ⟹ᶜᵒ[s] q' -> q' ↛ -> ¬ q must_pass (ta (E ∖ (coR_abs q')) s).
Proof.
  intros wt hst.
  dependent induction wt; intros hm. rename p into q.
  - inversion hm as [happy | ]; subst.
    ++ contradict happy. eapply test_ungood.
    ++ destruct ex as (t & l). inversion l; subst.
       +++ eapply (lts_refuses_spec2 q τ); eauto with mdb.
       +++ simpl in *. eapply (@lts_refuses_spec2 T), ta_does_no_tau; eauto.
       +++ destruct (decide (non_blocking μ2)) as [nb2 | not_nb2].
           ++++ exfalso. eapply (@lts_refuses_spec2 T).
                eauto. eapply ta_does_no_non_blocking_actions ;eauto.
           ++++ eapply ta_actions_are_in_its_gamma_set in l2 as mem; eauto.
                assert ((𝝳 ∘ Φ) μ2 ∉ coR_abs q) as not_in_mem.
                { set_solver. }
                assert ((𝝳 ∘ Φ) μ2 ∈ coR_abs q) as in_mem.
                { eapply coR_abs_spec2. eapply map_gamma_of_action. exists μ1. repeat split; eauto.
                eapply lts_refuses_spec2; eauto. }
                contradiction.
  - eapply (IHwt hst), (must_preserved_by_lts_tau_srv p q _ hm l).
  - simpl in hm. assert (ta (E ∖ (coR_abs t)) (μ :: s) ⟶⋍[μ]
              ta (E ∖ (coR_abs t)) s) as (e' & hle' & heqe')
    by eapply test_next_step.
    assert (¬ outcome (ta (E ∖ coR_abs t) (μ :: s))).
    { eapply test_ungood. }
    eapply (IHwt hst).
    eapply must_eq_client; eauto.
    eapply must_preserved_by_synch_if_notoutcome; eauto.
Qed.

Lemma completeness2_co {P Q : Type} `{CC : Countable PreAct} `{
  @gLtsObaFW P A H gLtsEqP gLtsObaP,
  @gLtsObaFW Q A H gLtsEqQ gLtsObaQ,
  @gLtsObaFB T A H gLtsEqT gLtsObaT,
  !coFiniteImagegLts P A, FiniteAbsP :@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ _ _ _ ,
  !coFiniteImagegLts Q A, FiniteAbsQ :@FinitaryAbsAction Q T FinA PreAct A H Φ 𝝳 _ _ _ _ ,
  !Testing_Predicate outcome _,
  !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳  (Φ x)))}

  `{!Prop_of_Inter P T A dual}
  `{!Prop_of_Inter Q T A dual}

  (p : P) (q : Q) : p ⊑ₘᵤₛₜᵢ q -> p ₂≼꜀ₒ₋ₐₛ q.
Proof.
  intros hpre s q' hacnv w st.
  destruct (must_ta_or_empty_pre_action_set_for_all_trace_co s p hacnv (coR_abs q')) as [(p' & w_tr & stable & sub)|hm].
  + exists p' ; repeat split ;eauto.
    intros pre mem. eapply coR_abs_spec1. eapply coR_abs_spec2 in mem. eapply sub. exact mem.
  + eapply hpre in hm. contradict hm.
    eapply (not_must_ta_without_required_acc_set_co _ _ s); eauto.
Qed.

(** ** Completeness for forwarder LTS *)
Lemma completeness_fw_co {P Q : Type} `{CC : Countable PreAct} `{
  @gLtsObaFW P A H gLtsEqP gLtsObaP, !coFiniteImagegLts P A,
  @gLtsObaFW Q A H gLtsEqQ gLtsObaQ, !coFiniteImagegLts Q A,
  @gLtsObaFB T A H gLtsEqT gLtsObaT,
  FiniteAbsP :@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 _ _ _ _ ,
  FiniteAbsQ :@FinitaryAbsAction Q T FinA PreAct A H Φ 𝝳 _ _ _ _ ,
  !Testing_Predicate outcome _, !test_convergence_spec tconv,
  !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳  (Φ x)))}

  `{!Prop_of_Inter P T A dual}
  `{!Prop_of_Inter Q T A dual}

  (p : P) (q : Q) : p ⊑ₘᵤₛₜᵢ q -> p ≼꜀ₒ₋ₐₛ q.
Proof.
  intros. split.
  - now apply completeness1_co.
  - now apply completeness2_co.
Qed.
