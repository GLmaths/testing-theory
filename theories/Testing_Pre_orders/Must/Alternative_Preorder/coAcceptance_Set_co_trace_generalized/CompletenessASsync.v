(* begin hide *)
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
(* end hide *)
(* begin hide *)
(* * Completeness for two alphabets: the convergence condition

    The port of the first half of [CompletenessASco.v] — everything that leads
    to [completeness1_co] — to processes over [Aproc] tested by observers over
    [Atest].

    The lemmas of [CompletenessASco.v] about the observers alone
    ([tconv_always_reduces], the [inversion_test_*] and [inversion_tconv_*]
    family) are reused unchanged: they only ever mention the test LTS and its
    own [dual], so they hold over [Atest] as they stand.  Only the lemmas that
    relate a process to an observer had to be ported, and they are below. *)
(* end hide *)

From Stdlib Require ssreflect Setoid.
From Stdlib Require Import Unicode.Utf8 List.
From Stdlib.Program Require Import Wf Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.

From stdpp Require Import sets base countable finite gmap list finite
                          decidable finite gmap.
From stdpp Require gmultiset.
From TestingTheory Require Import ActTau SyncActions gLts Bisimulation Lts_OBA
  WeakTransitions Lts_OBA_FB Lts_FW FiniteImageLTS
  InteractionBetweenLts MultisetLTSConstruction
  ParallelLTSConstruction
  Must Subset_Act Convergence Termination
  Testing_Predicate Lts_Finite_Non_Blocking_Chain
  coWeakTransition coConvergence coFiniteImage DefinitionASrel.

Import ListNotations.
(* begin hide *)
(* ** Axioms for completeness (copied from [Completeness.v], unchanged) *)
(* *** Common axioms for the generation of tests **)

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

(* *** Common axioms for the generation of tests **)
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

(* *** Axioms for tests on convergence *)
Class test_convergence_spec
  `{@gLtsEq T A H, !Testing_Predicate outcome _}
  (tconv : list A -> T) := {
    tconv_test_spec : test_spec tconv ;
    (* c1 *) tconv_does_no_external_action μ : tconv ε ↛[μ] ;
    (* c2 *) tconv_can_compute : ∃ e', tconv ε ⟶ e';
    (* c3 *) tconv_computes_to_good e : tconv ε ⟶ e -> outcome e;
  }.

#[global] Existing Instance tconv_test_spec.

(* *** Axioms for the tests on co-acceptance sets *)
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

(* *** Facts about test generators *)
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

Section Test_spec_inversion.

Context `{gLtsT : gLtsOba T}.
Context `{!Testing_Predicate outcome _}.
Context `{!test_spec f}.

Lemma f_gen_lts_mu_in_the_middle s1 s2 μ1 :
  Forall non_blocking s1
    -> f (s1 ++ μ1 :: s2) ⟶⋍[μ1] f (s1 ++ s2).
Proof.
  revert s2 μ1.
  induction s1 as [|μ2 s']; intros s2 μ1 his ; simpl in *.
  - eapply (test_next_step μ1).
  - inversion his as [| ? ? nb his']; subst.
    destruct (IHs' s2 μ1 his') as (r & hlr & heqr).
    edestruct (test_next_step μ2 (s' ++ μ1 :: s2))
      as (t & hlt & heqt).
    edestruct (eq_spec t r) as (u & hlu & hequ).
    { eauto with mdb. }
    destruct (nb_delay nb hlt hlu)
      as (v & l1 & (t' & l2 & heq')).
    exists v. split. eassumption.
    destruct (test_next_step μ2 (s' ++ s2)) as (w & hlw & heqw).
    eapply backwards_nb_determinacy; try eassumption.
    etrans. eauto. etrans. eauto. etrans. eauto. now symmetry.
Qed.

Lemma f_gen_lts_mu_in_the_middle' s1 s2 μ1 t :
  Forall non_blocking s1
    -> f (s1 ++ μ1 :: s2) ⟶⋍[μ1] t -> t ⋍ f (s1 ++ s2).
Proof.
  revert s2 μ1 t.
  induction s1 as [|μ2 s']; intros s2 μ1 t his HypTr; simpl in *.
  - destruct (decide (non_blocking μ1)) as [nb | not_nb].
    + assert (f (ε ++ μ1 :: s2) ⟶⋍[μ1] f (ε ++ s2)) as HypTr'.
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
    destruct (decide (non_blocking μ1)) as [nb | not_nb].
    + assert (f ((μ2 :: s') ++ μ1 :: s2) ⟶⋍[μ1] f ((μ2 :: s') ++ s2)) as HypTr'.
      { eapply f_gen_lts_mu_in_the_middle. eauto. }
      destruct HypTr as (e & HypTr & equiv).
      destruct HypTr' as (e' & HypTr' & equiv').
      assert (e ⋍ e').
      { eapply nb_determinacy; eauto. }
      etransitivity. symmetry. exact equiv. etransitivity; eauto.
    + destruct HypTr as (e & HypTr & equiv).
      destruct (decide (non_blocking μ2)) as [nb' | not_nb'].
      ++ assert (f (μ2 :: s' ++ μ1 :: s2) ⟶⋍[μ2] f (s' ++ μ1 :: s2)) as HypTr'.
         { eapply test_next_step. }
         destruct HypTr' as (e' & HypTr' & equiv').
         assert (μ1 <> μ2) as not_eq.
         { intro imp. rewrite imp in not_nb. contradiction. }
         destruct (nb_confluence nb' not_eq HypTr' HypTr )
           as (t' & l2 & (t'' & l1 & heq)).
         assert (f (s' ++ μ1 :: s2) ⟶⋍[μ1] f (s' ++ s2)) as HypTr''.
         { eapply f_gen_lts_mu_in_the_middle; eauto. }
         edestruct (eq_spec (f (s' ++ μ1 :: s2)) t' (ActExt μ1))
          as (v & hlv & heqv).
         exists e'. split; eauto. symmetry; eauto.
         assert (t' ⋍ (f (s' ++ s2))) as heq'.
         { eapply IHs'; eauto. exists v. split; eauto. }
         assert (f (μ2 :: s' ++ s2) ⟶⋍[μ2] f (s' ++ s2)) as (v' & hlv' & heqv').
         { eapply test_next_step. }
         assert (e ⋍ f (μ2 :: s' ++ s2)) as final.
         { eapply backwards_nb_determinacy; eauto.
         etransitivity. exact heq. etransitivity. exact heq'. symmetry; eauto. }
         etransitivity. symmetry. exact equiv. eauto.
      ++ inversion his; subst.
         contradiction.
Qed.

Lemma inversion_test_b_external_action s β' t :
  (forall μ1, f ε ↛[μ1] \/ (forall t, f ε ⟶[μ1] t -> outcome t)) ->
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
  destruct s as [|μ2 s']; intros μ1 t h l not_nb.
  - edestruct (h μ1) as [refuses_f | f_to_outcome].
    + now (exfalso; apply refuses_f, lts_performs_spec2; eauto).
    + left. eapply f_to_outcome. eauto.
  - destruct (decide (non_blocking μ2)) as [nb | b].
    + assert (f (μ2 :: s') ⟶⋍[μ2] f s') as (v & hlv & eqv).
      { eapply test_next_step. }
      assert (μ1 <> μ2) as not_eq.
      { intro. subst. contradiction. }
      destruct (nb_confluence nb not_eq hlv l)
           as (t' & l2 & (t'' & l1 & heq)).
      destruct (eq_spec (f s') t' (ActExt μ1)) as (v' & hlv' & heqv').
      { exists v. split. symmetry; eauto. exact l2. }
      destruct (decide (outcome v')) as [happy' | not_happy'].
      ++ left. eapply outcome_preserved_by_lts_non_blocking_action_converse; eauto.
         eapply outcome_preserved_by_eq; eauto. etransitivity; eauto. symmetry. eauto.
      ++ edestruct (Hlength s') as [happy | (s1 & s2 & μ1' & eq & equiv & eq_action & his)]; eauto.
         +++ contradiction.
         +++ right. subst.
             assert (t ⋍ f ((μ2 :: s1) ++ s2)).
             { eapply f_gen_lts_mu_in_the_middle'. constructor; eauto.
               exists t. split; eauto. reflexivity. }
             exists (μ2 :: s1). exists s2. exists μ1'.
             split. eauto. repeat split; eauto.
    + destruct (decide (μ1 = μ2)) as [eq | neq].
      ++ right. subst.
         exists ε, s', μ2. simpl. repeat split; simpl; eauto with mdb.
         repeat split;eauto. intros. eapply test_follows_trace_determinacy; eauto.
      ++ left. eapply test_side_effect_by_construction; eauto.
Qed.

Lemma inversion_test_nb_external_action s η' t :
  (forall μ1, f ε ↛[μ1] \/ (forall t, f ε ⟶[μ1] t -> outcome t)) ->
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
  destruct s as [|μ2 s']; intros η t h l nb.
  - edestruct (h η) as [Tr|]; eauto. now (exfalso; apply Tr, lts_performs_spec2; eauto).
  - edestruct (test_next_step μ2 s') as (r & hlr & heqr).
    destruct (decide (μ2 = η)) as [eq | not_eq].
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
             as [happy' | (s1' & s2' & μ1' & eq0 & eq1 & eq2 & eq3)]; try contradiction.
        destruct (decide (non_blocking μ2)) as [nb' | not_nb'].
        -- right. subst.
           assert (Forall non_blocking (μ2 :: s1')) as Hyp.
           { constructor; eauto. }
           exists (μ2 :: s1'), s2', μ1'. repeat split; eauto.
           edestruct (f_gen_lts_mu_in_the_middle (μ2 :: s1') s2' μ2)
            as (r' & hlr' & heqr'); eauto.
           edestruct (test_next_step μ2 (s1' ++ s2'))
            as (w & hlw & heqw).
           eapply backwards_nb_determinacy; try eassumption.
           transitivity t''. symmetry. eassumption.
           transitivity v. now symmetry.
           transitivity (f (s1' ++ s2')). eassumption. now symmetry.
        -- subst. assert (outcome t).
           { eapply test_side_effect_by_construction; eauto. } eauto.
Qed.

Lemma inversion_test_external_action s η' t :
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

Lemma inversion_test_tau_action s t :
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
    + eauto. now (exfalso; apply refuses_f, lts_performs_spec2; eauto).
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

End Test_spec_inversion.

Section Test_convergence_inversion.

Context `{gLtsT : gLtsOba T}.
Context `{!Testing_Predicate outcome _}.
Context `{!test_convergence_spec f}.

Lemma inversion_tconv_external_action s μ' t :
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

Lemma inversion_tconv_tau_action s t :
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

End Test_convergence_inversion.

Section Test_acceptance_inversion.

Context `{CC: Countable PreAct}.
Context `{gLtsT : gLtsOba T}.
Context `{!Testing_Predicate outcome _}.
Context `{!test_co_acceptance_set_spec PreAct f Γ}.

Lemma inversion_ta_external_action s μ' (t : T) (O : gset PreAct) :
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

Lemma inversion_ta_tau_action s O t :
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

End Test_acceptance_inversion.

Lemma after_blocking_co_of_must_tacc `{CC : Countable PreAct} `{
  gLtsEqP : @gLtsEq P Aproc Hp,
  gLtsEqT : !@gLtsEq T Atest Ht, gLtsObaT : !gLtsOba T,
  !Testing_Predicate outcome gLtsEqT,
  !test_co_acceptance_set_spec PreAct ta Γ,
  SA : !SyncAction Aproc Atest, STS : !ParSts P T _ _, !ParStsSpec P T _ _ SA STS}
  (p : P) (β : Atest) s E :
  p ⤓ → blocking β →
  (∀ q μ1, sync μ1 β → p ⟹{μ1} q → q must_pass (ta E s)) →
  p must_pass (ta E (β :: s)).
Proof.
  intro tp. revert E β s. induction tp as [p hp IHp].
  intros E β s b hmq.
  apply m_step.
  - apply test_ungood.
  - edestruct (test_tau_transition (test_spec := ta_test_spec E) β s b) as (x & hx).
    exists (p, x). by apply par_step_right.
  - intros p' l. eapply IHp; [exact l | exact b |].
    intros q μ1 hsy w. eapply hmq; [exact hsy |]. eauto with mdb.
  - intros e' l. apply m_now.
    by eapply (test_reset_tau_path (test_spec := ta_test_spec E) β s e').
  - intros p' e' μ1 μ2 hsy l0 l1.
    destruct (decide (μ2 = β)) as [-> | neq].
    + eapply (test_follows_trace_determinacy (test_spec := ta_test_spec E))
        in b as h1; [| exact l1].
      eapply must_eq_client; [by symmetry |].
      eapply hmq; [exact hsy |]. eauto with mdb.
    + apply m_now.
      by eapply (test_side_effect_by_construction (test_spec := ta_test_spec E)).
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
  gLtsP : @gLts P Aproc Hp,
  gLtsEqT : @gLtsEq T Atest Ht, gLtsObaT : !gLtsOba T, !gLtsObaFB T Atest,
  SA : !SyncAction Aproc Atest,
  AbsPT : !@AbsActionG P T PreAct Atest Ht Γ Aproc Hp _ _ SA,
  !Testing_Predicate outcome gLtsEqT,
  !test_co_acceptance_set_spec PreAct ta Γ,
  STS : !ParSts P T _ _, !ParStsSpec P T _ _ SA STS}
  (p : P) E1 :
  p must_pass (ta E1 ε) → ∀ E2, E1 ⊆ E2 → p must_pass (ta E2 ε).
Proof.
  intros hm.
  assert (hpt : p ⤓)
    by now (eapply must_terminate_unoutcome, test_ungood; eauto).
  induction hpt. dependent induction hm; intros E2 hsub.
  - exfalso. by eapply (test_ungood (test_spec := ta_test_spec E1) ε).
  - apply m_step.
    + apply test_ungood.
    + destruct ex as ((p' & e') & l'). pose proof (par_view_of _ _ _ l') as hv; inversion hv; subst.
      ++ exists (p', ta E2 ε). by apply par_step_left.
      ++ exfalso.
         assert ((ta E1 ε) ⟶) as himp by (eapply lts_performs_spec2; eauto).
         revert himp. eapply ta_does_no_tau; eauto.
      ++ destruct (decide (non_blocking η)) as [nb2 | not_nb2].
         +++ exfalso.
             assert ((ta E1 ε) ⟶[η]) as himp by (eapply lts_performs_spec2; eauto).
             revert himp. eapply ta_does_no_non_blocking_actions; eauto.
         +++ assert (η ∈ coR p) as co_set.
             { eapply coR_intro;
                 [ eapply lts_performs_spec2; eauto | exact hs | exact not_nb2 ]. }
             eapply ta_actions_are_in_its_gamma_set in l2 as mem; [| exact not_nb2].
             eapply hsub in mem.
             eapply ta_has_a_representative_transition_for_its_gamma_set in mem
               as (r & η' & Tr' & eq').
             assert (blocking η') as bη'.
             { intro imp. eapply ta_does_no_non_blocking_actions in imp.
               apply imp, (@lts_performs_spec2 T). exists r; exact Tr'. }
             assert (acc : ta E2 ε ⟶[η']) by (apply (@lts_performs_spec2 T); exists r; exact Tr').
             destruct (abstraction_step_test Γ p (ta E2 ε) η' η bη' eq' co_set acc)
               as (u & (μ'' & Tr & duo & bu) & Tr'').
             eapply lts_performs_spec1 in Tr'' as (e'' & Tr'').
             eapply lts_performs_spec1 in Tr as (p'' & Tr).
             exists (p'', e''). eapply par_step_sync; [exact duo | exact Tr | exact Tr''].
    + intros p'' l. eapply H3; eauto.
    + intros e l. exfalso.
      assert ((ta E2 ε) ⟶) as himp by (eapply lts_performs_spec2; eauto).
      revert himp. eapply ta_does_no_tau; eauto.
    + intros p'' e'' μ η hsy l2 l1.
      destruct (decide (non_blocking η)) as [nb | not_nb].
      ++ exfalso.
         assert ((ta E2 ε) ⟶[η]) as himp by (eapply lts_performs_spec2; eauto).
         revert himp. eapply ta_does_no_non_blocking_actions; eauto.
      ++ apply m_now. eapply (ta_transition_to_good η e'' E2 not_nb l1).
Qed.

Lemma stable_process_must_ta_or_empty_pre_action_set {P : Type}
  `{CC : Countable PreAct} `{
  gLtsEqP : @gLtsEq P Aproc Hp,
  gLtsEqT : !@gLtsEq T Atest Ht, gLtsObaT : !gLtsOba T,
  SA : !SyncAction Aproc Atest,
  FiniteAbs : !@FinitaryAbsActionG P T PreAct Atest Ht Γ Aproc Hp _ _ SA _ _,
  !Testing_Predicate outcome gLtsEqT,
  !test_co_acceptance_set_spec PreAct ta Γ,
  STS : !ParSts P T _ _, !ParStsSpec P T _ _ SA STS}
  (p : P) (E : gset PreAct) :
  p ↛ → p must_pass (ta ((coR_abs p) ∖ E) ε) ∨ (coR_abs p ⊆ E).
Proof.
  intros hst.
  remember ((coR_abs p) ∖ E) as D.
  destruct D as [| a D'] using set_ind_L.
  + right. set_solver.
  + left. apply m_step.
    ++ apply test_ungood.
    ++ assert (a ∈ coR_abs p ∖ E) as mem' by set_solver.
       assert (a ∈ coR_abs p) as co_set by (eapply elem_of_difference; eauto).
       eapply ta_has_a_representative_transition_for_its_gamma_set in mem'
         as (r & η & Tr & eq).
       subst. eapply coR_abs_spec1 in co_set.
       destruct co_set as (η'' & co_set & eq).
       assert (blocking η) as bη.
       { intro imp. eapply ta_does_no_non_blocking_actions in imp.
         apply imp, (@lts_performs_spec2 T). exists r; exact Tr. }
       assert (acc : ta (coR_abs p ∖ E) ε ⟶[η])
         by (apply (@lts_performs_spec2 T); exists r; exact Tr).
       destruct (abstraction_step_test Γ p _ η η'' bη eq co_set acc) as (η' & Tr' & Tr'').
       rewrite <- HeqD in Tr''.
       eapply lts_performs_spec1 in Tr'' as (e'' & Tr'').
       destruct Tr' as (μ''' & Tr' & duo & bη').
       eapply lts_performs_spec1 in Tr' as (p'' & Tr').
       exists (p'', e''). eapply par_step_sync; [exact duo | exact Tr' | exact Tr''].
    ++ intros p' l'. exfalso. generalize (lts_performs_spec2 p _ (exist _ p' l')). eauto with mdb.
    ++ intros e' l'. exfalso.
       assert (ta (coR_abs p ∖ E) ε ⟶).
       { rewrite <- HeqD. eapply lts_performs_spec2; eauto. }
       assert (ta (coR_abs p ∖ E) ε ↛).
       { rewrite <- HeqD. eapply ta_does_no_tau; eauto. }
       contradiction.
    ++ intros p'' e'' μ' η hsy l'1 l'0.
       destruct (decide (non_blocking η)) as [nb' | not_nb'].
       +++ exfalso. eapply ta_does_no_non_blocking_actions, (@lts_performs_spec2 T); eauto with mdb.
       +++ apply m_now. eapply ta_transition_to_good; eauto.
Qed.

Section Must_tconv_co.

Context `{gLtsP : @gLtsEq P Aproc Hp}.
Context `{gLtsT : !@gLtsEq T Atest Ht}.
Context `{!Testing_Predicate outcome gLtsT}.
Context `{!test_convergence_spec tconv}.
Context `{SA : !SyncAction Aproc Atest}.
Context `{STS : !ParSts P T _ _}.
Context `{!ParStsSpec P T _ _ SA STS}.

Lemma must_tconv_cowt_mu_gen (s0 : trace Atest) (p q : P) :
  p ⟹ᶜᵒ[s0] q → ∀ η s, s0 = [η] →
  p must_pass (tconv (η :: s)) → q must_pass (tconv s).
Proof.
  induction 1 as [p | s0 p r t l w IH | μ1 η s0 p r t hs l w IH]; intros μ2 s heq hm.
  - discriminate.
  - eapply IH; [exact heq |]. by eapply must_preserved_by_lts_tau_srv.
  - inversion heq; subst.
    edestruct (test_next_step μ2 s) as (t' & hlt' & heqt').
    eapply (must_eq_client _ _ _ heqt').
    eapply (must_preserved_by_weak_nil_srv r t);
      [| by apply (cowt_iff_wt_nil)].
    eapply must_preserved_by_synch_if_notoutcome;
      [exact hm | apply test_ungood | exact hs | exact l | exact hlt'].
Qed.

Lemma must_tconv_cowt_mu (η : Atest) s (p q : P) :
  p must_pass (tconv (η :: s)) → p ⟹ᶜᵒ[[η]] q → q must_pass (tconv s).
Proof. intros hm w. by eapply must_tconv_cowt_mu_gen. Qed.

Lemma cocnv_if_must s (p : P) : p must_pass (tconv s) → p ⇓ᶜᵒ s.
Proof.
  revert p. induction s as [| η s' IH]; intros p hm.
  - apply cocnv_nil.
    eapply (must_terminate_unoutcome _ _ hm), test_ungood.
  - apply cocnv_act.
    + eapply (must_terminate_unoutcome _ _ hm), test_ungood.
    + intros q w. eapply IH, must_tconv_cowt_mu; [exact hm | exact w].
Qed.

End Must_tconv_co.

Lemma after_blocking_co_of_must_tacc_co `{CC : Countable PreAct} `{
  gLtsEqP : @gLtsEq P Aproc Hp,
  gLtsEqT : !@gLtsEq T Atest Ht, gLtsObaT : !gLtsOba T,
  !Testing_Predicate outcome gLtsEqT,
  !test_co_acceptance_set_spec PreAct ta Γ,
  SA : !SyncAction Aproc Atest, STS : !ParSts P T _ _, !ParStsSpec P T _ _ SA STS}
  (p : P) (β : Atest) s E :
  p ⤓ → blocking β → (∀ q, p ⟹ᶜᵒ[[β]] q → q must_pass (ta E s)) →
  p must_pass (ta E (β :: s)).
Proof.
  intros hp hb hq.
  eapply after_blocking_co_of_must_tacc; [exact hp | exact hb |].
  intros q μ hsy w.
  eapply hq, (wt_to_cowt p [μ] q w).
  constructor; [exact hsy | constructor].
Qed.

Section Coacceptance_set_inclusions.

Context `{CC : Countable PreAct}.
Context `{gLtsP : @gLts P Aproc Hp}.
Context `{gLtsT : !@gLtsEq T A H}.
Context `{SA : !SyncAction Aproc A}.
Context `{!coFiniteImagegLts P A}.
Context `{FiniteAbs : !@FinitaryAbsActionG P T PreAct A H Γ Aproc Hp gLtsP gLtsT SA _ _}.

Lemma cowt_acceptance_set_subseteq μ s p q hacnv1 hacnv2 :
  p ⟹ᶜᵒ{μ} q ->
  map (coR_abs) (elements (cowaiting_states q s hacnv1)) ⊆
    map (coR_abs) (elements (cowaiting_states p (μ :: s) hacnv2)).
Proof.
  intros.
  intros a in__a.
  assert (cowaiting_states q s hacnv1 ⊆ cowaiting_states p (μ :: s) hacnv2).
  intros t in__t.
  eapply cowaiting_states_spec2.
  eapply cowaiting_states_spec1 in in__t.
  destruct in__t. split; eauto with mdb.
  eapply cowt_push_left; eauto.
  set_solver.
Qed.

Lemma lts_tau_cowt_acceptance_set_subseteq s p q hacnv1 hacnv2 :
  p ⟶ q ->
  map coR_abs  (elements $ cowaiting_states q s hacnv1) ⊆
    map coR_abs (elements $ cowaiting_states p s hacnv2).
Proof.
  intros.
  intros a in__a.
  assert (cowaiting_states q s hacnv1 ⊆ cowaiting_states p s hacnv2).
  { intros t in__t. eapply cowaiting_states_spec2.
    eapply cowaiting_states_spec1 in in__t.
    destruct in__t. split; eauto with mdb. }
  set_solver.
Qed.

Definition cooas (p : P) (s : list A) (hcocnv : p ⇓ᶜᵒ s) : gset PreAct :=
  let ps : list P := elements (cowaiting_states p s hcocnv) in
  ⋃ map coR_abs ps.

Lemma union_cowt_acceptance_set_subseteq μ s p q h1 h2 :
  p ⟹ᶜᵒ{μ} q -> cooas q s h1 ⊆ cooas p (μ :: s) h2.
Proof.
  intros hw a (O & mem1 & mem2)%elem_of_union_list.
  eapply elem_of_union_list.
  exists O. split; eauto. eapply cowt_acceptance_set_subseteq; eauto.
Qed.

Lemma union_acceptance_set_lts_tau_cowt_subseteq s p q h1 h2 :
  p ⟶ q -> cooas q s h1 ⊆ cooas p s h2.
Proof.
  intros l a (L & mem1 & mem2)%elem_of_union_list.
  eapply elem_of_union_list.
  exists L. split; eauto.
  eapply lts_tau_cowt_acceptance_set_subseteq; eauto.
Qed.

End Coacceptance_set_inclusions.

Lemma not_must_ta_without_required_acc_set_co {Q : Type} `{CC : Countable PreAct} `{
  gLtsQ : @gLts Q Aproc Hp,
  gLtsEqT : !@gLtsEq T A H, gLtsObaT : !gLtsOba T, !gLtsObaFB T A,
  SA : !SyncAction Aproc A,
  FiniteAbs : !@FinitaryAbsActionG Q T PreAct A H Γ Aproc Hp gLtsQ gLtsEqT SA _ _,
  !Testing_Predicate outcome _,
  !test_co_acceptance_set_spec PreAct ta Γ,
  STS : !ParSts Q T gLtsQ gLtsEqT, !ParStsSpec Q T gLtsQ gLtsEqT SA STS}
  (q q' : Q) s (E : gset PreAct) :
  q ⟹ᶜᵒ[s] q' -> q' ↛ -> ¬ q must_pass (ta (E ∖ (coR_abs q')) s).
Proof.
  intros wt hst.
  dependent induction wt; intros hm.
  - inversion hm as [happy |]; subst.
    ++ contradict happy. apply test_ungood.
    ++ destruct ex as (y & l). pose proof (par_view_of _ _ _ l) as hv. inversion hv; subst.
       +++ apply hst, (lts_performs_spec2 p τ); eauto with mdb.
       +++ eapply ta_does_no_tau, (@lts_performs_spec2 T); [eauto.. | by eexists].
       +++ destruct (decide (non_blocking η)) as [nb | not_nb].
           ++++ exfalso. eapply ta_does_no_non_blocking_actions, (@lts_performs_spec2 T); [eauto.. | by eexists].
           ++++ eapply ta_actions_are_in_its_gamma_set in l2 as mem; [| exact not_nb].
                assert (Γ η ∉ coR_abs p) as not_in_mem by set_solver.
                assert (Γ η ∈ coR_abs p) as in_mem.
                { eapply coR_abs_spec2, map_gamma_of_action.
                  eapply coR_intro;
                    [eapply lts_performs_spec2; by eexists | exact hs | exact not_nb]. }
                contradiction.
  - eapply (IHwt hst).
    by eapply must_preserved_by_lts_tau_srv.
  - assert (ta (E ∖ (coR_abs t)) (μ :: s) ⟶⋍[μ] ta (E ∖ (coR_abs t)) s)
      as (e' & hle' & heqe') by eapply (test_next_step (test_spec := ta_test_spec _)).
    eapply (IHwt hst).
    eapply must_eq_client; [exact heqe' |].
    eapply must_preserved_by_synch_if_notoutcome;
      [exact hm | apply test_ungood | exact duo | exact l | exact hle'].
Qed.

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Wf Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.
From stdpp Require Import base countable decidable finite gmap list.
From TestingTheory Require Import ActTau gLts SyncActions MemAction InteractionUnion MemForwarder Bisimulation Lts_OBA
  Lts_OBA_FB Lts_FW Subset_Act Termination WeakTransitions
  coWeakSync
  FiniteImageLTS coFiniteImage Testing_Predicate InteractionBetweenLts
  Must DefinitionASrel
  coWeakTransition coConvergence.

#[local] Hint Mode ExtAction ! : typeclass_instances.

(* ** Swapping a non-blocking action across the composition, on forwarders

    [Lift.must_non_blocking_action_swap_l_fw] for two alphabets.  In the
    homogeneous statement the process and the observer perform the /same/
    non-blocking action [η]; here the observer performs [ν] over [Atest] and
    the forwarder gives the same message back as [inr (msg ν)]. *)

Section SwapSync.

Context {P T Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context `{gLtsEqP : !gLtsEq P (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))}.
Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T} `{!gLtsObaFB T Atest}.
Context (outcome : T → Prop) `{!Testing_Predicate outcome gLtsEqT}.
Context `{!gLtsFWMem P Aproc Atest} `{!Prop_of_Inter P T (Aproc + MemAct Atest) Atest sync}.

Lemma must_non_blocking_action_swap_l_fw_sync_eq
  (p1 p2 : P) (e1 e2 : T) (η3 : Atest) :
  non_blocking η3 →
  p1 ⟶⋍[inr (msg η3)] p2 → e1 ⟶⋍[η3] e2 → p1 must_pass e2 → p2 must_pass e1.
Proof.
  intros nbν lp le hm.
  destruct (msg_spec (Aproc := Aproc) η3 nbν) as (nbγ & hdν).
  set (γ := inr (msg η3) : Aproc + MemAct Atest) in *.
  assert (hsyco : sync (inr (cobar η3) : Aproc + MemAct Atest) η3) by reflexivity.
  revert e1 p2 lp le.
  induction hm as [p e happy | p1 e2 nh ex Hpt IHpt Het IHet Hcom IHcom];
    intros e1 p2 lp le.
  - apply m_now.
    destruct le as (e' & hle' & heqe').
    eapply outcome_preserved_by_lts_non_blocking_action_converse;
      [exact nbν | exact hle' |].
    eapply outcome_preserved_by_eq; [exact happy | by symmetry].
  - apply m_step.
    + intro h.
      destruct le as (e' & hle' & heqe').
      eapply nh, (outcome_preserved_by_eq e' e2); [| exact heqe'].
      eapply outcome_preserved_by_lts_non_blocking_action;
        [exact nbν | exact hle' | exact h].
    + (* [fwm_boomerang]: [p2] can take back what [p1] has emitted, as the
         memory reception [inr (cobar η3)], which synchronises with [η3] *)
      destruct (fwm_boomerang p2 η3 nbν) as (p'2 & Tr1 & Tr2).
      destruct le as (e'1 & Tr & eq).
      exists (p'2, e'1). eapply par_step_sync; [exact hsyco | exact Tr1 | exact Tr].
    + intros p' l.
      destruct lp as (p0 & hlp0 & heqp0).
      edestruct (eq_spec p0 p' τ) as (p3 & hlp3 & heqp3).
      { exists p2. split; [by symmetry | exact l]. }
      destruct (fw_delay η3 nbν hlp0 hlp3) as (t & l1 & (p4 & hlp4 & heqp4)).
      eapply must_eq_server; [etrans; [eapply heqp4 | exact heqp3] |].
      eapply IHpt; [exact l1 | exists p4; split; [exact hlp4 | reflexivity] | exact le].
    + intros e' l.
      destruct le as (e0 & hle0 & heqe0).
      destruct (nb_tau nbν hle0 l) as [(t & l0 & l1) | Hyp].
      ++ destruct (eq_spec e2 t τ) as (v & hlv & heqv).
         { exists e0. split; [by symmetry | exact l0]. }
         eapply IHet; [exact hlv | exact lp |].
         destruct l1 as (e3 & hle3 & heqe3).
         exists e3. split; [exact hle3 | etrans; [exact heqe3 | by symmetry]].
      ++ destruct Hyp as (μ & duo & u & hlu & hequ).
         destruct (eq_spec e2 u (ActExt μ)) as (v & hlv & heqv).
         { exists e0. split; [by symmetry | exact hlu]. }
         eapply must_eq_client; [etrans; [exact heqv | exact hequ] |].
         destruct lp as (p0 & hlp0 & heqp0).
         eapply must_eq_server; [exact heqp0 |].
         eapply Hcom; [| exact hlp0 | exact hlv].
         (* [msg_spec]'s second clause: a dual of [η3] on the observer side
            is answered by [γ] itself *)
         by apply hdν.
    + intros p' e' μ1 μ2 hsy2 l1 l2.
      destruct lp as (p0 & hlp0 & heqp0).
      destruct le as (e0 & hle0 & heqe0).
      destruct (decide (μ2 = η3)) as [-> | n]; simpl in l2.
      ++ edestruct (eq_spec p0 p' (ActExt μ1)) as (p3 & hlp3 & heqp3).
         { exists p2. split; [by symmetry | exact l1]. }
         assert (heqe' : e0 ⋍ e')
           by (eapply nb_determinacy; [exact nbν | exact hle0 | exact l2]).
         destruct (sync_fwd_feedback η3 μ1 nbν hsy2 hlp0 hlp3) as [(p3' & hlp3' & heqp3') |].
         +++ eapply must_eq_client; [etrans; [by symmetry; exact heqe0 | exact heqe'] |].
             eapply must_eq_server; [etrans; [exact heqp3' | exact heqp3] |].
             by apply Hpt.
         +++ eapply must_eq_client; [etrans; [by symmetry; exact heqe0 | exact heqe'] |].
             eapply must_eq_server; [etrans; [exact H | exact heqp3] |].
             apply m_step; assumption.
      ++ destruct (nb_confluence nbν n hle0 l2) as (t & l3 & (e4 & hle4 & heqe4)).
         edestruct (eq_spec p0 p' (ActExt μ1)) as (p3 & hlp3 & heqp3).
         { exists p2. split; [by symmetry | exact l1]. }
         destruct (fw_delay η3 nbν hlp0 hlp3) as (r & l5 & (p4 & hlp4 & heqp4)).
         edestruct (eq_spec e2 t (ActExt μ2)) as (e3 & hle3 & heqe3).
         { exists e0. split; [by symmetry | exact l3]. }
         eapply IHcom.
         * exact hsy2.
         * exact l5.
         * exact hle3.
         * exists p4. split; [exact hlp4 | etrans; [exact heqp4 | exact heqp3]].
         * exists e4. split; [exact hle4 | etrans; [exact heqe4 | by symmetry]].
Qed.

Lemma must_non_blocking_action_swap_l_fw_sync
  (p1 p2 : P) (e1 e2 : T) (η : Atest) :
  non_blocking η →
  p1 ⟶[inr (msg η)] p2 → e1 ⟶[η] e2 → p1 must_pass e2 → p2 must_pass e1.
Proof.
  intros. eapply must_non_blocking_action_swap_l_fw_sync_eq;
    eauto; eexists; split; eauto; reflexivity.
Qed.

End SwapSync.

(* ** A single co-step against the convergence observer *)

(* the trace is kept as a variable, constrained by an equation, so that plain
   induction applies *)
(* ** The observer of convergence characterises co-convergence *)

Section Must_iff_cocnvs_sync.

Context `{Hp : ExtAction Aproc}.
Context `{Ht : ExtAction Atest}.
Context `{SA : !SyncAction Aproc Atest}.
Context `{gLtsEqP : @gLtsEq P (Aproc + MemAct Atest) (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))}.
Context `{gLtsEqT : !@gLtsEq T Atest Ht}.
Context `{gLtsObaT : !gLtsOba T}.
Context `{!gLtsObaFB T Atest}.
Context `{!Testing_Predicate outcome gLtsEqT}.
Context `{!test_convergence_spec tconv}.
Context `{!gLtsFWMem P Aproc Atest}.
Context `{!Prop_of_Inter P T (Aproc + MemAct Atest) Atest sync}.

Lemma must_sync_if_cocnvs s (p : P) : p ⇓ᶜᵒ s → p must_pass (tconv s).
Proof.
  revert p.
  induction s as (s & Hlength) using
    (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  intros p hc.
  induction (cocnv_terminate p s hc) as [p hp IHtp].
  apply m_step.
  + apply test_ungood.
  + edestruct tconv_always_reduces as (x & hx). exists (p, x). by apply par_step_right.
  + intros p' l. eapply IHtp; [exact l | by eapply cocnv_preserved_by_lts_tau].
  + intros e' l.
    destruct (inversion_tconv_tau_action s e' l)
      as [hu | (η & μ2 & s1 & s2 & s3 & eqs & sc & i0 & i1 & i2 & duo)];
      [by apply m_now |].
    eapply must_eq_client; [by symmetry |].
    subst. eapply Hlength.
    * rewrite 6 length_app. simpl. lia.
    * by eapply cocnv_annhil_fw.
  + intros p' e' μ1 μ2 hsy hlp hle.
    destruct (inversion_tconv_external_action s μ2 e' hle)
      as [hg | (s1 & s2 & μ2'' & heq & sc & eq & his)]; [by apply m_now |].
    subst.
    eapply must_eq_client; [by symmetry |].
    eapply Hlength.
    * rewrite length_app. simpl. rewrite length_app. simpl. lia.
    * by eapply cocnv_drop_action_in_the_middle_fw.
Qed.

Lemma must_sync_iff_cocnvs (p : P) s : p must_pass (tconv s) ↔ p ⇓ᶜᵒ s.
Proof.
  split; [by apply cocnv_if_must | by apply must_sync_if_cocnvs].
Qed.

End Must_iff_cocnvs_sync.

(* ** The convergence half of completeness *)

Lemma completeness1_co_sync `{
  Hp : ExtAction Aproc, Ht : ExtAction Atest, SA : !SyncAction Aproc Atest,
  gLtsEqP : @gLtsEq P (Aproc + MemAct Atest) (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht)),
  gLtsEqQ : !@gLtsEq Q (Aproc + MemAct Atest) (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht)),
  gLtsEqT : !@gLtsEq T Atest Ht, gLtsObaT : !gLtsOba T, !gLtsObaFB T Atest,
  !Testing_Predicate outcome gLtsEqT, !test_convergence_spec tconv,
  !gLtsFWMem P Aproc Atest, !gLtsFWMem Q Aproc Atest,
  !Prop_of_Inter P T (Aproc + MemAct Atest) Atest sync, !Prop_of_Inter Q T (Aproc + MemAct Atest) Atest sync}
  (p : P) (q : Q) :
  ctx_pre (gLtsT := gLtsEqT) p q → bhv_pre_g_cond1 (A := Atest) p q.
Proof.
  intros hleq s hc.
  by eapply must_sync_iff_cocnvs, hleq, must_sync_iff_cocnvs.
Qed.

(* ** Completeness, the acceptance-set half

    The port of the second half of [CompletenessASco.v].  The observer is now
    [ta E s] with [s : trace Atest] and [E : gset PreAct]; the co-actions it has
    to offer are read off [coR p], a set of /test/ actions. *)

(* *** Prefixing the observer with a blocking action *)

(* *** Monotonicity in the acceptance set, for the empty trace

    The interesting case is the synchronisation one: the observer [ta E1 ε] had
    a blocking action [η] matching an action of [p]; the bigger observer
    [ta E2 ε] has a representative [η'] of the same abstraction, and
    [abstraction_prog_spec] turns it back into an action [η''] of
    [coR p]. *)

(* *** Monotonicity in the acceptance set, for an arbitrary trace

    [inversion_ta_tau_action], [inversion_ta_external_action], [ta_tau_ex] and
    [f_gen_lts_mu_in_the_middle] are the observer-only lemmas of
    [CompletenessASco.v], reused here over [Atest].  The one step that changes
    is the synchronisation witness: where the homogeneous proof made [p] accept
    [co μ2] for the non-blocking [μ2] of the trace, here [fwm_boomerang] makes
    [p] accept [μ2] as the memory reception [inr (cobar μ2)]. *)

Lemma must_ta_monotonicity_sync {P : Type} `{CC : Countable PreAct} `{
  Hp : ExtAction Aproc, Ht : ExtAction Atest, SA : !SyncAction Aproc Atest,
  gLtsEqP : @gLtsEq P (Aproc + MemAct Atest) (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht)),
  gLtsEqT : !@gLtsEq T Atest Ht, gLtsObaT : !gLtsOba T, !gLtsObaFB T Atest,
  !gLtsFWMem P Aproc Atest,
  AbsPT : !@AbsActionG P T PreAct Atest Ht Γ (Aproc + MemAct Atest) ExtAction_sum _ _ SyncAction_mem,
  !Testing_Predicate outcome gLtsEqT,
  !test_co_acceptance_set_spec PreAct ta Γ,
  !Prop_of_Inter P T (Aproc + MemAct Atest) Atest sync}
  s (p : P) E1 :
  p must_pass (ta E1 s) → ∀ E2, E1 ⊆ E2 → p must_pass (ta E2 s).
Proof.
  revert p E1.
  induction s as (s & Hlength) using
    (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [| μ1 s']; intros p E1 hm E2 hsub.
  - eapply must_ta_monotonicity_nil; eauto.
  - assert (htp : p ⤓) by (eapply must_terminate_unoutcome, test_ungood; eauto).
    induction htp.
    inversion hm as [hg | nh ex pt et com].
    * exfalso. by eapply (test_ungood (test_spec := ta_test_spec E1) (μ1 :: s')).
    * apply m_step.
      + apply test_ungood.
      + destruct (decide (non_blocking μ1)) as [nb | not_nb].
        (* [fwm_boomerang]: the forwarder's memory receives [μ1] *)
        ++ destruct (fw_boomerang_total p μ1 nb) as (μ0 & p' & hsyco & tr_b & _).
           assert (ta E2 (μ1 :: s') ⟶⋍[μ1] ta E2 s') as (t' & tr' & eq')
             by eapply (test_next_step (test_spec := ta_test_spec E2)).
           exists (p', t'). eapply par_step_sync; [exact hsyco | exact tr_b | exact tr'].
        ++ assert (∃ e', ta E2 (μ1 :: s') ⟶ e') as (e' & tr')
             by (eapply (test_tau_transition (test_spec := ta_test_spec E2)); eauto).
           exists (p, e'). by eapply par_step_right.
      + intros p' l. eapply H0; eauto.
      + intros e' l.
        edestruct (inversion_ta_tau_action (μ1 :: s') E2 e' l) as [hg | Hyp];
          [by apply m_now |].
        destruct Hyp as (η & μ & s1 & s2 & s3 & heqs & sc & himu & his1 & his2 & duo).
        eapply (must_eq_client p (ta E2 (s1 ++ s2 ++ s3))); [by symmetry |].
        edestruct (ta_tau_ex s1 s2 s3 η μ E1) as (t & hlt & heqt); eauto.
        eapply Hlength.
        ++ rewrite heqs, 6 length_app. simpl. lia.
        ++ eapply must_eq_client; [eapply heqt |]. eapply et. by rewrite heqs.
        ++ exact hsub.
      + intros p' e' μ η hsy l1 l2.
        edestruct (inversion_ta_external_action (μ1 :: s') η e' E2) as [hg | Hyp];
          [exact l2 | by apply m_now |].
        destruct Hyp as (s1 & s2 & η''' & heqs & heq & eq & his1). subst.
        eapply must_eq_client; [by symmetry |].
        edestruct (f_gen_lts_mu_in_the_middle (f := ta E1) (test_spec0 := ta_test_spec E1)
                     s1 s2 η''' his1) as (t & l & heq').
        eapply Hlength.
        ++ rewrite heqs, 2 length_app. simpl. lia.
        ++ eapply must_eq_client; [eapply heq' |].
           eapply com; [exact hsy | exact l1 |]. rewrite heqs. exact l.
        ++ exact hsub.
Qed.

(* *** A stable process passes the observer of its own co-actions

    Unless that set is already contained in [E]: the observer [ta (coR_abs p ∖ E) ε]
    offers a representative of every abstract co-action of [p] that [E] misses,
    so the composition can always take a synchronisation step. *)

(* *** A blocking co-step of the process, in one go *)

(* ** The acceptance sets along a co-trace

    From here on the binders are collected in a section: every lemma needs the
    same long list, and naming the instances is also what keeps elaboration
    from searching for [FinitaryAbsActionG] with [T] unknown —
    hence the [coRa] abbreviation below. *)

Section AcceptanceSetsSync.

Context {P T PreAct Aproc Atest : Type}.
Context `{CC : Countable PreAct}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context `{gLtsEqP : !gLtsEq P (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))}.
Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T} `{!gLtsObaFB T Atest}.
Context `{!gLtsFWMem P Aproc Atest} `{!Prop_of_Inter P T (Aproc + MemAct Atest) Atest sync}.
Context `{CFI : !coFiniteImagegLts P Atest}.
Context (Γ : Atest → PreAct).
Context `{FiniteAbs : !FinitaryAbsActionG P T Ht Γ}.
Context (outcome : T → Prop) `{!Testing_Predicate outcome gLtsEqT}.
Context (ta : gset PreAct → list Atest → T)
        `{!test_co_acceptance_set_spec PreAct ta Γ}.

Notation coRa := (coR_abs (FinitaryAbsActionG := FiniteAbs)).

(* *** Monotonicity of the stable states reached along a co-trace *)

(* *** The union of the acceptance sets reachable along a co-trace *)

(* *** Either some stable state of [p] is covered by [E], or [p] passes the
    observer of what [E] misses — first for the empty co-trace *)

Lemma must_ta_or_empty_pre_action_set_for_empty_trace_co_sync
  (p : P) (hcocnv : p ⇓ᶜᵒ ε) (E : gset PreAct) :
  (∃ p', p ⟹ p' ∧ (p' ↛) ∧ coRa p' ⊆ E)
  ∨ p must_pass (ta ((cooas p ε hcocnv) ∖ E) ε).
Proof.
  induction (cocnv_terminate p ε hcocnv) as (p, hpt, ihhp).
  destruct (decide (p ⟶)) as [(p'' & l)%lts_performs_spec1 | st].
  + assert (∀ q0 : P,
         q0 ∈ cowt_tau_set p
         → (∃ p' : P, q0 ⟹ p' ∧ p' ↛ ∧ coRa p' ⊆ E)
           ∨ (∃ h, q0 must_pass (ta ((cooas q0 ε h) ∖ E) ε))) as Hyp.
    { intros q' l'%cowt_tau_set_spec. destruct (hpt q' l') as (hq).
      edestruct (ihhp q' l') as [hl | hr].
      * now left.
      * right. exists (cocnv_nil q' (tstep q' hq)). eauto. }
    destruct (@exists_forall_in P (cowt_tau_set p) _ _ Hyp) as [Hyp' | Hyp'].
    - eapply Exists_exists in Hyp' as (t & l'%cowt_tau_set_spec & t' & w & st & sub).
      left. exists t'. eauto with mdb.
    - right. apply m_step.
      * apply test_ungood.
      * exists (p'', ta ((cooas p ε hcocnv) ∖ E) ε). by eapply par_step_left.
      * intros p0 l0.
        assert (m0 : p0 ∈ cowt_tau_set p) by by eapply cowt_tau_set_spec.
        eapply Forall_forall in Hyp' as (h0 & hm); [| exact m0].
        eapply must_ta_monotonicity_sync; [exact hm |].
        eapply difference_mono_r, union_acceptance_set_lts_tau_cowt_subseteq, l0.
      * intros e' l'. exfalso.
        eapply ta_does_no_tau, (@lts_performs_spec2 T); [eauto.. | by exists e'].
      * intros p0 e0 μ1' η hsy lp le.
        destruct (decide (non_blocking η)) as [nb | not_nb].
        ++ exfalso.
           eapply ta_does_no_non_blocking_actions, (@lts_performs_spec2 T); [eauto.. | by exists e0].
        ++ apply m_now. eapply ta_transition_to_good; eauto.
  + destruct (stable_process_must_ta_or_empty_pre_action_set p E st) as [Hyp | Hyp].
    ++ right. assert (cooas p ε hcocnv = coRa p) as eq.
       { unfold cooas.
         rewrite cowaiting_states_stable_singleton, elements_singleton; [| exact st].
         simpl. by rewrite union_empty_r_L. }
       rewrite eq. exact Hyp.
    ++ left. exists p. split; [constructor | split; [exact st | exact Hyp]].
Qed.

(* *** ... and then for an arbitrary co-trace

    The non-blocking case is the one that changes: [fwm_boomerang] makes [p]
    receive the trace's [μ2] and give it back as [inr (msg μ2)], and
    [must_non_blocking_action_swap_l_fw_sync] moves it from the process side
    to [μ2] on the observer side. *)

Lemma must_ta_or_empty_pre_action_set_for_all_trace_co_sync
  s (p : P) (hcocnv : p ⇓ᶜᵒ s) (E : gset PreAct) :
  (∃ p', p ⟹ᶜᵒ[s] p' ∧ (p' ↛) ∧ coRa p' ⊆ E)
  ∨ p must_pass (ta ((cooas p s hcocnv) ∖ E) s).
Proof.
  revert p hcocnv E.
  induction s as [| μ1 s' IHs'].
  - intros p hcocnv E.
    destruct (must_ta_or_empty_pre_action_set_for_empty_trace_co_sync p hcocnv E)
      as [(p' & w & st & sub) | hm].
    + left. exists p'. split; [by eapply cowt_iff_wt_nil | by split].
    + right. exact hm.
  - intros p hcocnv E.
    set (ps := cowt_set_mu p μ1 s' hcocnv).
    inversion hcocnv as [| ? ? ? conv Hyp_conv]; subst.
    assert (hcocnv0 : ∀ p', p' ∈ ps → p' ⇓ᶜᵒ s')
      by (intros ? mem%cowt_set_mu_spec1; eauto).
    assert (he : ∀ p', p' ∈ ps →
      ((∃ pr p0, p0 ∈ cowaiting_states p' s' pr ∧ coRa p0 ⊆ E)
        ∨ (∃ h, p' must_pass (ta ((cooas p' s' h) ∖ E) s')))).
    { intros p' mem. destruct (IHs' p' (hcocnv0 _ mem) E) as [(r & w & st & sub) | hm].
      * left. eapply cowt_set_mu_spec1 in mem.
        exists (Hyp_conv _ mem), r. split; [eapply cowaiting_states_spec2 |]; eauto.
      * right. eauto. }
    destruct (exists_forall_in_gset ps _ _ he) as [Hyp | Hyp].
    + left. destruct Hyp
        as (p1 & ?%cowt_set_mu_spec1 & ? & r & (? & ?)%cowaiting_states_spec1 & ?).
      exists r. split; [by eapply cowt_push_left | by split].
    + right.
      destruct (decide (non_blocking μ1)) as [nb | b].
      ++ destruct (fw_boomerang_total p μ1 nb) as (μ0 & p'' & hsyco & l0 & l1).
         assert (ta ((cooas p (μ1 :: s') hcocnv) ∖ E) (μ1 :: s')
                  ⟶⋍[μ1] ta ((cooas p (μ1 :: s') hcocnv) ∖ E) s')
           as (e' & hle' & heqe')
           by eapply (test_next_step (test_spec := ta_test_spec _)).
         eapply (must_non_blocking_action_swap_l_fw_sync
                   outcome p'' p _ e' μ1 nb l1 hle').
         eapply (must_eq_client _ _ _ (symmetry heqe')).
         edestruct (Hyp p'') as (h & hm).
         { eapply cowt_set_mu_spec2. eapply lts_to_cowt; [exact hsyco | exact l0]. }
         eapply must_ta_monotonicity_sync; [exact hm |].
         eapply difference_mono_r, union_cowt_acceptance_set_subseteq.
         eapply lts_to_cowt; [exact hsyco | exact l0].
      ++ eapply after_blocking_co_of_must_tacc_co; [exact conv | exact b |].
         intros p' w.
         edestruct (Hyp p') as (h & hm).
         { by eapply cowt_set_mu_spec2. }
         eapply must_ta_monotonicity_sync; [exact hm |].
         eapply difference_mono_r, union_cowt_acceptance_set_subseteq, w.
Qed.

(* *** An observer that misses a reachable acceptance set is not passed *)

End AcceptanceSetsSync.

(* ** The acceptance-set half of completeness *)

Section Completeness2_co_sync.

Context {P Q T PreAct Aproc Atest : Type}.
Context `{CC : Countable PreAct}.
Context `{Hp : ExtAction Aproc}.
Context `{Ht : ExtAction Atest}.
Context `{SA : !SyncAction Aproc Atest}.
Context `{gLtsEqP : !gLtsEq P (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))}.
Context `{gLtsEqQ : !gLtsEq Q (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))}.
Context `{gLtsEqT : !gLtsEq T Ht}.
Context `{gLtsObaT : !gLtsOba T}.
Context `{!gLtsObaFB T Atest}.
Context `{!gLtsFWMem P Aproc Atest}.
Context `{!gLtsFWMem Q Aproc Atest}.
Context `{!Prop_of_Inter P T (Aproc + MemAct Atest) Atest sync}.
Context `{!Prop_of_Inter Q T (Aproc + MemAct Atest) Atest sync}.
Context `{CFIP : !coFiniteImagegLts P Atest}.
Context `{CFIQ : !coFiniteImagegLts Q Atest}.
Context {Γ : Atest → PreAct}.
Context `{FiniteAbsP : !FinitaryAbsActionG P T Ht Γ}.
Context `{FiniteAbsQ : !FinitaryAbsActionG Q T Ht Γ}.
Context {outcome : T → Prop}.
Context `{!Testing_Predicate outcome gLtsEqT}.
Context {ta : gset PreAct → list Atest → T}.
Context `{!test_co_acceptance_set_spec PreAct ta Γ}.
Context {tconv : list Atest → T}.
Context `{!test_convergence_spec tconv}.

Lemma completeness2_co_sync (p : P) (q : Q) :
  ctx_pre (gLtsT := gLtsEqT) p q →
  bhv_pre_g_cond2 Γ p q.
Proof.
  intros hpre s q' hacnv w st.
  destruct (must_ta_or_empty_pre_action_set_for_all_trace_co_sync Γ outcome ta s p hacnv (coR_abs q'))
    as [(p' & w_tr & stable & sub) | hm].
  + exists p'. split; [exact w_tr | split; [exact stable |]].
    intros pre mem. eapply coR_abs_spec1, sub, coR_abs_spec2, mem.
  + eapply hpre in hm. contradict hm.
    eapply (not_must_ta_without_required_acc_set_co q q' s); eauto.
Qed.

Lemma completeness_fw_co_sync (p : P) (q : Q) :
  ctx_pre (gLtsT := gLtsEqT) p q →
  p ≼ᴳ[ Γ ] q.
Proof.
  intro hpre. split.
  - by eapply (completeness1_co_sync (tconv := tconv)).
  - by eapply completeness2_co_sync.
Qed.

End Completeness2_co_sync.

(* ** Completeness on forwarders, for two alphabets *)

(* end hide *)
