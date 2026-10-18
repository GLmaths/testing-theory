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
  ParallelLTSConstruction ForwarderConstruction
  Must Lift Subset_Act Convergence Termination
  Testing_Predicate DefinitionAS ActTau Lts_Finite_Non_Blocking_Chain Subset_Act
  coWeakTransition coConvergence coFiniteImage DefinitionASrel LtsFW
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic.

Import ListNotations.
(* * Completeness for the co-acceptance-set preorder *)

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
Class test_co_acceptance_set_spec {PreAct : Type} `{CC : Countable PreAct}
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
                pβ ∈ E -> (∃ β, blocking β /\ Γ β = pβ) ->
                ∃ r β, ta E ε ⟶[β] r /\ (Γ β = pβ);
    (* t3 *) ta_transition_to_good β e' (E : gset PreAct) :
                blocking β -> ta E ε ⟶[β] e' -> outcome e' ;
  }.

#[global] Existing Instance ta_test_spec.

(* *** Facts about test generators *)
Lemma tconv_always_reduces `{
  gLtsOba T Rel , !Testing_Predicate outcome _, !test_convergence_spec tconv} s :
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

Context `{gLtsT : gLtsOba T Rel}.
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

Context `{gLtsT : gLtsOba T Rel}.
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
Context `{gLtsT : gLtsOba T Rel}.
Context `{!Testing_Predicate outcome _}.
Context `{!test_co_acceptance_set_spec (PreAct := PreAct) f Γ}.

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
  gLtsEqT : !@gLtsEq T Atest Ht, gLtsObaT : !gLtsOba T _,
  !Testing_Predicate outcome gLtsEqT,
  !test_co_acceptance_set_spec (PreAct := PreAct) ta Γ,
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

(* ** Completeness for co-acceptance sets *)

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

Section Must_iff_cocnv.

Context `{gLtsEqP : @gLtsEq P A H} `{!LtsFW P A}.
Context `{gLtsObaT : @gLtsOba T A H gLtsEqT}.
Context `{!Testing_Predicate outcome _}.
Context `{!test_convergence_spec tconv}.
Context `{!Prop_of_Inter P T A A dual}.

Lemma must_if_cocnv s (p : P) :
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
  + edestruct tconv_always_reduces. exists (p ∣ x). eapply ParRight; eauto.
  + intros p' l. eapply IHtp; [|eapply cocnv_preserved_by_lts_tau]; eauto.
  + intros e' l.
    destruct (inversion_tconv_tau_action s e' l)
      as [hu | (η & μ1 & s1 & s2 & s3 & eq__s & sc & i0 & i1 & i2 & duo)]; eauto with mdb.
    eapply must_eq_client. symmetry. eassumption.
    subst.
    eapply Hlength.
    * rewrite 6 length_app. simpl. lia.
    * eapply cocnv_annhil; eauto.
  + intros p' e' μ2' μ2 inter hlp hle.
    destruct (inversion_tconv_external_action s μ2 e' hle)
      as [hg | (s1 & s2 & μ2'' & heq & sc & eq & his)]; eauto with mdb.
    subst.
    eapply must_eq_client. symmetry. eassumption.
    eapply Hlength.
    * rewrite length_app. simpl. rewrite length_app. simpl. lia.
    * eapply cocnv_drop_action_in_the_middle; eauto.
Qed.

Lemma must_iff_cocnv (p : P) s : p must_pass (tconv s) <-> p ⇓ᶜᵒ s.
Proof. split; [eapply cocnv_if_must | eapply must_if_cocnv]; eauto. Qed.

End Must_iff_cocnv.

Lemma completeness1_co `{
    gLtsEqP : @gLtsEq P A H, !LtsFW P A,
    gLtsObaT : @gLtsOba T A H gLtsEqT, !Testing_Predicate outcome _,
    ! test_convergence_spec tconv}

    `{!Prop_of_Inter P T A A dual}

  (p q : P) : p ⊑ₘᵤₛₜᵢ q -> p ꜀ₙᵥ≼꜀ₒ₋ₐₛ q.
Proof. intros hleq s hcnv. now eapply must_iff_cocnv, hleq, must_iff_cocnv. Qed.

(* ** Completeness for co-acceptance sets *)

Lemma after_blocking_co_of_must_tacc_co `{CC : Countable PreAct} `{
  gLtsEqP : @gLtsEq P Aproc Hp,
  gLtsEqT : !@gLtsEq T Atest Ht, gLtsObaT : !gLtsOba T _,
  !Testing_Predicate outcome gLtsEqT,
  !test_co_acceptance_set_spec (PreAct := PreAct) ta Γ,
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

Lemma exists_included_or_witnesses `{Countable B} {P : Type}
  (ps : list P) (S : P → subset_of B) (C : subset_of B) :
  (∀ p, p ∈ ps → (S p ⊆ C) + { x | x ∈ S p ∧ x ∉ C }) →
  (∃ p, p ∈ ps ∧ S p ⊆ C)
  ∨ ∃ X : gset B, (∀ x, x ∈ X → x ∉ C) ∧ (∀ p, p ∈ ps → ∃ x, x ∈ X ∧ x ∈ S p).
Proof.
  induction ps as [| p ps IH]; intros h.
  - right. exists ∅. split.
    + intros x hx. set_solver.
    + intros p hp. by apply elem_of_nil in hp.
  - destruct (h p (list_elem_of_here p ps)) as [sub | (x & hx & hnx)].
    + left. exists p. split; [apply list_elem_of_here | exact sub].
    + destruct IH as [(p' & hp' & sub) | (X & hXC & hXS)].
      * intros p' hp'. apply h, list_elem_of_further, hp'.
      * left. exists p'. split; [apply list_elem_of_further, hp' | exact sub].
      * right. exists ({[x]} ∪ X). split.
        -- intros y [->%elem_of_singleton | hy]%elem_of_union; [exact hnx | exact (hXC y hy)].
        -- intros p0 [-> | hp0]%elem_of_cons.
           ++ exists x. split; [set_solver | exact hx].
           ++ destruct (hXS p0 hp0) as (y & hy & hyS).
              exists y. split; [set_solver | exact hyS].
Qed.

Lemma stable_process_must_ta {P : Type} `{
  gLtsEqP : @gLtsEq P Aproc Hp,
  gLtsEqT : !@gLtsEq T Atest Ht, gLtsObaT : !gLtsOba T _,
  SA : !SyncAction Aproc Atest,
  !Testing_Predicate outcome gLtsEqT,
  STS : !ParSts P T _ _, !ParStsSpec P T _ _ SA STS}
  (𝔸 : Label_abstraction P T) `{!test_co_acceptance_set_spec ta ρ[𝔸] }
  (p : P) (X : gset (Atest / 𝔸)) :
  p ↛ → (∃ x, x ∈ X ∧ x ∈ ⌈ ρ[𝔸] ⌉ (coR p)) → p must_pass (ta X ε).
Proof.
  intros hst (a & mem' & co_set).
  apply m_step.
  - apply test_ungood.
  - assert (∃ β, blocking β ∧ ρ[𝔸] β = a) as hb.
    { destruct co_set as (η0 & h0 & e0). exists η0.
      split; [by destruct h0 as (? & ? & ? & ?) | by symmetry]. }
    destruct (ta_has_a_representative_transition_for_its_gamma_set X a mem' hb)
      as (r & η & Tr & eq).
    subst. destruct co_set as (η'' & co_set & eq).
    assert (blocking η) as bη.
    { intro imp. eapply ta_does_no_non_blocking_actions in imp.
      apply imp, (@lts_performs_spec2 T). exists r; exact Tr. }
    assert (acc : ta X ε ⟶[η]) by (apply (@lts_performs_spec2 T); exists r; exact Tr).
    apply (LA_class_proj (label_ker 𝔸)) in eq.
    apply rel_ker_sub in eq as (η' & hu & hu''); [| intros μ; exists μ; split; reflexivity].
    pose proof (coR_reverse_inclusion η' η'' hu'' p co_set) as Tr'.
    pose proof (Ready_set_inclusion η η' hu _ acc) as Tr''.
    eapply lts_performs_spec1 in Tr'' as (e'' & Tr'').
    destruct Tr' as (μ''' & Tr' & duo & bη').
    eapply lts_performs_spec1 in Tr' as (p'' & Tr').
    exists (p'', e''). eapply par_step_sync; [exact duo | exact Tr' | exact Tr''].
  - intros p' l'. exfalso. generalize (lts_performs_spec2 p _ (exist _ p' l')). eauto with mdb.
  - intros e' l'. exfalso.
    eapply (ta_does_no_tau X). eapply lts_performs_spec2. exists e'. exact l'.
  - intros p'' e'' μ' η hsy l'1 l'0.
    destruct (decide (non_blocking η)) as [nb' | not_nb'].
    + exfalso. eapply ta_does_no_non_blocking_actions, (@lts_performs_spec2 T); eauto with mdb.
    + apply m_now. eapply ta_transition_to_good; eauto.
Qed.

Section Must_ta.

Context {P : Type}.
Context `{gLtsEqP : @gLtsEq P A H} `{!LtsFW P A}.
Context `{gLtsObaT : @gLtsOba T A H gLtsEqT}.
Context `{!Prop_of_Inter P T A A dual}.
Context (𝔸 : Label_abstraction P T).
Context `{!Testing_Predicate outcome _}.
Context `{!test_co_acceptance_set_spec ta ρ[𝔸] }.

Lemma must_ta_for_empty_trace (p : P) (X : gset (A / 𝔸)) :
  p ⤓ →
  (∀ p', p ⟹ p' → p' ↛ → ∃ x, x ∈ X ∧ x ∈ ⌈ ρ[𝔸] ⌉ (coR p')) →
  p must_pass (ta X ε).
Proof.
  intros ht. induction ht as [p hpt IH]. intros hX.
  destruct (decide (p ⟶)) as [(p'' & l)%lts_performs_spec1 | st].
  - eapply m_step.
    + eapply test_ungood.
    + exists (p'' ∣ ta X ε). eapply ParLeft; eauto.
    + intros p0 l0. eapply IH; [exact l0 |].
      intros p' w st'. eapply hX; [| exact st']. eauto with mdb.
    + intros e' l'. exfalso.
      eapply ta_does_no_tau, (@lts_performs_spec2 T); eauto.
    + intros p0 e0 μ' μ inter lp le.
      destruct (decide (non_blocking μ)) as [nb | not_nb].
      * exfalso.
        assert ({q' : T | ta X ε ⟶[μ] q'}) by eauto.
        eapply ta_does_no_non_blocking_actions, (@lts_performs_spec2 T); eauto.
      * eapply m_now. eapply ta_transition_to_good; eauto.
  - eapply (stable_process_must_ta 𝔸); [exact st |].
    eapply hX; [constructor | exact st].
Qed.

Lemma must_ta_for_all_trace_co s (p : P) (hcocnv : p ⇓ᶜᵒ s) (X : gset (A / 𝔸)) :
  (∀ p', p ⟹ᶜᵒ[s] p' → p' ↛ → ∃ x, x ∈ X ∧ x ∈ ⌈ ρ[𝔸] ⌉ (coR p')) →
  p must_pass (ta X s).
Proof.
  revert p hcocnv.
  induction s as [| μ s' IHs'].
  - intros p hcocnv hX.
    eapply must_ta_for_empty_trace; [exact (cocnv_terminate p ε hcocnv) |].
    intros p' w st. eapply hX; [eapply cowt_iff_wt_nil; exact w | exact st].
  - intros p hcocnv hX.
    inversion hcocnv as [| ? ? ? conv Hyp_conv]; subst.
    destruct (decide (non_blocking μ)) as [nb | b].
    + destruct (lfw_boomerang p μ nb) as (p' & l0 & l1).
      assert (w0 : p ⟹ᶜᵒ{μ} p') by (eapply lts_to_cowt; [exact (co_dual μ) | exact l0]).
      assert (ta X (μ :: s') ⟶⋍[μ] ta X s') as (e' & hle' & heqe') by eapply test_next_step.
      eapply must_non_blocking_action_swap_l_fw; eauto.
      eapply (must_eq_client _ _ _ (symmetry heqe')).
      eapply IHs'; [exact (Hyp_conv p' w0) |].
      intros p'' w st. eapply hX; [eapply cowt_push_left; eauto | exact st].
    + eapply after_blocking_co_of_must_tacc_co; eauto.
      intros p' w. eapply IHs'; [exact (Hyp_conv p' w) |].
      intros p'' w' st. eapply hX; [eapply cowt_push_left; eauto | exact st].
Qed.

End Must_ta.

Lemma not_must_ta_without_required_acc_set {Q : Type} `{CC : Countable PreAct} `{
  gLtsQ : @gLts Q Aproc Hp,
  gLtsEqT : !@gLtsEq T A H, gLtsObaT : !gLtsOba T _,
  SA : !SyncAction Aproc A,
  !Testing_Predicate outcome _} {Γ : A → PreAct} `{
  !test_co_acceptance_set_spec ta Γ,
  STS : !ParSts Q T gLtsQ gLtsEqT, !ParStsSpec Q T gLtsQ gLtsEqT SA STS}
  (q q' : Q) s (X : gset PreAct) :
  q ⟹ᶜᵒ[s] q' → q' ↛ → (∀ x, x ∈ X → x ∉ ⌈ Γ ⌉ (coR q')) →
  ¬ q must_pass (ta X s).
Proof.
  intros wt hst.
  dependent induction wt; intros hX hm.
  - inversion hm as [happy |]; subst.
    ++ contradict happy. apply test_ungood.
    ++ destruct ex as (y & l). pose proof (par_view_of _ _ _ l) as hv. inversion hv; subst.
       +++ apply hst, (lts_performs_spec2 p τ); eauto with mdb.
       +++ eapply ta_does_no_tau, (@lts_performs_spec2 T); [eauto.. | by eexists].
       +++ destruct (decide (non_blocking η)) as [nb | not_nb].
           ++++ exfalso. eapply ta_does_no_non_blocking_actions, (@lts_performs_spec2 T); [eauto.. | by eexists].
           ++++ eapply ta_actions_are_in_its_gamma_set in l2 as mem; [| exact not_nb].
                apply (hX _ mem), (map_gamma_of_action Γ).
                eapply coR_intro;
                  [eapply lts_performs_spec2; by eexists | exact hs | exact not_nb].
  - eapply (IHwt hst hX).
    by eapply must_preserved_by_lts_tau_srv.
  - assert (ta X (μ :: s) ⟶⋍[μ] ta X s)
      as (e' & hle' & heqe') by eapply (test_next_step (test_spec := ta_test_spec _)).
    eapply (IHwt hst hX).
    eapply must_eq_client; [exact heqe' |].
    eapply must_preserved_by_synch_if_notoutcome;
      [exact hm | apply test_ungood | exact duo | exact l | exact hle'].
Qed.

Section Completeness2_co.

Context {P : Type}.
Context `{gLtsEqP : @gLtsEq P A H} `{!LtsFW P A}.
Context `{gLtsObaT : @gLtsOba T A H gLtsEqT}.
Context `{!coFiniteImagegLts P A}.
Context `{!Prop_of_Inter P T A A dual}.
Context (𝔸 : Label_abstraction P T).
Context `{DichP : !Dichotomic P ρ[𝔸] }.
Context `{!Testing_Predicate outcome _}.
Context `{!test_co_acceptance_set_spec ta ρ[𝔸] }.
Context `{!test_convergence_spec tconv}.

Lemma completeness2_co (p q : P) : p ⊑ₘᵤₛₜᵢ q → p ₐ꜀꜀≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] q.
Proof.
  intros hpre s q' hacnv w st.
  destruct (exists_included_or_witnesses (elements (cowaiting_states p s hacnv))
              (λ p', ⌈ ρ[𝔸] ⌉ (coR p')) (⌈ ρ[𝔸] ⌉ (coR q')))
    as [(p' & mem & sub) | (X & hXC & hXS)].
  - intros p' (_ & st')%elem_of_elements%cowaiting_states_spec1. exact (coR_dichotomy p' q' st' st).
  - apply elem_of_elements, cowaiting_states_spec1 in mem as (w' & st').
    exists p'. split_and!; [exact w' | exact st' | exact sub].
  - exfalso. eapply (not_must_ta_without_required_acc_set q q' s X w st hXC).
    eapply hpre, (must_ta_for_all_trace_co 𝔸 s p hacnv X).
    intros p' w' st'. eapply hXS, elem_of_elements, cowaiting_states_spec2. split; [exact w' | exact st'].
Qed.

Lemma completeness_fw_co (p q : P) : p ⊑ₘᵤₛₜᵢ q → p ≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] q.
Proof.
  intros. split.
  - now apply completeness1_co.
  - now apply completeness2_co.
Qed.

End Completeness2_co.
