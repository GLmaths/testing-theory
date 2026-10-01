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

(** * Completeness for two alphabets: the convergence condition

    The port of the first half of [CompletenessASco.v] — everything that leads
    to [completeness1_co] — to processes over [Aproc] tested by observers over
    [Atest].

    The lemmas of [CompletenessASco.v] about the observers alone
    ([tconv_always_reduces], the [inversion_test_*] and [inversion_tconv_*]
    family) are reused unchanged: they only ever mention the test LTS and its
    own [dual], so they hold over [Atest] as they stand.  Only the lemmas that
    relate a process to an observer had to be ported, and they are below. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Wf Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.
From stdpp Require Import base countable decidable finite gmap list.
From TestingTheory Require Import ActTau gLts SyncActions UnionAction UnionSync SyncForwarder Bisimulation Lts_OBA
  Lts_OBA_FB Lts_FW Subset_Act Termination WeakTransitions
  coWeakSync
  FiniteImageLTS coFiniteImage Testing_Predicate InteractionBetweenLts
  Must Completeness CompletenessASco DefinitionAS DefinitionASco
  coWeakTransition coConvergence.

(** ** Swapping a non-blocking action across the composition, on forwarders

    [Lift.must_non_blocking_action_swap_l_fw] for two alphabets.  In the
    homogeneous statement the process and the observer perform the /same/
    non-blocking action [η]; here the observer performs [ν] over [Atest] and
    the forwarder gives the same message back as [inr ν]. *)

Section SwapSync.

Context {P T Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{FS : !FwSync Aproc Atest}.
Context `{gLtsEqP : !gLtsEq P ExtAction_fw} `{gLtsObaP : !gLtsOba P}.
Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T} `{!gLtsObaFB T Atest}.
Context (outcome : T → Prop) `{!Testing_Predicate outcome gLtsEqT}.
Context `{!gLtsObaFWSync P Aproc Atest} `{!Prop_of_Inter P T (Aproc + Atest) Atest sync}.

Lemma must_non_blocking_action_swap_l_fw_sync_eq
  (p1 p2 : P) (e1 e2 : T) (ν : Atest) :
  non_blocking ν →
  p1 ⟶⋍[inr ν] p2 → e1 ⟶⋍[ν] e2 → p1 must_pass e2 → p2 must_pass e1.
Proof.
  intros nbν lp le hm.
  destruct (inr_spec ν nbν) as (nbγ & hiff & hdν).
  set (γ := inr ν) in *.
  destruct (fsync_total ν nbν) as (μ0 & hμ0).
  assert (hsyco : sync (inl μ0 : Aproc + Atest) ν) by exact hμ0.
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
    + (* [fw_boomerang]: [p2] can take back what [p1] has emitted, as the
         process reception [inl μ0], which synchronises with [ν] *)
      destruct (fw_boomerang p2 ν μ0 nbν hμ0) as (p'2 & Tr1 & Tr2).
      destruct le as (e'1 & Tr & eq).
      exists (p'2, e'1). eapply TauSync; [exact hsyco | exact Tr1 | exact Tr].
    + intros p' l.
      destruct lp as (p0 & hlp0 & heqp0).
      edestruct (eq_spec p0 p' τ) as (p3 & hlp3 & heqp3).
      { exists p2. split; [by symmetry | exact l]. }
      destruct (nb_delay nbγ hlp0 hlp3) as (t & l1 & (p4 & hlp4 & heqp4)).
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
         (* [inr_spec]'s third clause: a dual of [ν] on the observer side
            is answered by [γ] itself *)
         by apply hdν.
    + intros p' e' μ1 μ2 hsy2 l1 l2.
      destruct lp as (p0 & hlp0 & heqp0).
      destruct le as (e0 & hle0 & heqe0).
      destruct (decide (μ2 = ν)) as [-> | n]; simpl in l2.
      ++ edestruct (eq_spec p0 p' (ActExt μ1)) as (p3 & hlp3 & heqp3).
         { exists p2. split; [by symmetry | exact l1]. }
         assert (heqe' : e0 ⋍ e')
           by (eapply nb_determinacy; [exact nbν | exact hle0 | exact l2]).
         destruct (sync_fwd_feedback ν μ1 nbν hsy2 hlp0 hlp3) as [(p3' & hlp3' & heqp3') |].
         +++ eapply must_eq_client; [etrans; [by symmetry; exact heqe0 | exact heqe'] |].
             eapply must_eq_server; [etrans; [exact heqp3' | exact heqp3] |].
             by apply Hpt.
         +++ eapply must_eq_client; [etrans; [by symmetry; exact heqe0 | exact heqe'] |].
             eapply must_eq_server; [etrans; [exact H | exact heqp3] |].
             apply m_step; assumption.
      ++ destruct (nb_confluence nbν n hle0 l2) as (t & l3 & (e4 & hle4 & heqe4)).
         edestruct (eq_spec p0 p' (ActExt μ1)) as (p3 & hlp3 & heqp3).
         { exists p2. split; [by symmetry | exact l1]. }
         destruct (nb_delay nbγ hlp0 hlp3) as (r & l5 & (p4 & hlp4 & heqp4)).
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
  (p1 p2 : P) (e1 e2 : T) (ν : Atest) :
  non_blocking ν →
  p1 ⟶[inr ν] p2 → e1 ⟶[ν] e2 → p1 must_pass e2 → p2 must_pass e1.
Proof.
  intros. eapply must_non_blocking_action_swap_l_fw_sync_eq;
    eauto; eexists; split; eauto; reflexivity.
Qed.

End SwapSync.

(** ** A single co-step against the convergence observer *)

(* the trace is kept as a variable, constrained by an equation, so that plain
   induction applies *)
(** ** The observer of convergence characterises co-convergence *)

Lemma must_sync_if_cocnvs `{
  Hp : ExtAction Aproc, Ht : ExtAction Atest, FS : !FwSync Aproc Atest,
  gLtsEqP : @gLtsEq P (Aproc + Atest) ExtAction_fw, gLtsObaP : !gLtsOba P,
  gLtsEqT : !@gLtsEq T Atest Ht, gLtsObaT : !gLtsOba T, !gLtsObaFB T Atest,
  !Testing_Predicate outcome gLtsEqT, !test_convergence_spec tconv,
  !gLtsObaFWSync P Aproc Atest, !Prop_of_Inter P T (Aproc + Atest) Atest sync}
  s (p : P) : p ⇓ᶜᵒ s → p must_pass (tconv s).
Proof.
  revert p.
  induction s as (s & Hlength) using
    (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  intros p hc.
  induction (cocnv_terminate p s hc) as [p hp IHtp].
  apply m_step.
  + apply test_ungood.
  + edestruct tconv_always_reduces as (x & hx). exists (p, x). by apply TauRight.
  + intros p' l. eapply IHtp; [exact l | by eapply cocnv_preserved_by_lts_tau].
  + intros e' l.
    destruct (inversion_tconv_tau_action s e' l)
      as [hu | (η & ν & s1 & s2 & s3 & eqs & sc & i0 & i1 & i2 & duo)];
      [by apply m_now |].
    eapply must_eq_client; [by symmetry |].
    subst. eapply Hlength.
    * rewrite 6 length_app. simpl. lia.
    * by eapply cocnv_annhil_fw.
  + intros p' e' μ ν hsy hlp hle.
    destruct (inversion_tconv_external_action s ν e' hle)
      as [hg | (s1 & s2 & ν'' & heq & sc & eq & his)]; [by apply m_now |].
    subst.
    eapply must_eq_client; [by symmetry |].
    eapply Hlength.
    * rewrite length_app. simpl. rewrite length_app. simpl. lia.
    * by eapply cocnv_drop_action_in_the_middle_fw.
Qed.

Lemma must_sync_iff_cocnvs `{
  Hp : ExtAction Aproc, Ht : ExtAction Atest, FS : !FwSync Aproc Atest,
  gLtsEqP : @gLtsEq P (Aproc + Atest) ExtAction_fw, gLtsObaP : !gLtsOba P,
  gLtsEqT : !@gLtsEq T Atest Ht, gLtsObaT : !gLtsOba T, !gLtsObaFB T Atest,
  !Testing_Predicate outcome gLtsEqT, !test_convergence_spec tconv,
  !gLtsObaFWSync P Aproc Atest, !Prop_of_Inter P T (Aproc + Atest) Atest sync}
  (p : P) s : p must_pass (tconv s) ↔ p ⇓ᶜᵒ s.
Proof.
  split; [by apply cocnv_if_must | by apply must_sync_if_cocnvs].
Qed.

(** ** The convergence half of completeness *)

Lemma completeness1_co_sync `{
  Hp : ExtAction Aproc, Ht : ExtAction Atest, FS : !FwSync Aproc Atest,
  gLtsEqP : @gLtsEq P (Aproc + Atest) ExtAction_fw, gLtsObaP : !gLtsOba P,
  gLtsEqQ : !@gLtsEq Q (Aproc + Atest) ExtAction_fw, gLtsObaQ : !gLtsOba Q,
  gLtsEqT : !@gLtsEq T Atest Ht, gLtsObaT : !gLtsOba T, !gLtsObaFB T Atest,
  !Testing_Predicate outcome gLtsEqT, !test_convergence_spec tconv,
  !gLtsObaFWSync P Aproc Atest, !gLtsObaFWSync Q Aproc Atest,
  !Prop_of_Inter P T (Aproc + Atest) Atest sync, !Prop_of_Inter Q T (Aproc + Atest) Atest sync}
  (p : P) (q : Q) :
  p ⊆ₘᵤₛₜᵢ q → p ₁≼꜀ₒ₋ₐₛ q.
Proof.
  intros hleq s hc.
  by eapply must_sync_iff_cocnvs, hleq, must_sync_iff_cocnvs.
Qed.

(** ** Completeness, the acceptance-set half

    The port of the second half of [CompletenessASco.v].  The observer is now
    [ta E s] with [s : trace Atest] and [E : gset PreAct]; the co-actions it has
    to offer are read off [coR p], a set of /test/ actions. *)

(** *** Prefixing the observer with a blocking action *)

(** *** Monotonicity in the acceptance set, for the empty trace

    The interesting case is the synchronisation one: the observer [ta E1 ε] had
    a blocking action [η] matching an action of [p]; the bigger observer
    [ta E2 ε] has a representative [η'] of the same abstraction, and
    [abstraction_prog_spec] turns it back into an action [η''] of
    [coR p]. *)

(** *** Monotonicity in the acceptance set, for an arbitrary trace

    [inversion_ta_tau_action], [inversion_ta_external_action], [ta_tau_ex] and
    [f_gen_lts_mu_in_the_middle] are the observer-only lemmas of
    [CompletenessASco.v], reused here over [Atest].  The one step that changes
    is the synchronisation witness: where the homogeneous proof made [p] accept
    [co ν] for the non-blocking [ν] of the trace, here [fsync_total] picks a
    process reception [μ] answering [ν], and [fw_boomerang] makes [p] accept
    [inl μ]. *)

Lemma must_ta_monotonicity_sync {P : Type} `{CC : Countable PreAct} `{
  Hp : ExtAction Aproc, Ht : ExtAction Atest, FS : !FwSync Aproc Atest,
  gLtsEqP : @gLtsEq P (Aproc + Atest) ExtAction_fw, gLtsObaP : !gLtsOba P,
  gLtsEqT : !@gLtsEq T Atest Ht, gLtsObaT : !gLtsOba T, !gLtsObaFB T Atest,
  !gLtsObaFWSync P Aproc Atest,
  AbsPT : !@AbsAction P T FinA PreAct Atest Ht Φ 𝝳 (Aproc + Atest) ExtAction_fw _ _ SyncAction_fw,
  !Testing_Predicate outcome gLtsEqT,
  !test_co_acceptance_set_spec PreAct ta (fun x => (𝝳 (Φ x))),
  !Prop_of_Inter P T (Aproc + Atest) Atest sync}
  s (p : P) E1 :
  p must_pass (ta E1 s) → ∀ E2, E1 ⊆ E2 → p must_pass (ta E2 s).
Proof.
  revert p E1.
  induction s as (s & Hlength) using
    (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [| ν s']; intros p E1 hm E2 hsub.
  - eapply must_ta_monotonicity_nil; eauto.
  - assert (htp : p ⤓) by (eapply must_terminate_unoutcome, test_ungood; eauto).
    induction htp.
    inversion hm as [hg | nh ex pt et com].
    * exfalso. by eapply (test_ungood (test_spec := ta_test_spec E1) (ν :: s')).
    * apply m_step.
      + apply test_ungood.
      + destruct (decide (non_blocking ν)) as [nb | not_nb].
        (* [fw_boomerang]: the forwarder receives [ν] as a process action *)
        ++ destruct (fw_boomerang_total p ν nb) as (μ0 & p' & hsyco & tr_b & _).
           assert (ta E2 (ν :: s') ⟶⋍[ν] ta E2 s') as (t' & tr' & eq')
             by eapply (test_next_step (test_spec := ta_test_spec E2)).
           exists (p', t'). eapply TauSync; [exact hsyco | exact tr_b | exact tr'].
        ++ assert (∃ e', ta E2 (ν :: s') ⟶ e') as (e' & tr')
             by (eapply (test_tau_transition (test_spec := ta_test_spec E2)); eauto).
           exists (p, e'). by eapply TauRight.
      + intros p' l. eapply H0; eauto.
      + intros e' l.
        edestruct (inversion_ta_tau_action (ν :: s') E2 e' l) as [hg | Hyp];
          [by apply m_now |].
        destruct Hyp as (η & μ & s1 & s2 & s3 & heqs & sc & himu & his1 & his2 & duo).
        eapply (must_eq_client p (ta E2 (s1 ++ s2 ++ s3))); [by symmetry |].
        edestruct (ta_tau_ex s1 s2 s3 η μ E1) as (t & hlt & heqt); eauto.
        eapply Hlength.
        ++ rewrite heqs, 6 length_app. simpl. lia.
        ++ eapply must_eq_client; [eapply heqt |]. eapply et. by rewrite heqs.
        ++ exact hsub.
      + intros p' e' μ η hsy l1 l2.
        edestruct (inversion_ta_external_action (ν :: s') η e' E2) as [hg | Hyp];
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

(** *** A stable process passes the observer of its own co-actions

    Unless that set is already contained in [E]: the observer [ta (coR_abs p ∖ E) ε]
    offers a representative of every abstract co-action of [p] that [E] misses,
    so the composition can always take a synchronisation step. *)

(** *** A blocking co-step of the process, in one go *)

(** ** The acceptance sets along a co-trace

    From here on the binders are collected in a section: every lemma needs the
    same long list, and naming the instances is also what keeps elaboration
    from searching for [FinitaryAbsActionSync] with [T] and [FinA] unknown —
    hence the [coRa] abbreviation below. *)

Section AcceptanceSetsSync.

Context {P T FinA PreAct Aproc Atest : Type}.
Context `{CC : Countable PreAct}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{FS : !FwSync Aproc Atest}.
Context `{gLtsEqP : !gLtsEq P ExtAction_fw} `{gLtsObaP : !gLtsOba P}.
Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T} `{!gLtsObaFB T Atest}.
Context `{!gLtsObaFWSync P Aproc Atest} `{!Prop_of_Inter P T (Aproc + Atest) Atest sync}.
Context `{CFI : !coFiniteImagegLts P Atest}.
Context (Φ : Atest → FinA) (𝝳 : FinA → PreAct).
Context `{FiniteAbs : !FinitaryAbsAction P T Atest Ht Φ 𝝳}.
Context (outcome : T → Prop) `{!Testing_Predicate outcome gLtsEqT}.
Context (ta : gset PreAct → list Atest → T)
        `{!test_co_acceptance_set_spec PreAct ta (fun x => 𝝳 (Φ x))}.

Notation coRa := (coR_abs (FinitaryAbsAction := FiniteAbs)).

(** *** Monotonicity of the stable states reached along a co-trace *)

(** *** The union of the acceptance sets reachable along a co-trace *)

(** *** Either some stable state of [p] is covered by [E], or [p] passes the
    observer of what [E] misses — first for the empty co-trace *)

Lemma must_ta_or_empty_pre_action_set_for_empty_trace_co_sync
  (p : P) (hcocnv : p ⇓ᶜᵒ ε) (E : gset PreAct) :
  (∃ p', p ⟹ p' ∧ lts_refuses p' τ ∧ coRa p' ⊆ E)
  ∨ p must_pass (ta ((cooas p ε hcocnv) ∖ E) ε).
Proof.
  induction (cocnv_terminate p ε hcocnv) as (p, hpt, ihhp).
  destruct (decide (lts_refuses p τ)) as [st | (p'' & l)%lts_refuses_spec1].
  + destruct (stable_process_must_ta_or_empty_pre_action_set p E st) as [Hyp | Hyp].
    ++ right. assert (cooas p ε hcocnv = coRa p) as eq.
       { unfold cooas.
         rewrite cowt_refuses_set_refuses_singleton, elements_singleton; [| exact st].
         simpl. by rewrite union_empty_r_L. }
       rewrite eq. exact Hyp.
    ++ left. exists p. split; [constructor | split; [exact st | exact Hyp]].
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
      * exists (p'', ta ((cooas p ε hcocnv) ∖ E) ε). by eapply TauLeft.
      * intros p0 l0.
        assert (m0 : p0 ∈ cowt_tau_set p) by by eapply cowt_tau_set_spec.
        eapply Forall_forall in Hyp' as (h0 & hm); [| exact m0].
        eapply must_ta_monotonicity_sync; [exact hm |].
        eapply difference_mono_r, union_acceptance_set_lts_tau_cowt_subseteq, l0.
      * intros e' l'. exfalso.
        eapply (@lts_refuses_spec2 T); [by exists e' | eapply ta_does_no_tau; eauto].
      * intros p0 e0 μ' η hsy lp le.
        destruct (decide (non_blocking η)) as [nb | not_nb].
        ++ exfalso.
           eapply (@lts_refuses_spec2 T); [by exists e0 |].
           eapply ta_does_no_non_blocking_actions; eauto.
        ++ apply m_now. eapply ta_transition_to_good; eauto.
Qed.

(** *** ... and then for an arbitrary co-trace

    The non-blocking case is the one that changes: [fw_boomerang] makes [p]
    receive the trace's [ν] and give it back as [inr ν], and
    [must_non_blocking_action_swap_l_fw_sync] moves it from the process side
    to [ν] on the observer side. *)

Lemma must_ta_or_empty_pre_action_set_for_all_trace_co_sync
  s (p : P) (hcocnv : p ⇓ᶜᵒ s) (E : gset PreAct) :
  (∃ p', p ⟹ᶜᵒ[s] p' ∧ lts_refuses p' τ ∧ coRa p' ⊆ E)
  ∨ p must_pass (ta ((cooas p s hcocnv) ∖ E) s).
Proof.
  revert p hcocnv E.
  induction s as [| ν s' IHs'].
  - intros p hcocnv E.
    destruct (must_ta_or_empty_pre_action_set_for_empty_trace_co_sync p hcocnv E)
      as [(p' & w & st & sub) | hm].
    + left. exists p'. split; [by eapply cowt_iff_wt_nil | by split].
    + right. exact hm.
  - intros p hcocnv E.
    set (ps := cowt_set_mu p ν s' hcocnv).
    inversion hcocnv as [| ? ? ? conv Hyp_conv]; subst.
    assert (hcocnv0 : ∀ p', p' ∈ ps → p' ⇓ᶜᵒ s')
      by (intros ? mem%cowt_set_mu_spec1; eauto).
    assert (he : ∀ p', p' ∈ ps →
      ((∃ pr p0, p0 ∈ cowt_refuses_set p' s' pr ∧ coRa p0 ⊆ E)
        ∨ (∃ h, p' must_pass (ta ((cooas p' s' h) ∖ E) s')))).
    { intros p' mem. destruct (IHs' p' (hcocnv0 _ mem) E) as [(r & w & st & sub) | hm].
      * left. eapply cowt_set_mu_spec1 in mem.
        exists (Hyp_conv _ mem), r. split; [eapply cowt_refuses_set_spec2 |]; eauto.
      * right. eauto. }
    destruct (exists_forall_in_gset ps _ _ he) as [Hyp | Hyp].
    + left. destruct Hyp
        as (p1 & ?%cowt_set_mu_spec1 & ? & r & (? & ?)%cowt_refuses_set_spec1 & ?).
      exists r. split; [by eapply cowt_push_left | by split].
    + right.
      destruct (decide (non_blocking ν)) as [nb | b].
      ++ destruct (fw_boomerang_total p ν nb) as (μ0 & p'' & hsyco & l0 & l1).
         assert (ta ((cooas p (ν :: s') hcocnv) ∖ E) (ν :: s')
                  ⟶⋍[ν] ta ((cooas p (ν :: s') hcocnv) ∖ E) s')
           as (e' & hle' & heqe')
           by eapply (test_next_step (test_spec := ta_test_spec _)).
         eapply (must_non_blocking_action_swap_l_fw_sync
                   outcome p'' p _ e' ν nb l1 hle').
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

(** *** An observer that misses a reachable acceptance set is not passed *)

End AcceptanceSetsSync.

(** ** The acceptance-set half of completeness *)

Lemma completeness2_co_sync {P Q T FinA PreAct Aproc Atest : Type}
  `{CC : Countable PreAct}
  `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{FS : !FwSync Aproc Atest}
  `{gLtsEqP : !gLtsEq P ExtAction_fw} `{gLtsObaP : !gLtsOba P}
  `{gLtsEqQ : !gLtsEq Q ExtAction_fw} `{gLtsObaQ : !gLtsOba Q}
  `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T} `{!gLtsObaFB T Atest}
  
  `{!gLtsObaFWSync P Aproc Atest, !gLtsObaFWSync Q Aproc Atest, !Prop_of_Inter P T (Aproc + Atest) Atest sync} `{!Prop_of_Inter Q T (Aproc + Atest) Atest sync}
  `{CFIP : !coFiniteImagegLts P Atest}
  `{CFIQ : !coFiniteImagegLts Q Atest}
  {Φ : Atest → FinA} {𝝳 : FinA → PreAct}
  `{FiniteAbsP : !FinitaryAbsAction P T Atest Ht Φ 𝝳}
  `{FiniteAbsQ : !FinitaryAbsAction Q T Atest Ht Φ 𝝳}
  {outcome : T → Prop} `{!Testing_Predicate outcome gLtsEqT}
  {ta : gset PreAct → list Atest → T}
  `{!test_co_acceptance_set_spec PreAct ta (fun x => 𝝳 (Φ x))}
  (p : P) (q : Q) :
  p ⊆ₘᵤₛₜᵢ q →
  p ₂≼꜀ₒ₋ₐₛ q.
Proof.
  intros hpre s q' hacnv w st.
  destruct (must_ta_or_empty_pre_action_set_for_all_trace_co_sync Φ 𝝳 outcome ta s p hacnv (coR_abs q'))
    as [(p' & w_tr & stable & sub) | hm].
  + exists p'. split; [exact w_tr | split; [exact stable |]].
    intros pre mem. eapply coR_abs_spec1, sub, coR_abs_spec2, mem.
  + eapply hpre in hm. contradict hm.
    eapply (not_must_ta_without_required_acc_set_co q q' s); eauto.
Qed.

(** ** Completeness on forwarders, for two alphabets *)

Lemma completeness_fw_co_sync {P Q T FinA PreAct Aproc Atest : Type}
  `{CC : Countable PreAct}
  `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{FS : !FwSync Aproc Atest}
  `{gLtsEqP : !gLtsEq P ExtAction_fw} `{gLtsObaP : !gLtsOba P}
  `{gLtsEqQ : !gLtsEq Q ExtAction_fw} `{gLtsObaQ : !gLtsOba Q}
  `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T} `{!gLtsObaFB T Atest}
  
  `{!gLtsObaFWSync P Aproc Atest, !gLtsObaFWSync Q Aproc Atest, !Prop_of_Inter P T (Aproc + Atest) Atest sync} `{!Prop_of_Inter Q T (Aproc + Atest) Atest sync}
  `{CFIP : !coFiniteImagegLts P Atest}
  `{CFIQ : !coFiniteImagegLts Q Atest}
  {Φ : Atest → FinA} {𝝳 : FinA → PreAct}
  `{FiniteAbsP : !FinitaryAbsAction P T Atest Ht Φ 𝝳}
  `{FiniteAbsQ : !FinitaryAbsAction Q T Atest Ht Φ 𝝳}
  {outcome : T → Prop} `{!Testing_Predicate outcome gLtsEqT}
  {tconv : list Atest → T} `{!test_convergence_spec tconv}
  {ta : gset PreAct → list Atest → T}
  `{!test_co_acceptance_set_spec PreAct ta (fun x => 𝝳 (Φ x))}
  (p : P) (q : Q) :
  p ⊆ₘᵤₛₜᵢ q →
  p ≼꜀ₒ₋ₐₛ q.
Proof.
  intro hpre. split.
  - by eapply (completeness1_co_sync (tconv := tconv)).
  - by eapply (completeness2_co_sync (ta := ta)).
Qed.
