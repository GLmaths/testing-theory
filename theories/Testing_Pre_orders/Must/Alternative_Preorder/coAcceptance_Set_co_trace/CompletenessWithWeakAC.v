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

From stdpp Require Import sets base countable finite gmap list decidable.
From TestingTheory Require Import ActTau SyncActions gLts Bisimulation Lts_OBA
  WeakTransitions Lts_OBA_FB Lts_FW FiniteImageLTS
  InteractionBetweenLts ParallelLTSConstruction
  Must Lift Subset_Act Termination
  Testing_Predicate DefinitionAS
  coWeakTransition coConvergence coFiniteImage DefinitionASco CompletenessASco.

Import ListNotations.
(* begin hide *)

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

Lemma stable_process_must_ta_weak {P : Type}
  `{CC : Countable PreAct} `{
  gLtsEqP : @gLtsEq P Aproc Hp,
  gLtsEqT : !@gLtsEq T Atest Ht, gLtsObaT : !gLtsOba T,
  SA : !SyncAction Aproc Atest,
  AbsPT : !@AbsAction P T FinA PreAct Atest Ht αᴛᴇꜱᴛ αᴘʀᴏ Aproc Hp _ _ SA,
  !Testing_Predicate outcome gLtsEqT,
  !test_co_acceptance_set_spec PreAct ta (fun x => (αᴘʀᴏ (αᴛᴇꜱᴛ x))),
  STS : !ParSts P T _ _, !ParStsSpec P T _ _ SA STS}
  (p : P) (X : gset PreAct) :
  p ↛ → (∃ x, x ∈ X ∧ x ∈ ⌈ αᴘʀᴏ ∘ αᴛᴇꜱᴛ ⌉ (coR p)) → p must_pass (ta X ε).
Proof.
  intros hst (a & mem' & co_set).
  apply m_step.
  - apply test_ungood.
  - eapply ta_has_a_representative_transition_for_its_gamma_set in mem'
      as (r & η & Tr & eq).
    subst. destruct co_set as (η'' & co_set & eq).
    assert (blocking η) as bη.
    { intro imp. eapply ta_does_no_non_blocking_actions in imp.
      apply imp, (@lts_performs_spec2 T). exists r; exact Tr. }
    assert ((αᴛᴇꜱᴛ η) ∈ ⌈ αᴛᴇꜱᴛ ⌉ (coR p)) as mem.
    { symmetry in eq.
      eapply (abstraction_prog_spec (AbsAction := AbsPT) p η'' η); eauto.
      - by destruct co_set as (? & ? & ? & ?).
      - eapply map_gamma_of_action. exact co_set. }
    destruct mem as (η' & Tr' & eq').
    assert (Tr'' : (ta X ε) ⟶[η']).
    { eapply (abstraction_test_spec (AbsAction := AbsPT) (ta X ε) η η' bη).
      - by destruct Tr' as (? & ? & ? & ?).
      - exact eq'.
      - eapply lts_performs_spec2. exists r. exact Tr. }
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

Section Must_ta_weak.

Context {P : Type}.
Context `{CC : Countable PreAct}.
Context `{@gLtsObaFW P A H gLtsEqP gLtsObaP}.
Context `{@gLtsObaFB T A H gLtsEqT gLtsObaT}.
Context `{AbsPT : @AbsAction P T FinA PreAct A H αᴛᴇꜱᴛ αᴘʀᴏ _ _ _ _ _}.
Context `{!Testing_Predicate outcome _}.
Context `{!test_co_acceptance_set_spec PreAct ta (fun x => (αᴘʀᴏ (αᴛᴇꜱᴛ x)))}.
Context `{!Prop_of_Inter P T A A dual}.

Lemma must_ta_weak_for_empty_trace (p : P) (X : gset PreAct) :
  p ⤓ →
  (∀ p', p ⟹ p' → p' ↛ → ∃ x, x ∈ X ∧ x ∈ ⌈ αᴘʀᴏ ∘ αᴛᴇꜱᴛ ⌉ (coR p')) →
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
  - eapply stable_process_must_ta_weak; [exact st |].
    eapply hX; [constructor | exact st].
Qed.

Lemma must_ta_weak_for_all_trace_co s (p : P) (hcocnv : p ⇓ᶜᵒ s) (X : gset PreAct) :
  (∀ p', p ⟹ᶜᵒ[s] p' → p' ↛ → ∃ x, x ∈ X ∧ x ∈ ⌈ αᴘʀᴏ ∘ αᴛᴇꜱᴛ ⌉ (coR p')) →
  p must_pass (ta X s).
Proof.
  revert p hcocnv.
  induction s as [| μ s' IHs'].
  - intros p hcocnv hX.
    eapply must_ta_weak_for_empty_trace; [exact (cocnv_terminate p ε hcocnv) |].
    intros p' w st. eapply hX; [eapply cowt_iff_wt_nil; exact w | exact st].
  - intros p hcocnv hX.
    inversion hcocnv as [| ? ? ? conv Hyp_conv]; subst.
    destruct (decide (non_blocking μ)) as [nb | b].
    + destruct (boomerang p μ (co μ)) as (p' & Hb).
      destruct (Hb nb (symmetry (proj2_sig (exists_dual μ)))) as (l0 & l1).
      assert (w0 : p ⟹ᶜᵒ{μ} p').
      { eapply lts_to_cowt; [symmetry; exact (proj2_sig (exists_dual μ)) | exact l0]. }
      assert (ta X (μ :: s') ⟶⋍[μ] ta X s') as (e' & hle' & heqe') by eapply test_next_step.
      eapply must_non_blocking_action_swap_l_fw; eauto.
      eapply (must_eq_client _ _ _ (symmetry heqe')).
      eapply IHs'; [exact (Hyp_conv p' w0) |].
      intros p'' w st. eapply hX; [eapply cowt_push_left; eauto | exact st].
    + eapply after_blocking_co_of_must_tacc_co; eauto.
      intros p' w. eapply IHs'; [exact (Hyp_conv p' w) |].
      intros p'' w' st. eapply hX; [eapply cowt_push_left; eauto | exact st].
Qed.

End Must_ta_weak.

Lemma not_must_ta_without_required_acc_set_weak {Q : Type} `{CC : Countable PreAct} `{
  gLtsQ : @gLts Q Aproc Hp,
  gLtsEqT : !@gLtsEq T A H, gLtsObaT : !gLtsOba T, !gLtsObaFB T A,
  SA : !SyncAction Aproc A,
  !Testing_Predicate outcome _} {FinA : Type} {αᴛᴇꜱᴛ : A → FinA} {αᴘʀᴏ : FinA → PreAct} `{
  !test_co_acceptance_set_spec PreAct ta (fun x => (αᴘʀᴏ (αᴛᴇꜱᴛ x))),
  STS : !ParSts Q T gLtsQ gLtsEqT, !ParStsSpec Q T gLtsQ gLtsEqT SA STS}
  (q q' : Q) s (X : gset PreAct) :
  q ⟹ᶜᵒ[s] q' → q' ↛ → (∀ x, x ∈ X → x ∉ ⌈ αᴘʀᴏ ∘ αᴛᴇꜱᴛ ⌉ (coR q')) →
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
                apply (hX _ mem), (map_gamma_of_action (αᴘʀᴏ ∘ αᴛᴇꜱᴛ)).
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

Section Completeness2_co_weak.

Context {P Q : Type}.
Context `{CC : Countable PreAct}.
Context `{@gLtsObaFW P A H gLtsEqP gLtsObaP}.
Context `{@gLtsObaFW Q A H gLtsEqQ gLtsObaQ}.
Context `{@gLtsObaFB T A H gLtsEqT gLtsObaT}.
Context `{!coFiniteImagegLts P A}.
Context `{AbsPT : @AbsAction P T FinA PreAct A H αᴛᴇꜱᴛ αᴘʀᴏ _ _ _ _ _}.
Context `{AbsQT : @AbsAction Q T FinA PreAct A H αᴛᴇꜱᴛ αᴘʀᴏ _ _ _ _ _}.
Context `{!Testing_Predicate outcome _}.
Context `{!test_co_acceptance_set_spec PreAct ta (fun x => (αᴘʀᴏ (αᴛᴇꜱᴛ x)))}.
Context `{!Prop_of_Inter P T A A dual}.
Context `{!Prop_of_Inter Q T A A dual}.
Context `{!coFiniteImagegLts Q A}.
Context `{!test_convergence_spec tconv}.

Lemma completeness2_co_weak (dich : ∀ (p' : P) (q' : Q), p' ↛ → q' ↛ → (⌈ αᴘʀᴏ ∘ αᴛᴇꜱᴛ ⌉ (coR p') ⊆ ⌈ αᴘʀᴏ ∘ αᴛᴇꜱᴛ ⌉ (coR q')) + { x | x ∈ ⌈ αᴘʀᴏ ∘ αᴛᴇꜱᴛ ⌉ (coR p') ∧ x ∉ ⌈ αᴘʀᴏ ∘ αᴛᴇꜱᴛ ⌉ (coR q') }) (p : P) (q : Q) : p ⊑ₘᵤₛₜᵢ q → p ₐ꜀꜀≼꜀ₒ₋ₐₛ q.
Proof.
  intros hpre s q' hacnv w st.
  destruct (exists_included_or_witnesses (elements (cowaiting_states p s hacnv))
              (λ p', ⌈ αᴘʀᴏ ∘ αᴛᴇꜱᴛ ⌉ (coR p')) (⌈ αᴘʀᴏ ∘ αᴛᴇꜱᴛ ⌉ (coR q')))
    as [(p' & mem & sub) | (X & hXC & hXS)].
  - intros p' (_ & st')%elem_of_elements%cowaiting_states_spec1. exact (dich p' q' st' st).
  - apply elem_of_elements, cowaiting_states_spec1 in mem as (w' & st').
    exists p'. split_and!; [exact w' | exact st' | exact sub].
  - exfalso. eapply (not_must_ta_without_required_acc_set_weak q q' s X w st hXC).
    eapply hpre, (must_ta_weak_for_all_trace_co s p hacnv X).
    intros p' w' st'. eapply hXS, elem_of_elements, cowaiting_states_spec2. split; [exact w' | exact st'].
Qed.

Lemma completeness_fw_co_weak (dich : ∀ (p' : P) (q' : Q), p' ↛ → q' ↛ → (⌈ αᴘʀᴏ ∘ αᴛᴇꜱᴛ ⌉ (coR p') ⊆ ⌈ αᴘʀᴏ ∘ αᴛᴇꜱᴛ ⌉ (coR q')) + { x | x ∈ ⌈ αᴘʀᴏ ∘ αᴛᴇꜱᴛ ⌉ (coR p') ∧ x ∉ ⌈ αᴘʀᴏ ∘ αᴛᴇꜱᴛ ⌉ (coR q') }) (p : P) (q : Q) : p ⊑ₘᵤₛₜᵢ q → p ≼꜀ₒ₋ₐₛ q.
Proof.
  intros. split.
  - now apply completeness1_co.
  - now apply completeness2_co_weak.
Qed.

End Completeness2_co_weak.

(* end hide *)
