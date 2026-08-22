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

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable gmultiset.
From TestingTheory Require Import gLts ActTau InputOutputActions Bisimulation
     Lts_OBA Lts_FW MultisetLTSConstruction InteractionBetweenLts
     ForwarderConstruction VACCS VACCS_Instance WeakTransitions
     coWeakTransition NormalForm Normalisation NormalisationCo RestrictedSimulation.

(** * The feedback simplification is not reversible

    [wt_fnf] states that a process performing [s] also performs the simplified
    trace [nlin (fnf s)].  The converse fails, and this file exhibits a
    counterexample in the forwarder lifting of VACCS.

    Consequence: [fnf] can only ever justify an *inclusion*, never an
    equivalence, by the method used for [nform] -- which needs both
    directions.

    The last section of this file goes further and settles the corresponding
    question about the *preorders*: comparing processes on their simplified
    traces is strictly weaker than comparing them on all their traces
    ([feedback_free_strictly_weaker]). *)

(** ** A generic tool for negative results *)

Lemma wt_nil_stable `{gLts P A} (p r : P) : p ↛ -> p ⟹ r -> r = p.
Proof.
  intros hst w. remember ([] : trace A) as s0 eqn:Hs. revert Hs.
  induction w as [ p0 | s p0 q0 t l w IH | μ s p0 q0 t l w IH ]; intro Hs.
  - reflexivity.
  - exfalso. eapply (lts_refuses_spec2 p0 τ); [exists q0; exact l | exact hst].
  - discriminate.
Qed.

(** A stable process refusing [μ] performs no trace starting with [μ]. *)
Lemma no_wt_of_refuses `{gLts P A} (p : P) (μ : A) s :
  p ↛ -> p ↛[μ] -> ¬ (exists q, p ⟹[μ :: s] q).
Proof.
  intros ht hm (q & w).
  eapply wt_pop in w as (t & w1 & _).
  eapply wt_decomp_one in w1 as (r1 & r2 & w2 & l & _).
  eapply wt_nil_stable in w2; [| exact ht]. subst r1.
  eapply (lts_refuses_spec2 p (ActExt μ)); [exists r2; exact l | exact hm].
Qed.

(** ** The counterexample, in the forwarder lifting of VACCS *)

#[local] Instance NatVP : VACCS_Parameters :=
  {| Channel := nat ; Value := nat ; O := 0 |}.

Definition a1 : TypeOfActions := (cst 1, cst 0).

(** The idle process, with an empty mailbox. *)
Definition z : proc * MO (ExtAct TypeOfActions) := (g 𝟘, ∅).

Lemma nil_no_step (α : ActIO TypeOfActions) (p' : proc) : ¬ lts (g 𝟘) α p'.
Proof.
  intro l. eapply lts_set_spec1 in l. revert l.
  destruct α as [[a|a]|]; vm_compute; discriminate.
Qed.

Lemma z_stable : z ↛.
Proof.
  destruct (decide (z ↛)) as [h | h]; [exact h |].
  exfalso. eapply lts_refuses_spec1 in h as ((p', m') & l).
  inversion l; subst.
  - eapply nil_no_step; eassumption.
  - inversion l0.
  - eapply nil_no_step; eassumption.
Qed.

(** [z] cannot emit: the process is idle and the mailbox is empty. *)
Lemma z_no_out : z ↛[ActOut a1].
Proof.
  destruct (decide (z ↛[ActOut a1])) as [h | h]; [exact h |].
  exfalso. eapply lts_refuses_spec1 in h as ((p', m') & l).
  inversion l; subst.
  - eapply nil_no_step; eassumption.
  - inversion l0; subst; [| multiset_solver].
    destruct nb as (c & eq). subst η. simpl in duo. exact duo.
Qed.

(** The trace [ā ; a] is entirely consumed by the feedback simplification. *)
Definition s_ce : trace (ExtAct TypeOfActions) := [ActOut a1 ; ActIn a1].

Lemma fnf_s_ce : nlin (fnf s_ce) = [].
Proof. vm_compute. reflexivity. Qed.

(** [z] performs the simplified trace but not the original one. *)
Theorem feedback_not_reversible :
  (exists r, z ⟹[nlin (fnf s_ce)] r) /\ ¬ (exists r, z ⟹[s_ce] r).
Proof.
  split.
  - rewrite fnf_s_ce. exists z. eapply wt_nil.
  - exact (no_wt_of_refuses z (ActOut a1) [ActIn a1] z_stable z_no_out).
Qed.

(** * The candidate witness for the open question

    Refuting the equivalence of the two preorders needs a pair [p], [q]
    agreeing on every feedback-free trace but not on some trace with a
    feedback.  The first candidate is

      p = 𝛕•ā + 𝛕•b̄ + 𝛕•(ā ‖ a?•b̄)      q = 𝛕•ā + 𝛕•b̄

    separated by [ā ; a ; b̄], which has a feedback ([ā] at 0, its dual [a] at
    1).  This section proves that half: [p] performs it and [q] does not.

    What is *not* proved here is that [p] and [q] agree on all the
    feedback-free traces -- and in fact they do not, as the next section
    shows.  The repaired witness is handled with the restricted simulations of
    [RestrictedSimulation.v]. *)

Definition c1 : ChannelData := cst 1.
Definition c2 : ChannelData := cst 2.
Definition v0 : ValueData := cst 0.

Definition oA : proc := c1 ! v0 • 𝟘.                    (* the message ā *)
Definition oB : proc := c2 ! v0 • 𝟘.                    (* the message b̄ *)
Definition Bp : proc := oA ‖ (g (c1 ? oB)).             (* ā ‖ a?•b̄ *)
Definition Q0 : gproc := (𝛕 • oA) + (𝛕 • oB).
Definition P0 : gproc := Q0 + (𝛕 • Bp).

Definition aOut : ExtAct TypeOfActions := ActOut (c1, v0).
Definition aIn  : ExtAct TypeOfActions := ActIn  (c1, v0).
Definition bOut : ExtAct TypeOfActions := ActOut (c2, v0).
Definition mt : MO (ExtAct TypeOfActions) := ∅.

Lemma subst_oB (v : ValueData) : oB ^ v = oB.
Proof. vm_compute. reflexivity. Qed.

(** [p] performs the discriminating trace, through its third branch. *)
Lemma p_does : exists r, (g P0, mt) ⟹[[aOut; aIn; bOut]] r.
Proof.
  eexists.
  eapply (wt_tau _ _ (Bp, mt)).
  { eapply ParLeft. eapply lts_choiceR. eapply lts_tau. }
  eapply (wt_act _ _ _ ((𝟘 ‖ (g (c1 ? oB))), mt)).
  { eapply ParLeft. eapply lts_parL. eapply lts_output. }
  eapply (wt_act _ _ _ ((𝟘 ‖ oB), mt)).
  { eapply ParLeft. eapply lts_parR. rewrite <- (subst_oB v0). eapply lts_input. }
  eapply (wt_act _ _ _ ((𝟘 ‖ 𝟘), mt)).
  { eapply ParLeft. eapply lts_parR. eapply lts_output. }
  eapply wt_nil.
Qed.

(** ** Inversion tools for the forwarder lifting *)

Lemma fw_tau_empty (p : proc) (r : proc * MO (ExtAct TypeOfActions)) :
  (p, mt) ⟶ r -> exists p', lts p τ p' /\ r = (p', mt).
Proof.
  intro l. inversion l; subst.
  - eexists. split; [eassumption | reflexivity].
  - inversion l0.
  - exfalso. inversion l2; subst.
    + destruct eq as (duo2 & nb2). exact (dual_blocks μ2 η nb duo nb2).
    + unfold mt in H0. multiset_solver.
Qed.

Lemma fw_act_empty (p : proc) (μ : ExtAct TypeOfActions) r :
  (p, mt) ⟶[μ] r ->
  (exists p', lts p (ActExt μ) p' /\ r = (p', mt))
  \/ (exists η, dual μ η /\ non_blocking η /\ r = (p, {[+ η +]} ⊎ mt)).
Proof.
  intro l. inversion l; subst.
  - left. eexists. split; [eassumption | reflexivity].
  - right. inversion l0; subst.
    + eexists. split; [eassumption | split; [eassumption | reflexivity]].
    + exfalso. unfold mt in H0. multiset_solver.
Qed.

Lemma stable_of_no_tau (p : proc) : (forall p', ¬ lts p τ p') -> (p, mt) ↛.
Proof.
  intro h. destruct (decide ((p, mt) ↛)) as [k | k]; [exact k |].
  exfalso. eapply lts_refuses_spec1 in k as (r & l).
  eapply fw_tau_empty in l as (p' & l' & _). eapply h, l'.
Qed.

Lemma nil_mb_stable (m : MO (ExtAct TypeOfActions)) : (g 𝟘, m) ↛.
Proof.
  destruct (decide ((g 𝟘, m) ↛)) as [k | k]; [exact k |].
  exfalso. eapply lts_refuses_spec1 in k as (r & l). inversion l; subst.
  - eapply nil_no_step; eassumption.
  - inversion l0.
  - eapply nil_no_step; eassumption.
Qed.

Lemma oA_no_tau : forall p', ¬ lts oA τ p'.
Proof. intros p' l. eapply lts_set_spec1 in l. revert l. vm_compute. discriminate. Qed.

Lemma oB_no_tau : forall p', ¬ lts oB τ p'.
Proof. intros p' l. eapply lts_set_spec1 in l. revert l. vm_compute. discriminate. Qed.

(** ** [q] cannot perform the discriminating trace *)

Lemma Q0_tau_step p' : lts (g Q0) τ p' -> p' = oA \/ p' = oB.
Proof.
  intro l. inversion l; subst;
    match goal with [ h : lts (g (𝛕 • _)) τ _ |- _ ] => inversion h; subst end.
  - now left.
  - now right.
Qed.

Lemma Q0_tau_closure r :
  (g Q0, mt) ⟹ r -> r = (g Q0, mt) \/ r = (oA, mt) \/ r = (oB, mt).
Proof.
  intro w. remember ([] : trace (ExtAct TypeOfActions)) as s0 eqn:Hs.
  remember ((g Q0, mt) : proc * MO (ExtAct TypeOfActions)) as z0 eqn:Hz.
  revert Hs Hz.
  induction w as [ x | s x y t l w IH | μ s x y t l w IH ]; intros Hs Hz.
  - subst. now left.
  - subst x. subst s. eapply fw_tau_empty in l as (p' & l' & ->).
    eapply Q0_tau_step in l' as [-> | ->].
    + right. left. eapply wt_nil_stable in w; [exact w | eapply stable_of_no_tau, oA_no_tau].
    + right. right. eapply wt_nil_stable in w; [exact w | eapply stable_of_no_tau, oB_no_tau].
  - discriminate.
Qed.

Lemma out_from_Q0 t : (g Q0, mt) ⟹{aOut} t -> t = (g 𝟘, mt).
Proof.
  intro w. eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  eapply Q0_tau_closure in w1 as [-> | [-> | ->]].
  - eapply fw_act_empty in l as [(p' & l' & ->) | (η & duo & nb & ->)].
    + exfalso. inversion l'; subst;
        match goal with [ h : lts (g (𝛕 • _)) _ _ |- _ ] => inversion h end.
    + exfalso. destruct nb as (c & ->). simpl in duo. exact duo.
  - eapply fw_act_empty in l as [(p' & l' & ->) | (η & duo & nb & ->)].
    + inversion l'; subst.
      eapply wt_nil_stable in w2; [exact w2 | eapply nil_mb_stable].
    + exfalso. destruct nb as (c & ->). simpl in duo. exact duo.
  - eapply fw_act_empty in l as [(p' & l' & ->) | (η & duo & nb & ->)].
    + exfalso. inversion l'.
    + exfalso. destruct nb as (c & ->). simpl in duo. exact duo.
Qed.

Lemma in_from_nil t : (g 𝟘, mt) ⟹{aIn} t -> t = (g 𝟘, {[+ aOut +]} ⊎ mt).
Proof.
  intro w. eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  eapply wt_nil_stable in w1; [| eapply nil_mb_stable]. subst r1.
  eapply fw_act_empty in l as [(p' & l' & ->) | (η & duo & nb & ->)].
  - exfalso. eapply nil_no_step; eassumption.
  - eapply simplify_match_input in duo. subst η.
    eapply wt_nil_stable in w2; [exact w2 | eapply nil_mb_stable].
Qed.

Lemma aOut_neq_bOut : aOut <> bOut.
Proof. unfold aOut, bOut, c1, c2. discriminate. Qed.

Lemma nilA_no_bOut : (g 𝟘, {[+ aOut +]} ⊎ mt) ↛[bOut].
Proof.
  destruct (decide ((g 𝟘, {[+ aOut +]} ⊎ mt) ↛[bOut])) as [k | k]; [exact k |].
  exfalso. eapply lts_refuses_spec1 in k as (r & l). inversion l; subst.
  - eapply nil_no_step; eassumption.
  - inversion l0; subst.
    + destruct nb as (c & ->). simpl in duo. exact duo.
    + eapply aOut_neq_bOut. unfold mt in H0. multiset_solver.
Qed.

Theorem q_does_not : ¬ exists r, (g Q0, mt) ⟹[[aOut; aIn; bOut]] r.
Proof.
  intros (r & w).
  eapply wt_pop in w as (t1 & w1 & w2). eapply out_from_Q0 in w1. subst t1.
  eapply wt_pop in w2 as (t2 & w3 & w4). eapply in_from_nil in w3. subst t2.
  exact (no_wt_of_refuses _ bOut [] (nil_mb_stable _) nilA_no_bOut (ex_intro _ r w4)).
Qed.

(** The witness is separated by a trace carrying a feedback. *)
Theorem witness_separated :
  (exists r, (g P0, mt) ⟹[[aOut; aIn; bOut]] r)
  /\ ¬ (exists r, (g Q0, mt) ⟹[[aOut; aIn; bOut]] r)
  /\ has_fb [aOut; aIn; bOut].
Proof.
  split; [exact p_does |]. split; [exact q_does_not |].
  simpl. left. split.
  - exists (c1, v0). reflexivity.
  - constructor. reflexivity.
Qed.

(** * The witness does not work

    The candidate above is *not* a counterexample to the open question, and the
    reason is specific to a calculus with values: the input [c1 ? P] of VACCS
    accepts *any* value on the channel, so [p] can be unlocked by an input that
    is not the co-action of what it emitted.

    Concretely, [ā = ActOut (c1,v0)] and the input [ActIn (c1,v1)] with
    [v1 ≠ v0] are not dual, so the trace [ā ; (c1,v1)? ; b̄] carries no feedback
    -- and it separates [p] from [q] just as well.  Hence [p] and [q] already
    disagree on a feedback-free trace: [p ⋠_fnf q], and the pair says nothing
    about the open question.

    Repairing this needs the continuation of the input to be guarded on the
    received value, e.g. [c1 ? (If (bvar 0 = v0) Then b̄ Else 𝟘)], so that only
    the co-action of [ā] unlocks [b̄].  That is the next candidate. *)

Definition v1 : ValueData := cst 1.
Definition aIn1 : ExtAct TypeOfActions := ActIn (c1, v1).
Definition t_ff : trace (ExtAct TypeOfActions) := [aOut; aIn1; bOut].

Lemma t_ff_no_fb : ¬ has_fb t_ff.
Proof.
  simpl. intros [ (_ & h) | [ (h & _) | [ (_ & h) | h ] ] ].
  - inversion h; subst.
    + unfold aIn1, aOut, c1, v1, v0 in H0. simpl in H0. inversion H0.
    + inversion H0; subst;
        [ simpl in *; assumption
        | match goal with [ k : Exists _ [] |- _ ] => inversion k end ].
  - destruct h as (c & hc). unfold aIn1 in hc. discriminate.
  - inversion h.
  - exact h.
Qed.

(** [p] is unlocked by *any* value on the channel. *)
Lemma p_does_gen (v : ValueData) :
  exists r, (g P0, mt) ⟹[[aOut; ActIn (c1, v); bOut]] r.
Proof.
  eexists.
  eapply (wt_tau _ _ (Bp, mt)).
  { eapply ParLeft. eapply lts_choiceR. eapply lts_tau. }
  eapply (wt_act _ _ _ ((𝟘 ‖ (g (c1 ? oB))), mt)).
  { eapply ParLeft. eapply lts_parL. eapply lts_output. }
  eapply (wt_act _ _ _ ((𝟘 ‖ oB), mt)).
  { eapply ParLeft. eapply lts_parR. rewrite <- (subst_oB v). eapply lts_input. }
  eapply (wt_act _ _ _ ((𝟘 ‖ 𝟘), mt)).
  { eapply ParLeft. eapply lts_parR. eapply lts_output. }
  eapply wt_nil.
Qed.

Lemma in_from_nil_gen (a : TypeOfActions) t :
  (g 𝟘, mt) ⟹{ActIn a} t -> t = (g 𝟘, {[+ ActOut a +]} ⊎ mt).
Proof.
  intro w. eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  eapply wt_nil_stable in w1; [| eapply nil_mb_stable]. subst r1.
  eapply fw_act_empty in l as [(p' & l' & ->) | (η & duo & nb & ->)].
  - exfalso. eapply nil_no_step; eassumption.
  - eapply simplify_match_input in duo. subst η.
    eapply wt_nil_stable in w2; [exact w2 | eapply nil_mb_stable].
Qed.

Lemma nilA_no_bOut_gen (a : TypeOfActions) :
  ActOut a <> bOut -> (g 𝟘, {[+ ActOut a +]} ⊎ mt) ↛[bOut].
Proof.
  intro hne.
  destruct (decide ((g 𝟘, {[+ ActOut a +]} ⊎ mt) ↛[bOut])) as [k | k]; [exact k |].
  exfalso. eapply lts_refuses_spec1 in k as (r & l). inversion l; subst.
  - eapply nil_no_step; eassumption.
  - inversion l0; subst.
    + destruct nb as (c & ->). simpl in duo. exact duo.
    + eapply hne. unfold mt in H0. multiset_solver.
Qed.

Lemma q_does_not_gen (a : TypeOfActions) :
  ActOut a <> bOut -> ¬ exists r, (g Q0, mt) ⟹[[aOut; ActIn a; bOut]] r.
Proof.
  intros hne (r & w).
  eapply wt_pop in w as (t1 & w1 & w2). eapply out_from_Q0 in w1. subst t1.
  eapply wt_pop in w2 as (t2 & w3 & w4). eapply in_from_nil_gen in w3. subst t2.
  exact (no_wt_of_refuses _ bOut [] (nil_mb_stable _) (nilA_no_bOut_gen a hne)
           (ex_intro _ r w4)).
Qed.

(** [p] and [q] are separated by a *feedback-free* trace, so the pair is not a
    counterexample to the open question. *)
Theorem witness_fails :
  ¬ has_fb t_ff
  /\ (exists r, (g P0, mt) ⟹[t_ff] r)
  /\ ¬ (exists r, (g Q0, mt) ⟹[t_ff] r).
Proof.
  split; [exact t_ff_no_fb |]. split.
  - eapply (p_does_gen v1).
  - eapply q_does_not_gen. unfold bOut, c1, c2. discriminate.
Qed.

(** * The repaired witness

    Guarding the continuation of the input on the received value makes the
    unlocking of [b̄] depend on the *exact* co-action of [ā]:

      p₂ = 𝛕•ā + 𝛕•b̄ + 𝛕•(ā ‖ c1 ? (If (bvar 0 = v0) Then b̄ Else 𝟘))

    Only the value [v0] fires the guard ([guard_v0_fires]); any other value
    leaves a dead process ([guard_v1_blocks]).  So the hole of the previous
    section is plugged: an input on another value no longer unlocks [b̄].

    [q] is unchanged, so [q_does_not] still applies and the pair is still
    separated by a trace carrying a feedback. *)

Definition Gd : proc := If (Equality (bvar 0) v0) Then oB Else 𝟘.
Definition Bp2 : proc := oA ‖ (g (c1 ? Gd)).
Definition P2 : gproc := Q0 + (𝛕 • Bp2).

Lemma Gd_v0 : Gd ^ v0 = If (Equality v0 v0) Then oB Else 𝟘.
Proof. vm_compute. reflexivity. Qed.

Lemma Gd_v1 : Gd ^ v1 = If (Equality v1 v0) Then oB Else 𝟘.
Proof. vm_compute. reflexivity. Qed.

(** The co-action of [ā] fires the guard... *)
Lemma guard_v0_fires : lts (Gd ^ v0) (ActExt bOut) (g 𝟘).
Proof. rewrite Gd_v0. eapply lts_ifOne; [vm_compute; reflexivity | eapply lts_output]. Qed.

(** ...and no other value does. *)
Lemma guard_v1_blocks (p' : proc) : ¬ lts (Gd ^ v1) (ActExt bOut) p'.
Proof. intro l. eapply lts_set_spec1 in l. revert l. vm_compute. discriminate. Qed.

Lemma p2_does : exists r, (g P2, mt) ⟹[[aOut; aIn; bOut]] r.
Proof.
  eexists.
  eapply (wt_tau _ _ (Bp2, mt)).
  { eapply ParLeft. eapply lts_choiceR. eapply lts_tau. }
  eapply (wt_act _ _ _ ((𝟘 ‖ (g (c1 ? Gd))), mt)).
  { eapply ParLeft. eapply lts_parL. eapply lts_output. }
  eapply (wt_act _ _ _ ((𝟘 ‖ (Gd ^ v0)), mt)).
  { eapply ParLeft. eapply lts_parR. eapply lts_input. }
  eapply (wt_act _ _ _ ((𝟘 ‖ (g 𝟘)), mt)).
  { eapply ParLeft. eapply lts_parR. eapply guard_v0_fires. }
  eapply wt_nil.
Qed.

Theorem witness2_separated :
  (exists r, (g P2, mt) ⟹[[aOut; aIn; bOut]] r)
  /\ ¬ (exists r, (g Q0, mt) ⟹[[aOut; aIn; bOut]] r)
  /\ has_fb [aOut; aIn; bOut].
Proof.
  split; [exact p2_does |]. split; [exact q_does_not |].
  simpl. left. split.
  - exists (c1, v0). reflexivity.
  - constructor. reflexivity.
Qed.

(** * Feedback-free traces do not determine the traces

    The pair below settles the question left open above: restricting the trace
    preorder to the feedback-free traces is *strictly weaker* than the trace
    preorder itself.  The witness is the third branch of [P2] on its own,

      p = ā ‖ c1 ? (If (bvar 0 = v0) Then b̄ Else 𝟘)      q = 𝛕•ā + 𝛕•b̄

    both read in the forwarder lifting of VACCS, started with an empty mailbox.

    - [p] performs [ā ; a ; b̄], which carries a feedback, and [q] does not
      ([q_does_not]).
    - [p] and [q] agree on every feedback-free trace ([bp2_ff_included]),
      because [p] can produce both [ā] and [b̄] only by receiving [a], and after
      [ā] has been emitted that input is exactly what a feedback-free trace
      forbids.

    The proof of the second point is a restricted simulation in the sense of
    [RestrictedSimulation.v]: an ordinary simulation would have to match the
    input closing the feedback, and there [q] gets stuck. *)

(** ** The guard *)

Definition fires (v : ValueData) : Prop := Eval_Eq 0 (Equality v v0) = Some true.

Lemma Gd_subst (v : ValueData) : Gd ^ v = If (Equality v v0) Then oB Else 𝟘.
Proof. vm_compute. reflexivity. Qed.

Lemma fires_v0 : fires v0.
Proof. vm_compute. reflexivity. Qed.

(** On [Data], syntactic equality is the only way to satisfy the guard. *)
Lemma fires_eq (v : ValueData) : fires v -> v = v0.
Proof.
  unfold fires, v0. destruct v as [t | i]; simpl.
  - case_decide as e; [intros _; rewrite e; reflexivity | discriminate].
  - discriminate.
Qed.

(** Hence the guard fires only on the co-action of [ā], and then emits [b̄]. *)
Lemma guard_step (v : ValueData) α r :
  lts (Gd ^ v) α r -> v = v0 /\ α = ActExt bOut /\ r = g 𝟘.
Proof.
  rewrite Gd_subst. intro l. inversion l; subst.
  - inversion H5; subst. repeat split. eapply fires_eq. exact H4.
  - inversion H5.
Qed.

(** ** Inert processes *)

Definition W : proc := g (c1 ? Gd).
Definition dead (p : proc) : Prop := forall α r, ¬ lts p α r.

Lemma dead_zero : dead (g 𝟘).
Proof. intros α r. eapply nil_no_step. Qed.

Lemma dead_Gd (v : ValueData) : v <> v0 -> dead (Gd ^ v).
Proof. intros ne α r l. eapply guard_step in l as (e & _ & _). exact (ne e). Qed.

Lemma dead_par (p q : proc) : dead p -> dead q -> dead (p ‖ q).
Proof.
  intros hp hq α r l. inversion l; subst.
  - eapply hp; eassumption.
  - eapply hq; eassumption.
  - eapply hp; eassumption.
  - eapply hq; eassumption.
Qed.

(** ** Inversion in the forwarder lifting, with an arbitrary mailbox *)

Lemma fw_tau_inv (p : proc) (m : MO (ExtAct TypeOfActions))
  (r : proc * MO (ExtAct TypeOfActions)) :
  (p, m) ⟶ r ->
  (exists p', lts p τ p' /\ r = (p', m))
  \/ (exists (a : TypeOfActions) p' m', lts p (ActExt (ActIn a)) p'
        /\ m = {[+ ActOut a +]} ⊎ m' /\ r = (p', m')).
Proof.
  intro l. inversion l; subst.
  - left. eexists. split; [eassumption | reflexivity].
  - inversion l0.
  - right. destruct eq as (duo & nb). destruct nb as (a & ->).
    eapply ext_act_match_sym, simplify_match_output in duo. subst μ1.
    exists a, a0, b2. split; [assumption | split; [| reflexivity]].
    symmetry. eapply non_blocking_action_in_ms; [exists a; reflexivity | exact l2].
Qed.

Lemma fw_act_inv (p : proc) (m : MO (ExtAct TypeOfActions)) (μ : ExtAct TypeOfActions)
  (r : proc * MO (ExtAct TypeOfActions)) :
  (p, m) ⟶[μ] r ->
  (exists p', lts p (ActExt μ) p' /\ r = (p', m))
  \/ (exists (a : TypeOfActions), μ = ActIn a /\ r = (p, {[+ ActOut a +]} ⊎ m))
  \/ (exists (a : TypeOfActions) m', μ = ActOut a /\ m = {[+ ActOut a +]} ⊎ m' /\ r = (p, m')).
Proof.
  intro l. inversion l; subst.
  - left. eexists. split; [eassumption | reflexivity].
  - inversion l0; subst.
    + right. left. destruct nb as (a & ->).
      eapply ext_act_match_sym, simplify_match_output in duo. subst μ.
      exists a. split; reflexivity.
    + right. right. destruct nb as (a & ->).
      exists a, b2. split; [reflexivity | split; reflexivity].
Qed.

(** ** Inversion of the components *)

Lemma oA_inv α r : lts oA α r -> α = ActExt aOut /\ r = g 𝟘.
Proof. intro l. inversion l; subst. split; reflexivity. Qed.

Lemma oB_inv α r : lts oB α r -> α = ActExt bOut /\ r = g 𝟘.
Proof. intro l. inversion l; subst. split; reflexivity. Qed.

Lemma W_inv α r : lts W α r -> exists v, α = ActExt (ActIn (c1, v)) /\ r = Gd ^ v.
Proof. intro l. inversion l; subst. exists v. split; reflexivity. Qed.

Lemma par_inv (p q : proc) α r :
  lts (p ‖ q) α r ->
  (exists p', lts p α p' /\ r = p' ‖ q)
  \/ (exists q', lts q α q' /\ r = p ‖ q')
  \/ (exists (a : TypeOfActions) p' q', lts p (ActExt (ActOut a)) p' /\ lts q (ActExt (ActIn a)) q'
        /\ α = τ /\ r = p' ‖ q')
  \/ (exists (a : TypeOfActions) p' q', lts p (ActExt (ActIn a)) p' /\ lts q (ActExt (ActOut a)) q'
        /\ α = τ /\ r = p' ‖ q').
Proof.
  intro l. inversion l; subst.
  - right. right. left. exists (c, v), p2, q2. repeat split; assumption.
  - right. right. right. exists (c, v), q2, p2. repeat split; assumption.
  - left. eexists. split; [eassumption | reflexivity].
  - right. left. eexists. split; [eassumption | reflexivity].
Qed.

(** ** The moves available to [q] *)

Notation st := (proc * MO (ExtAct TypeOfActions))%type.

Lemma wt_one (x y : st) (μ : ExtAct TypeOfActions) : x ⟶[μ] y -> x ⟹{μ} y.
Proof. intro l. eapply wt_act; [exact l | eapply wt_nil]. Qed.

Lemma wt_one_tau (x y : st) : x ⟶ y -> x ⟹ y.
Proof. intro l. eapply wt_tau; [exact l | eapply wt_nil]. Qed.

(** The mailbox forwards what it holds, and absorbs any input. *)
Lemma q_mb_out (q : proc) (n : MO (ExtAct TypeOfActions)) (a : TypeOfActions) :
  ((q, {[+ ActOut a +]} ⊎ n) : st) ⟶[ActOut a] (q, n).
Proof. eapply ParRight. eapply lts_multiset_minus. exists a. reflexivity. Qed.

Lemma q_mb_in (q : proc) (n : MO (ExtAct TypeOfActions)) (a : TypeOfActions) :
  ((q, n) : st) ⟶[ActIn a] (q, {[+ ActOut a +]} ⊎ n).
Proof. eapply ParRight. eapply lts_multiset_add; [reflexivity | exists a; reflexivity]. Qed.

Lemma q0_to_oA (n : MO (ExtAct TypeOfActions)) : ((g Q0, n) : st) ⟶ (oA, n).
Proof. eapply ParLeft. eapply lts_choiceL. eapply lts_tau. Qed.

Lemma q0_to_oB (n : MO (ExtAct TypeOfActions)) : ((g Q0, n) : st) ⟶ (oB, n).
Proof. eapply ParLeft. eapply lts_choiceR. eapply lts_tau. Qed.

(** [q] spends its branch on [ā]... *)
Lemma q0_out_aOut (n : MO (ExtAct TypeOfActions)) : ((g Q0, n) : st) ⟹{aOut} (g 𝟘, n).
Proof. eapply wt_tau; [eapply q0_to_oA |]. eapply wt_one. eapply ParLeft. eapply lts_output. Qed.

(** ...or on [b̄], but never on both. *)
Lemma q0_out_bOut (n : MO (ExtAct TypeOfActions)) : ((g Q0, n) : st) ⟹{bOut} (g 𝟘, n).
Proof. eapply wt_tau; [eapply q0_to_oB |]. eapply wt_one. eapply ParLeft. eapply lts_output. Qed.

(** ** The restricted simulation

    [Rel E p q] relates a state of [p] to a state of [q], where [E] is the
    ledger of the non-blocking actions [p] has already emitted.  The mailbox of
    [q] is always *at least* that of [p]: what [p] consumes internally to fire
    its guard, [q] keeps and forwards.  The clauses [K2], [K4], [K6], [K9]
    carry an extra [ā] on the [q] side, the "debt" [q] still owes; the clause
    [K3] is the one where the ledger closes the door: [ā] has been emitted, so
    the input that would unlock [b̄] is forbidden, and [q] may spend its branch
    on [ā]. *)

Inductive Rel : list (ExtAct TypeOfActions) -> st -> st -> Prop :=
| K1 E m n : m ⊆ n -> Rel E (oA ‖ W, m) (g Q0, n)
| K2 E m n : m ⊆ {[+ aOut +]} ⊎ n -> aOut ∈ E -> Rel E (𝟘 ‖ W, m) (g Q0, n)
| K3 E m n : m ⊆ n -> aOut ∈ E -> aOut ∉ m -> Rel E (𝟘 ‖ W, m) (g 𝟘, n)
| K4 E m n : {[+ aOut +]} ⊎ m ⊆ n -> Rel E (oA ‖ (Gd ^ v0), m) (g Q0, n)
| K5 E m n : m ⊆ n -> Rel E (𝟘 ‖ (Gd ^ v0), m) (g Q0, n)
| K6 E m n : {[+ aOut +]} ⊎ m ⊆ n -> Rel E (oA ‖ 𝟘, m) (g 𝟘, n)
| K7 E v m n : v <> v0 -> m ⊆ n -> Rel E (oA ‖ (Gd ^ v), m) (g Q0, n)
| K8 E p m n : dead p -> m ⊆ n -> Rel E (p, m) (g 𝟘, n)
| K9 E p m n : dead p -> m ⊆ {[+ aOut +]} ⊎ n -> Rel E (p, m) (g Q0, n).

(** A process with neither a [τ] nor an input cannot move at all once lifted:
    the mailbox alone never produces a [τ]. *)
Definition inert (p : proc) : Prop :=
  (forall p', ¬ lts p τ p') /\ (forall (a : TypeOfActions) p', ¬ lts p (ActExt (ActIn a)) p').

Lemma inert_dead (p : proc) : dead p -> inert p.
Proof. intro h. split; intros; eapply h. Qed.

Lemma inert_oA : inert oA.
Proof. split; intros; intro l; eapply oA_inv in l as (e & _); discriminate. Qed.

Lemma inert_Gd (v : ValueData) : inert (Gd ^ v).
Proof. split; intros; intro l; eapply guard_step in l as (_ & e & _); discriminate. Qed.

Lemma inert_par (p q : proc) : inert p -> inert q -> inert (p ‖ q).
Proof.
  intros (hpt & hpi) (hqt & hqi). split.
  - intros p' l.
    eapply par_inv in l
      as [(x & l & _) | [(x & l & _) | [(a & x & y & _ & l & _) | (a & x & y & l & _)]]].
    + eapply hpt; eassumption.
    + eapply hqt; eassumption.
    + eapply hqi; eassumption.
    + eapply hpi; eassumption.
  - intros a p' l.
    eapply par_inv in l
      as [(x & l & _) | [(x & l & _) | [(b & x & y & _ & _ & e & _) | (b & x & y & _ & _ & e & _)]]].
    + eapply hpi; eassumption.
    + eapply hqi; eassumption.
    + discriminate.
    + discriminate.
Qed.

Lemma inert_no_tau (p : proc) (m : MO (ExtAct TypeOfActions)) r :
  inert p -> ((p, m) : st) ⟶ r -> False.
Proof.
  intros (ht & hi) l. eapply fw_tau_inv in l as [(p' & l & _) | (a & p' & m' & l & _)].
  - eapply ht; eassumption.
  - eapply hi; eassumption.
Qed.

(** *** The silent clause

    Only [K1], [K2] and [K3] move silently, and always by forwarding a message
    of the mailbox to the waiting input -- or, in [K1], by the internal
    communication that consumes [ā] on the spot. *)
Lemma rel_tau E p1 q1 p2 : Rel E p1 q1 -> p1 ⟶ p2 -> exists q2, q1 ⟹ q2 /\ Rel E p2 q2.
Proof.
  intros hr l. inversion hr; subst.
  - eapply fw_tau_inv in l as [(p' & l & ->) | (a & p' & m' & l & -> & ->)].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(b & x & y & l1 & l2 & _ & ->) | (b & x & y & l1 & l2 & _ & ->)]]].
      * eapply oA_inv in l as (e & _). discriminate.
      * eapply W_inv in l as (v & e & _). discriminate.
      * eapply oA_inv in l1 as (e1 & ->). injection e1 as ->.
        eapply W_inv in l2 as (v & e2 & ->). injection e2 as <-.
        exists (g Q0, n). split; [eapply wt_nil | eapply K5; exact H].
      * eapply oA_inv in l1 as (e1 & _). discriminate.
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(b & x & y & _ & _ & e & _) | (b & x & y & _ & _ & e & _)]]].
      * eapply oA_inv in l as (e & _). discriminate.
      * eapply W_inv in l as (v & e2 & ->). injection e2 as ->.
        destruct (Data_dec v v0) as [-> | ne].
        -- exists (g Q0, n). split; [eapply wt_nil | eapply K4; exact H].
        -- exists (g Q0, n). split; [eapply wt_nil | eapply K7; [exact ne | multiset_solver]].
      * discriminate.
      * discriminate.
  - eapply fw_tau_inv in l as [(p' & l & ->) | (a & p' & m' & l & -> & ->)].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(b & x & y & l1 & l2 & _ & ->) | (b & x & y & l1 & l2 & _ & ->)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply W_inv in l as (v & e & _). discriminate.
      * exfalso. eapply dead_zero; eassumption.
      * exfalso. eapply dead_zero; eassumption.
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(b & x & y & _ & _ & e & _) | (b & x & y & _ & _ & e & _)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply W_inv in l as (v & e2 & ->). injection e2 as ->.
        destruct (Data_dec v v0) as [-> | ne].
        -- exists (g Q0, n). split; [eapply wt_nil | eapply K5; multiset_solver].
        -- exists (g Q0, n). split; [eapply wt_nil |].
           eapply K9; [eapply dead_par; [eapply dead_zero | eapply dead_Gd; exact ne] |].
           etransitivity; [eapply gmultiset_disj_union_subseteq_r | exact H].
      * discriminate.
      * discriminate.
  - eapply fw_tau_inv in l as [(p' & l & ->) | (a & p' & m' & l & -> & ->)].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(b & x & y & l1 & l2 & _ & ->) | (b & x & y & l1 & l2 & _ & ->)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply W_inv in l as (v & e & _). discriminate.
      * exfalso. eapply dead_zero; eassumption.
      * exfalso. eapply dead_zero; eassumption.
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(b & x & y & _ & _ & e & _) | (b & x & y & _ & _ & e & _)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply W_inv in l as (v & e2 & ->). injection e2 as ->.
        destruct (Data_dec v v0) as [-> | ne].
        -- exfalso. eapply H1. multiset_solver.
        -- exists (g 𝟘, n). split; [eapply wt_nil |].
           eapply K8; [eapply dead_par; [eapply dead_zero | eapply dead_Gd; exact ne] |].
           etransitivity; [eapply gmultiset_disj_union_subseteq_r | exact H].
      * discriminate.
      * discriminate.
  - exfalso. eapply inert_no_tau; [eapply inert_par; [eapply inert_oA | eapply inert_Gd] | exact l].
  - exfalso. eapply inert_no_tau; [eapply inert_par; [eapply inert_dead, dead_zero | eapply inert_Gd] | exact l].
  - exfalso. eapply inert_no_tau; [eapply inert_par; [eapply inert_oA | eapply inert_dead, dead_zero] | exact l].
  - exfalso. eapply inert_no_tau; [eapply inert_par; [eapply inert_oA | eapply inert_Gd] | exact l].
  - exfalso. eapply inert_no_tau; [eapply inert_dead; exact H | exact l].
  - exfalso. eapply inert_no_tau; [eapply inert_dead; exact H | exact l].
Qed.

(** *** Small multiset lemmas, to keep [multiset_solver] out of the big cases *)

Lemma mb_split (x : ExtAct TypeOfActions) (n : MO (ExtAct TypeOfActions)) :
  x ∈ n -> exists n', n = {[+ x +]} ⊎ n'.
Proof. intro h. exists (n ∖ {[+ x +]}). multiset_solver. Qed.

Lemma mb_cancel (x : ExtAct TypeOfActions) (u w : MO (ExtAct TypeOfActions)) :
  {[+ x +]} ⊎ u ⊆ {[+ x +]} ⊎ w -> u ⊆ w.
Proof. multiset_solver. Qed.

Lemma mb_swap (x y : ExtAct TypeOfActions) (u : MO (ExtAct TypeOfActions)) :
  {[+ x +]} ⊎ ({[+ y +]} ⊎ u) = {[+ y +]} ⊎ ({[+ x +]} ⊎ u).
Proof. multiset_solver. Qed.

Lemma mb_drop (x : ExtAct TypeOfActions) (u w : MO (ExtAct TypeOfActions)) :
  {[+ x +]} ⊎ u ⊆ w -> u ⊆ w.
Proof. intro h. etransitivity; [eapply gmultiset_disj_union_subseteq_r | exact h]. Qed.

(** *** The non-blocking clause

    Every output of [p] is matched: those of its mailbox by the corresponding
    message of the mailbox of [q], which is larger; the [ā] of the left
    component either by that same message, or -- when [q] has none -- by
    spending the branch [𝛕•ā], which is exactly the move that lands in [K3]. *)
Lemma rel_nb E p1 q1 (η : ExtAct TypeOfActions) p2 :
  Rel E p1 q1 -> non_blocking η -> p1 ⟶[η] p2 ->
  exists q2, q1 ⟹{η} q2 /\ Rel (η :: E) p2 q2.
Proof.
  intros hr nb l. destruct nb as (aa & ->). inversion hr; subst.
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & _) | (b & m' & e & -> & ->)]].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(b & x & y & _ & _ & e & _) | (b & x & y & _ & _ & e & _)]]].
      * eapply oA_inv in l as (e & ->). injection e as ->.
        destruct (decide (aOut ∈ n)) as [hin | hout].
        -- eapply mb_split in hin as (n' & ->).
           exists (g Q0, n'). split; [eapply wt_one, q_mb_out |].
           eapply K2; [exact H | eapply elem_of_cons; left; reflexivity].
        -- exists (g 𝟘, n). split; [eapply q0_out_aOut |].
           eapply K3; [exact H | eapply elem_of_cons; left; reflexivity |].
           intro hm. eapply hout. multiset_solver.
      * eapply W_inv in l as (v & e & _). discriminate.
      * discriminate.
      * discriminate.
    + discriminate.
    + injection e as <-.
      assert (hin : ActOut aa ∈ n) by multiset_solver.
      eapply mb_split in hin as (n' & ->).
      exists (g Q0, n'). split; [eapply wt_one, q_mb_out |].
      eapply K1. eapply mb_cancel. exact H.
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & _) | (b & m' & e & -> & ->)]].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(b & x & y & _ & _ & e & _) | (b & x & y & _ & _ & e & _)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply W_inv in l as (v & e & _). discriminate.
      * discriminate.
      * discriminate.
    + discriminate.
    + injection e as <-.
      destruct (decide (ActOut aa ∈ n)) as [hin | hout].
      * eapply mb_split in hin as (n' & ->).
        exists (g Q0, n'). split; [eapply wt_one, q_mb_out |].
        rewrite mb_swap in H. eapply mb_cancel in H.
        eapply K2; [exact H | eapply elem_of_cons; right; exact H0].
      * assert (hx : ActOut aa ∈ {[+ aOut +]} ⊎ n) by multiset_solver.
        eapply gmultiset_elem_of_disj_union in hx as [hx | hx]; [| contradiction].
        eapply gmultiset_elem_of_singleton in hx. rewrite hx in H. rewrite hx in hout. rewrite hx.
        eapply mb_cancel in H.
        exists (g 𝟘, n). split; [eapply q0_out_aOut |].
        eapply K3; [exact H | eapply elem_of_cons; right; exact H0 |].
        intro hm. eapply hout. multiset_solver.
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & _) | (b & m' & e & -> & ->)]].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(b & x & y & _ & _ & e & _) | (b & x & y & _ & _ & e & _)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply W_inv in l as (v & e & _). discriminate.
      * discriminate.
      * discriminate.
    + discriminate.
    + injection e as <-.
      assert (hin : ActOut aa ∈ n) by multiset_solver.
      eapply mb_split in hin as (n' & ->).
      exists (g 𝟘, n'). split; [eapply wt_one, q_mb_out |].
      eapply K3; [eapply mb_cancel; exact H | eapply elem_of_cons; right; exact H0 |].
      intro hm. eapply H1. multiset_solver.
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & _) | (b & m' & e & -> & ->)]].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(b & x & y & _ & _ & e & _) | (b & x & y & _ & _ & e & _)]]].
      * eapply oA_inv in l as (e & ->). injection e as ->.
        assert (hin : aOut ∈ n) by multiset_solver.
        eapply mb_split in hin as (n' & ->).
        exists (g Q0, n'). split; [eapply wt_one, q_mb_out |].
        eapply K5. eapply mb_cancel. exact H.
      * eapply guard_step in l as (_ & e & ->). injection e as ->.
        exists (g 𝟘, n). split; [eapply q0_out_bOut |].
        eapply K6. exact H.
      * discriminate.
      * discriminate.
    + discriminate.
    + injection e as <-.
      assert (hin : ActOut aa ∈ n) by multiset_solver.
      eapply mb_split in hin as (n' & ->).
      exists (g Q0, n'). split; [eapply wt_one, q_mb_out |].
      rewrite mb_swap in H. eapply mb_cancel in H.
      eapply K4. exact H.
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & _) | (b & m' & e & -> & ->)]].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(b & x & y & _ & _ & e & _) | (b & x & y & _ & _ & e & _)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply guard_step in l as (_ & e & ->). injection e as ->.
        exists (g 𝟘, n). split; [eapply q0_out_bOut |].
        eapply K8; [eapply dead_par; eapply dead_zero | exact H].
      * discriminate.
      * discriminate.
    + discriminate.
    + injection e as <-.
      assert (hin : ActOut aa ∈ n) by multiset_solver.
      eapply mb_split in hin as (n' & ->).
      exists (g Q0, n'). split; [eapply wt_one, q_mb_out |].
      eapply K5. eapply mb_cancel. exact H.
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & _) | (b & m' & e & -> & ->)]].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(b & x & y & _ & _ & e & _) | (b & x & y & _ & _ & e & _)]]].
      * eapply oA_inv in l as (e & ->). injection e as ->.
        assert (hin : aOut ∈ n) by multiset_solver.
        eapply mb_split in hin as (n' & ->).
        exists (g 𝟘, n'). split; [eapply wt_one, q_mb_out |].
        eapply K8; [eapply dead_par; eapply dead_zero | eapply mb_cancel; exact H].
      * exfalso. eapply dead_zero; eassumption.
      * discriminate.
      * discriminate.
    + discriminate.
    + injection e as <-.
      assert (hin : ActOut aa ∈ n) by multiset_solver.
      eapply mb_split in hin as (n' & ->).
      exists (g 𝟘, n'). split; [eapply wt_one, q_mb_out |].
      rewrite mb_swap in H. eapply mb_cancel in H.
      eapply K6. exact H.
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & _) | (b & m' & e & -> & ->)]].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(b & x & y & _ & _ & e & _) | (b & x & y & _ & _ & e & _)]]].
      * eapply oA_inv in l as (e & ->). injection e as ->.
        exists (g 𝟘, n). split; [eapply q0_out_aOut |].
        eapply K8; [eapply dead_par; [eapply dead_zero | eapply dead_Gd; exact H] | exact H0].
      * eapply guard_step in l as (e & _ & _). contradiction.
      * discriminate.
      * discriminate.
    + discriminate.
    + injection e as <-.
      assert (hin : ActOut aa ∈ n) by multiset_solver.
      eapply mb_split in hin as (n' & ->).
      exists (g Q0, n'). split; [eapply wt_one, q_mb_out |].
      eapply K7; [exact H | eapply mb_cancel; exact H0].
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & _) | (b & m' & e & -> & ->)]].
    + exfalso. eapply H; eassumption.
    + discriminate.
    + injection e as <-.
      assert (hin : ActOut aa ∈ n) by multiset_solver.
      eapply mb_split in hin as (n' & ->).
      exists (g 𝟘, n'). split; [eapply wt_one, q_mb_out |].
      eapply K8; [exact H | eapply mb_cancel; exact H0].
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & _) | (b & m' & e & -> & ->)]].
    + exfalso. eapply H; eassumption.
    + discriminate.
    + injection e as <-.
      destruct (decide (ActOut aa ∈ n)) as [hin | hout].
      * eapply mb_split in hin as (n' & ->).
        exists (g Q0, n'). split; [eapply wt_one, q_mb_out |].
        rewrite mb_swap in H0. eapply mb_cancel in H0.
        eapply K9; [exact H | exact H0].
      * assert (hx : ActOut aa ∈ {[+ aOut +]} ⊎ n) by multiset_solver.
        eapply gmultiset_elem_of_disj_union in hx as [hx | hx]; [| contradiction].
        eapply gmultiset_elem_of_singleton in hx. rewrite hx in H0. rewrite hx.
        eapply mb_cancel in H0.
        exists (g 𝟘, n). split; [eapply q0_out_aOut |].
        eapply K8; [exact H | exact H0].
Qed.

Lemma mb_mono (x : ExtAct TypeOfActions) (u w : MO (ExtAct TypeOfActions)) :
  u ⊆ w -> {[+ x +]} ⊎ u ⊆ {[+ x +]} ⊎ w.
Proof. eapply gmultiset_disj_union_mono_l. Qed.

Lemma mb_weak (x : ExtAct TypeOfActions) (u w : MO (ExtAct TypeOfActions)) :
  u ⊆ w -> u ⊆ {[+ x +]} ⊎ w.
Proof. intro h. etransitivity; [exact h | eapply gmultiset_disj_union_subseteq_r]. Qed.

(** The point of the whole construction: once [ā] is in the ledger, the input
    that would fire the guard closes a feedback, so a feedback-free trace never
    offers it. *)
Lemma no_fb_aIn E (a : TypeOfActions) : no_fb_after E (ActIn a) -> aOut ∈ E -> a <> (c1, v0).
Proof.
  intros h hin e. subst a. unfold no_fb_after in h. rewrite List.Forall_forall in h.
  eapply (h aOut); [| reflexivity]. clear h.
  induction E as [|y E IH]; [inversion hin |].
  eapply elem_of_cons in hin as [-> | hin]; [left; reflexivity | right; eapply IH; exact hin].
Qed.

Lemma out_neq (a : TypeOfActions) : a <> (c1, v0) -> ActOut a <> aOut.
Proof. intros ne e. eapply ne. injection e as ->. reflexivity. Qed.

(** *** The blocking clause

    [q] answers every input by letting its mailbox absorb it, which keeps the
    invariant since both mailboxes grow by the same message.  In [K2] and [K3]
    the input [a] itself is excluded by [no_fb_aIn], and that is the only place
    where the hypothesis [no_fb_after] is used. *)
Lemma rel_b E p1 q1 (μ : ExtAct TypeOfActions) p2 :
  Rel E p1 q1 -> ¬ non_blocking μ -> no_fb_after E μ -> p1 ⟶[μ] p2 ->
  exists q2, q1 ⟹{μ} q2 /\ Rel E p2 q2.
Proof.
  intros hr nb hok l. destruct μ as [a | a]; [| exfalso; eapply nb; exists a; reflexivity].
  inversion hr; subst.
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & ->) | (b & m' & e & _ & _)]].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(c & x & y & _ & _ & e & _) | (c & x & y & _ & _ & e & _)]]].
      * eapply oA_inv in l as (e & _). discriminate.
      * eapply W_inv in l as (v & e & ->). injection e as ->.
        exists (g Q0, {[+ ActOut (c1, v) +]} ⊎ n). split; [eapply wt_one, q_mb_in |].
        destruct (Data_dec v v0) as [-> | ne].
        -- eapply K4. eapply mb_mono. exact H.
        -- eapply K7; [exact ne | eapply mb_weak; exact H].
      * discriminate.
      * discriminate.
    + injection e as <-.
      exists (g Q0, {[+ ActOut a +]} ⊎ n). split; [eapply wt_one, q_mb_in |].
      eapply K1. eapply mb_mono. exact H.
    + discriminate.
  - assert (hne : a <> (c1, v0)) by (eapply no_fb_aIn; eassumption).
    eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & ->) | (b & m' & e & _ & _)]].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(c & x & y & _ & _ & e & _) | (c & x & y & _ & _ & e & _)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply W_inv in l as (v & e & ->). injection e as ->.
        assert (ne : v <> v0) by (intro; subst; eapply hne; reflexivity).
        exists (g Q0, {[+ ActOut (c1, v) +]} ⊎ n). split; [eapply wt_one, q_mb_in |].
        eapply K9; [eapply dead_par; [eapply dead_zero | eapply dead_Gd; exact ne] |].
        etransitivity; [exact H | eapply mb_mono, mb_weak; reflexivity].
      * discriminate.
      * discriminate.
    + injection e as <-.
      exists (g Q0, {[+ ActOut a +]} ⊎ n). split; [eapply wt_one, q_mb_in |].
      eapply K2; [| exact H0]. rewrite mb_swap. eapply mb_mono. exact H.
    + discriminate.
  - assert (hne : a <> (c1, v0)) by (eapply no_fb_aIn; eassumption).
    eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & ->) | (b & m' & e & _ & _)]].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(c & x & y & _ & _ & e & _) | (c & x & y & _ & _ & e & _)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply W_inv in l as (v & e & ->). injection e as ->.
        assert (ne : v <> v0) by (intro; subst; eapply hne; reflexivity).
        exists (g 𝟘, {[+ ActOut (c1, v) +]} ⊎ n). split; [eapply wt_one, q_mb_in |].
        eapply K8; [eapply dead_par; [eapply dead_zero | eapply dead_Gd; exact ne] |].
        eapply mb_weak. exact H.
      * discriminate.
      * discriminate.
    + injection e as <-.
      exists (g 𝟘, {[+ ActOut a +]} ⊎ n). split; [eapply wt_one, q_mb_in |].
      eapply K3; [eapply mb_mono; exact H | exact H0 |].
      intro hm. eapply gmultiset_elem_of_disj_union in hm as [hm | hm]; [| contradiction].
      eapply gmultiset_elem_of_singleton in hm. eapply (out_neq a hne). symmetry. exact hm.
    + discriminate.
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & ->) | (b & m' & e & _ & _)]].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(c & x & y & _ & _ & e & _) | (c & x & y & _ & _ & e & _)]]].
      * eapply oA_inv in l as (e & _). discriminate.
      * eapply guard_step in l as (_ & e & _). discriminate.
      * discriminate.
      * discriminate.
    + injection e as <-.
      exists (g Q0, {[+ ActOut a +]} ⊎ n). split; [eapply wt_one, q_mb_in |].
      eapply K4. rewrite mb_swap. eapply mb_mono. exact H.
    + discriminate.
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & ->) | (b & m' & e & _ & _)]].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(c & x & y & _ & _ & e & _) | (c & x & y & _ & _ & e & _)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply guard_step in l as (_ & e & _). discriminate.
      * discriminate.
      * discriminate.
    + injection e as <-.
      exists (g Q0, {[+ ActOut a +]} ⊎ n). split; [eapply wt_one, q_mb_in |].
      eapply K5. eapply mb_mono. exact H.
    + discriminate.
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & ->) | (b & m' & e & _ & _)]].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(c & x & y & _ & _ & e & _) | (c & x & y & _ & _ & e & _)]]].
      * eapply oA_inv in l as (e & _). discriminate.
      * exfalso. eapply dead_zero; eassumption.
      * discriminate.
      * discriminate.
    + injection e as <-.
      exists (g 𝟘, {[+ ActOut a +]} ⊎ n). split; [eapply wt_one, q_mb_in |].
      eapply K6. rewrite mb_swap. eapply mb_mono. exact H.
    + discriminate.
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & ->) | (b & m' & e & _ & _)]].
    + eapply par_inv in l
        as [(x & l & ->) | [(x & l & ->) | [(c & x & y & _ & _ & e & _) | (c & x & y & _ & _ & e & _)]]].
      * eapply oA_inv in l as (e & _). discriminate.
      * eapply guard_step in l as (_ & e & _). discriminate.
      * discriminate.
      * discriminate.
    + injection e as <-.
      exists (g Q0, {[+ ActOut a +]} ⊎ n). split; [eapply wt_one, q_mb_in |].
      eapply K7; [exact H | eapply mb_mono; exact H0].
    + discriminate.
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & ->) | (b & m' & e & _ & _)]].
    + exfalso. eapply H; eassumption.
    + injection e as <-.
      exists (g 𝟘, {[+ ActOut a +]} ⊎ n). split; [eapply wt_one, q_mb_in |].
      eapply K8; [exact H | eapply mb_mono; exact H0].
    + discriminate.
  - eapply fw_act_inv in l as [(p' & l & ->) | [(b & e & ->) | (b & m' & e & _ & _)]].
    + exfalso. eapply H; eassumption.
    + injection e as <-.
      exists (g Q0, {[+ ActOut a +]} ⊎ n). split; [eapply wt_one, q_mb_in |].
      eapply K9; [exact H |]. rewrite mb_swap. eapply mb_mono. exact H0.
    + discriminate.
Qed.

(** ** The conclusion *)

Theorem Rel_rsim : rsim Rel.
Proof. split; [exact rel_tau | split; [exact rel_nb | exact rel_b]]. Qed.

Lemma Rel_init : Rel [] ((Bp2, mt) : st) (g Q0, mt).
Proof. eapply K1. multiset_solver. Qed.

(** Every feedback-free trace of [p] is a trace of [q]. *)
Theorem bp2_ff_included (s : trace (ExtAct TypeOfActions)) :
  ¬ has_fb s -> (exists r, ((Bp2, mt) : st) ⟹[s] r) -> exists r, ((g Q0, mt) : st) ⟹[s] r.
Proof.
  intros hff hp.
  eapply (rsim_traces_ff Rel Rel_rsim (Bp2, mt) (g Q0, mt) s Rel_init hff hp).
Qed.

(** But [ā ; a ; b̄] is a trace of [p] -- and, by [q_does_not], not one of [q]. *)
Lemma bp2_does : exists r, ((Bp2, mt) : st) ⟹[[aOut; aIn; bOut]] r.
Proof.
  eexists.
  eapply (wt_act _ _ _ ((𝟘 ‖ W), mt)).
  { eapply ParLeft. eapply lts_parL. eapply lts_output. }
  eapply (wt_act _ _ _ ((𝟘 ‖ (Gd ^ v0)), mt)).
  { eapply ParLeft. eapply lts_parR. eapply lts_input. }
  eapply (wt_act _ _ _ ((𝟘 ‖ (g 𝟘)), mt)).
  { eapply ParLeft. eapply lts_parR. eapply guard_v0_fires. }
  eapply wt_nil.
Qed.

(** Since the traces of [p] are closed under [fnf] ([wt_fnf]) and [fnf]
    produces feedback-free traces ([fnf_no_fb]), the inclusion above is exactly
    the preorder "every trace of [p], simplified, is a trace of [q]". *)
Corollary bp2_pre_fnf (s : trace (ExtAct TypeOfActions)) :
  (exists r, ((Bp2, mt) : st) ⟹[s] r) -> exists r, ((g Q0, mt) : st) ⟹[nlin (fnf s)] r.
Proof.
  intros (r & w). eapply wt_fnf in w as (r' & w' & _).
  eapply bp2_ff_included; [eapply fnf_no_fb | exists r'; exact w'].
Qed.

(** The answer to the open question: the preorder obtained by normalising *and*
    simplifying the feedbacks is *strictly weaker* than trace inclusion.  So

      p ≼_fnf q  <->  p ≼ₜᵢ q

    is false; only the left-to-right reading of [wt_fnf] survives. *)
Theorem feedback_free_strictly_weaker :
  (forall s, (exists r, ((Bp2, mt) : st) ⟹[s] r) -> exists r, ((g Q0, mt) : st) ⟹[nlin (fnf s)] r)
  /\ ¬ (forall s, (exists r, ((Bp2, mt) : st) ⟹[s] r) -> exists r, ((g Q0, mt) : st) ⟹[s] r).
Proof.
  split; [exact bp2_pre_fnf |].
  intro h. eapply q_does_not. eapply h. exact bp2_does.
Qed.

(** * The same failure on co-traces

    The question has an exact mirror on the co-trace side, and the answer is
    the same.  In VACCS the dual is unique, so a co-trace is nothing but the
    dual trace ([cowt_iff_wt]) and a co-feedback is nothing but a feedback of
    the dual trace ([co_nb_iff], [co_feedback_iff]).  The very same pair is
    therefore a counterexample, read through [co]: it is separated by the
    co-trace [a ; ā ; b], which carries a co-feedback ([co_s_has_feedback]).

    On the abstract [unique_nb]: it is not used here.  [dual_iff_co] is a
    computation inside the VACCS instance -- [simplify_match_input] and
    [simplify_match_output] -- which says what the dual of a VACCS label *is*;
    exhibiting a counterexample in a concrete calculus cannot avoid computing
    its duals.  What is avoided is the abstract appeal: the results below hold
    for an arbitrary [CoClassifier] ([coclassifier_eq]), so they never go
    through [CoClassifier_cls_co], the one instance of [NormalisationCo.v]
    proved from [unique_nb]. *)

Lemma dual_iff_co (μ η : ExtAct TypeOfActions) : dual μ η <-> η = co μ.
Proof.
  split.
  - intro d. destruct μ as [a | a];
      [eapply simplify_match_input in d | eapply simplify_match_output in d]; exact d.
  - intros ->. destruct μ as [a | a]; reflexivity.
Qed.

Lemma co_nb_iff (μ : ExtAct TypeOfActions) : co_non_blocking μ <-> non_blocking (co μ).
Proof.
  split.
  - intro h. eapply h. eapply dual_iff_co. symmetry. eapply co_involution.
  - intros nb μ' d. eapply dual_iff_co in d.
    rewrite d, co_involution_generic in nb. exact nb.
Qed.

(** A co-feedback [μ1 ; μ2] is exactly a pair of dual labels. *)
Lemma co_feedback_iff (μ1 μ2 : ExtAct TypeOfActions) : co_feedback μ1 μ2 <-> μ2 = co μ1.
Proof.
  split.
  - intro h. assert (d : dual (co μ2) (co μ1)).
    { eapply h; eapply dual_iff_co; symmetry; eapply co_involution_generic. }
    eapply dual_iff_co in d.
    rewrite <- (co_involution_generic μ2), d, co_involution_generic. reflexivity.
  - intros -> ν1 ν2 d1 d2.
    eapply dual_iff_co in d1. eapply dual_iff_co in d2.
    rewrite <- (co_involution_generic ν1), <- (co_involution_generic ν2), <- d1, <- d2.
    eapply dual_iff_co. rewrite co_involution_generic. reflexivity.
Qed.

#[local] Instance co_nb_dec (μ : ExtAct TypeOfActions) : Decision (co_non_blocking μ).
Proof.
  destruct (decide (non_blocking (co μ))) as [h | h];
    [left | right]; rewrite co_nb_iff; exact h.
Qed.

#[local] Instance co_fb_dec (μ1 μ2 : ExtAct TypeOfActions) : Decision (co_feedback μ1 μ2).
Proof.
  destruct (decide (μ2 = co μ1)) as [h | h];
    [left | right]; rewrite co_feedback_iff; exact h.
Qed.

(** [co] is a notation, so it needs a name of its own to be mapped over a
    co-trace. *)
Definition cov (x : ExtAct TypeOfActions) : ExtAct TypeOfActions := co x.

Lemma cov_invol (x : ExtAct TypeOfActions) : cov (cov x) = x.
Proof. eapply co_involution_generic. Qed.

Lemma map_cov_invol (s : trace (ExtAct TypeOfActions)) : map cov (map cov s) = s.
Proof.
  induction s as [| x s IH]; simpl; [reflexivity |]. rewrite cov_invol, IH. reflexivity.
Qed.

Lemma forall2_dual_map (s s' : trace (ExtAct TypeOfActions)) :
  ForAllHelper.Forall2 dual s s' <-> s' = map cov s.
Proof.
  split.
  - induction 1 as [| x y s t d _ IH]; simpl; [reflexivity |].
    eapply dual_iff_co in d. subst y. rewrite IH. reflexivity.
  - intros ->. induction s as [| x s IH]; simpl; constructor;
      [eapply dual_iff_co; reflexivity | exact IH].
Qed.

(** A co-trace is the dual trace. *)
Lemma cowt_iff_wt (p q : st) s : p ⟹ᶜᵒ[s] q <-> p ⟹[map cov s] q.
Proof.
  split.
  - intro w. eapply cowt_to_wt_dual in w as (s' & hf & w').
    eapply forall2_dual_map in hf. subst s'. exact w'.
  - intro w. eapply wt_to_cowt_dual; [exact w | eapply forall2_dual_map; reflexivity].
Qed.

Lemma co_nb_iff' (μ : ExtAct TypeOfActions) : co_non_blocking μ <-> non_blocking (cov μ).
Proof. exact (co_nb_iff μ). Qed.

Lemma co_feedback_iff' (μ1 μ2 : ExtAct TypeOfActions) : co_feedback μ1 μ2 <-> μ2 = cov μ1.
Proof. exact (co_feedback_iff μ1 μ2). Qed.

Theorem co_bp2_ff_included (s : trace (ExtAct TypeOfActions)) :
  ¬ has_fb (map cov s) ->
  (exists r, ((Bp2, mt) : st) ⟹ᶜᵒ[s] r) -> exists r, ((g Q0, mt) : st) ⟹ᶜᵒ[s] r.
Proof.
  intros hff (r & w). eapply cowt_iff_wt in w.
  destruct (bp2_ff_included (map cov s) hff (ex_intro _ r w)) as (r' & w').
  exists r'. eapply cowt_iff_wt. exact w'.
Qed.

(** The discriminating co-trace [a ; ā ; b] -- the dual of [ā ; a ; b̄]. *)
Definition bIn : ExtAct TypeOfActions := ActIn (c2, v0).
Definition co_s : trace (ExtAct TypeOfActions) := [aIn; aOut; bIn].

Lemma map_cov_co_s : map cov co_s = [aOut; aIn; bOut].
Proof. vm_compute. reflexivity. Qed.

Lemma co_s_has_feedback : co_non_blocking aIn /\ co_feedback aIn aOut.
Proof.
  split.
  - eapply co_nb_iff'. exists (c1, v0). vm_compute. reflexivity.
  - eapply co_feedback_iff'. vm_compute. reflexivity.
Qed.

Lemma co_bp2_does : exists r, ((Bp2, mt) : st) ⟹ᶜᵒ[co_s] r.
Proof.
  destruct bp2_does as (r & w). exists r.
  eapply cowt_iff_wt. rewrite map_cov_co_s. exact w.
Qed.

Lemma co_q_does_not : ¬ exists r, ((g Q0, mt) : st) ⟹ᶜᵒ[co_s] r.
Proof.
  intros (r & w). eapply cowt_iff_wt in w. rewrite map_cov_co_s in w.
  eapply q_does_not. exists r. exact w.
Qed.

(** ** Independence from the classifier

    [NormalisationCo.v] never assumes that the dual is unique: the class of a
    label of a co-trace is whatever a [CoClassifier] says, and the only
    instance it exhibits, [CoClassifier_cls_co], is the one place where
    [unique_nb] is used.  The statement below avoids it: on VACCS *every*
    [CoClassifier] is [cls_tr ∘ co], so the normal form -- and hence the
    counterexample -- does not depend on which one is taken, nor on the
    instance of [NormalisationCo.v]. *)

Lemma co_exist_co_nba_iff (μ : ExtAct TypeOfActions) :
  co_exist_co_nba μ <-> exist_co_nba (cov μ).
Proof.
  split.
  - intros (η & nb & h). exists η. split; [exact nb |].
    eapply h. eapply dual_iff_co. symmetry. eapply cov_invol.
  - intros (η & nb & d). exists η. split; [exact nb |].
    intros nu dnu. eapply dual_iff_co in dnu.
    assert (e : nu = cov μ) by (rewrite dnu; symmetry; eapply cov_invol).
    rewrite e. exact d.
Qed.

Lemma coclassifier_eq (cls : ExtAct TypeOfActions -> act_class) `{!CoClassifier cls}
  (μ : ExtAct TypeOfActions) : cls μ = cls_tr (cov μ).
Proof.
  assert (bnb : cls μ = CNB <-> cls_tr (cov μ) = CNB).
  { rewrite cls_CNB_iff, co_nb_iff', cls_tr_CNB. reflexivity. }
  assert (bin : cls μ = CIN <-> cls_tr (cov μ) = CIN).
  { rewrite cls_CIN_iff, co_exist_co_nba_iff, cls_tr_CIN. reflexivity. }
  destruct (cls μ) as [ | | ] eqn:e1; destruct (cls_tr (cov μ)) as [ | | ] eqn:e2;
    try reflexivity; exfalso.
  - discriminate (proj1 bnb eq_refl).
  - discriminate (proj1 bnb eq_refl).
  - discriminate (proj1 bin eq_refl).
  - discriminate (proj1 bin eq_refl).
  - discriminate (proj2 bnb eq_refl).
  - discriminate (proj2 bin eq_refl).
Qed.

(** ** The conclusion on co-traces, for an arbitrary classifier *)

Section AnyCoClassifier.

  Context `{!forall μ : ExtAct TypeOfActions, Decision (co_non_blocking μ)}.
  Context `{!forall μ1 μ2 : ExtAct TypeOfActions, Decision (co_feedback μ1 μ2)}.
  Context (kls : ExtAct TypeOfActions -> act_class) `{!CoClassifier kls}.

  (** No co-feedback in [co_fbnf s] means no feedback in its dual trace. *)
  Lemma no_fb_cov_co_fbnf (s : trace (ExtAct TypeOfActions)) :
    ¬ has_fb (map cov (co_fbnf s)).
  Proof.
    intro h. eapply has_fb_decomp in h as (s1 & η & s2 & μ & s3 & e & nb & d).
    assert (e2 : co_fbnf s = map cov s1 ++ cov η :: (map cov s2 ++ cov μ :: map cov s3)).
    { rewrite <- (map_cov_invol (co_fbnf s)), e, !map_app. simpl.
      rewrite map_app. simpl. reflexivity. }
    eapply (co_fbnf_feedback_free s _ _ _ (cov η) (cov μ) e2).
    - eapply co_nb_iff'. rewrite cov_invol. exact nb.
    - eapply co_feedback_iff'. rewrite cov_invol. symmetry. eapply dual_iff_co. exact d.
  Qed.

  (** And the regrouping into multisets exposes none, by [has_fb_tequiv]. *)
  Lemma no_fb_cov_co_fnf (s : trace (ExtAct TypeOfActions)) :
    ¬ has_fb (map cov (nlin (co_fnf kls s))).
  Proof.
    intro h. eapply (no_fb_cov_co_fbnf s).
    eapply has_fb_tequiv; [| exact h].
    eapply (tequiv_map cov kls cls_tr); [intro x; symmetry; exact (coclassifier_eq kls x) |].
    exact (tequiv_sym kls (co_fbnf s) (nlin (nform kls (co_fbnf s)))
             (tequiv_nform kls (co_fbnf s))).
  Qed.

  Corollary co_bp2_pre_fnf (s : trace (ExtAct TypeOfActions)) :
    (exists r, ((Bp2, mt) : st) ⟹ᶜᵒ[s] r) ->
    exists r, ((g Q0, mt) : st) ⟹ᶜᵒ[nlin (co_fnf kls s)] r.
  Proof.
    intros (r & w).
    destruct (cowt_co_fnf kls (Bp2, mt) r s w) as (r' & w' & _).
    eapply co_bp2_ff_included; [eapply no_fb_cov_co_fnf | exists r'; exact w'].
  Qed.

  (** The co-trace answer: the co-preorder obtained by normalising *and*
      simplifying the co-feedbacks is strictly weaker than co-trace inclusion,
      exactly as on traces -- whichever classifier is used. *)
  Theorem co_feedback_free_strictly_weaker :
    (forall s, (exists r, ((Bp2, mt) : st) ⟹ᶜᵒ[s] r) ->
               exists r, ((g Q0, mt) : st) ⟹ᶜᵒ[nlin (co_fnf kls s)] r)
    /\ ¬ (forall s, (exists r, ((Bp2, mt) : st) ⟹ᶜᵒ[s] r) ->
                    exists r, ((g Q0, mt) : st) ⟹ᶜᵒ[s] r).
  Proof.
    split; [exact co_bp2_pre_fnf |].
    intro h. eapply co_q_does_not. eapply h. exact co_bp2_does.
  Qed.

End AnyCoClassifier.

(** * Reading [fnf] directly on a co-trace does not work

    It is tempting to drop [co_fnf] and keep the ordinary [fnf], only replacing
    [⟹] by [⟹ᶜᵒ].  That is unsound, and for a structural reason: on a co-trace
    the two classes are *exchanged*.

    A label [μ] of a co-trace is realised by an action [ν] of the process with
    [dual ν μ].  What may be postponed along [⟹ᶜᵒ] is the label whose realising
    action is an output, that is [co_non_blocking μ] -- the label the observer
    *inputs*.  [cls_tr] calls [CNB] the label that is itself non-blocking --
    the label the observer *outputs*.  The two are opposite, which is exactly
    what [coclassifier_eq] says in the positive form: a [CoClassifier] is
    [cls_tr ∘ co], never [cls_tr]. *)

Lemma cls_tr_aOut_CNB : cls_tr aOut = CNB.
Proof. vm_compute. reflexivity. Qed.

Lemma co_nb_aOut_false : ¬ co_non_blocking aOut.
Proof. rewrite co_nb_iff'. intros (a & e). vm_compute in e. discriminate. Qed.

Theorem cls_tr_not_a_coclassifier :
  ¬ (forall μ : ExtAct TypeOfActions, cls_tr μ = CNB <-> co_non_blocking μ).
Proof. intro h. eapply co_nb_aOut_false, h, cls_tr_aOut_CNB. Qed.

(** ** A co-trace that [fnf] wrongly simplifies

    [Pin] waits for a message on [c1] and then emits [ā] and [b̄].  The observer
    sends [a], receives [ā] back and receives [b̄]: the co-trace [ā ; a ; b].

    Read with [cls_tr], the head [ā] is [CNB] and the next label [a] is its
    dual, so [fnf] sees a feedback and erases both, leaving [b].  But [Pin]
    cannot emit [b̄] before receiving anything: [fnf_unsound_on_cotraces].

    Read with a [CoClassifier], nothing happens: [ā] is not [co_non_blocking]
    -- the process *receives* there -- so there is no co-feedback to consume.
    That is the correct reading. *)

Definition Pin : proc := g (c1 ? (oA ‖ oB)).
Definition s_bad : trace (ExtAct TypeOfActions) := [aOut; aIn; bIn].

Lemma fnf_s_bad : nlin (fnf s_bad) = [bIn].
Proof. vm_compute. reflexivity. Qed.

Lemma Pin_subst : (oA ‖ oB) ^ v0 = oA ‖ oB.
Proof. vm_compute. reflexivity. Qed.

Lemma pin_cowt : exists r, ((Pin, mt) : st) ⟹ᶜᵒ[s_bad] r.
Proof.
  eexists.
  eapply (cowt_act aOut aIn _ _ ((oA ‖ oB), mt)).
  { reflexivity. }
  { eapply ParLeft. rewrite <- Pin_subst. eapply lts_input. }
  eapply (cowt_act aIn aOut _ _ ((𝟘 ‖ oB), mt)).
  { reflexivity. }
  { eapply ParLeft. eapply lts_parL. eapply lts_output. }
  eapply (cowt_act bIn bOut _ _ ((𝟘 ‖ 𝟘), mt)).
  { reflexivity. }
  { eapply ParLeft. eapply lts_parR. eapply lts_output. }
  eapply cowt_nil.
Qed.

Lemma Pin_inv α r : lts Pin α r -> exists v, α = ActExt (ActIn (c1, v)) /\ r = (oA ‖ oB) ^ v.
Proof. intro l. inversion l; subst. exists v. split; reflexivity. Qed.

Lemma pin_stable : ((Pin, mt) : st) ↛.
Proof. eapply stable_of_no_tau. intros p' l. eapply Pin_inv in l as (v & e & _). discriminate. Qed.

Lemma pin_no_bOut : ((Pin, mt) : st) ↛[bOut].
Proof.
  destruct (decide (((Pin, mt) : st) ↛[bOut])) as [h | h]; [exact h |].
  exfalso. eapply lts_refuses_spec1 in h as (r & l).
  eapply fw_act_inv in l as [(p' & l' & _) | [(a & e & _) | (a & m' & _ & e & _)]].
  - eapply Pin_inv in l' as (v & e & _). discriminate.
  - discriminate.
  - unfold mt in e. multiset_solver.
Qed.

(** The analogue of [wt_fnf] for [⟹ᶜᵒ] and [fnf] is false. *)
Theorem fnf_unsound_on_cotraces :
  (exists r, ((Pin, mt) : st) ⟹ᶜᵒ[s_bad] r)
  /\ ¬ (exists r, ((Pin, mt) : st) ⟹ᶜᵒ[nlin (fnf s_bad)] r).
Proof.
  split; [exact pin_cowt |].
  rewrite fnf_s_bad. intros (r & w). eapply cowt_iff_wt in w.
  eapply (no_wt_of_refuses (Pin, mt) bOut [] pin_stable pin_no_bOut).
  exists r. exact w.
Qed.

(** ** The co-trace statement with [fnf] alone

    [fnf] can still be the only normal form in the statement, provided it is
    applied where it makes sense: to the dual trace.  [co_nf] normalises a
    co-trace by dualising it, running the ordinary [fnf], and dualising back --
    no [co_fnf], no [CoClassifier].  By [cowt_iff_wt] this is literally the
    trace statement read through [co], so the answer on co-traces is the answer
    on traces: the same pair, the same conclusion. *)

Definition co_nf (s : trace (ExtAct TypeOfActions)) : trace (ExtAct TypeOfActions) :=
  map cov (nlin (fnf (map cov s))).

Corollary co_bp2_pre_nf (s : trace (ExtAct TypeOfActions)) :
  (exists r, ((Bp2, mt) : st) ⟹ᶜᵒ[s] r) -> exists r, ((g Q0, mt) : st) ⟹ᶜᵒ[co_nf s] r.
Proof.
  intros (r & w). eapply cowt_iff_wt in w.
  destruct (bp2_pre_fnf (map cov s) (ex_intro _ r w)) as (r' & w').
  exists r'. eapply cowt_iff_wt. unfold co_nf. rewrite map_cov_invol. exact w'.
Qed.

Theorem co_feedback_free_strictly_weaker_fnf :
  (forall s, (exists r, ((Bp2, mt) : st) ⟹ᶜᵒ[s] r) ->
             exists r, ((g Q0, mt) : st) ⟹ᶜᵒ[co_nf s] r)
  /\ ¬ (forall s, (exists r, ((Bp2, mt) : st) ⟹ᶜᵒ[s] r) ->
                  exists r, ((g Q0, mt) : st) ⟹ᶜᵒ[s] r).
Proof.
  split; [exact co_bp2_pre_nf |].
  intro h. eapply co_q_does_not. eapply h. exact co_bp2_does.
Qed.

(** ** Where [cls_tr] *is* harmless: the grouping

    The exchange of the classes above is fatal to the feedback step, but not to
    the grouping.  [nform] only reads the partition the classifier induces, not
    the names of the classes ([nlin_nform_same]); on VACCS both [cls_tr] and
    any [CoClassifier] split the labels into outputs and inputs, they merely
    call the two parts by opposite names.  So the normalised co-trace is the
    same either way, and the may characterisation on normalised co-traces can
    be stated with [cls_tr] alone, with no [CoClassifier] in sight.

    It is the feedback simplification that must dualise, and only it. *)

Lemma cls_tr_never_COP (x : ExtAct TypeOfActions) : cls_tr x <> COP.
Proof. destruct x as [a | a]; vm_compute; discriminate. Qed.

Lemma cls_tr_cov_COP (x : ExtAct TypeOfActions) : cls_tr (cov x) = COP <-> cls_tr x = COP.
Proof.
  split; intro h; exfalso;
    [eapply (cls_tr_never_COP (cov x)) | eapply (cls_tr_never_COP x)]; exact h.
Qed.

Lemma cls_tr_cov_part (x y : ExtAct TypeOfActions) :
  cls_tr (cov x) = cls_tr (cov y) <-> cls_tr x = cls_tr y.
Proof.
  destruct x as [a | a]; destruct y as [b | b]; vm_compute;
    split; intro h; (reflexivity || discriminate h).
Qed.

Theorem nlin_nform_coclassifier (kls : ExtAct TypeOfActions -> act_class) `{!CoClassifier kls}
  (s : trace (ExtAct TypeOfActions)) : nlin (nform kls s) = nlin (nform cls_tr s).
Proof.
  transitivity (nlin (nform (fun μ => cls_tr (cov μ)) s)).
  - eapply nlin_nform_same.
    + intro x. rewrite (coclassifier_eq kls x). reflexivity.
    + intros x y. rewrite (coclassifier_eq kls x), (coclassifier_eq kls y). reflexivity.
  - eapply nlin_nform_same; [eapply cls_tr_cov_COP | eapply cls_tr_cov_part].
Qed.

(** * The preorder read on normalised traces on both sides

    [bhv_pre_ti_fnf] quantifies over the normalised traces on both sides, in
    the style of [bhv_pre_ti_nf]; [bhv_pre_ti_fnf_iff] shows it agrees with the
    reading used above.  It is the stronger of the two to establish, and it
    comes for free here: a normalised trace carries no feedback, so
    [bp2_ff_included] applies to it directly. *)

Theorem bp2_pre_ti_fnf (s : trace (ExtAct TypeOfActions)) :
  (exists r, ((Bp2, mt) : st) ⟹[nlin (fnf s)] r) ->
  exists r, ((g Q0, mt) : st) ⟹[nlin (fnf s)] r.
Proof. exact (bp2_ff_included (nlin (fnf s)) (fnf_no_fb s)). Qed.

Theorem feedback_free_strictly_weaker_nf :
  (forall s, (exists r, ((Bp2, mt) : st) ⟹[nlin (fnf s)] r) ->
             exists r, ((g Q0, mt) : st) ⟹[nlin (fnf s)] r)
  /\ ¬ (forall s, (exists r, ((Bp2, mt) : st) ⟹[s] r) ->
                  exists r, ((g Q0, mt) : st) ⟹[s] r).
Proof.
  split; [exact bp2_pre_ti_fnf |].
  intro h. eapply q_does_not. eapply h. exact bp2_does.
Qed.
