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
     coWeakTransition Termination Convergence NormalForm Normalisation
     RestrictedSimulation Subset_Act coConvergence DefinitionAS DefinitionASco.

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

Lemma dual_iff_co (μ η : ExtAct TypeOfActions) : dual μ η <-> η = co μ.
Proof.
  split.
  - intro d. destruct μ as [a | a];
      [eapply simplify_match_input in d | eapply simplify_match_output in d]; exact d.
  - intros ->. destruct μ as [a | a]; reflexivity.
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

Definition bIn : ExtAct TypeOfActions := ActIn (c2, v0).
Definition co_s : trace (ExtAct TypeOfActions) := [aIn; aOut; bIn].



(** ** A co-trace that [fnf] wrongly simplifies

    [Pin] waits for a message on [c1] and then emits [ā] and [b̄].  The observer
    sends [a], receives [ā] back and receives [b̄]: the co-trace [ā ; a ; b].

    Read with [cls_tr], the head [ā] is [CNB] and the next label [a] is its
    dual, so [fnf] sees a feedback and erases both, leaving [b].  But [Pin]
    cannot emit [b̄] before receiving anything: [fnf_unsound_on_cotraces].

    So [fnf] read on a co-trace consumes the wrong pairs, and the mistake is
    structural: on a co-trace [has_fb] designates an *output of the observer*
    followed by its dual input, that is the process receiving a message and
    echoing it back later -- not the process emitting and receiving its own
    message, which is what [wt_annhil] annihilates. *)

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

(** * The must side: the feedback cannot be simplified either

    The must characterisations of [NormalisationMust.v] rest on convergence,
    and convergence travels along the trace preorder in the *opposite*
    direction to the traces ([cnv_trace_leq] is contravariant).  That already
    says the feedback simplification cannot be used there the way [nform] is;
    this section makes it concrete.

    Two facts are proved:

    - [cnv_fnf_not_reversible]: a process may converge on a trace carrying a
      feedback and *not* on its simplification.  So the quantification over
      traces in [bhv_pre_cond1] cannot be collapsed onto the simplified ones,
      the way [cnv_norm] collapses it onto the normalised ones.
    - [must_cond1_separated]: a pair [p], [q] with [p ⇓ s] and [¬ q ⇓ s] for a
      trace [s] carrying a feedback -- the negative half of a counterexample to
      the feedback-simplified must preorder.

    The divergence used is [Dv = rec x • 𝛕 • x]. *)

Definition c3 : ChannelData := cst 3.
Definition Dv : proc := rec 0 • (𝛕 • (pr_var 0)).
Definition cIn : ExtAct TypeOfActions := ActIn (c3, v0).

(** [b̄ ; b ; c]: the feedback pair [b̄ ; b], then an input on a third channel.
    Its simplification is [c]. *)
Definition s_must : trace (ExtAct TypeOfActions) := [bOut; bIn; cIn].

(** [Gd2] diverges on the co-action of [b̄], and only on it. *)
Definition Gd2 : proc := If (Equality (bvar 0) v0) Then Dv Else 𝟘.
Definition Wc2 : proc := g (c2 ? Gd2).
Definition Wc3 : proc := g (c3 ? Wc2).

(** [p] diverges as soon as it receives on [c3] -- and has no output at all. *)
Definition Pdv : proc := g (c3 ? Dv).

(** [q] emits [b̄]; after a message on [c3] it starts listening on [c2], where
    the co-action of [b̄] makes it diverge. *)
Definition Qdv : proc := oB ‖ Wc3.

(** ** The divergence *)

Lemma Dv_subst (v : ValueData) : Dv ^ v = Dv.
Proof. vm_compute. reflexivity. Qed.

Lemma Wc2_subst (v : ValueData) : Wc2 ^ v = Wc2.
Proof. vm_compute. reflexivity. Qed.

Lemma Dv_step : lts Dv τ (g (𝛕 • Dv)).
Proof. exact (@lts_recursion _ 0 (g (𝛕 • (pr_var 0)))). Qed.

Lemma Dv_step2 : lts (g (𝛕 • Dv)) τ Dv.
Proof. eapply lts_tau. Qed.

(** A two-state [τ]-cycle never terminates. *)
Lemma loop_not_term (x y : st) : x ⟶ y -> y ⟶ x -> ¬ x ⤓.
Proof.
  intros lxy lyx hx.
  assert (h : forall z : st, z ⤓ -> z = x \/ z = y -> False).
  { intros z hz. induction hz as [z hz IH]. intros [-> | ->].
    - eapply (IH y lxy). now right.
    - eapply (IH x lyx). now left. }
  eapply (h x hx). now left.
Qed.

Lemma par_Dv_not_term (X : proc) (m : MO (ExtAct TypeOfActions)) : ¬ ((X ‖ Dv, m) : st) ⤓.
Proof.
  eapply (loop_not_term _ ((X ‖ (g (𝛕 • Dv))), m)).
  - eapply ParLeft. eapply lts_parR. eapply Dv_step.
  - eapply ParLeft. eapply lts_parR. eapply Dv_step2.
Qed.

Lemma Dv_not_term (m : MO (ExtAct TypeOfActions)) : ¬ ((Dv, m) : st) ⤓.
Proof.
  eapply (loop_not_term _ ((g (𝛕 • Dv)), m)).
  - eapply ParLeft. eapply Dv_step.
  - eapply ParLeft. eapply Dv_step2.
Qed.

(** ** Inversion tools for convergence *)

Lemma cnv_nil_term (x : st) : x ⇓ [] -> x ⤓.
Proof. intro h. inversion h; subst. assumption. Qed.

Lemma cnv_act_inv (x : st) (μ : ExtAct TypeOfActions) s :
  x ⇓ (μ :: s) -> forall y, x ⟹{μ} y -> y ⇓ s.
Proof. intro h. inversion h; subst. assumption. Qed.

Lemma stable_term (x : st) : x ↛ -> x ⤓.
Proof.
  intro hst. eapply tstep. intros y l. exfalso.
  eapply (lts_refuses_spec2 x τ); [exists y; exact l | exact hst].
Qed.

Lemma not_term_step (x y : st) : x ⟶ y -> ¬ y ⤓ -> ¬ x ⤓.
Proof. intros l hy hx. inversion hx as [h]. eapply hy, h, l. Qed.

(** ** [p] converges on the feedback trace, not on its simplification *)

Lemma Pdv_inv α r : lts Pdv α r -> exists v, α = ActExt (ActIn (c3, v)) /\ r = Dv.
Proof. intro l. inversion l; subst. exists v. split; [reflexivity | eapply Dv_subst]. Qed.

Lemma Pdv_stable : ((Pdv, mt) : st) ↛.
Proof. eapply stable_of_no_tau. intros p' l. eapply Pdv_inv in l as (v & e & _). discriminate. Qed.

Lemma Pdv_no_bOut : ((Pdv, mt) : st) ↛[bOut].
Proof.
  destruct (decide (((Pdv, mt) : st) ↛[bOut])) as [h | h]; [exact h |].
  exfalso. eapply lts_refuses_spec1 in h as (r & l).
  eapply fw_act_inv in l as [(p' & l' & _) | [(a & e & _) | (a & m' & _ & e & _)]].
  - eapply Pdv_inv in l' as (v & e & _). discriminate.
  - discriminate.
  - unfold mt in e. multiset_solver.
Qed.

(** [p] has no [b̄] at all, so it converges on [s_must] vacuously. *)
Lemma pdv_cnv : ((Pdv, mt) : st) ⇓ s_must.
Proof.
  eapply cnv_act; [eapply stable_term, Pdv_stable |].
  intros q w. exfalso.
  eapply (no_wt_of_refuses (Pdv, mt) bOut [] Pdv_stable Pdv_no_bOut). exists q. exact w.
Qed.

(** But the simplified trace starts with the input that makes it diverge. *)
Lemma pdv_not_cnv : ¬ ((Pdv, mt) : st) ⇓ [cIn].
Proof.
  intro h. eapply (Dv_not_term mt). eapply cnv_nil_term.
  eapply (cnv_act_inv _ _ _ h (Dv, mt)).
  eapply wt_one. eapply ParLeft. rewrite <- (Dv_subst v0). eapply lts_input.
Qed.

Lemma fnf_s_must : nlin (fnf s_must) = [cIn].
Proof. vm_compute. reflexivity. Qed.

Lemma s_must_has_fb : has_fb s_must.
Proof. simpl. left. split; [exists (c2, v0); reflexivity | constructor; reflexivity]. Qed.

(** Convergence is not transported along the feedback simplification: the
    counterpart of [cnv_norm] fails for [fnf]. *)
Theorem cnv_fnf_not_reversible :
  has_fb s_must
  /\ ((Pdv, mt) : st) ⇓ s_must
  /\ ¬ ((Pdv, mt) : st) ⇓ (nlin (fnf s_must)).
Proof.
  split; [exact s_must_has_fb |]. split; [exact pdv_cnv |].
  rewrite fnf_s_must. exact pdv_not_cnv.
Qed.

(** ** [q] does not converge on the feedback trace

    After emitting [b̄], receiving it back and receiving on [c3], the mailbox of
    [q] holds [b̄] and the process is listening on [c2]: the forwarder feeds it
    the co-action of [b̄], the guard fires, and [q] diverges. *)

Lemma guard2_diverges (m : MO (ExtAct TypeOfActions)) : ¬ ((𝟘 ‖ (Gd2 ^ v0), m) : st) ⤓.
Proof.
  eapply not_term_step with (y := ((𝟘 ‖ (g (𝛕 • Dv))), m)).
  - eapply ParLeft. eapply lts_parR. eapply lts_ifOne; [vm_compute; reflexivity | eapply Dv_step].
  - eapply not_term_step with (y := ((𝟘 ‖ Dv), m)).
    + eapply ParLeft. eapply lts_parR. eapply Dv_step2.
    + eapply par_Dv_not_term.
Qed.

Lemma wc2_mailbox_diverges (m : MO (ExtAct TypeOfActions)) :
  ¬ ((𝟘 ‖ Wc2, {[+ bOut +]} ⊎ m) : st) ⤓.
Proof.
  eapply not_term_step with (y := ((𝟘 ‖ (Gd2 ^ v0)), m)).
  - eapply (ParSync bIn bOut).
    + split; [reflexivity | exists (c2, v0); reflexivity].
    + eapply lts_parR. eapply lts_input.
    + eapply lts_multiset_minus. exists (c2, v0). reflexivity.
  - eapply guard2_diverges.
Qed.

Theorem qdv_not_cnv : ¬ ((Qdv, mt) : st) ⇓ s_must.
Proof.
  intro h.
  assert (w1 : ((Qdv, mt) : st) ⟹{bOut} ((𝟘 ‖ Wc3), mt)).
  { eapply wt_one. eapply ParLeft. eapply lts_parL. eapply lts_output. }
  unfold s_must in h.
  pose proof (cnv_act_inv _ _ _ h _ w1) as h1.
  assert (w2 : (((𝟘 ‖ Wc3), mt) : st) ⟹{bIn} ((𝟘 ‖ Wc3), {[+ bOut +]} ⊎ mt)).
  { eapply wt_one. eapply (q_mb_in _ _ (c2, v0)). }
  pose proof (cnv_act_inv _ _ _ h1 _ w2) as h2.
  assert (w3 : (((𝟘 ‖ Wc3), {[+ bOut +]} ⊎ mt) : st) ⟹{cIn} ((𝟘 ‖ Wc2), {[+ bOut +]} ⊎ mt)).
  { eapply wt_one. eapply ParLeft. eapply lts_parR.
    rewrite <- (Wc2_subst v0). eapply lts_input. }
  pose proof (cnv_act_inv _ _ _ h2 _ w3) as h3.
  eapply (wc2_mailbox_diverges mt). eapply cnv_nil_term. exact h3.
Qed.

(** The pair is separated on a trace carrying a feedback, by the termination
    condition alone.

    What is *not* proved here is the other half -- that [p] and [q] satisfy the
    must conditions on every feedback-free trace.  That needs the convergence
    counterpart of [RestrictedSimulation.v]: a relation reflecting termination
    and simulating [q] by [p], restricted by the same ledger. *)
Theorem must_cond1_separated :
  has_fb s_must
  /\ ((Pdv, mt) : st) ⇓ s_must
  /\ ¬ ((Qdv, mt) : st) ⇓ s_must.
Proof. split; [exact s_must_has_fb |]. split; [exact pdv_cnv | exact qdv_not_cnv]. Qed.

(** ** The other half: [p] and [q] agree on the feedback-free traces

    The tool is [csim] of [RestrictedSimulation.v]: a relation simulating [q]
    by [p] and reflecting termination, restricted by the ledger. *)

(** *** When [p] terminates

    [p = c3 ? Ω] is stable unless its mailbox holds a message on [c3], in which
    case the forwarder feeds it and it diverges.  So [p ⤓] is exactly "no [c3]
    message in the mailbox" -- and any trace offering [c3] to a live [p] makes
    [p ⇓] fail, which is what makes those obligations void. *)

Definition no_c3 (m : MO (ExtAct TypeOfActions)) : Prop := forall v, ActOut (c3, v) ∉ m.

Lemma Pdv_stable_gen (m : MO (ExtAct TypeOfActions)) : no_c3 m -> ((Pdv, m) : st) ↛.
Proof.
  intro hno.
  destruct (decide (((Pdv, m) : st) ↛)) as [h | h]; [exact h |].
  exfalso. eapply lts_refuses_spec1 in h as (r & l).
  eapply fw_tau_inv in l as [(p' & l' & _) | (a & p' & m' & l' & -> & _)].
  - eapply Pdv_inv in l' as (v & e & _). discriminate.
  - eapply Pdv_inv in l' as (v & e & _). injection e as ->.
    eapply (hno v). multiset_solver.
Qed.

Lemma Pdv_term_gen (m : MO (ExtAct TypeOfActions)) : no_c3 m -> ((Pdv, m) : st) ⤓.
Proof. intro h. eapply stable_term, Pdv_stable_gen, h. Qed.

Lemma Pdv_c3_not_term (v : ValueData) (m : MO (ExtAct TypeOfActions)) :
  ActOut (c3, v) ∈ m -> ¬ ((Pdv, m) : st) ⤓.
Proof.
  intro hin. eapply mb_split in hin as (m' & ->).
  eapply not_term_step with (y := ((Dv, m') : st)); [| eapply Dv_not_term].
  eapply (ParSync (ActIn (c3, v)) (ActOut (c3, v))).
  - split; [reflexivity | exists (c3, v); reflexivity].
  - rewrite <- (Dv_subst v). eapply lts_input.
  - eapply lts_multiset_minus. exists (c3, v). reflexivity.
Qed.

Lemma Pdv_term_no_c3 (m : MO (ExtAct TypeOfActions)) : ((Pdv, m) : st) ⤓ -> no_c3 m.
Proof. intros ht v hin. eapply (Pdv_c3_not_term v m hin ht). Qed.

(** *** The states of [q] that can no longer diverge

    Once [b̄] has left through [oB], the only way back to [Ω] is the co-action
    of [b̄] reaching the guard, and that message can only come from the mailbox.
    A [qgood] process with no [b̄] in its mailbox is therefore safe forever --
    provided the trace never offers [b] again, which is exactly what the ledger
    guarantees. *)

Lemma Gd2_subst (v : ValueData) : Gd2 ^ v = If (Equality v v0) Then Dv Else 𝟘.
Proof. vm_compute. reflexivity. Qed.

Lemma Dv_inv α r : lts Dv α r -> α = τ /\ r = g (𝛕 • Dv).
Proof. intro l. inversion l; subst. split; reflexivity. Qed.

Lemma Gd2_step (v : ValueData) α r : lts (Gd2 ^ v) α r -> v = v0 /\ α = τ /\ r = g (𝛕 • Dv).
Proof.
  rewrite Gd2_subst. intro l. inversion l; subst.
  - eapply Dv_inv in H5 as (-> & ->). split; [eapply fires_eq; exact H4 | split; reflexivity].
  - inversion H5.
Qed.

Lemma Gd2_dead (v : ValueData) : v <> v0 -> dead (Gd2 ^ v).
Proof. intros ne α r l. eapply Gd2_step in l as (e & _ & _). exact (ne e). Qed.

Lemma Wc3_inv α r : lts Wc3 α r -> exists v, α = ActExt (ActIn (c3, v)) /\ r = Wc2.
Proof. intro l. inversion l; subst. exists v. split; [reflexivity | eapply Wc2_subst]. Qed.

Lemma Wc2_inv α r : lts Wc2 α r -> exists v, α = ActExt (ActIn (c2, v)) /\ r = Gd2 ^ v.
Proof. intro l. inversion l; subst. exists v. split; reflexivity. Qed.

Inductive qgood : proc -> Prop :=
| qg_wc3 : qgood (𝟘 ‖ Wc3)
| qg_wc2 : qgood (𝟘 ‖ Wc2)
| qg_gd v : v <> v0 -> qgood (𝟘 ‖ (Gd2 ^ v))
| qg_nil : qgood (𝟘 ‖ 𝟘).

Lemma qgood_no_tau (X : proc) : qgood X -> forall r, ¬ lts X τ r.
Proof.
  intros hg r l.
  destruct hg as [ | | v ne | ];
    eapply par_inv in l
      as [(x & l' & _) | [(x & l' & _) | [(b & x & y & l1 & _ & _ & _) | (b & x & y & l1 & _ & _ & _)]]];
    try (eapply dead_zero; eassumption).
  - eapply Wc3_inv in l' as (w & e & _). discriminate.
  - eapply Wc2_inv in l' as (w & e & _). discriminate.
  - eapply Gd2_dead; eassumption.
Qed.

(** Every silent step of a [qgood] state consumes one message of the mailbox. *)
Lemma qgood_tau (X : proc) (m : MO (ExtAct TypeOfActions)) r :
  qgood X -> bOut ∉ m -> ((X, m) : st) ⟶ r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)),
    r = (Y, m') /\ qgood Y /\ bOut ∉ m' /\ m' ⊂ m.
Proof.
  intros hg hb l.
  eapply fw_tau_inv in l as [(p' & l' & _) | (a & p' & m' & l' & -> & ->)].
  - exfalso. eapply qgood_no_tau; eassumption.
  - exists p', m'. split; [reflexivity |].
    assert (hsz : m' ⊂ {[+ ActOut a +]} ⊎ m') by multiset_solver.
    assert (hb' : bOut ∉ m') by multiset_solver.
    split; [| split; [exact hb' | exact hsz]].
    destruct hg as [ | | v ne | ];
      eapply par_inv in l'
        as [(x & l2 & ->) | [(x & l2 & ->) | [(b & x & y & l1 & _ & e & _) | (b & x & y & l1 & _ & e & _)]]];
      try (exfalso; eapply dead_zero; eassumption); try discriminate.
    + eapply Wc3_inv in l2 as (w & e & ->). eapply qg_wc2.
    + eapply Wc2_inv in l2 as (w & e & ->). injection e as ->.
      destruct (Data_dec w v0) as [-> | new].
      * exfalso. eapply hb. multiset_solver.
      * eapply qg_gd. exact new.
    + exfalso. eapply Gd2_dead; eassumption.
Qed.

(** Hence a [qgood] state terminates: the mailbox is a well-founded measure. *)
Lemma qgood_term (m : MO (ExtAct TypeOfActions)) :
  forall X, qgood X -> bOut ∉ m -> ((X, m) : st) ⤓.
Proof.
  induction m as [m IH] using (well_founded_induction gmultiset_wf).
  intros X hg hb. eapply tstep. intros y l.
  eapply qgood_tau in l as (Y & m' & -> & hg' & hb' & hs); [| exact hg | exact hb].
  eapply IH; eassumption.
Qed.

Lemma qgood_act (X : proc) (m : MO (ExtAct TypeOfActions)) (μ : ExtAct TypeOfActions) r :
  qgood X -> bOut ∉ m -> μ <> bIn -> ((X, m) : st) ⟶[μ] r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)), r = (Y, m') /\ qgood Y /\ bOut ∉ m'.
Proof.
  intros hg hb hne l.
  eapply fw_act_inv in l as [(p' & l' & ->) | [(a & -> & ->) | (a & m'' & -> & -> & ->)]].
  - exists p', m. split; [reflexivity | split; [| exact hb]].
    destruct hg as [ | | v ne | ];
      eapply par_inv in l'
        as [(x & l2 & ->) | [(x & l2 & ->) | [(b & x & y & l1 & _ & e & _) | (b & x & y & l1 & _ & e & _)]]];
      try (exfalso; eapply dead_zero; eassumption); try discriminate.
    + eapply Wc3_inv in l2 as (w & e & ->). eapply qg_wc2.
    + eapply Wc2_inv in l2 as (w & e & ->). eapply qg_gd.
      intro ew. eapply hne. injection e as e. rewrite e, ew. reflexivity.
    + exfalso. eapply Gd2_dead; eassumption.
  - exists X, ({[+ ActOut a +]} ⊎ m). split; [reflexivity | split; [exact hg |]].
    intro hin. eapply gmultiset_elem_of_disj_union in hin as [hin | hin]; [| contradiction].
    eapply gmultiset_elem_of_singleton in hin. eapply hne.
    unfold bOut in hin. injection hin as hin. rewrite <- hin. reflexivity.
  - exists X, m''. split; [reflexivity | split; [exact hg |]]. multiset_solver.
Qed.

Lemma qgood_wt_tau (X : proc) (m : MO (ExtAct TypeOfActions)) r :
  qgood X -> bOut ∉ m -> ((X, m) : st) ⟹ r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)), r = (Y, m') /\ qgood Y /\ bOut ∉ m'.
Proof.
  intros hg hb w. remember ((X, m) : st) as x eqn:Hx.
  remember ([] : trace (ExtAct TypeOfActions)) as s0 eqn:Hs.
  revert X m hg hb Hx Hs.
  induction w as [ z | s z y t l w IH | μ s z y t l w IH ]; intros X m hg hb Hx Hs.
  - subst z. exists X, m. split; [reflexivity | split; [exact hg | exact hb]].
  - subst z. subst s.
    eapply qgood_tau in l as (Y & m' & -> & hg' & hb' & _); [| exact hg | exact hb].
    eapply IH; [exact hg' | exact hb' | reflexivity | reflexivity].
  - discriminate.
Qed.

Lemma qgood_wt_act (X : proc) (m : MO (ExtAct TypeOfActions)) (μ : ExtAct TypeOfActions) r :
  qgood X -> bOut ∉ m -> μ <> bIn -> ((X, m) : st) ⟹{μ} r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)), r = (Y, m') /\ qgood Y /\ bOut ∉ m'.
Proof.
  intros hg hb hne w.
  eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  eapply qgood_wt_tau in w1 as (Y1 & m1 & -> & hg1 & hb1); [| exact hg | exact hb].
  eapply qgood_act in l as (Y2 & m2 & -> & hg2 & hb2); [| exact hg1 | exact hb1 | exact hne].
  eapply qgood_wt_tau in w2 as (Y3 & m3 & -> & hg3 & hb3); [| exact hg2 | exact hb2].
  exists Y3, m3. split; [reflexivity | split; assumption].
Qed.

Lemma qgood_cnv (s : trace (ExtAct TypeOfActions)) :
  Forall (fun x => x <> bIn) s ->
  forall (X : proc) (m : MO (ExtAct TypeOfActions)), qgood X -> bOut ∉ m -> ((X, m) : st) ⇓ s.
Proof.
  induction s as [| μ s IH]; intros hf X m hg hb.
  - eapply cnv_nil. eapply qgood_term; assumption.
  - eapply Forall_cons_1 in hf as (hne & hf).
    eapply cnv_act; [eapply qgood_term; assumption |].
    intros q' w.
    eapply qgood_wt_act in w as (Y & m' & -> & hg' & hb'); [| exact hg | exact hb | exact hne].
    eapply IH; assumption.
Qed.

(** A feedback-free trace whose ledger already holds [b̄] never offers [b]. *)
Lemma no_fb_after_elem (E : list (ExtAct TypeOfActions)) (μ η : ExtAct TypeOfActions) :
  no_fb_after E μ -> η ∈ E -> ¬ dual μ η.
Proof.
  intros h hin. unfold no_fb_after in h. rewrite List.Forall_forall in h. eapply h.
  clear h. induction E as [| y E IH]; [inversion hin |].
  eapply elem_of_cons in hin as [-> | hin]; [left; reflexivity | right; eapply IH; exact hin].
Qed.

Lemma ff_no_bIn (s : trace (ExtAct TypeOfActions)) :
  forall E, bOut ∈ E -> ff_from E s -> Forall (fun x => x <> bIn) s.
Proof.
  induction s as [| x s IH]; intros E hin hff; [constructor |].
  simpl in hff. revert hff. case_decide as nb; intro hff.
  - constructor.
    + intro e. subst x. destruct nb as (c & ec). discriminate.
    + eapply (IH (x :: E)); [eapply elem_of_cons; right; exact hin | exact hff].
  - destruct hff as (hok & hff). constructor.
    + intro e. subst x. eapply (no_fb_after_elem E bIn bOut hok hin). reflexivity.
    + eapply IH; eassumption.
Qed.

(** So a [qgood] state without [b̄] in its mailbox converges on every
    continuation a feedback-free trace can offer. *)
Lemma qgood_safe (X : proc) (m : MO (ExtAct TypeOfActions)) (E : list (ExtAct TypeOfActions)) :
  qgood X -> bOut ∉ m -> bOut ∈ E -> forall s, ff_from E s -> ((X, m) : st) ⇓ s.
Proof.
  intros hg hb hin s hff.
  eapply qgood_cnv; [eapply ff_no_bIn; eassumption | exact hg | exact hb].
Qed.

(** *** Stability of the states in play *)

Lemma no_c3_sub (m' m : MO (ExtAct TypeOfActions)) : m' ⊆ m -> no_c3 m -> no_c3 m'.
Proof. intros hs h v hin. eapply (h v). multiset_solver. Qed.

Lemma no_c3_add (a : TypeOfActions) (m : MO (ExtAct TypeOfActions)) :
  fst a <> c3 -> no_c3 m -> no_c3 ({[+ ActOut a +]} ⊎ m).
Proof.
  intros hne h v hin.
  eapply gmultiset_elem_of_disj_union in hin as [hin | hin]; [| eapply (h v), hin].
  eapply gmultiset_elem_of_singleton in hin. injection hin as hin.
  eapply hne. rewrite <- hin. reflexivity.
Qed.

Lemma Qdv_stable (m : MO (ExtAct TypeOfActions)) : no_c3 m -> ((Qdv, m) : st) ↛.
Proof.
  intro hno.
  destruct (decide (((Qdv, m) : st) ↛)) as [h | h]; [exact h |].
  exfalso. eapply lts_refuses_spec1 in h as (r & l).
  eapply fw_tau_inv in l as [(p' & l' & _) | (a & p' & m' & l' & -> & _)].
  - eapply par_inv in l'
      as [(x & l2 & _) | [(x & l2 & _) | [(b & x & y & l1 & l2 & _ & _) | (b & x & y & l1 & l2 & _ & _)]]].
    + eapply oB_inv in l2 as (e & _). discriminate.
    + eapply Wc3_inv in l2 as (w & e & _). discriminate.
    + eapply Wc3_inv in l2 as (w & e & _). eapply oB_inv in l1 as (e1 & _).
      injection e1 as ->. injection e as e. discriminate.
    + eapply oB_inv in l1 as (e & _). discriminate.
  - eapply par_inv in l'
      as [(x & l2 & _) | [(x & l2 & _) | [(b & x & y & _ & _ & e & _) | (b & x & y & _ & _ & e & _)]]].
    + eapply oB_inv in l2 as (e & _). discriminate.
    + eapply Wc3_inv in l2 as (w & e & _). injection e as ->.
      eapply (hno w). multiset_solver.
    + discriminate.
    + discriminate.
Qed.

Lemma Wc3_par_stable (m : MO (ExtAct TypeOfActions)) : no_c3 m -> (((𝟘 ‖ Wc3), m) : st) ↛.
Proof.
  intro hno.
  destruct (decide ((((𝟘 ‖ Wc3), m) : st) ↛)) as [h | h]; [exact h |].
  exfalso. eapply lts_refuses_spec1 in h as (r & l).
  eapply fw_tau_inv in l as [(p' & l' & _) | (a & p' & m' & l' & -> & _)].
  - eapply qgood_no_tau; [eapply qg_wc3 | exact l'].
  - eapply par_inv in l'
      as [(x & l2 & _) | [(x & l2 & _) | [(b & x & y & _ & _ & e & _) | (b & x & y & _ & _ & e & _)]]].
    + eapply dead_zero; eassumption.
    + eapply Wc3_inv in l2 as (w & e & _). injection e as ->.
      eapply (hno w). multiset_solver.
    + discriminate.
    + discriminate.
Qed.

(** *** The restricted convergence simulation

    [M1] is the phase where [oB] is still there: the mailbox of [q] is included
    in that of [p], so [p] matches every emission of [q] except the [b̄] of
    [oB].  [M2] is the phase after [p] has answered that [b̄] from its own
    mailbox: [q] then owes one [b̄], whence the shifted invariant.

    [Mdead] is the case that makes the [c3] messages free: whenever [q] takes
    one, [p] can take it too, and [p] then diverges -- so [p ⇓] fails there and
    the obligation is void.

    [Msafe] is the phase where [p] has run out of moves.  It is entered exactly
    when [q] spends the [b̄] of [oB] and [p] has none left, and the counting
    then forces [q]'s mailbox to hold no [b̄] either: [q] can no longer reach
    the guard, and the ledger -- which now holds [b̄] -- forbids the trace from
    ever handing it one. *)

Inductive Rel3 : list (ExtAct TypeOfActions) -> st -> st -> Prop :=
| M1 E mp mq : mq ⊆ mp -> Rel3 E (Pdv, mp) (Qdv, mq)
| M2 E mp mq : mq ⊆ {[+ bOut +]} ⊎ mp -> Rel3 E (Pdv, mp) ((𝟘 ‖ Wc3), mq)
| Mdead E p q : ¬ p ⤓ -> Rel3 E p q
| Msafe E p q : (forall s, ff_from E s -> q ⇓ s) -> Rel3 E p q.

Lemma Rel3_term E p q : Rel3 E p q -> p ⤓ -> q ⤓.
Proof.
  intros hr ht. destruct hr as [E mp mq hs | E mp mq hs | E p q hnt | E p q hsafe].
  - eapply stable_term, Qdv_stable, no_c3_sub; [exact hs | eapply Pdv_term_no_c3, ht].
  - eapply stable_term, Wc3_par_stable, no_c3_sub; [exact hs |].
    eapply (no_c3_add (c2, v0)); [simpl; discriminate | eapply Pdv_term_no_c3, ht].
  - contradiction.
  - eapply cnv_term. eapply (hsafe []). exact I.
Qed.

Lemma Rel3_nb E p q (η : ExtAct TypeOfActions) q' :
  Rel3 E p q -> p ⤓ -> non_blocking η -> q ⟹{η} q' ->
  (exists p', p ⟹{η} p' /\ Rel3 (η :: E) p' q') \/ (forall s, ff_from (η :: E) s -> q' ⇓ s).
Proof.
  intros hr ht nb w. destruct nb as (aa & ->).
  destruct hr as [E mp mq hs | E mp mq hs | E p q hnt | E p q hsafe].
  - assert (hc3p : no_c3 mp) by (eapply Pdv_term_no_c3, ht).
    assert (hc3q : no_c3 mq) by (eapply no_c3_sub; eassumption).
    eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
    eapply wt_nil_stable in w1; [| eapply Qdv_stable, hc3q]. subst r1.
    eapply fw_act_inv in l as [(x & l' & ->) | [(a & e & _) | (a & mq' & e & -> & ->)]].
    + eapply par_inv in l'
        as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply oB_inv in l2 as (e & ->). injection e as ->.
        eapply wt_nil_stable in w2; [| eapply Wc3_par_stable, hc3q]. subst q'.
        destruct (decide (bOut ∈ mp)) as [hin | hout].
        -- left. eapply mb_split in hin as (mp' & ->).
           exists (Pdv, mp'). split.
           ++ eapply wt_one, (q_mb_out Pdv mp' (c2, v0)).
           ++ eapply M2. exact hs.
        -- right. intros s hff.
           eapply (qgood_safe _ _ (ActOut (c2, v0) :: E)).
           ++ eapply qg_wc3.
           ++ intro hin. eapply hout. multiset_solver.
           ++ eapply elem_of_cons; left; reflexivity.
           ++ exact hff.
      * eapply Wc3_inv in l2 as (w0 & e & _). discriminate.
      * discriminate.
      * discriminate.
    + discriminate.
    + injection e as <-.
      eapply wt_nil_stable in w2;
        [| eapply Qdv_stable, (no_c3_sub mq' ({[+ ActOut aa +]} ⊎ mq')); [multiset_solver | exact hc3q]].
      subst q'.
      left. assert (hin : ActOut aa ∈ mp) by multiset_solver.
      eapply mb_split in hin as (mp' & ->).
      exists (Pdv, mp'). split.
      * eapply wt_one, q_mb_out.
      * eapply M1. eapply mb_cancel. exact hs.
  - assert (hc3p : no_c3 mp) by (eapply Pdv_term_no_c3, ht).
    assert (hc3q : no_c3 mq).
    { eapply no_c3_sub; [exact hs |]. eapply (no_c3_add (c2, v0)); [simpl; discriminate | exact hc3p]. }
    eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
    eapply wt_nil_stable in w1; [| eapply Wc3_par_stable, hc3q]. subst r1.
    eapply fw_act_inv in l as [(x & l' & ->) | [(a & e & _) | (a & mq' & e & -> & ->)]].
    + exfalso. eapply par_inv in l'
        as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply dead_zero; eassumption.
      * eapply Wc3_inv in l2 as (w0 & e & _). discriminate.
      * discriminate.
      * discriminate.
    + discriminate.
    + injection e as <-.
      eapply wt_nil_stable in w2;
        [| eapply Wc3_par_stable, (no_c3_sub mq' ({[+ ActOut aa +]} ⊎ mq')); [multiset_solver | exact hc3q]].
      subst q'.
      destruct (decide (ActOut aa ∈ mp)) as [hin | hout].
      * left. eapply mb_split in hin as (mp' & ->).
        exists (Pdv, mp'). split; [eapply wt_one, q_mb_out |].
        eapply M2. rewrite mb_swap in hs. eapply mb_cancel. exact hs.
      * right.
        assert (hx : ActOut aa ∈ {[+ bOut +]} ⊎ mp) by multiset_solver.
        eapply gmultiset_elem_of_disj_union in hx as [hx | hx]; [| contradiction].
        eapply gmultiset_elem_of_singleton in hx. rewrite hx in hs. rewrite hx.
        eapply mb_cancel in hs.
        intros s hff. eapply (qgood_safe _ _ (bOut :: E)).
        -- eapply qg_wc3.
        -- intro hb. eapply hout. rewrite hx. multiset_solver.
        -- eapply elem_of_cons; left; reflexivity.
        -- exact hff.
  - contradiction.
  - right. intros s hff. eapply cnv_step; [| exact w]. eapply hsafe. simpl. exact hff.
Qed.

Lemma Rel3_b E p q (μ : ExtAct TypeOfActions) q' :
  Rel3 E p q -> p ⤓ -> ¬ non_blocking μ -> no_fb_after E μ -> q ⟹{μ} q' ->
  (exists p', p ⟹{μ} p' /\ Rel3 E p' q') \/ (forall s, ff_from E s -> q' ⇓ s).
Proof.
  intros hr ht nb hok w.
  destruct μ as [a | a]; [| exfalso; eapply nb; exists a; reflexivity].
  destruct hr as [E mp mq hs | E mp mq hs | E p q hnt | E p q hsafe].
  - assert (hc3p : no_c3 mp) by (eapply Pdv_term_no_c3, ht).
    assert (hc3q : no_c3 mq) by (eapply no_c3_sub; eassumption).
    eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
    eapply wt_nil_stable in w1; [| eapply Qdv_stable, hc3q]. subst r1.
    destruct a as (ca, va). destruct (Data_dec ca c3) as [-> | hne].
    + left. exists (Pdv, {[+ ActOut (c3, va) +]} ⊎ mp). split.
      * eapply wt_one, (q_mb_in Pdv mp (c3, va)).
      * eapply Mdead. eapply (Pdv_c3_not_term va). multiset_solver.
    + eapply fw_act_inv in l as [(x & l' & ->) | [(b & e & ->) | (b & mq'' & e & _ & _)]].
      * exfalso. eapply par_inv in l'
          as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
        -- eapply oB_inv in l2 as (e & _). discriminate.
        -- eapply Wc3_inv in l2 as (w0 & e & _). injection e as e1 e2. eapply hne. now subst.
        -- discriminate.
        -- discriminate.
      * injection e as <-.
        eapply wt_nil_stable in w2;
          [| eapply Qdv_stable, (no_c3_add (ca, va)); [simpl; exact hne | exact hc3q]].
        subst q'.
        left. exists (Pdv, {[+ ActOut (ca, va) +]} ⊎ mp). split.
        -- eapply wt_one, q_mb_in.
        -- eapply M1. eapply mb_mono. exact hs.
      * discriminate.
  - assert (hc3p : no_c3 mp) by (eapply Pdv_term_no_c3, ht).
    assert (hc3q : no_c3 mq).
    { eapply no_c3_sub; [exact hs |]. eapply (no_c3_add (c2, v0)); [simpl; discriminate | exact hc3p]. }
    eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
    eapply wt_nil_stable in w1; [| eapply Wc3_par_stable, hc3q]. subst r1.
    destruct a as (ca, va). destruct (Data_dec ca c3) as [-> | hne].
    + left. exists (Pdv, {[+ ActOut (c3, va) +]} ⊎ mp). split.
      * eapply wt_one, (q_mb_in Pdv mp (c3, va)).
      * eapply Mdead. eapply (Pdv_c3_not_term va). multiset_solver.
    + eapply fw_act_inv in l as [(x & l' & ->) | [(b & e & ->) | (b & mq'' & e & _ & _)]].
      * exfalso. eapply par_inv in l'
          as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
        -- eapply dead_zero; eassumption.
        -- eapply Wc3_inv in l2 as (w0 & e & _). injection e as e1 e2. eapply hne. now subst.
        -- discriminate.
        -- discriminate.
      * injection e as <-.
        eapply wt_nil_stable in w2;
          [| eapply Wc3_par_stable, (no_c3_add (ca, va)); [simpl; exact hne | exact hc3q]].
        subst q'.
        left. exists (Pdv, {[+ ActOut (ca, va) +]} ⊎ mp). split.
        -- eapply wt_one, q_mb_in.
        -- eapply M2. rewrite mb_swap. eapply mb_mono. exact hs.
      * discriminate.
  - contradiction.
  - right. intros s hff. eapply cnv_step; [| exact w]. eapply hsafe.
    simpl. split; [exact hok | exact hff].
Qed.

(** ** The conclusion on the must side *)

Theorem Rel3_csim : csim Rel3.
Proof. split; [exact Rel3_term | split; [exact Rel3_nb | exact Rel3_b]]. Qed.

Lemma Rel3_init : Rel3 [] ((Pdv, mt) : st) (Qdv, mt).
Proof. eapply M1. multiset_solver. Qed.

(** On every feedback-free trace, [p] converging forces [q] to converge. *)
Theorem pdv_qdv_ff_cnv (s : trace (ExtAct TypeOfActions)) :
  ¬ has_fb s -> ((Pdv, mt) : st) ⇓ s -> ((Qdv, mt) : st) ⇓ s.
Proof. eapply (csim_cnv_ff Rel3 Rel3_csim (Pdv, mt) (Qdv, mt) s Rel3_init). Qed.

(** In particular on the simplified traces, which carry no feedback. *)
Theorem pdv_qdv_pre_fnf (s : trace (ExtAct TypeOfActions)) :
  ((Pdv, mt) : st) ⇓ (nlin (fnf s)) -> ((Qdv, mt) : st) ⇓ (nlin (fnf s)).
Proof. eapply pdv_qdv_ff_cnv, fnf_no_fb. Qed.

(** The must counterpart of [feedback_free_strictly_weaker_nf]: the termination
    condition of the acceptance-set preorder, checked on the normalised and
    feedback-simplified traces only, is strictly weaker than the condition
    itself.  So the must characterisation cannot be restricted to the
    simplified traces either -- and this time it is convergence, not the
    traces, that breaks. *)
Theorem must_cond1_strictly_weaker :
  (forall s, ((Pdv, mt) : st) ⇓ (nlin (fnf s)) -> ((Qdv, mt) : st) ⇓ (nlin (fnf s)))
  /\ ¬ (forall s, ((Pdv, mt) : st) ⇓ s -> ((Qdv, mt) : st) ⇓ s).
Proof.
  split; [exact pdv_qdv_pre_fnf |].
  intro h. eapply qdv_not_cnv, h, pdv_cnv.
Qed.

(** * The second must condition

    [bhv_pre_cond2] asks that every stable state [q] reaches along a trace be
    matched by a stable state of [p] accepting no more.  The counterexample
    below makes it fail in the crudest possible way: along a trace carrying a
    feedback, [q] reaches a stable state and [p] cannot perform the trace at
    all -- so the existential has nothing to offer, whatever the abstraction of
    the labels.

    The pair is the may witness read in the other direction: [p = 𝛕•ā + 𝛕•b̄]
    and [q = ā ‖ c1 ? (If (bvar 0 = v0) Then b̄ Else 𝟘)]. *)

(** ** [p = Q0] converges on every trace *)

Inductive q0good : proc -> Prop :=
| q0_root : q0good (g Q0)
| q0_oA : q0good oA
| q0_oB : q0good oB
| q0_nil : q0good (g 𝟘).

Lemma q0good_stable_or_root (X : proc) (m : MO (ExtAct TypeOfActions)) :
  q0good X -> X <> g Q0 -> ((X, m) : st) ↛.
Proof.
  intros hg hne.
  destruct (decide (((X, m) : st) ↛)) as [h | h]; [exact h |].
  exfalso. eapply lts_refuses_spec1 in h as (r & l).
  eapply fw_tau_inv in l as [(p' & l' & _) | (a & p' & m' & l' & -> & _)];
    destruct hg as [ | | | ]; try (eapply hne; reflexivity).
  - eapply oA_inv in l' as (e & _). discriminate.
  - eapply oB_inv in l' as (e & _). discriminate.
  - eapply nil_no_step; eassumption.
  - eapply oA_inv in l' as (e & _). discriminate.
  - eapply oB_inv in l' as (e & _). discriminate.
  - eapply nil_no_step; eassumption.
Qed.

Lemma Q0_no_ext (μ : ExtAct TypeOfActions) r : ¬ lts (g Q0) (ActExt μ) r.
Proof.
  intro l. inversion l; subst;
    match goal with [ h : lts (g (𝛕 • _)) _ _ |- _ ] => inversion h end.
Qed.

Lemma q0good_tau (X : proc) (m : MO (ExtAct TypeOfActions)) r :
  q0good X -> ((X, m) : st) ⟶ r ->
  exists Y : proc, r = (Y, m) /\ q0good Y /\ Y <> g Q0.
Proof.
  intros hg l.
  eapply fw_tau_inv in l as [(p' & l' & ->) | (a & p' & m' & l' & -> & ->)].
  - destruct hg as [ | | | ].
    + eapply Q0_tau_step in l' as [-> | ->]; eexists;
        (split; [reflexivity | split; [constructor | unfold oA, oB, Q0; discriminate]]).
    + exfalso. eapply oA_inv in l' as (e & _). discriminate.
    + exfalso. eapply oB_inv in l' as (e & _). discriminate.
    + exfalso. eapply nil_no_step; eassumption.
  - exfalso. destruct hg as [ | | | ].
    + eapply Q0_no_ext; eassumption.
    + eapply oA_inv in l' as (e & _). discriminate.
    + eapply oB_inv in l' as (e & _). discriminate.
    + eapply nil_no_step; eassumption.
Qed.

Lemma q0good_term (X : proc) (m : MO (ExtAct TypeOfActions)) : q0good X -> ((X, m) : st) ⤓.
Proof.
  intro hg. eapply tstep. intros y l.
  eapply q0good_tau in l as (Y & -> & hg' & hne); [| exact hg].
  eapply stable_term, q0good_stable_or_root; assumption.
Qed.

Lemma q0good_act (X : proc) (m : MO (ExtAct TypeOfActions)) (μ : ExtAct TypeOfActions) r :
  q0good X -> ((X, m) : st) ⟶[μ] r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)), r = (Y, m') /\ q0good Y.
Proof.
  intros hg l.
  eapply fw_act_inv in l as [(p' & l' & ->) | [(a & -> & ->) | (a & m'' & -> & -> & ->)]].
  - destruct hg as [ | | | ].
    + exfalso. eapply Q0_no_ext; eassumption.
    + eapply oA_inv in l' as (_ & ->). exists (g 𝟘), m. split; [reflexivity | constructor].
    + eapply oB_inv in l' as (_ & ->). exists (g 𝟘), m. split; [reflexivity | constructor].
    + exfalso. eapply nil_no_step; eassumption.
  - exists X, ({[+ ActOut a +]} ⊎ m). split; [reflexivity | exact hg].
  - exists X, m''. split; [reflexivity | exact hg].
Qed.

Lemma q0good_wt_tau (X : proc) (m : MO (ExtAct TypeOfActions)) r :
  q0good X -> ((X, m) : st) ⟹ r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)), r = (Y, m') /\ q0good Y.
Proof.
  intros hg w. remember ((X, m) : st) as x eqn:Hx.
  remember ([] : trace (ExtAct TypeOfActions)) as s0 eqn:Hs.
  revert X m hg Hx Hs.
  induction w as [ z | s z y t l w IH | μ s z y t l w IH ]; intros X m hg Hx Hs.
  - subst z. exists X, m. split; [reflexivity | exact hg].
  - subst z. subst s. eapply q0good_tau in l as (Y & -> & hg' & _); [| exact hg].
    eapply IH; [exact hg' | reflexivity | reflexivity].
  - discriminate.
Qed.

Lemma q0good_wt_act (X : proc) (m : MO (ExtAct TypeOfActions)) (μ : ExtAct TypeOfActions) r :
  q0good X -> ((X, m) : st) ⟹{μ} r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)), r = (Y, m') /\ q0good Y.
Proof.
  intros hg w.
  eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  eapply q0good_wt_tau in w1 as (Y1 & m1 & -> & hg1); [| exact hg].
  eapply q0good_act in l as (Y2 & m2 & -> & hg2); [| exact hg1].
  eapply q0good_wt_tau in w2 as (Y3 & m3 & -> & hg3); [| exact hg2].
  exists Y3, m3. split; [reflexivity | exact hg3].
Qed.

Lemma q0good_cnv (s : trace (ExtAct TypeOfActions)) :
  forall (X : proc) (m : MO (ExtAct TypeOfActions)), q0good X -> ((X, m) : st) ⇓ s.
Proof.
  induction s as [| μ s IH]; intros X m hg.
  - eapply cnv_nil, q0good_term, hg.
  - eapply cnv_act; [eapply q0good_term, hg |].
    intros q' w. eapply q0good_wt_act in w as (Y & m' & -> & hg'); [| exact hg].
    eapply IH, hg'.
Qed.

(** ** [q = Bp2] reaches a stable state along the feedback trace *)

Definition s_cnd2 : trace (ExtAct TypeOfActions) := [aOut; aIn; bOut].

Lemma nilnil_stable : (((𝟘 ‖ 𝟘), mt) : st) ↛.
Proof.
  eapply stable_of_no_tau. intros p' l.
  eapply (dead_par (g 𝟘) (g 𝟘) dead_zero dead_zero); exact l.
Qed.

Lemma bp2_reaches_stable : ((Bp2, mt) : st) ⟹[s_cnd2] ((𝟘 ‖ 𝟘), mt).
Proof.
  eapply (wt_act _ _ _ ((𝟘 ‖ W), mt)).
  { eapply ParLeft. eapply lts_parL. eapply lts_output. }
  eapply (wt_act _ _ _ ((𝟘 ‖ (Gd ^ v0)), mt)).
  { eapply ParLeft. eapply lts_parR. eapply lts_input. }
  eapply (wt_act _ _ _ ((𝟘 ‖ (g 𝟘)), mt)).
  { eapply ParLeft. eapply lts_parR. eapply guard_v0_fires. }
  eapply wt_nil.
Qed.

(** All four ingredients of a failure of [bhv_pre_cond2] at a trace carrying a
    feedback: [p] converges on it, [q] reaches a stable state along it, and [p]
    cannot perform it at all. *)
Theorem must_cond2_fails_at_feedback :
  has_fb s_cnd2
  /\ ((g Q0, mt) : st) ⇓ s_cnd2
  /\ (exists q', ((Bp2, mt) : st) ⟹[s_cnd2] q' /\ q' ↛)
  /\ ¬ (exists p', ((g Q0, mt) : st) ⟹[s_cnd2] p').
Proof.
  split.
  { simpl. left. split; [exists (c1, v0); reflexivity | constructor; reflexivity]. }
  split; [eapply q0good_cnv, q0_root |].
  split.
  - exists ((𝟘 ‖ 𝟘), mt). split; [exact bp2_reaches_stable | exact nilnil_stable].
  - exact q_does_not.
Qed.

(** ** The failure, for an arbitrary abstraction of the labels

    The existential of [bhv_pre_cond2] fails outright -- there is no [p'] at
    all -- so the conclusion does not depend on [Φ], [𝝳P], [𝝳Q] nor on the
    acceptance sets. *)

Section Cond2Generic.

  Context {T FinA PreAct : Type}.
  Context {Φ : ExtAct TypeOfActions -> FinA} {𝝳P 𝝳Q : FinA -> PreAct}.
  Context {gLtsT : gLtsEq T VACCS_ExtAction}.
  Context (AbsP : @AbsAction st T FinA PreAct (ExtAct TypeOfActions) VACCS_ExtAction Φ 𝝳P _ gLtsT).
  Context (AbsQ : @AbsAction st T FinA PreAct (ExtAct TypeOfActions) VACCS_ExtAction Φ 𝝳Q _ gLtsT).

  Theorem must_cond2_false :
    ¬ @bhv_pre_cond2 st (ExtAct TypeOfActions) VACCS_ExtAction _ T FinA PreAct Φ 𝝳P gLtsT AbsP
        st _ 𝝳Q AbsQ ((g Q0, mt) : st) ((Bp2, mt) : st).
  Proof.
    intro h.
    destruct (h s_cnd2 ((𝟘 ‖ 𝟘), mt) (q0good_cnv _ _ _ q0_root) bp2_reaches_stable nilnil_stable)
      as (p' & w & _ & _).
    eapply q_does_not. exists p'. exact w.
  Qed.

End Cond2Generic.

(** ** What is *not* claimed here

    Unlike [must_cond1_strictly_weaker], this is only the negative half.  The
    pair above does *not* separate "[bhv_pre_cond2] on the feedback-free
    traces" from [bhv_pre_cond2]: it fails on feedback-free traces too.  The
    obstruction is specific to the acceptance sets and to the forwarder.

    Take [t = [ActIn (c1, v1)]] with [v1 ≠ v0], which carries no feedback.
    [Bp2] can let its own input consume the message, reaching the stable state
    [(ā ‖ Gd^v1, ∅)] whose mailbox is empty, so it accepts only [a].  [Q0] has
    no input of its own: the forwarder must park the message in its mailbox,
    from where it is offered back -- every stable state of [Q0] along [t]
    accepts [(c1,v1)?] as well, and the inclusion fails.

    So a witness separating the two readings of the second condition has to
    give [p] the same input capabilities as [q], while still failing to
    perform the feedback trace.  The next section builds one. *)

(** * A pair that separates the second condition

    The obstruction above says what a witness must look like: [p] needs the
    same input capabilities as [q], so that the forwarder never has to park a
    message [q] consumed.  The pair below does that.

      q = ā ‖ c1 ? Gd                                       (as before)
      p = 𝛕•(ā ‖ c1 ? 𝟘) + 𝛕•b̄ + c1 ? (ā ‖ Gd)

    [p] mirrors [q] branch by branch: the third branch *is* [q] after its
    input, the second one is [q] after its internal communication, and the
    first one is [q] with a deaf guard.  What [p] does not have is [q]'s
    parallel composition: committing to the branch that emits [ā] costs it the
    guard for ever, so [ā ; a ; b̄] is out of its reach -- while [a ; ā ; b̄],
    the same actions in a feedback-free order, is not. *)

Lemma coR_char (X : proc) (m : MO (ExtAct TypeOfActions)) (μ : ExtAct TypeOfActions) :
  coR ((X, m) : st) μ <->
  exists a, μ = ActIn a /\ ((exists X', lts X (ActExt (ActOut a)) X') \/ ActOut a ∈ m).
Proof.
  split.
  - intros (μ2 & hns & duo & hb).
    destruct μ as [a | a]; [| exfalso; eapply hb; exists a; reflexivity].
    exists a. split; [reflexivity |].
    eapply ext_act_match_sym, simplify_match_input in duo. subst μ2.
    eapply lts_refuses_spec1 in hns as (r & l).
    eapply fw_act_inv in l as [(X' & l' & _) | [(b & e & _) | (b & m' & e & -> & _)]].
    + left. exists X'. exact l'.
    + discriminate.
    + right. injection e as <-. multiset_solver.
  - intros (a & -> & hcase).
    exists (ActOut a). split; [| split].
    + intro hns. destruct hcase as [(X' & l') | hin].
      * eapply (lts_refuses_spec2 ((X, m) : st) (ActExt (ActOut a))); [| exact hns].
        exists ((X', m) : st). eapply ParLeft. exact l'.
      * eapply mb_split in hin as (m' & ->).
        eapply (lts_refuses_spec2 ((X, {[+ ActOut a +]} ⊎ m') : st) (ActExt (ActOut a)));
          [| exact hns].
        exists ((X, m') : st). eapply q_mb_out.
    + reflexivity.
    + intros (b & e). discriminate.
Qed.

Definition Wd : proc := g (c1 ? 𝟘).
Definition Pc : gproc := ((𝛕 • (oA ‖ Wd)) + (𝛕 • oB)) + (c1 ? (oA ‖ Gd)).
Definition Pw : proc := g Pc.

Lemma Wd_subst (v : ValueData) : Wd ^ v = Wd.
Proof. vm_compute. reflexivity. Qed.

Lemma oAGd_subst (v : ValueData) : (oA ‖ Gd) ^ v = oA ‖ (Gd ^ v).
Proof. vm_compute. reflexivity. Qed.

Lemma Pw_inv α r : lts Pw α r ->
  (α = τ /\ r = oA ‖ Wd) \/ (α = τ /\ r = oB)
  \/ (exists v, α = ActExt (ActIn (c1, v)) /\ r = oA ‖ (Gd ^ v)).
Proof.
  intro l. inversion l; subst.
  - inversion H3; subst.
    + inversion H4; subst. left. split; reflexivity.
    + inversion H4; subst. right. left. split; reflexivity.
  - inversion H3; subst. right. right. exists v. split; [reflexivity | eapply oAGd_subst].
Qed.

Lemma Wd_inv α r : lts Wd α r -> exists v, α = ActExt (ActIn (c1, v)) /\ r = g 𝟘.
Proof. intro l. inversion l; subst. exists v. split; reflexivity. Qed.

Lemma dead_nilnil : dead (𝟘 ‖ 𝟘).
Proof. eapply dead_par; eapply dead_zero. Qed.

Lemma dead_nilGd (v : ValueData) : v <> v0 -> dead (𝟘 ‖ (Gd ^ v)).
Proof. intro ne. eapply dead_par; [eapply dead_zero | eapply dead_Gd, ne]. Qed.

(** *** The relation

    [N1] is the two roots in step.  [N2] is the phase where [q] has emitted the
    [ā] of its [ā] and [p] has answered from its mailbox, so [q] owes one [ā]
    and keeps all its branches; [N3] is the phase where [p] had to commit to
    its first branch, and then [q]'s mailbox holds no [ā] either -- so its
    guard can only ever be fed a value that kills it.  [N4] pairs [q] after its
    internal communication with [p]'s second branch, and [N5] pairs [q] after a
    dead guard with [p]'s third branch, which still holds the [ā] that [q] owes.
    [Nid] is where they coincide, [Ndead] where both are inert. *)

Inductive Rel4 : list (ExtAct TypeOfActions) -> st -> st -> Prop :=
| N1 E m : Rel4 E (Pw, m) (Bp2, m)
| N2 E n : aOut ∈ E -> Rel4 E (Pw, n) ((𝟘 ‖ W), {[+ aOut +]} ⊎ n)
| N3 E m : aOut ∉ m -> aOut ∈ E -> Rel4 E ((𝟘 ‖ Wd), m) ((𝟘 ‖ W), m)
| N4 E m : Rel4 E (oB, m) ((𝟘 ‖ (Gd ^ v0)), m)
| N5 E v n : v <> v0 -> Rel4 E ((oA ‖ (Gd ^ v)), n) ((𝟘 ‖ (Gd ^ v)), {[+ aOut +]} ⊎ n)
| Nid E x : Rel4 E x x
| Ndead E Xp Xq m : dead Xp -> dead Xq -> Rel4 E ((Xp, m) : st) ((Xq, m) : st).

Lemma Rel4_mono E (η : ExtAct TypeOfActions) p q : Rel4 E p q -> Rel4 (η :: E) p q.
Proof.
  intro hr. destruct hr as [E m | E n hin | E m hnin hin | E m | E v n ne | E x | E Xp Xq m d1 d2].
  - eapply N1.
  - eapply N2. eapply elem_of_cons; right; exact hin.
  - eapply N3; [exact hnin | eapply elem_of_cons; right; exact hin].
  - eapply N4.
  - eapply N5, ne.
  - eapply Nid.
  - eapply Ndead; assumption.
Qed.

(** *** The moves of [p] *)

Lemma Pw_to_oB (m : MO (ExtAct TypeOfActions)) : ((Pw, m) : st) ⟶ (oB, m).
Proof. eapply ParLeft. eapply lts_choiceL. eapply lts_choiceR. eapply lts_tau. Qed.

Lemma Pw_to_br1 (m : MO (ExtAct TypeOfActions)) : ((Pw, m) : st) ⟶ ((oA ‖ Wd), m).
Proof. eapply ParLeft. eapply lts_choiceL. eapply lts_choiceL. eapply lts_tau. Qed.

Lemma Pw_in (v : ValueData) (m : MO (ExtAct TypeOfActions)) :
  lts Pw (ActExt (ActIn (c1, v))) (oA ‖ (Gd ^ v)).
Proof. eapply lts_choiceR. rewrite <- (oAGd_subst v). eapply lts_input. Qed.

Lemma Pw_sync (v : ValueData) (m : MO (ExtAct TypeOfActions)) :
  ((Pw, {[+ ActOut (c1, v) +]} ⊎ m) : st) ⟶ ((oA ‖ (Gd ^ v)), m).
Proof.
  eapply (ParSync (ActIn (c1, v)) (ActOut (c1, v))).
  - split; [reflexivity | exists (c1, v); reflexivity].
  - eapply Pw_in. exact m.
  - eapply lts_multiset_minus. exists (c1, v). reflexivity.
Qed.

Lemma Wd_sync (v : ValueData) (m : MO (ExtAct TypeOfActions)) :
  (((𝟘 ‖ Wd), {[+ ActOut (c1, v) +]} ⊎ m) : st) ⟶ ((𝟘 ‖ 𝟘), m).
Proof.
  eapply (ParSync (ActIn (c1, v)) (ActOut (c1, v))).
  - split; [reflexivity | exists (c1, v); reflexivity].
  - eapply lts_parR. exact (@lts_input _ c1 v (g 𝟘)).
  - eapply lts_multiset_minus. exists (c1, v). reflexivity.
Qed.

Lemma mb_neq_in (x y : ExtAct TypeOfActions) (n m' : MO (ExtAct TypeOfActions)) :
  {[+ x +]} ⊎ n = {[+ y +]} ⊎ m' -> y <> x -> y ∈ n /\ m' = {[+ x +]} ⊎ (n ∖ {[+ y +]}).
Proof. intros e hne. split; multiset_solver. Qed.

Lemma mb_eq_cancel (x : ExtAct TypeOfActions) (n m' : MO (ExtAct TypeOfActions)) :
  {[+ x +]} ⊎ n = {[+ x +]} ⊎ m' -> n = m'.
Proof. intro e. multiset_solver. Qed.

Lemma out_c1_neq (w : ValueData) : w <> v0 -> ActOut (c1, w) <> aOut.
Proof. intros ne e. eapply ne. injection e as e. exact e. Qed.

(** *** The silent clause *)

Lemma Rel4_tau1 E p q q' : Rel4 E p q -> q ⟶ q' -> exists p', p ⟹ p' /\ Rel4 E p' q'.
Proof.
  intros hr l.
  destruct hr as [E m | E n hin | E m hnin hin | E m | E v n ne | E x | E Xp Xq m d1 d2].
  - eapply fw_tau_inv in l as [(X' & l' & ->) | (a & X' & m' & l' & -> & ->)].
    + eapply par_inv in l'
        as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & l1 & l2 & _ & ->) | (b & y & z & l1 & l2 & _ & ->)]]].
      * eapply oA_inv in l2 as (e & _). discriminate.
      * eapply W_inv in l2 as (w & e & _). discriminate.
      * eapply oA_inv in l1 as (e1 & ->). injection e1 as ->.
        eapply W_inv in l2 as (w & e2 & ->). injection e2 as <-.
        exists (oB, m). split; [eapply wt_one_tau, Pw_to_oB | eapply N4].
      * eapply oA_inv in l1 as (e & _). discriminate.
    + eapply par_inv in l'
        as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply oA_inv in l2 as (e & _). discriminate.
      * eapply W_inv in l2 as (w & e2 & ->). injection e2 as ->.
        exists ((oA ‖ (Gd ^ w)), m'). split; [eapply wt_one_tau, Pw_sync | eapply Nid].
      * discriminate.
      * discriminate.
  - eapply fw_tau_inv in l as [(X' & l' & ->) | (a & X' & m' & l' & e & ->)].
    + exfalso. eapply par_inv in l'
        as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & l1 & _ & _ & _) | (b & y & z & l1 & _ & _ & _)]]].
      * eapply dead_zero; eassumption.
      * eapply W_inv in l2 as (w & e & _). discriminate.
      * eapply dead_zero; eassumption.
      * eapply dead_zero; eassumption.
    + eapply par_inv in l'
        as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & _ & _ & e2 & _) | (b & y & z & _ & _ & e2 & _)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply W_inv in l2 as (w & e2 & ->). injection e2 as ->.
        destruct (Data_dec w v0) as [-> | new].
        -- eapply mb_eq_cancel in e. subst m'.
           exists (oB, n). split; [eapply wt_one_tau, Pw_to_oB | eapply N4].
        -- destruct (mb_neq_in aOut (ActOut (c1, w)) n m' e (out_c1_neq w new)) as (hx & hm).
           eapply mb_split in hx as (n2 & e3). subst n. clear hm.
           rewrite mb_swap in e. eapply mb_eq_cancel in e. subst m'.
           exists ((oA ‖ (Gd ^ w)), n2). split; [eapply wt_one_tau, Pw_sync | eapply N5, new].
      * discriminate.
      * discriminate.
  - eapply fw_tau_inv in l as [(X' & l' & ->) | (a & X' & m' & l' & -> & ->)].
    + exfalso. eapply par_inv in l'
        as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & l1 & _ & _ & _) | (b & y & z & l1 & _ & _ & _)]]].
      * eapply dead_zero; eassumption.
      * eapply W_inv in l2 as (w & e & _). discriminate.
      * eapply dead_zero; eassumption.
      * eapply dead_zero; eassumption.
    + eapply par_inv in l'
        as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & _ & _ & e2 & _) | (b & y & z & _ & _ & e2 & _)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply W_inv in l2 as (w & e2 & ->). injection e2 as ->.
        assert (new : w <> v0).
        { intro ew. subst w. eapply hnin. eapply gmultiset_elem_of_disj_union. left.
          eapply gmultiset_elem_of_singleton. reflexivity. }
        exists ((𝟘 ‖ 𝟘), m'). split; [eapply wt_one_tau, Wd_sync |].
        eapply Ndead; [eapply dead_nilnil | eapply dead_nilGd, new].
      * discriminate.
      * discriminate.
  - exfalso. eapply fw_tau_inv in l as [(X' & l' & _) | (a & X' & m' & l' & _ & _)].
    + eapply par_inv in l'
        as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & l1 & _ & _ & _) | (b & y & z & l1 & _ & _ & _)]]].
      * eapply dead_zero; eassumption.
      * eapply guard_step in l2 as (_ & e & _). discriminate.
      * eapply dead_zero; eassumption.
      * eapply dead_zero; eassumption.
    + eapply par_inv in l'
        as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & _ & _ & e2 & _) | (b & y & z & _ & _ & e2 & _)]]].
      * eapply dead_zero; eassumption.
      * eapply guard_step in l2 as (_ & e & _). discriminate.
      * discriminate.
      * discriminate.
  - exfalso. eapply fw_tau_inv in l as [(X' & l' & _) | (a & X' & m' & l' & _ & _)];
      eapply (dead_nilGd v ne); eassumption.
  - exists q'. split; [eapply wt_one_tau, l | eapply Nid].
  - exfalso. eapply fw_tau_inv in l as [(X' & l' & _) | (a & X' & m' & l' & _ & _)];
      eapply d2; eassumption.
Qed.

Lemma Rel4_tau E p q q' : Rel4 E p q -> q ⟹ q' -> exists p', p ⟹ p' /\ Rel4 E p' q'.
Proof.
  intros hr w. remember ([] : trace (ExtAct TypeOfActions)) as s0 eqn:Hs.
  revert p hr Hs.
  induction w as [ z | s z y t l w IH | μ s z y t l w IH ]; intros p hr Hs.
  - exists p. split; [eapply wt_nil | exact hr].
  - subst s. destruct (Rel4_tau1 E p z y hr l) as (p1 & w1 & hr1).
    destruct (IH p1 hr1 eq_refl) as (p2 & w2 & hr2).
    exists p2. split; [eapply wt_join_nil; eassumption | exact hr2].
  - discriminate.
Qed.

(** *** The clauses on actions *)

Lemma Pw_emit_aOut (m : MO (ExtAct TypeOfActions)) :
  ((Pw, m) : st) ⟹{aOut} ((𝟘 ‖ Wd), m).
Proof.
  eapply wt_tau; [eapply Pw_to_br1 |].
  eapply wt_one. eapply ParLeft. eapply lts_parL. eapply lts_output.
Qed.

Lemma Rel4_nb1 E p q (a : TypeOfActions) q' :
  Rel4 E p q -> q ⟶[ActOut a] q' ->
  exists p', p ⟹{ActOut a} p' /\ Rel4 (ActOut a :: E) p' q'.
Proof.
  intros hr l.
  destruct hr as [E m | E n hin | E m hnin hin | E m | E v n ne | E x | E Xp Xq m d1 d2].
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(b & e & _) | (b & m2 & e & -> & ->)]].
    + eapply par_inv in l'
        as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply oA_inv in l2 as (e & ->). injection e as ->.
        destruct (decide (aOut ∈ m)) as [hinm | hnin].
        -- eapply mb_split in hinm as (m2 & ->).
           exists (Pw, m2). split; [eapply wt_one, q_mb_out |].
           eapply N2. eapply elem_of_cons; left; reflexivity.
        -- exists ((𝟘 ‖ Wd), m). split; [eapply Pw_emit_aOut |].
           eapply N3; [exact hnin | eapply elem_of_cons; left; reflexivity].
      * eapply W_inv in l2 as (w & e & _). discriminate.
      * discriminate.
      * discriminate.
    + discriminate.
    + injection e as <-. exists (Pw, m2). split; [eapply wt_one, q_mb_out | eapply N1].
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(b & e & _) | (b & m2 & e & e2 & ->)]].
    + exfalso. eapply par_inv in l'
        as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & l1 & _ & _ & _) | (b & y & z & l1 & _ & _ & _)]]].
      * eapply dead_zero; eassumption.
      * eapply W_inv in l2 as (w & e & _). discriminate.
      * eapply dead_zero; eassumption.
      * eapply dead_zero; eassumption.
    + discriminate.
    + injection e as <-.
      destruct (decide (ActOut a = aOut)) as [ea | ea].
      * rewrite ea in e2. eapply mb_eq_cancel in e2. subst m2.
        destruct (decide (aOut ∈ n)) as [hinn | hninn].
        -- eapply mb_split in hinn as (n2 & e3).
           exists (Pw, n2). split.
           ++ rewrite ea, e3. eapply wt_one, q_mb_out.
           ++ rewrite e3. eapply N2. eapply elem_of_cons; right; exact hin.
        -- exists ((𝟘 ‖ Wd), n). split; [rewrite ea; eapply Pw_emit_aOut |].
           eapply N3; [exact hninn | eapply elem_of_cons; right; exact hin].
      * destruct (mb_neq_in aOut (ActOut a) n m2 e2 ea) as (hx & _).
        eapply mb_split in hx as (n2 & ->).
        rewrite mb_swap in e2. eapply mb_eq_cancel in e2. subst m2.
        exists (Pw, n2). split; [eapply wt_one, q_mb_out |].
        eapply N2. eapply elem_of_cons; right; exact hin.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(b & e & _) | (b & m2 & e & -> & ->)]].
    + exfalso. eapply par_inv in l'
        as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & l1 & _ & _ & _) | (b & y & z & l1 & _ & _ & _)]]].
      * eapply dead_zero; eassumption.
      * eapply W_inv in l2 as (w & e & _). discriminate.
      * eapply dead_zero; eassumption.
      * eapply dead_zero; eassumption.
    + discriminate.
    + injection e as <-.
      exists ((𝟘 ‖ Wd), m2). split; [eapply wt_one, q_mb_out |].
      eapply N3; [| eapply elem_of_cons; right; exact hin].
      intro hm. eapply hnin. multiset_solver.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(b & e & _) | (b & m2 & e & -> & ->)]].
    + eapply par_inv in l'
        as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply guard_step in l2 as (_ & e & ->). injection e as ->.
        exists ((g 𝟘), m). split.
        -- eapply wt_one. eapply ParLeft. eapply lts_output.
        -- eapply Ndead; [eapply dead_zero | eapply dead_nilnil].
      * discriminate.
      * discriminate.
    + discriminate.
    + injection e as <-. exists (oB, m2). split; [eapply wt_one, q_mb_out | eapply N4].
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(b & e & _) | (b & m2 & e & e2 & ->)]].
    + exfalso. eapply (dead_nilGd v ne); eassumption.
    + discriminate.
    + injection e as <-.
      destruct (decide (ActOut a = aOut)) as [ea | ea].
      * rewrite ea in e2. eapply mb_eq_cancel in e2. subst m2.
        exists ((𝟘 ‖ (Gd ^ v)), n). split.
        -- rewrite ea. eapply wt_one. eapply ParLeft. eapply lts_parL. eapply lts_output.
        -- eapply Nid.
      * destruct (mb_neq_in aOut (ActOut a) n m2 e2 ea) as (hx & _).
        eapply mb_split in hx as (n2 & ->).
        rewrite mb_swap in e2. eapply mb_eq_cancel in e2. subst m2.
        exists ((oA ‖ (Gd ^ v)), n2). split; [eapply wt_one, q_mb_out | eapply N5, ne].
  - exists q'. split; [eapply wt_one, l | eapply Nid].
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(b & e & _) | (b & m2 & e & -> & ->)]].
    + exfalso. eapply d2; eassumption.
    + discriminate.
    + injection e as <-.
      exists ((Xp, m2) : st). split; [eapply wt_one, q_mb_out | eapply Ndead; assumption].
Qed.

Lemma Rel4_b1 E p q (a : TypeOfActions) q' :
  Rel4 E p q -> no_fb_after E (ActIn a) -> q ⟶[ActIn a] q' ->
  exists p', p ⟹{ActIn a} p' /\ Rel4 E p' q'.
Proof.
  intros hr hok l.
  destruct hr as [E m | E n hin | E m hnin hin | E m | E v n ne | E x | E Xp Xq m d1 d2].
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(b & e & ->) | (b & m2 & e & _ & _)]].
    + eapply par_inv in l'
        as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply oA_inv in l2 as (e & _). discriminate.
      * eapply W_inv in l2 as (w & e & ->). injection e as ->.
        exists ((oA ‖ (Gd ^ w)), m). split; [eapply wt_one, ParLeft, Pw_in; exact m | eapply Nid].
      * discriminate.
      * discriminate.
    + injection e as <-.
      exists (Pw, {[+ ActOut a +]} ⊎ m). split; [eapply wt_one, q_mb_in | eapply N1].
    + discriminate.
  - assert (hne : a <> (c1, v0)) by (eapply no_fb_aIn; eassumption).
    eapply fw_act_inv in l as [(X' & l' & ->) | [(b & e & ->) | (b & m2 & e & _ & _)]].
    + eapply par_inv in l'
        as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply W_inv in l2 as (w & e & ->). injection e as ->.
        assert (new : w <> v0) by (intro ew; eapply hne; rewrite ew; reflexivity).
        exists ((oA ‖ (Gd ^ w)), n). split; [eapply wt_one, ParLeft, Pw_in; exact n |].
        eapply N5, new.
      * discriminate.
      * discriminate.
    + injection e as <-.
      exists (Pw, {[+ ActOut a +]} ⊎ n). split; [eapply wt_one, q_mb_in |].
      rewrite mb_swap. eapply N2, hin.
    + discriminate.
  - assert (hne : a <> (c1, v0)) by (eapply no_fb_aIn; eassumption).
    eapply fw_act_inv in l as [(X' & l' & ->) | [(b & e & ->) | (b & m2 & e & _ & _)]].
    + eapply par_inv in l'
        as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply W_inv in l2 as (w & e & ->). injection e as ->.
        assert (new : w <> v0) by (intro ew; eapply hne; rewrite ew; reflexivity).
        exists ((𝟘 ‖ 𝟘), m). split.
        -- eapply wt_one. eapply ParLeft. eapply lts_parR.
           exact (@lts_input _ c1 w (g 𝟘)).
        -- eapply Ndead; [eapply dead_nilnil | eapply dead_nilGd, new].
      * discriminate.
      * discriminate.
    + injection e as <-.
      exists ((𝟘 ‖ Wd), {[+ ActOut a +]} ⊎ m). split; [eapply wt_one, q_mb_in |].
      eapply N3; [| exact hin].
      intro hm. eapply gmultiset_elem_of_disj_union in hm as [hm | hm]; [| contradiction].
      eapply gmultiset_elem_of_singleton in hm. eapply hne.
      unfold aOut in hm. injection hm as hm. rewrite hm. reflexivity.
    + discriminate.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(b & e & ->) | (b & m2 & e & _ & _)]].
    + exfalso. eapply par_inv in l'
        as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & l1 & _ & _ & _) | (b & y & z & l1 & _ & _ & _)]]].
      * eapply dead_zero; eassumption.
      * eapply guard_step in l2 as (_ & e & _). discriminate.
      * eapply dead_zero; eassumption.
      * eapply dead_zero; eassumption.
    + injection e as <-.
      exists (oB, {[+ ActOut a +]} ⊎ m). split; [eapply wt_one, q_mb_in | eapply N4].
    + discriminate.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(b & e & ->) | (b & m2 & e & _ & _)]].
    + exfalso. eapply (dead_nilGd v ne); eassumption.
    + injection e as <-.
      exists ((oA ‖ (Gd ^ v)), {[+ ActOut a +]} ⊎ n). split; [eapply wt_one, q_mb_in |].
      rewrite mb_swap. eapply N5, ne.
    + discriminate.
  - exists q'. split; [eapply wt_one, l | eapply Nid].
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(b & e & ->) | (b & m2 & e & _ & _)]].
    + exfalso. eapply d2; eassumption.
    + injection e as <-.
      exists ((Xp, {[+ ActOut a +]} ⊎ m) : st). split;
        [eapply wt_one, q_mb_in | eapply Ndead; assumption].
    + discriminate.
Qed.

Lemma Rel4_nb E p q (η : ExtAct TypeOfActions) q' :
  Rel4 E p q -> non_blocking η -> q ⟹{η} q' -> exists p', p ⟹{η} p' /\ Rel4 (η :: E) p' q'.
Proof.
  intros hr nb w. destruct nb as (a & ->).
  eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  destruct (Rel4_tau E p q r1 hr w1) as (p1 & wp1 & hr1).
  destruct (Rel4_nb1 E p1 r1 a r2 hr1 l) as (p2 & wp2 & hr2).
  destruct (Rel4_tau (ActOut a :: E) p2 r2 q' hr2 w2) as (p3 & wp3 & hr3).
  exists p3. split; [| exact hr3].
  eapply wt_push_nil_left; [exact wp1 |]. eapply wt_push_nil_right; [exact wp2 | exact wp3].
Qed.

Lemma Rel4_b E p q (μ : ExtAct TypeOfActions) q' :
  Rel4 E p q -> ¬ non_blocking μ -> no_fb_after E μ -> q ⟹{μ} q' ->
  exists p', p ⟹{μ} p' /\ Rel4 E p' q'.
Proof.
  intros hr nb hok w.
  destruct μ as [a | a]; [| exfalso; eapply nb; exists a; reflexivity].
  eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  destruct (Rel4_tau E p q r1 hr w1) as (p1 & wp1 & hr1).
  destruct (Rel4_b1 E p1 r1 a r2 hr1 hok l) as (p2 & wp2 & hr2).
  destruct (Rel4_tau E p2 r2 q' hr2 w2) as (p3 & wp3 & hr3).
  exists p3. split; [| exact hr3].
  eapply wt_push_nil_left; [exact wp1 |]. eapply wt_push_nil_right; [exact wp2 | exact wp3].
Qed.

(** *** The acceptance clause *)

Lemma stable_of_inert (X : proc) (m : MO (ExtAct TypeOfActions)) : inert X -> ((X, m) : st) ↛.
Proof.
  intro hi. destruct (decide (((X, m) : st) ↛)) as [h | h]; [exact h |].
  exfalso. eapply lts_refuses_spec1 in h as (r & l). eapply inert_no_tau; eassumption.
Qed.

Lemma W_sync (v : ValueData) (m : MO (ExtAct TypeOfActions)) :
  (((𝟘 ‖ W), {[+ ActOut (c1, v) +]} ⊎ m) : st) ⟶ ((𝟘 ‖ (Gd ^ v)), m).
Proof.
  eapply (ParSync (ActIn (c1, v)) (ActOut (c1, v))).
  - split; [reflexivity | exists (c1, v); reflexivity].
  - eapply lts_parR. eapply lts_input.
  - eapply lts_multiset_minus. exists (c1, v). reflexivity.
Qed.

Lemma nilW_no_c1 (m : MO (ExtAct TypeOfActions)) :
  (((𝟘 ‖ W), m) : st) ↛ -> forall v, ActOut (c1, v) ∉ m.
Proof.
  intros hst v hin. eapply mb_split in hin as (m2 & ->).
  eapply (lts_refuses_spec2 (((𝟘 ‖ W), {[+ ActOut (c1, v) +]} ⊎ m2) : st) τ); [| exact hst].
  exists (((𝟘 ‖ (Gd ^ v)), m2) : st). eapply W_sync.
Qed.

Lemma nilWd_stable (m : MO (ExtAct TypeOfActions)) :
  (forall v, ActOut (c1, v) ∉ m) -> (((𝟘 ‖ Wd), m) : st) ↛.
Proof.
  intro hno.
  destruct (decide ((((𝟘 ‖ Wd), m) : st) ↛)) as [h | h]; [exact h |].
  exfalso. eapply lts_refuses_spec1 in h as (r & l).
  eapply fw_tau_inv in l as [(X' & l' & _) | (a & X' & m' & l' & -> & _)].
  - eapply par_inv in l'
      as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & l1 & _ & _ & _) | (b & y & z & l1 & _ & _ & _)]]].
    + eapply dead_zero; eassumption.
    + eapply Wd_inv in l2 as (w & e & _). discriminate.
    + eapply dead_zero; eassumption.
    + eapply dead_zero; eassumption.
  - eapply par_inv in l'
      as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
    + eapply dead_zero; eassumption.
    + eapply Wd_inv in l2 as (w & e & _). injection e as ->.
      eapply (hno w). multiset_solver.
    + discriminate.
    + discriminate.
Qed.

Lemma inert_oB : inert oB.
Proof. split; intros; intro l; eapply oB_inv in l as (e & _); discriminate. Qed.

Lemma Bp2_comL (m : MO (ExtAct TypeOfActions)) : ((Bp2, m) : st) ⟶ ((𝟘 ‖ (Gd ^ v0)), m).
Proof. eapply ParLeft. eapply lts_comL; [eapply lts_output | eapply lts_input]. Qed.

Lemma Rel4_stable E p q : Rel4 E p q -> q ↛ -> exists p', p ⟹ p' /\ p' ↛ /\ coR p' ⊆ coR q.
Proof.
  intros hr hst.
  destruct hr as [E m | E n hin | E m hnin hin | E m | E v n ne | E x | E Xp Xq m d1 d2].
  - exfalso. eapply (lts_refuses_spec2 ((Bp2, m) : st) τ); [| exact hst].
    exists (((𝟘 ‖ (Gd ^ v0)), m) : st). eapply Bp2_comL.
  - exfalso. eapply (lts_refuses_spec2 (((𝟘 ‖ W), {[+ aOut +]} ⊎ n) : st) τ); [| exact hst].
    exists (((𝟘 ‖ (Gd ^ v0)), n) : st). eapply (W_sync v0 n).
  - exists (((𝟘 ‖ Wd), m) : st). split; [eapply wt_nil | split].
    + eapply nilWd_stable, nilW_no_c1, hst.
    + intros μ hm. eapply coR_char in hm as (a & -> & hcase). eapply coR_char.
      exists a. split; [reflexivity |]. destruct hcase as [(X' & l') | hin2]; [| right; exact hin2].
      exfalso. eapply par_inv in l'
        as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply dead_zero; eassumption.
      * eapply Wd_inv in l2 as (w & e & _). discriminate.
      * discriminate.
      * discriminate.
  - exists ((oB, m) : st). split; [eapply wt_nil | split].
    + eapply stable_of_inert, inert_oB.
    + intros μ hm. eapply coR_char in hm as (a & -> & hcase). eapply coR_char.
      exists a. split; [reflexivity |]. destruct hcase as [(X' & l') | hin2]; [| right; exact hin2].
      left. eapply oB_inv in l' as (e & _). injection e as ->.
      exists ((𝟘 ‖ (g 𝟘)) : proc). eapply lts_parR. eapply guard_v0_fires.
  - exists (((oA ‖ (Gd ^ v)), n) : st). split; [eapply wt_nil | split].
    + eapply stable_of_inert, inert_par; [eapply inert_oA | eapply inert_Gd].
    + intros μ hm. eapply coR_char in hm as (a & -> & hcase). eapply coR_char.
      exists a. split; [reflexivity |].
      destruct hcase as [(X' & l') | hin2]; [| right; multiset_solver].
      eapply par_inv in l'
        as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply oA_inv in l2 as (e & _). injection e as ->. right. multiset_solver.
      * exfalso. eapply guard_step in l2 as (e & _ & _). exact (ne e).
      * discriminate.
      * discriminate.
  - exists x. split; [eapply wt_nil | split; [exact hst | reflexivity]].
  - exists ((Xp, m) : st). split; [eapply wt_nil | split].
    + eapply stable_of_inert, inert_dead, d1.
    + intros μ hm. eapply coR_char in hm as (a & -> & hcase). eapply coR_char.
      exists a. split; [reflexivity |]. destruct hcase as [(X' & l') | hin2]; [| right; exact hin2].
      exfalso. eapply d1; eassumption.
Qed.

(** *** [p] converges, and cannot perform the feedback trace *)

Lemma Pw_mt_tau (r : st) : ((Pw, mt) : st) ⟶ r -> r = ((oA ‖ Wd), mt) \/ r = (oB, mt).
Proof.
  intro l. eapply fw_tau_inv in l as [(X' & l' & ->) | (a & X' & m' & l' & e & _)].
  - eapply Pw_inv in l' as [(_ & ->) | [(_ & ->) | (w & e & _)]].
    + left. reflexivity.
    + right. reflexivity.
    + discriminate.
  - exfalso. unfold mt in e. multiset_solver.
Qed.

Lemma br1_mt_tau (r : st) : (((oA ‖ Wd), mt) : st) ⟶ r -> r = ((𝟘 ‖ 𝟘), mt).
Proof.
  intro l. eapply fw_tau_inv in l as [(X' & l' & ->) | (a & X' & m' & l' & e & _)].
  - eapply par_inv in l'
      as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & l1 & l2 & _ & ->) | (b & y & z & l1 & l2 & _ & ->)]]].
    + eapply oA_inv in l2 as (e & _). discriminate.
    + eapply Wd_inv in l2 as (w & e & _). discriminate.
    + eapply oA_inv in l1 as (e1 & ->). injection e1 as ->.
      eapply Wd_inv in l2 as (w & e2 & ->). reflexivity.
    + eapply oA_inv in l1 as (e & _). discriminate.
  - exfalso. unfold mt in e. multiset_solver.
Qed.

Lemma Pw_mt_term : ((Pw, mt) : st) ⤓.
Proof.
  eapply tstep. intros y l. eapply Pw_mt_tau in l as [-> | ->].
  - eapply tstep. intros z l2. eapply br1_mt_tau in l2 as ->.
    eapply stable_term, stable_of_inert, inert_dead, dead_nilnil.
  - eapply stable_term, stable_of_inert, inert_oB.
Qed.

Lemma Pw_mt_tau_closure (r : st) : ((Pw, mt) : st) ⟹ r ->
  r = (Pw, mt) \/ r = ((oA ‖ Wd), mt) \/ r = (oB, mt) \/ r = ((𝟘 ‖ 𝟘), mt).
Proof.
  intro w. remember ((Pw, mt) : st) as x eqn:Hx.
  remember ([] : trace (ExtAct TypeOfActions)) as s0 eqn:Hs. revert Hx Hs.
  induction w as [ z | s z y t l w IH | μ s z y t l w IH ]; intros Hx Hs.
  - subst z. left. reflexivity.
  - subst z. subst s. eapply Pw_mt_tau in l as [-> | ->].
    + right. clear IH.
      remember (((oA ‖ Wd), mt) : st) as x2 eqn:Hx2.
      remember ([] : trace (ExtAct TypeOfActions)) as s2 eqn:Hs2. revert Hx2 Hs2.
      induction w as [ z2 | s2 z2 y2 t2 l2 w2 IH2 | μ2 s2 z2 y2 t2 l2 w2 IH2 ]; intros Hx2 Hs2.
      * subst z2. left. reflexivity.
      * subst z2. subst s2. eapply br1_mt_tau in l2 as ->.
        eapply wt_nil_stable in w2; [| eapply stable_of_inert, inert_dead, dead_nilnil].
        subst t2. right. right. reflexivity.
      * discriminate.
    + eapply wt_nil_stable in w; [| eapply stable_of_inert, inert_oB]. subst t.
      right. right. left. reflexivity.
  - discriminate.
Qed.

Lemma Pw_mt_aOut (r : st) : ((Pw, mt) : st) ⟹{aOut} r -> r = ((𝟘 ‖ Wd), mt).
Proof.
  intro w. eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  eapply Pw_mt_tau_closure in w1 as [-> | [-> | [-> | ->]]].
  - exfalso. eapply fw_act_inv in l as [(X' & l' & _) | [(b & e & _) | (b & m2 & _ & e & _)]].
    + eapply Pw_inv in l' as [(e & _) | [(e & _) | (w0 & e & _)]]; discriminate.
    + discriminate.
    + unfold mt in e. multiset_solver.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(b & e & _) | (b & m2 & _ & e & _)]].
    + eapply par_inv in l'
        as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply oA_inv in l2 as (_ & ->).
        eapply wt_nil_stable in w2; [exact w2 | eapply nilWd_stable].
        intros v hin. unfold mt in hin. multiset_solver.
      * eapply Wd_inv in l2 as (w0 & e & _). discriminate.
      * discriminate.
      * discriminate.
    + discriminate.
    + exfalso. unfold mt in e. multiset_solver.
  - exfalso. eapply fw_act_inv in l as [(X' & l' & _) | [(b & e & _) | (b & m2 & _ & e & _)]].
    + eapply oB_inv in l' as (e & _). discriminate.
    + discriminate.
    + unfold mt in e. multiset_solver.
  - exfalso. eapply fw_act_inv in l as [(X' & l' & _) | [(b & e & _) | (b & m2 & _ & e & _)]].
    + eapply dead_nilnil; eassumption.
    + discriminate.
    + unfold mt in e. multiset_solver.
Qed.

Lemma nilWd_aOut_tau (r : st) :
  (((𝟘 ‖ Wd), {[+ aOut +]} ⊎ mt) : st) ⟶ r -> r = ((𝟘 ‖ 𝟘), mt).
Proof.
  intro l. eapply fw_tau_inv in l as [(X' & l' & ->) | (a & X' & m' & l' & e & ->)].
  - exfalso. eapply par_inv in l'
      as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & l1 & _ & _ & _) | (b & y & z & l1 & _ & _ & _)]]].
    + eapply dead_zero; eassumption.
    + eapply Wd_inv in l2 as (w & e & _). discriminate.
    + eapply dead_zero; eassumption.
    + eapply dead_zero; eassumption.
  - eapply par_inv in l'
      as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & _ & _ & e2 & _) | (b & y & z & _ & _ & e2 & _)]]].
    + exfalso. eapply dead_zero; eassumption.
    + eapply Wd_inv in l2 as (w & e2 & ->). injection e2 as ->.
      destruct (decide (ActOut (c1, w) = aOut)) as [ea | ea].
      * injection ea as ->. eapply mb_eq_cancel in e. subst m'. reflexivity.
      * exfalso. destruct (mb_neq_in aOut (ActOut (c1, w)) mt m' e ea) as (hx & _).
        unfold mt in hx. multiset_solver.
    + discriminate.
    + discriminate.
Qed.

Lemma nilWd_aOut_closure (r : st) :
  (((𝟘 ‖ Wd), {[+ aOut +]} ⊎ mt) : st) ⟹ r ->
  r = ((𝟘 ‖ Wd), {[+ aOut +]} ⊎ mt) \/ r = ((𝟘 ‖ 𝟘), mt).
Proof.
  intro w. remember ((((𝟘 ‖ Wd), {[+ aOut +]} ⊎ mt)) : st) as x eqn:Hx.
  remember ([] : trace (ExtAct TypeOfActions)) as s0 eqn:Hs. revert Hx Hs.
  induction w as [ z | s z y t l w IH | μ s z y t l w IH ]; intros Hx Hs.
  - subst z. left. reflexivity.
  - subst z. subst s. eapply nilWd_aOut_tau in l as ->.
    eapply wt_nil_stable in w; [| eapply stable_of_inert, inert_dead, dead_nilnil].
    subst t. right. reflexivity.
  - discriminate.
Qed.

Lemma nilnil_mt_no_bOut : ¬ exists r, (((𝟘 ‖ 𝟘), mt) : st) ⟹{bOut} r.
Proof.
  intros (r & w). eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  eapply wt_nil_stable in w1; [| eapply stable_of_inert, inert_dead, dead_nilnil]. subst r1.
  eapply fw_act_inv in l as [(X' & l' & _) | [(b & e & _) | (b & m2 & _ & e & _)]].
  - eapply dead_nilnil; eassumption.
  - discriminate.
  - unfold mt in e. multiset_solver.
Qed.

Lemma nilWd_aOut_no_bOut : ¬ exists r, (((𝟘 ‖ Wd), {[+ aOut +]} ⊎ mt) : st) ⟹{bOut} r.
Proof.
  intros (r & w). eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  eapply nilWd_aOut_closure in w1 as [-> | ->].
  - eapply fw_act_inv in l as [(X' & l' & _) | [(b & e & _) | (b & m2 & e & e2 & _)]].
    + eapply par_inv in l'
        as [(y & l2 & _) | [(y & l2 & _) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply dead_zero; eassumption.
      * eapply Wd_inv in l2 as (w0 & e & _). discriminate.
      * discriminate.
      * discriminate.
    + discriminate.
    + injection e as <-.
      destruct (decide (bOut = aOut)) as [eb | eb]; [discriminate |].
      destruct (mb_neq_in aOut bOut mt m2 e2 eb) as (hx & _).
      unfold mt in hx. multiset_solver.
  - eapply nilnil_mt_no_bOut. exists r. eapply wt_act; [exact l | exact w2].
Qed.

Lemma nilWd_mt_stable : (((𝟘 ‖ Wd), mt) : st) ↛.
Proof. eapply nilWd_stable. intros v hin. unfold mt in hin. multiset_solver. Qed.

Lemma nilWd_mt_aIn (r : st) : (((𝟘 ‖ Wd), mt) : st) ⟹{aIn} r ->
  r = ((𝟘 ‖ 𝟘), mt) \/ r = ((𝟘 ‖ Wd), {[+ aOut +]} ⊎ mt).
Proof.
  intro w. eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  eapply wt_nil_stable in w1; [| eapply nilWd_mt_stable]. subst r1.
  eapply fw_act_inv in l as [(X' & l' & ->) | [(b & e & ->) | (b & m2 & e & _ & _)]].
  - eapply par_inv in l'
      as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
    + exfalso. eapply dead_zero; eassumption.
    + eapply Wd_inv in l2 as (w0 & e & ->).
      eapply wt_nil_stable in w2; [| eapply stable_of_inert, inert_dead, dead_nilnil].
      subst r. left. reflexivity.
    + discriminate.
    + discriminate.
  - injection e as <-.
    eapply nilWd_aOut_closure in w2 as [-> | ->]; [right | left]; reflexivity.
  - discriminate.
Qed.

Lemma nilWd_aOut_term : (((𝟘 ‖ Wd), {[+ aOut +]} ⊎ mt) : st) ⤓.
Proof.
  eapply tstep. intros y l. eapply nilWd_aOut_tau in l as ->.
  eapply stable_term, stable_of_inert, inert_dead, dead_nilnil.
Qed.

Lemma pw_cnv_s_cnd2 : ((Pw, mt) : st) ⇓ s_cnd2.
Proof.
  eapply cnv_act; [exact Pw_mt_term |]. intros p1 w. eapply Pw_mt_aOut in w. subst p1.
  eapply cnv_act; [eapply stable_term, nilWd_mt_stable |].
  intros p2 w. eapply nilWd_mt_aIn in w as [-> | ->].
  - eapply cnv_act; [eapply stable_term, stable_of_inert, inert_dead, dead_nilnil |].
    intros p3 w3. exfalso. eapply nilnil_mt_no_bOut. exists p3. exact w3.
  - eapply cnv_act; [exact nilWd_aOut_term |].
    intros p3 w3. exfalso. eapply nilWd_aOut_no_bOut. exists p3. exact w3.
Qed.

(** [p] commits when it emits [ā]: after that its guard is gone for ever, so
    the feedback trace is out of its reach. *)
Lemma pw_no_s_cnd2 : ¬ exists r, ((Pw, mt) : st) ⟹[s_cnd2] r.
Proof.
  intros (r & w).
  eapply wt_pop in w as (t1 & w1 & w2). eapply Pw_mt_aOut in w1. subst t1.
  eapply wt_pop in w2 as (t2 & w3 & w4). eapply nilWd_mt_aIn in w3 as [-> | ->].
  - eapply nilnil_mt_no_bOut. exists r. exact w4.
  - eapply nilWd_aOut_no_bOut. exists r. exact w4.
Qed.

(** ** The conclusion on the second condition *)

Theorem Rel4_asim : asim Rel4.
Proof.
  split; [exact Rel4_tau | split; [exact Rel4_stable | split; [exact Rel4_nb | exact Rel4_b]]].
Qed.

Lemma Rel4_init : Rel4 [] ((Pw, mt) : st) ((Bp2, mt) : st).
Proof. eapply N1. Qed.

(** On every feedback-free trace, each stable state of [q] is matched by a
    stable state of [p] accepting no more -- so [bhv_pre_cond2] holds there,
    for every abstraction, by monotonicity of the image. *)
Theorem pw_bp2_cond2_ff (s : trace (ExtAct TypeOfActions)) (q' : st) :
  ¬ has_fb s -> ((Bp2, mt) : st) ⟹[s] q' -> q' ↛ ->
  exists p', ((Pw, mt) : st) ⟹[s] p' /\ p' ↛ /\ coR p' ⊆ coR q'.
Proof. eapply (asim_cond2_ff Rel4 Rel4_asim (Pw, mt) (Bp2, mt) s q' Rel4_init). Qed.

Theorem must_cond2_strictly_weaker :
  (forall s q', ¬ has_fb s -> ((Bp2, mt) : st) ⟹[s] q' -> q' ↛ ->
     exists p', ((Pw, mt) : st) ⟹[s] p' /\ p' ↛ /\ coR p' ⊆ coR q')
  /\ has_fb s_cnd2
  /\ ((Pw, mt) : st) ⇓ s_cnd2
  /\ (exists q', ((Bp2, mt) : st) ⟹[s_cnd2] q' /\ q' ↛)
  /\ ¬ (exists p', ((Pw, mt) : st) ⟹[s_cnd2] p').
Proof.
  split; [exact pw_bp2_cond2_ff |].
  split.
  { simpl. left. split; [exists (c1, v0); reflexivity | constructor; reflexivity]. }
  split; [exact pw_cnv_s_cnd2 |].
  split.
  - exists ((𝟘 ‖ 𝟘), mt). split; [exact bp2_reaches_stable | exact nilnil_stable].
  - exact pw_no_s_cnd2.
Qed.

(** And the failure of the condition itself, for an arbitrary abstraction. *)
Section Cond2GenericPw.

  Context {T FinA PreAct : Type}.
  Context {Φ : ExtAct TypeOfActions -> FinA} {𝝳P 𝝳Q : FinA -> PreAct}.
  Context {gLtsT : gLtsEq T VACCS_ExtAction}.
  Context (AbsP : @AbsAction st T FinA PreAct (ExtAct TypeOfActions) VACCS_ExtAction Φ 𝝳P _ gLtsT).
  Context (AbsQ : @AbsAction st T FinA PreAct (ExtAct TypeOfActions) VACCS_ExtAction Φ 𝝳Q _ gLtsT).

  Theorem must_cond2_false_Pw :
    ¬ @bhv_pre_cond2 st (ExtAct TypeOfActions) VACCS_ExtAction _ T FinA PreAct Φ 𝝳P gLtsT AbsP
        st _ 𝝳Q AbsQ ((Pw, mt) : st) ((Bp2, mt) : st).
  Proof.
    intro h.
    destruct (h s_cnd2 ((𝟘 ‖ 𝟘), mt) pw_cnv_s_cnd2 bp2_reaches_stable nilnil_stable)
      as (p' & w & _ & _).
    eapply pw_no_s_cnd2. exists p'. exact w.
  Qed.

  (** The positive half in the abstracted form [bhv_pre_cond2] uses.  Both
      sides must read the acceptance sets through the *same* abstraction --
      the very restriction [SoundnessASco] already imposes on [𝝳] -- and the
      step from the raw inclusion is then the monotonicity of the image. *)
  Context (same_delta : forall x, 𝝳P x = 𝝳Q x).

  Lemma abs_of_coR_sub (p q : st) :
    coR p ⊆ coR q -> ⌈ (𝝳P ∘ Φ) ⌉ (coR p) ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q).
  Proof.
    intros hsub y hy.
    eapply (map_set_mono (𝝳P ∘ Φ) (coR p) (coR q) hsub) in hy as (μ & hμ & ->).
    exists μ. split; [exact hμ | eapply same_delta].
  Qed.

  Theorem pw_bp2_cond2_ff_abs (s : trace (ExtAct TypeOfActions)) (q' : st) :
    ¬ has_fb s -> ((Bp2, mt) : st) ⟹[s] q' -> q' ↛ ->
    exists p', ((Pw, mt) : st) ⟹[s] p' /\ p' ↛
               /\ ⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q').
  Proof.
    intros hfb w hst. destruct (pw_bp2_cond2_ff s q' hfb w hst) as (p' & wp & hp & hsub).
    exists p'. split; [exact wp | split; [exact hp | eapply abs_of_coR_sub, hsub]].
  Qed.

End Cond2GenericPw.

(** * The must preorder, restricted to the feedback-free traces

    The two conditions of [≼ₐₛ] were refuted separately above, by two different
    pairs.  The pair [Pw], [Bp2] settles both at once: neither process
    diverges, so the termination condition holds outright, and the acceptance
    condition then carries the whole separation.

    [Bp2] is finite and has no recursion, so it converges on every trace: its
    only silent steps either consume a message of the mailbox, or take
    [ā ‖ W] to [𝟘 ‖ Gd^v0], which has none left. *)

Inductive bgood : proc -> Prop :=
| bg_root : bgood (oA ‖ W)
| bg_nilW : bgood (𝟘 ‖ W)
| bg_oAGd v : bgood (oA ‖ (Gd ^ v))
| bg_nilGd v : bgood (𝟘 ‖ (Gd ^ v))
| bg_oAnil : bgood (oA ‖ 𝟘)
| bg_nilnil : bgood (𝟘 ‖ 𝟘).

Lemma inert_nilGd (v : ValueData) : inert (𝟘 ‖ (Gd ^ v)).
Proof. eapply inert_par; [eapply inert_dead, dead_zero | eapply inert_Gd]. Qed.

Lemma bgood_tau (X : proc) (m : MO (ExtAct TypeOfActions)) r :
  bgood X -> ((X, m) : st) ⟶ r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)),
    r = (Y, m') /\ bgood Y /\ (m' ⊂ m \/ (m' = m /\ inert Y)).
Proof.
  intros hg l.
  eapply fw_tau_inv in l as [(X' & l' & ->) | (a & X' & m' & l' & -> & ->)].
  - destruct hg as [ | | v | v | | ];
      eapply par_inv in l'
        as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & l1 & l2 & _ & ->) | (b & y & z & l1 & l2 & _ & ->)]]];
      try (exfalso; eapply dead_zero; eassumption).
    + eapply oA_inv in l2 as (e & _). discriminate.
    + eapply W_inv in l2 as (w & e & _). discriminate.
    + eapply oA_inv in l1 as (e1 & ->). injection e1 as ->.
      eapply W_inv in l2 as (w & e2 & ->). injection e2 as <-.
      exists ((𝟘 ‖ (Gd ^ v0)) : proc), m. split; [reflexivity |].
      split; [eapply bg_nilGd | right; split; [reflexivity | eapply inert_nilGd]].
    + eapply oA_inv in l1 as (e & _). discriminate.
    + eapply W_inv in l2 as (w & e & _). discriminate.
    + eapply oA_inv in l2 as (e & _). discriminate.
    + eapply guard_step in l2 as (_ & e & _). discriminate.
    + eapply oA_inv in l1 as (e1 & ->). injection e1 as ->.
      eapply guard_step in l2 as (_ & e2 & _). discriminate.
    + eapply oA_inv in l1 as (e & _). discriminate.
    + eapply guard_step in l2 as (_ & e & _). discriminate.
    + eapply oA_inv in l2 as (e & _). discriminate.
  - assert (hsub : m' ⊂ {[+ ActOut a +]} ⊎ m') by multiset_solver.
    destruct hg as [ | | v | v | | ];
      eapply par_inv in l'
        as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]];
      try (exfalso; eapply dead_zero; eassumption); try discriminate.
    + eapply oA_inv in l2 as (e & _). discriminate.
    + eapply W_inv in l2 as (w & e & ->).
      exists ((oA ‖ (Gd ^ w)) : proc), m'.
      split; [reflexivity | split; [eapply bg_oAGd | left; exact hsub]].
    + eapply W_inv in l2 as (w & e & ->).
      exists ((𝟘 ‖ (Gd ^ w)) : proc), m'.
      split; [reflexivity | split; [eapply bg_nilGd | left; exact hsub]].
    + eapply oA_inv in l2 as (e & _). discriminate.
    + eapply guard_step in l2 as (_ & e & _). discriminate.
    + eapply guard_step in l2 as (_ & e & _). discriminate.
    + eapply oA_inv in l2 as (e & _). discriminate.
Qed.

Lemma bgood_term (m : MO (ExtAct TypeOfActions)) : forall X, bgood X -> ((X, m) : st) ⤓.
Proof.
  induction m as [m IH] using (well_founded_induction gmultiset_wf).
  intros X hg. eapply tstep. intros y l.
  destruct (bgood_tau X m y hg l) as (Y & m' & -> & hg' & [hs | (-> & hin)]).
  - eapply IH; eassumption.
  - eapply stable_term, stable_of_inert, hin.
Qed.

Lemma bgood_act (X : proc) (m : MO (ExtAct TypeOfActions)) (μ : ExtAct TypeOfActions) r :
  bgood X -> ((X, m) : st) ⟶[μ] r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)), r = (Y, m') /\ bgood Y.
Proof.
  intros hg l.
  eapply fw_act_inv in l as [(X' & l' & ->) | [(a & -> & ->) | (a & m'' & -> & -> & ->)]].
  - destruct hg as [ | | v | v | | ];
      eapply par_inv in l'
        as [(y & l2 & ->) | [(y & l2 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]];
      try (exfalso; eapply dead_zero; eassumption); try discriminate.
    + eapply oA_inv in l2 as (_ & ->). eexists; eexists; split; [reflexivity | eapply bg_nilW].
    + eapply W_inv in l2 as (w & _ & ->). eexists; eexists; split; [reflexivity | eapply bg_oAGd].
    + eapply W_inv in l2 as (w & _ & ->). eexists; eexists; split; [reflexivity | eapply bg_nilGd].
    + eapply oA_inv in l2 as (_ & ->). eexists; eexists; split; [reflexivity | eapply bg_nilGd].
    + eapply guard_step in l2 as (_ & _ & ->). eexists; eexists; split; [reflexivity | eapply bg_oAnil].
    + eapply guard_step in l2 as (_ & _ & ->). eexists; eexists; split; [reflexivity | eapply bg_nilnil].
    + eapply oA_inv in l2 as (_ & ->). eexists; eexists; split; [reflexivity | eapply bg_nilnil].
  - exists X, ({[+ ActOut a +]} ⊎ m). split; [reflexivity | exact hg].
  - exists X, m''. split; [reflexivity | exact hg].
Qed.

Lemma bgood_wt_tau (X : proc) (m : MO (ExtAct TypeOfActions)) r :
  bgood X -> ((X, m) : st) ⟹ r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)), r = (Y, m') /\ bgood Y.
Proof.
  intros hg w. remember ((X, m) : st) as x eqn:Hx.
  remember ([] : trace (ExtAct TypeOfActions)) as s0 eqn:Hs.
  revert X m hg Hx Hs.
  induction w as [ z | s z y t l w IH | μ s z y t l w IH ]; intros X m hg Hx Hs.
  - subst z. exists X, m. split; [reflexivity | exact hg].
  - subst z. subst s. destruct (bgood_tau X m y hg l) as (Y & m' & -> & hg' & _).
    eapply IH; [exact hg' | reflexivity | reflexivity].
  - discriminate.
Qed.

Lemma bgood_wt_act (X : proc) (m : MO (ExtAct TypeOfActions)) (μ : ExtAct TypeOfActions) r :
  bgood X -> ((X, m) : st) ⟹{μ} r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)), r = (Y, m') /\ bgood Y.
Proof.
  intros hg w.
  eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  eapply bgood_wt_tau in w1 as (Y1 & m1 & -> & hg1); [| exact hg].
  eapply bgood_act in l as (Y2 & m2 & -> & hg2); [| exact hg1].
  eapply bgood_wt_tau in w2 as (Y3 & m3 & -> & hg3); [| exact hg2].
  exists Y3, m3. split; [reflexivity | exact hg3].
Qed.

Lemma bgood_cnv (s : trace (ExtAct TypeOfActions)) :
  forall (X : proc) (m : MO (ExtAct TypeOfActions)), bgood X -> ((X, m) : st) ⇓ s.
Proof.
  induction s as [| μ s IH]; intros X m hg.
  - eapply cnv_nil, bgood_term, hg.
  - eapply cnv_act; [eapply bgood_term, hg |].
    intros q' w. eapply bgood_wt_act in w as (Y & m' & -> & hg'); [| exact hg].
    eapply IH, hg'.
Qed.

Lemma bp2_cnv (s : trace (ExtAct TypeOfActions)) : ((Bp2, mt) : st) ⇓ s.
Proof. eapply bgood_cnv, bg_root. Qed.

(** The must preorder restricted to the feedback-free traces does not imply the
    must preorder: on one and the same pair, the termination condition holds
    outright, the acceptance condition holds on every feedback-free trace, and
    the acceptance condition fails on a trace carrying a feedback -- so
    [Pw ≼ₐₛ Bp2] is false ([must_cond2_false_Pw]) while its feedback-free
    restriction holds. *)
Theorem must_ff_not_must :
  (forall s, ((Pw, mt) : st) ⇓ s -> ((Bp2, mt) : st) ⇓ s)
  /\ (forall s q', ¬ has_fb s -> ((Bp2, mt) : st) ⟹[s] q' -> q' ↛ ->
        exists p', ((Pw, mt) : st) ⟹[s] p' /\ p' ↛ /\ coR p' ⊆ coR q')
  /\ has_fb s_cnd2
  /\ ((Pw, mt) : st) ⇓ s_cnd2
  /\ (exists q', ((Bp2, mt) : st) ⟹[s_cnd2] q' /\ q' ↛)
  /\ ¬ (exists p', ((Pw, mt) : st) ⟹[s_cnd2] p').
Proof.
  split; [intros s _; eapply bp2_cnv |].
  exact must_cond2_strictly_weaker.
Qed.

(** A co-trace is the dual trace, and co-convergence the convergence of the
    dual trace. *)
Lemma cocnv_iff_cnv (s : trace (ExtAct TypeOfActions)) :
  forall x : st, x ⇓ᶜᵒ s <-> x ⇓ (map cov s).
Proof.
  induction s as [| μ s IH]; intro x; simpl.
  - split; intro h; inversion h; subst; [eapply cnv_nil | eapply cocnv_nil]; assumption.
  - split; intro h; inversion h; subst.
    + eapply cnv_act; [assumption |]. intros y w.
      eapply IH. eapply H3. eapply cowt_iff_wt. exact w.
    + eapply cocnv_act; [assumption |]. intros y w.
      eapply IH. eapply H3. eapply cowt_iff_wt in w. exact w.
Qed.

(** * Feedback on co-traces: the echo

    Read on a co-trace, [has_fb] bans the pattern "an output [η] appears, and
    its dual input [μ] appears later".  Dualising the whole co-trace, the
    pattern banned on the trace performed by the process is the *echo*: the
    process receives a message and later sends the very same message back.
    This is [has_echo] of [RestrictedSimulation], and the ledger [ef_from]
    together with the simulation [easim] are the tools tailored to it.

    We now separate two processes with an echo.  Both wait for [v0] on [c1];
    [Qe] then offers the two outputs [ā] and [b̄] in parallel, while [Pe] picks
    one of them internally.  Along a trace with an echo -- [a?] then [a!] then
    [b!] -- [Qe] reaches a stable state that [Pe] cannot match, because [Pe]
    has to commit to a single output.  Along every echo-free trace the output
    [a!] is unavailable to [Qe] (it can only be produced after the input [a?]
    that would make the trace an echo), so [Pe]'s internal choice of the [b̄]
    branch always matches. *)

Definition Pch : gproc := (𝛕 • oA) + (𝛕 • oB).
Definition Gch : proc := If (Equality (bvar 0) v0) Then (g Pch) Else 𝟘.
Definition Gpair : proc := If (Equality (bvar 0) v0) Then (oA ‖ oB) Else 𝟘.

(** [Pe] commits to one of the two outputs, [Qe] offers both. *)
Definition Pe : proc := g (c1 ? Gch).
Definition Qe : proc := g (c1 ? Gpair).

Lemma Gch_subst (v : ValueData) : Gch ^ v = If (Equality v v0) Then (g Pch) Else 𝟘.
Proof. vm_compute. reflexivity. Qed.

Lemma Gpair_subst (v : ValueData) : Gpair ^ v = If (Equality v v0) Then (oA ‖ oB) Else 𝟘.
Proof. vm_compute. reflexivity. Qed.

Lemma Gpair_step (v : ValueData) α r : lts (Gpair ^ v) α r -> v = v0 /\ lts (oA ‖ oB) α r.
Proof.
  rewrite Gpair_subst. intro l. inversion l; subst.
  - split; [eapply fires_eq; exact H4 | exact H5].
  - exfalso. inversion H5.
Qed.

Lemma Gch_step (v : ValueData) α r : lts (Gch ^ v) α r -> v = v0 /\ lts (g Pch) α r.
Proof.
  rewrite Gch_subst. intro l. inversion l; subst.
  - split; [eapply fires_eq; exact H4 | exact H5].
  - exfalso. inversion H5.
Qed.

Lemma dead_Gpair (v : ValueData) : v <> v0 -> dead (Gpair ^ v).
Proof. intros ne α r l. eapply Gpair_step in l as (e & _). exact (ne e). Qed.

Lemma dead_Gch (v : ValueData) : v <> v0 -> dead (Gch ^ v).
Proof. intros ne α r l. eapply Gch_step in l as (e & _). exact (ne e). Qed.

Lemma Pe_inv α r : lts Pe α r -> exists v, α = ActExt (ActIn (c1, v)) /\ r = Gch ^ v.
Proof. intro l. inversion l; subst. exists v. split; reflexivity. Qed.

Lemma Qe_inv α r : lts Qe α r -> exists v, α = ActExt (ActIn (c1, v)) /\ r = Gpair ^ v.
Proof. intro l. inversion l; subst. exists v. split; reflexivity. Qed.

Lemma Pch_to_oA (m : MO (ExtAct TypeOfActions)) : (((Gch ^ v0), m) : st) ⟶ (oA, m).
Proof.
  eapply ParLeft. rewrite Gch_subst.
  eapply lts_ifOne; [vm_compute; reflexivity |].
  eapply lts_choiceL, lts_tau.
Qed.

Lemma Pch_to_oB (m : MO (ExtAct TypeOfActions)) : (((Gch ^ v0), m) : st) ⟶ (oB, m).
Proof.
  eapply ParLeft. rewrite Gch_subst.
  eapply lts_ifOne; [vm_compute; reflexivity |].
  eapply lts_choiceR, lts_tau.
Qed.

Lemma no_echo_elem (E : list (ExtAct TypeOfActions)) (η μ : ExtAct TypeOfActions) :
  no_echo_after E η -> μ ∈ E -> ¬ dual η μ.
Proof.
  intros h hin. unfold no_echo_after in h. rewrite List.Forall_forall in h.
  eapply h. clear h.
  induction E as [| y E IH]; [inversion hin |].
  eapply elem_of_cons in hin as [-> | hin]; [left; reflexivity | right; eapply IH; exact hin].
Qed.

(** The mailbox can only hold the message [ā] if the input [a?] has already
    been received: this is the invariant that makes the echo the only way to
    reach the output [ā]. *)
Definition mb_ok (E : list (ExtAct TypeOfActions)) (m : MO (ExtAct TypeOfActions)) : Prop :=
  aOut ∈ m -> aIn ∈ E.

Inductive Rel5 : list (ExtAct TypeOfActions) -> st -> st -> Prop :=
| G1 E m : mb_ok E m -> Rel5 E (Pe, m) (Qe, m)
| G2 E m : aIn ∈ E -> Rel5 E ((Gch ^ v0), m) ((Gpair ^ v0), m)
| G3 E m : aIn ∈ E -> Rel5 E ((g 𝟘), m) ((oA ‖ 𝟘), m)
| Gdead E Xp Xq m : dead Xp -> dead Xq -> Rel5 E ((Xp, m) : st) ((Xq, m) : st).

Lemma Pe_sync (v : ValueData) (m : MO (ExtAct TypeOfActions)) :
  ((Pe, {[+ ActOut (c1, v) +]} ⊎ m) : st) ⟶ ((Gch ^ v), m).
Proof.
  eapply (ParSync (ActIn (c1, v)) (ActOut (c1, v))).
  - split; [reflexivity | exists (c1, v); reflexivity].
  - eapply lts_input.
  - eapply lts_multiset_minus. exists (c1, v). reflexivity.
Qed.

Lemma Rel5_tau1 E p q q' : Rel5 E p q -> q ⟶ q' -> exists p', p ⟹ p' /\ Rel5 E p' q'.
Proof.
  intros hr l. destruct hr as [E m hmb | E m hin | E m hin | E Xp Xq m d1 d2].
  - eapply fw_tau_inv in l as [(X' & l' & ->) | (a & X' & m' & l' & -> & ->)].
    + exfalso. eapply Qe_inv in l' as (v & e & _). discriminate.
    + eapply Qe_inv in l' as (v & e & ->). injection e as ->.
      destruct (Data_dec v v0) as [-> | ne].
      * exists ((Gch ^ v0), m'). split; [eapply wt_one_tau, Pe_sync |].
        eapply G2. eapply hmb. multiset_solver.
      * exists ((Gch ^ v), m'). split; [eapply wt_one_tau, Pe_sync |].
        eapply Gdead; [eapply dead_Gch, ne | eapply dead_Gpair, ne].
  - exfalso. eapply fw_tau_inv in l as [(X' & l' & _) | (a & X' & m' & l' & _ & _)].
    + eapply Gpair_step in l' as (_ & l2). eapply par_inv in l2
        as [(y & l3 & _) | [(y & l3 & _) | [(b & y & z & l4 & l5 & _ & _) | (b & y & z & l4 & l5 & _ & _)]]].
      * eapply oA_inv in l3 as (e & _). discriminate.
      * eapply oB_inv in l3 as (e & _). discriminate.
      * eapply oB_inv in l5 as (e & _). discriminate.
      * eapply oA_inv in l4 as (e & _). discriminate.
    + eapply Gpair_step in l' as (_ & l2). eapply par_inv in l2
        as [(y & l3 & _) | [(y & l3 & _) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply oA_inv in l3 as (e & _). discriminate.
      * eapply oB_inv in l3 as (e & _). discriminate.
      * discriminate.
      * discriminate.
  - exfalso. eapply fw_tau_inv in l as [(X' & l' & _) | (a & X' & m' & l' & _ & _)];
      eapply par_inv in l'
        as [(y & l3 & _) | [(y & l3 & _) | [(b & y & z & l4 & l5 & _ & _) | (b & y & z & l4 & l5 & _ & _)]]];
      try (eapply dead_zero; eassumption).
    + eapply oA_inv in l3 as (e & _). discriminate.
    + eapply oA_inv in l3 as (e & _). discriminate.
  - exfalso. eapply fw_tau_inv in l as [(X' & l' & _) | (a & X' & m' & l' & _ & _)];
      eapply d2; eassumption.
Qed.

Lemma Rel5_tau E p q q' : Rel5 E p q -> q ⟹ q' -> exists p', p ⟹ p' /\ Rel5 E p' q'.
Proof.
  intros hr w.
  remember ([] : trace (ExtAct TypeOfActions)) as s0 eqn:Hs.
  revert p hr Hs.
  induction w as [ z | s z y t l w IH | μ s z y t l w IH ]; intros p hr Hs.
  - exists p. split; [eapply wt_nil | exact hr].
  - subst s. destruct (Rel5_tau1 E p z y hr l) as (p1 & w1 & hr1).
    destruct (IH p1 hr1 eq_refl) as (p2 & w2 & hr2).
    exists p2. split; [eapply wt_join_nil; eassumption | exact hr2].
  - discriminate.
Qed.

Lemma oB_out (m : MO (ExtAct TypeOfActions)) : ((oB, m) : st) ⟶[bOut] ((g 𝟘), m).
Proof. eapply ParLeft. eapply lts_output. Qed.

(** The heart of the matter: [q] can produce [ā] only through its process
    component, and [aIn] is then in the ledger, so the step is barred by
    [no_echo_after].  Every other output is matched by [p] committing to [b̄]. *)
Lemma Rel5_nb1 E p q η q' :
  Rel5 E p q -> non_blocking η -> no_echo_after E η -> q ⟶[η] q' ->
  exists p', p ⟹{η} p' /\ Rel5 E p' q'.
Proof.
  intros hr nb hok l. revert nb hok l.
  destruct hr as [E m hmb | E m hin | E m hin | E Xp Xq m d1 d2]; intros nb hok l.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(a & -> & ->) | (a & m' & -> & -> & ->)]].
    + exfalso. eapply Qe_inv in l' as (v & e & _). injection e as ->.
      destruct nb as (b & e2). discriminate.
    + exfalso. destruct nb as (b & e2). discriminate.
    + exists (Pe, m'). split; [eapply wt_one, q_mb_out |].
      eapply G1. intro h. eapply hmb. multiset_solver.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(a & -> & ->) | (a & m' & -> & -> & ->)]].
    + eapply Gpair_step in l' as (_ & l2). eapply par_inv in l2
        as [(y & l3 & ->) | [(y & l3 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * exfalso. eapply oA_inv in l3 as (e & _). injection e as ->.
        eapply (no_echo_elem E aOut aIn hok hin). eapply dual_iff_co. reflexivity.
      * eapply oB_inv in l3 as (e & ->). injection e as ->.
        exists ((g 𝟘), m). split; [eapply wt_tau; [eapply Pch_to_oB | eapply wt_one, oB_out] |].
        eapply G3, hin.
      * discriminate.
      * discriminate.
    + exfalso. destruct nb as (b & e2). discriminate.
    + exists ((Gch ^ v0), m'). split; [eapply wt_one, q_mb_out |]. eapply G2, hin.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(a & -> & ->) | (a & m' & -> & -> & ->)]].
    + exfalso. eapply par_inv in l'
        as [(y & l3 & ->) | [(y & l3 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply oA_inv in l3 as (e & _). injection e as ->.
        eapply (no_echo_elem E aOut aIn hok hin). eapply dual_iff_co. reflexivity.
      * eapply dead_zero; eassumption.
      * discriminate.
      * discriminate.
    + exfalso. destruct nb as (b & e2). discriminate.
    + exists ((g 𝟘), m'). split; [eapply wt_one, q_mb_out |]. eapply G3, hin.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(a & -> & ->) | (a & m' & -> & -> & ->)]].
    + exfalso. eapply d2; eassumption.
    + exfalso. destruct nb as (b & e2). discriminate.
    + exists (Xp, m'). split; [eapply wt_one, q_mb_out |]. eapply Gdead; assumption.
Qed.

Lemma Pe_in (v : ValueData) (m : MO (ExtAct TypeOfActions)) :
  ((Pe, m) : st) ⟶[ActIn (c1, v)] ((Gch ^ v), m).
Proof. eapply ParLeft. eapply lts_input. Qed.

(** A blocking action either enters the mailbox -- and then it is [a?] that
    puts [ā] there, which is exactly what the ledger records -- or is consumed
    by the process. *)
Lemma Rel5_b1 E p q μ q' :
  Rel5 E p q -> ¬ non_blocking μ -> q ⟶[μ] q' ->
  exists p', p ⟹{μ} p' /\ Rel5 (μ :: E) p' q'.
Proof.
  intros hr nb l. revert nb l.
  destruct hr as [E m hmb | E m hin | E m hin | E Xp Xq m d1 d2]; intros nb l.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(a & -> & ->) | (a & m' & -> & -> & ->)]].
    + eapply Qe_inv in l' as (v & e & ->). injection e as ->.
      exists ((Gch ^ v), m). split; [eapply wt_one, Pe_in |].
      destruct (Data_dec v v0) as [-> | ne].
      * eapply G2. left.
      * eapply Gdead; [eapply dead_Gch, ne | eapply dead_Gpair, ne].
    + exists (Pe, {[+ ActOut a +]} ⊎ m). split; [eapply wt_one, q_mb_in |].
      eapply G1. intro h. destruct (decide (ActOut a = aOut)) as [e | ne].
      * injection e as ->. left.
      * right. eapply hmb. multiset_solver.
    + exfalso. eapply nb. exists a. reflexivity.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(a & -> & ->) | (a & m' & -> & -> & ->)]].
    + exfalso. eapply Gpair_step in l' as (_ & l2). eapply par_inv in l2
        as [(y & l3 & ->) | [(y & l3 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply oA_inv in l3 as (e & _). injection e as ->. eapply nb. exists (c1, v0). reflexivity.
      * eapply oB_inv in l3 as (e & _). injection e as ->. eapply nb. exists (c2, v0). reflexivity.
      * discriminate.
      * discriminate.
    + exists ((Gch ^ v0), {[+ ActOut a +]} ⊎ m). split; [eapply wt_one, q_mb_in |].
      eapply G2. right. exact hin.
    + exfalso. eapply nb. exists a. reflexivity.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(a & -> & ->) | (a & m' & -> & -> & ->)]].
    + exfalso. eapply par_inv in l'
        as [(y & l3 & ->) | [(y & l3 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply oA_inv in l3 as (e & _). injection e as ->. eapply nb. exists (c1, v0). reflexivity.
      * eapply dead_zero; eassumption.
      * discriminate.
      * discriminate.
    + exists ((g 𝟘), {[+ ActOut a +]} ⊎ m). split; [eapply wt_one, q_mb_in |].
      eapply G3. right. exact hin.
    + exfalso. eapply nb. exists a. reflexivity.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(a & -> & ->) | (a & m' & -> & -> & ->)]].
    + exfalso. eapply d2; eassumption.
    + exists (Xp, {[+ ActOut a +]} ⊎ m). split; [eapply wt_one, q_mb_in |].
      eapply Gdead; assumption.
    + exfalso. eapply nb. exists a. reflexivity.
Qed.

Lemma Rel5_nb E p q η q' :
  Rel5 E p q -> non_blocking η -> no_echo_after E η -> q ⟹{η} q' ->
  exists p', p ⟹{η} p' /\ Rel5 E p' q'.
Proof.
  intros hr nb hok w. eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  destruct (Rel5_tau E p q r1 hr w1) as (p1 & wp1 & hr1).
  destruct (Rel5_nb1 E p1 r1 η r2 hr1 nb hok l) as (p2 & wp2 & hr2).
  destruct (Rel5_tau E p2 r2 q' hr2 w2) as (p3 & wp3 & hr3).
  exists p3. split; [| exact hr3].
  eapply wt_push_nil_left; [exact wp1 | eapply wt_push_left; [exact wp2 | exact wp3]].
Qed.

Lemma Rel5_b E p q μ q' :
  Rel5 E p q -> ¬ non_blocking μ -> q ⟹{μ} q' ->
  exists p', p ⟹{μ} p' /\ Rel5 (μ :: E) p' q'.
Proof.
  intros hr nb w. eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  destruct (Rel5_tau E p q r1 hr w1) as (p1 & wp1 & hr1).
  destruct (Rel5_b1 E p1 r1 μ r2 hr1 nb l) as (p2 & wp2 & hr2).
  destruct (Rel5_tau (μ :: E) p2 r2 q' hr2 w2) as (p3 & wp3 & hr3).
  exists p3. split; [| exact hr3].
  eapply wt_push_nil_left; [exact wp1 | eapply wt_push_left; [exact wp2 | exact wp3]].
Qed.

Lemma st_stable_intro (X : proc) (m : MO (ExtAct TypeOfActions)) :
  (forall r, ¬ (((X, m) : st) ⟶ r)) -> ((X, m) : st) ↛.
Proof.
  intro h. destruct (decide (((X, m) : st) ↛)) as [k | k]; [exact k |].
  exfalso. eapply lts_refuses_spec1 in k as (r & l). eapply h; exact l.
Qed.

Lemma oB_stable (m : MO (ExtAct TypeOfActions)) : ((oB, m) : st) ↛.
Proof.
  eapply st_stable_intro. intros r l.
  eapply fw_tau_inv in l as [(X' & l' & _) | (a & X' & m' & l' & _ & _)];
    eapply oB_inv in l' as (e & _); discriminate.
Qed.

Lemma Gpair_out_b : lts (Gpair ^ v0) (ActExt bOut) (oA ‖ (g 𝟘)).
Proof.
  rewrite Gpair_subst. eapply lts_ifOne; [vm_compute; reflexivity |].
  eapply lts_parR. eapply lts_output.
Qed.

Lemma dead_stable (X : proc) (m : MO (ExtAct TypeOfActions)) : dead X -> ((X, m) : st) ↛.
Proof.
  intro d. eapply st_stable_intro. intros r l.
  eapply fw_tau_inv in l as [(X' & l' & _) | (a & X' & m' & l' & _ & _)]; eapply d; eassumption.
Qed.

Lemma Qe_sync (v : ValueData) (m : MO (ExtAct TypeOfActions)) :
  ((Qe, {[+ ActOut (c1, v) +]} ⊎ m) : st) ⟶ ((Gpair ^ v), m).
Proof.
  eapply (ParSync (ActIn (c1, v)) (ActOut (c1, v))).
  - split; [reflexivity | exists (c1, v); reflexivity].
  - eapply lts_input.
  - eapply lts_multiset_minus. exists (c1, v). reflexivity.
Qed.

Lemma Pe_stable_of_Qe (m : MO (ExtAct TypeOfActions)) :
  ((Qe, m) : st) ↛ -> ((Pe, m) : st) ↛.
Proof.
  intro hst. eapply st_stable_intro. intros r l.
  eapply fw_tau_inv in l as [(X' & l' & _) | (a & X' & m' & l' & -> & _)].
  - eapply Pe_inv in l' as (v & e & _). discriminate.
  - eapply Pe_inv in l' as (v & e & _). injection e as ->.
    eapply (lts_refuses_spec2 ((Qe, {[+ ActOut (c1, v) +]} ⊎ m') : st) τ); [| exact hst].
    exists (((Gpair ^ v), m') : st). eapply Qe_sync.
Qed.

(** [p] can always fall back on its [b̄] branch, which accepts strictly less
    than [q]'s parallel pair. *)
Lemma Rel5_stable E p q :
  Rel5 E p q -> q ↛ -> exists p', p ⟹ p' /\ p' ↛ /\ coR p' ⊆ coR q.
Proof.
  intro hr. revert p q hr.
  intros p q hr. destruct hr as [E m hmb | E m hin | E m hin | E Xp Xq m d1 d2]; intro hst.
  - exists ((Pe, m) : st). split; [eapply wt_nil | split; [eapply Pe_stable_of_Qe, hst |]].
    intros μ hm. eapply coR_char in hm as (a & -> & hcase). eapply coR_char.
    exists a. split; [reflexivity |]. destruct hcase as [(X' & l') | hin]; [| right; exact hin].
    exfalso. eapply Pe_inv in l' as (v & e & _). discriminate.
  - exists ((oB, m) : st). split; [eapply wt_one_tau, Pch_to_oB | split; [eapply oB_stable |]].
    intros μ hm. eapply coR_char in hm as (a & -> & hcase). eapply coR_char.
    exists a. split; [reflexivity |]. destruct hcase as [(X' & l') | hin2]; [| right; exact hin2].
    left. eapply oB_inv in l' as (e & _). injection e as ->.
    exists (oA ‖ (g 𝟘)). eapply Gpair_out_b.
  - exists (((g 𝟘), m) : st). split; [eapply wt_nil | split; [eapply dead_stable, dead_zero |]].
    intros μ hm. eapply coR_char in hm as (a & -> & hcase). eapply coR_char.
    exists a. split; [reflexivity |]. destruct hcase as [(X' & l') | hin2]; [| right; exact hin2].
    exfalso. eapply dead_zero; eassumption.
  - exists ((Xp, m) : st). split; [eapply wt_nil | split; [eapply dead_stable, d1 |]].
    intros μ hm. eapply coR_char in hm as (a & -> & hcase). eapply coR_char.
    exists a. split; [reflexivity |]. destruct hcase as [(X' & l') | hin2]; [| right; exact hin2].
    exfalso. eapply d1; eassumption.
Qed.

Theorem Rel5_easim : easim Rel5.
Proof.
  split; [exact Rel5_tau | split; [exact Rel5_stable | split; [exact Rel5_nb | exact Rel5_b]]].
Qed.

Lemma Rel5_init : Rel5 [] ((Pe, mt) : st) ((Qe, mt) : st).
Proof. eapply G1. intro h. exfalso. multiset_solver. Qed.

(** On every echo-free trace, each stable state of [Qe] is matched by a stable
    state of [Pe] accepting no more. *)
Theorem pe_qe_cond2_ef (s : trace (ExtAct TypeOfActions)) (q' : st) :
  ¬ has_echo s -> ((Qe, mt) : st) ⟹[s] q' -> q' ↛ ->
  exists p', ((Pe, mt) : st) ⟹[s] p' /\ p' ↛ /\ coR p' ⊆ coR q'.
Proof. eapply (easim_cond2_ef Rel5 Rel5_easim (Pe, mt) (Qe, mt) s q' Rel5_init). Qed.

(** ** [Pe] cannot answer the echo

    After the input [a?], [Pe] is in one of four states; from each of them the
    output [ā] leaves it with nothing more to say. *)

Lemma Pch_inv α r : lts (g Pch) α r -> α = τ /\ (r = oA \/ r = oB).
Proof.
  intro l. inversion l; subst.
  - inversion H3; subst. split; [reflexivity | left; reflexivity].
  - inversion H3; subst. split; [reflexivity | right; reflexivity].
Qed.

Lemma oA_stable (m : MO (ExtAct TypeOfActions)) : ((oA, m) : st) ↛.
Proof.
  eapply st_stable_intro. intros r l.
  eapply fw_tau_inv in l as [(X' & l' & _) | (a & X' & m' & l' & _ & _)];
    eapply oA_inv in l' as (e & _); discriminate.
Qed.

Lemma Pe_mt_stable : ((Pe, mt) : st) ↛.
Proof.
  eapply st_stable_intro. intros r l.
  eapply fw_tau_inv in l as [(X' & l' & _) | (a & X' & m' & l' & e & _)].
  - eapply Pe_inv in l' as (v & e & _). discriminate.
  - unfold mt in e. multiset_solver.
Qed.

Lemma Gch_v0_tau (r : st) :
  ((Gch ^ v0, mt) : st) ⟶ r -> r = ((oA, mt) : st) \/ r = ((oB, mt) : st).
Proof.
  intro l. eapply fw_tau_inv in l as [(X' & l' & ->) | (a & X' & m' & l' & e & _)].
  - eapply Gch_step in l' as (_ & l2). eapply Pch_inv in l2 as (_ & [-> | ->]);
      [left | right]; reflexivity.
  - exfalso. unfold mt in e. multiset_solver.
Qed.

Lemma Pe_aOut_tau (r : st) : ((Pe, {[+ aOut +]} ⊎ mt) : st) ⟶ r -> r = ((Gch ^ v0, mt) : st).
Proof.
  intro l. eapply fw_tau_inv in l as [(X' & l' & _) | (a & X' & m' & l' & e & ->)].
  - exfalso. eapply Pe_inv in l' as (v & ea & _). discriminate.
  - eapply Pe_inv in l' as (v & ea & ->). injection ea as ->.
    destruct (decide (ActOut (c1, v) = aOut)) as [eq | ne].
    + rewrite <- eq in e. eapply mb_eq_cancel in e. subst m'.
      unfold aOut in eq. assert (v = v0) as -> by congruence. reflexivity.
    + exfalso. eapply mb_neq_in in e as (hin & _); [| exact ne].
      unfold mt in hin. multiset_solver.
Qed.

Definition PS (x : st) : Prop :=
  x = ((Pe, {[+ aOut +]} ⊎ mt) : st) \/ x = ((Gch ^ v0, mt) : st)
  \/ x = ((oA, mt) : st) \/ x = ((oB, mt) : st).

Lemma PS_tau (x y : st) : PS x -> x ⟶ y -> PS y.
Proof.
  intros [-> | [-> | [-> | ->]]] l.
  - eapply Pe_aOut_tau in l as ->. right; left; reflexivity.
  - eapply Gch_v0_tau in l as [-> | ->]; [right; right; left | right; right; right]; reflexivity.
  - exfalso. eapply (lts_refuses_spec2 ((oA, mt) : st) τ); [exists y; exact l | eapply oA_stable].
  - exfalso. eapply (lts_refuses_spec2 ((oB, mt) : st) τ); [exists y; exact l | eapply oB_stable].
Qed.

Lemma PS_wt (x y : st) : PS x -> x ⟹ y -> PS y.
Proof.
  intros hx w. remember ([] : trace (ExtAct TypeOfActions)) as s0 eqn:Hs.
  revert hx Hs. induction w as [ z | s z y1 t l w IH | μ s z y1 t l w IH ]; intros hx Hs.
  - exact hx.
  - subst s. eapply IH; [eapply PS_tau; eassumption | reflexivity].
  - discriminate.
Qed.

Lemma Pe_mt_aIn (r : st) : ((Pe, mt) : st) ⟹{aIn} r -> PS r.
Proof.
  intro w. eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  eapply wt_nil_stable in w1; [| eapply Pe_mt_stable]. subst r1.
  eapply (PS_wt r2 r); [| exact w2].
  eapply fw_act_inv in l as [(X' & l' & ->) | [(a & e & ->) | (a & m' & e & _ & _)]].
  - eapply Pe_inv in l' as (v & ea & ->). unfold aIn in ea.
    assert (v = v0) as -> by congruence. right; left; reflexivity.
  - assert (a = (c1, v0)) as -> by (unfold aIn in e; congruence). left. reflexivity.
  - unfold aIn in e. discriminate.
Qed.

Definition PS2 (x : st) : Prop := x = ((Pe, mt) : st) \/ x = (((g 𝟘), mt) : st).

Lemma PS2_stable (x : st) : PS2 x -> x ↛.
Proof. intros [-> | ->]; [eapply Pe_mt_stable | eapply dead_stable, dead_zero]. Qed.

Lemma PS_aOut1 (x y : st) : PS x -> x ⟶[aOut] y -> PS2 y.
Proof.
  intros [-> | [-> | [-> | ->]]] l.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(a & e & ->) | (a & m' & e & e2 & ->)]].
    + exfalso. eapply Pe_inv in l' as (v & ea & _). discriminate.
    + discriminate.
    + rewrite <- e in e2. eapply mb_eq_cancel in e2. subst m'. left. reflexivity.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(a & e & ->) | (a & m' & e & e2 & ->)]].
    + exfalso. eapply Gch_step in l' as (_ & l2). eapply Pch_inv in l2 as (ea & _). discriminate.
    + discriminate.
    + exfalso. unfold mt in e2. multiset_solver.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(a & e & ->) | (a & m' & e & e2 & ->)]].
    + eapply oA_inv in l' as (_ & ->). right. reflexivity.
    + discriminate.
    + exfalso. unfold mt in e2. multiset_solver.
  - eapply fw_act_inv in l as [(X' & l' & ->) | [(a & e & ->) | (a & m' & e & e2 & ->)]].
    + exfalso. eapply oB_inv in l' as (ea & _). unfold aOut, bOut, c1, c2 in ea. discriminate.
    + discriminate.
    + exfalso. unfold mt in e2. multiset_solver.
Qed.

Lemma PS_aOut (x y : st) : PS x -> x ⟹{aOut} y -> PS2 y.
Proof.
  intros hx w. eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  eapply (PS_wt x r1) in w1; [| exact hx].
  eapply PS_aOut1 in l as h2; [| exact w1].
  eapply wt_nil_stable in w2; [| eapply PS2_stable, h2]. subst y. exact h2.
Qed.

Lemma PS2_no_bOut (x : st) : PS2 x -> ¬ exists y, x ⟹{bOut} y.
Proof.
  intros hx (y & w). eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  eapply wt_nil_stable in w1; [| eapply PS2_stable, hx]. subst r1.
  destruct hx as [-> | ->];
    eapply fw_act_inv in l as [(X' & l' & _) | [(a & e & _) | (a & m' & e & e2 & _)]].
  - eapply Pe_inv in l' as (v & ea & _). discriminate.
  - discriminate.
  - unfold mt in e2. multiset_solver.
  - eapply dead_zero; eassumption.
  - discriminate.
  - unfold mt in e2. multiset_solver.
Qed.

(** The separating trace: [Qe] receives [a], echoes it back and still has [b̄]
    to send; [Pe] has spent its single branch. *)
Definition s_echo : trace (ExtAct TypeOfActions) := [aIn; aOut; bOut].

Lemma pe_no_s_echo : ¬ exists r, ((Pe, mt) : st) ⟹[s_echo] r.
Proof.
  intros (r & w).
  eapply wt_pop in w as (t1 & w1 & w2). eapply Pe_mt_aIn in w1.
  eapply wt_pop in w2 as (t2 & w3 & w4). eapply PS_aOut in w3; [| exact w1].
  eapply PS2_no_bOut; [exact w3 | exists r; exact w4].
Qed.

Lemma Gch_v0_term : ((Gch ^ v0, mt) : st) ⤓.
Proof.
  eapply tstep. intros y l. eapply Gch_v0_tau in l as [-> | ->];
    [eapply stable_term, oA_stable | eapply stable_term, oB_stable].
Qed.

Lemma PS_term (x : st) : PS x -> x ⤓.
Proof.
  intros [-> | [-> | [-> | ->]]].
  - eapply tstep. intros y l. eapply Pe_aOut_tau in l as ->. eapply Gch_v0_term.
  - eapply Gch_v0_term.
  - eapply stable_term, oA_stable.
  - eapply stable_term, oB_stable.
Qed.

Lemma pe_cnv_s_echo : ((Pe, mt) : st) ⇓ s_echo.
Proof.
  eapply cnv_act; [eapply stable_term, Pe_mt_stable |].
  intros p1 w1. eapply Pe_mt_aIn in w1.
  eapply cnv_act; [eapply PS_term, w1 |].
  intros p2 w2. eapply PS_aOut in w2; [| exact w1].
  eapply cnv_act; [eapply stable_term, PS2_stable, w2 |].
  intros p3 w3. exfalso. eapply PS2_no_bOut; [exact w2 | exists p3; exact w3].
Qed.

Lemma Qe_in (v : ValueData) (m : MO (ExtAct TypeOfActions)) :
  ((Qe, m) : st) ⟶[ActIn (c1, v)] ((Gpair ^ v), m).
Proof. eapply ParLeft. eapply lts_input. Qed.

Lemma Gpair_out_a : lts (Gpair ^ v0) (ActExt aOut) ((g 𝟘) ‖ oB).
Proof.
  rewrite Gpair_subst. eapply lts_ifOne; [vm_compute; reflexivity |].
  eapply lts_parL. eapply lts_output.
Qed.

Lemma qe_reaches_stable : ((Qe, mt) : st) ⟹[s_echo] ((((g 𝟘) ‖ (g 𝟘)), mt) : st).
Proof.
  eapply wt_act; [eapply (Qe_in v0 mt) |].
  eapply wt_act; [eapply ParLeft, Gpair_out_a |].
  eapply wt_act; [eapply ParLeft, lts_parR, lts_output |].
  eapply wt_nil.
Qed.

Lemma nilnil_e_stable : ((((g 𝟘) ‖ (g 𝟘)), mt) : st) ↛.
Proof. eapply dead_stable, dead_par; eapply dead_zero. Qed.

Lemma s_echo_has_echo : has_echo s_echo.
Proof.
  simpl. left. split.
  - intros (b & e). discriminate.
  - econstructor. split; [exists (c1, v0); reflexivity | eapply dual_iff_co; reflexivity].
Qed.

(** ** The echo on a trace is exactly the feedback on the dual co-trace *)

Lemma cov_in (a : TypeOfActions) : cov (ActIn a) = ActOut a.
Proof. reflexivity. Qed.

Lemma cov_out (a : TypeOfActions) : cov (ActOut a) = ActIn a.
Proof. reflexivity. Qed.

Lemma cov_nb (x : ExtAct TypeOfActions) : non_blocking (cov x) <-> ¬ non_blocking x.
Proof.
  destruct x as [a | a].
  - rewrite cov_in. split.
    + intros _ (b & e). discriminate.
    + intros _. exists a. reflexivity.
  - rewrite cov_out. split.
    + intros (b & e). discriminate.
    + intro h. exfalso. eapply h. exists a. reflexivity.
Qed.

Lemma dual_cov2 (x y : ExtAct TypeOfActions) : dual y x <-> x = cov y.
Proof. eapply dual_iff_co. Qed.

Lemma dual_cov (x y : ExtAct TypeOfActions) : dual (cov y) (cov x) <-> cov x = y.
Proof. rewrite dual_cov2. rewrite cov_invol. reflexivity. Qed.

Lemma exists_map_cov (P : ExtAct TypeOfActions -> Prop) (l : trace (ExtAct TypeOfActions)) :
  Exists P (map cov l) <-> Exists (fun x => P (cov x)) l.
Proof.
  induction l as [| y l IH]; simpl.
  - split; intro h; inversion h.
  - split; intro h; inversion h; subst;
      [left | right; eapply IH | left | right; eapply IH]; assumption.
Qed.

Lemma exists_echo_cov (x : ExtAct TypeOfActions) (s : trace (ExtAct TypeOfActions)) :
  non_blocking (cov x) ->
  (Exists (fun η => non_blocking η /\ dual η x) s <-> Exists (fun μ => dual μ (cov x)) (map cov s)).
Proof.
  intro hnb. rewrite exists_map_cov. split; intro h; induction h as [y l hy | y l _ IH].
  - left. eapply dual_cov. destruct hy as (_ & d). eapply dual_cov2 in d. subst x.
    eapply cov_invol.
  - right. exact IH.
  - left. eapply dual_cov in hy. subst y. split;
      [exact hnb | eapply dual_cov2; rewrite cov_invol; reflexivity].
  - right. exact IH.
Qed.

(** An echo on a trace is exactly a feedback on the dual co-trace: this is the
    bridge between [easim], which lives on traces, and the statement the user
    asks for, which reads [has_fb] on co-traces. *)
Theorem has_echo_cov (s : trace (ExtAct TypeOfActions)) : has_echo s <-> has_fb (map cov s).
Proof.
  induction s as [| x s IH]; simpl; [reflexivity |].
  unfold dual_later. rewrite <- IH.
  destruct (decide (non_blocking x)) as [nb | nb].
  - split.
    + intros [(h1 & _) | h]; [exfalso; exact (h1 nb) | right; exact h].
    + intros [(h1 & _) | h]; [exfalso; eapply cov_nb in h1; exact (h1 nb) | right; exact h].
  - assert (non_blocking (cov x)) as hnb by (eapply cov_nb, nb).
    rewrite (exists_echo_cov x s hnb). tauto.
Qed.

(** ** [Qe] converges on every trace

    [Qe] is finite and recursion-free: apart from the root, every state it
    reaches is inert, and the root's only silent step consumes a message. *)

Lemma inert_Gpair (v : ValueData) : inert (Gpair ^ v).
Proof.
  destruct (inert_par oA oB inert_oA inert_oB) as (ht & hi). split; intros.
  - intro l. eapply Gpair_step in l as (_ & l2). eapply ht; exact l2.
  - intro l. eapply Gpair_step in l as (_ & l2). eapply hi; exact l2.
Qed.

Inductive egood : proc -> Prop :=
| eg_root : egood Qe
| eg_pair v : egood (Gpair ^ v)
| eg_nilB : egood ((g 𝟘) ‖ oB)
| eg_Anil : egood (oA ‖ (g 𝟘))
| eg_nilnil : egood ((g 𝟘) ‖ (g 𝟘)).

Lemma egood_inert (X : proc) : egood X -> X = Qe \/ inert X.
Proof.
  intros [ | v | | | ]; [left; reflexivity | right | right | right | right].
  - eapply inert_Gpair.
  - eapply inert_par; [eapply inert_dead, dead_zero | eapply inert_oB].
  - eapply inert_par; [eapply inert_oA | eapply inert_dead, dead_zero].
  - eapply inert_par; eapply inert_dead, dead_zero.
Qed.

Lemma egood_tau (X : proc) (m : MO (ExtAct TypeOfActions)) r :
  egood X -> ((X, m) : st) ⟶ r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)),
    r = (Y, m') /\ egood Y /\ (m' ⊂ m \/ (m' = m /\ inert Y)).
Proof.
  intros hg l. destruct (egood_inert X hg) as [-> | hin].
  - eapply fw_tau_inv in l as [(X' & l' & _) | (a & X' & m' & l' & -> & ->)].
    + exfalso. eapply Qe_inv in l' as (v & e & _). discriminate.
    + eapply Qe_inv in l' as (v & e & ->). exists (Gpair ^ v), m'.
      split; [reflexivity | split; [eapply eg_pair | left; multiset_solver]].
  - exfalso. eapply inert_no_tau; eassumption.
Qed.

Lemma egood_act (X : proc) (m : MO (ExtAct TypeOfActions)) (μ : ExtAct TypeOfActions) r :
  egood X -> ((X, m) : st) ⟶[μ] r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)), r = (Y, m') /\ egood Y.
Proof.
  intros hg l.
  eapply fw_act_inv in l as [(X' & l' & ->) | [(a & -> & ->) | (a & m'' & -> & -> & ->)]].
  - destruct hg as [ | v | | | ].
    + eapply Qe_inv in l' as (w & _ & ->).
      eexists; eexists; split; [reflexivity | eapply eg_pair].
    + eapply Gpair_step in l' as (_ & l2). eapply par_inv in l2
        as [(y & l3 & ->) | [(y & l3 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply oA_inv in l3 as (_ & ->). eexists; eexists; split; [reflexivity | eapply eg_nilB].
      * eapply oB_inv in l3 as (_ & ->). eexists; eexists; split; [reflexivity | eapply eg_Anil].
      * discriminate.
      * discriminate.
    + eapply par_inv in l'
        as [(y & l3 & ->) | [(y & l3 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * exfalso. eapply dead_zero; eassumption.
      * eapply oB_inv in l3 as (_ & ->). eexists; eexists; split; [reflexivity | eapply eg_nilnil].
      * discriminate.
      * discriminate.
    + eapply par_inv in l'
        as [(y & l3 & ->) | [(y & l3 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]].
      * eapply oA_inv in l3 as (_ & ->). eexists; eexists; split; [reflexivity | eapply eg_nilnil].
      * exfalso. eapply dead_zero; eassumption.
      * discriminate.
      * discriminate.
    + eapply par_inv in l'
        as [(y & l3 & ->) | [(y & l3 & ->) | [(b & y & z & _ & _ & e & _) | (b & y & z & _ & _ & e & _)]]];
      try (exfalso; eapply dead_zero; eassumption); discriminate.
  - exists X, ({[+ ActOut a +]} ⊎ m). split; [reflexivity | exact hg].
  - exists X, m''. split; [reflexivity | exact hg].
Qed.

Lemma egood_term (m : MO (ExtAct TypeOfActions)) : forall X, egood X -> ((X, m) : st) ⤓.
Proof.
  induction m as [m IH] using (well_founded_induction gmultiset_wf).
  intros X hg. eapply tstep. intros y l.
  destruct (egood_tau X m y hg l) as (Y & m' & -> & hg' & [hs | (-> & hin)]).
  - eapply IH; eassumption.
  - eapply stable_term, stable_of_inert, hin.
Qed.

Lemma egood_wt_tau (X : proc) (m : MO (ExtAct TypeOfActions)) r :
  egood X -> ((X, m) : st) ⟹ r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)), r = (Y, m') /\ egood Y.
Proof.
  intros hg w. remember ((X, m) : st) as x eqn:Hx.
  remember ([] : trace (ExtAct TypeOfActions)) as s0 eqn:Hs.
  revert X m hg Hx Hs.
  induction w as [ z | s z y t l w IH | μ s z y t l w IH ]; intros X m hg Hx Hs.
  - subst z. exists X, m. split; [reflexivity | exact hg].
  - subst z. subst s. destruct (egood_tau X m y hg l) as (Y & m' & -> & hg' & _).
    eapply IH; [exact hg' | reflexivity | reflexivity].
  - discriminate.
Qed.

Lemma egood_wt_act (X : proc) (m : MO (ExtAct TypeOfActions)) (μ : ExtAct TypeOfActions) r :
  egood X -> ((X, m) : st) ⟹{μ} r ->
  exists (Y : proc) (m' : MO (ExtAct TypeOfActions)), r = (Y, m') /\ egood Y.
Proof.
  intros hg w.
  eapply wt_decomp_one in w as (r1 & r2 & w1 & l & w2).
  eapply egood_wt_tau in w1 as (Y1 & m1 & -> & hg1); [| exact hg].
  eapply egood_act in l as (Y2 & m2 & -> & hg2); [| exact hg1].
  eapply egood_wt_tau in w2 as (Y3 & m3 & -> & hg3); [| exact hg2].
  exists Y3, m3. split; [reflexivity | exact hg3].
Qed.

Lemma egood_cnv (s : trace (ExtAct TypeOfActions)) :
  forall (X : proc) (m : MO (ExtAct TypeOfActions)), egood X -> ((X, m) : st) ⇓ s.
Proof.
  induction s as [| μ s IH]; intros X m hg.
  - eapply cnv_nil, egood_term, hg.
  - eapply cnv_act; [eapply egood_term, hg |].
    intros q' w. eapply egood_wt_act in w as (Y & m' & -> & hg'); [| exact hg].
    eapply IH, hg'.
Qed.

Lemma qe_cnv (s : trace (ExtAct TypeOfActions)) : ((Qe, mt) : st) ⇓ s.
Proof. eapply egood_cnv, eg_root. Qed.

(** ** The must preorder read on co-traces, restricted to those without a
       feedback, does not imply the must preorder

    [s_bad = ā ; a ; b] is a co-trace with a feedback; the trace it stands for
    is [s_echo = a ; ā ; b̄], an echo. *)

Lemma map_cov_s_bad : map cov s_bad = s_echo.
Proof. reflexivity. Qed.

Lemma map_cov_s_echo : map cov s_echo = s_bad.
Proof. reflexivity. Qed.

Lemma s_bad_has_fb : has_fb s_bad.
Proof. rewrite <- map_cov_s_echo. eapply has_echo_cov, s_echo_has_echo. Qed.

Theorem pe_qe_co_cond2_ff (s : trace (ExtAct TypeOfActions)) (q' : st) :
  ¬ has_fb s -> ((Qe, mt) : st) ⟹ᶜᵒ[s] q' -> q' ↛ ->
  exists p', ((Pe, mt) : st) ⟹ᶜᵒ[s] p' /\ p' ↛ /\ coR p' ⊆ coR q'.
Proof.
  intros hfb w hst. eapply cowt_iff_wt in w.
  assert (¬ has_echo (map cov s)) as hec.
  { intro h. eapply has_echo_cov in h. rewrite map_cov_invol in h. exact (hfb h). }
  destruct (pe_qe_cond2_ef (map cov s) q' hec w hst) as (p' & wp & hp & hsub).
  exists p'. split; [eapply cowt_iff_wt, wp | split; [exact hp | exact hsub]].
Qed.

Lemma pe_cocnv_s_bad : ((Pe, mt) : st) ⇓ᶜᵒ s_bad.
Proof. eapply cocnv_iff_cnv. rewrite map_cov_s_bad. eapply pe_cnv_s_echo. Qed.

Lemma qe_co_reaches_stable : ((Qe, mt) : st) ⟹ᶜᵒ[s_bad] ((((g 𝟘) ‖ (g 𝟘)), mt) : st).
Proof. eapply cowt_iff_wt. rewrite map_cov_s_bad. eapply qe_reaches_stable. Qed.

Lemma pe_no_co_s_bad : ¬ exists p', ((Pe, mt) : st) ⟹ᶜᵒ[s_bad] p'.
Proof.
  intros (p' & w). eapply cowt_iff_wt in w. rewrite map_cov_s_bad in w.
  eapply pe_no_s_echo. exists p'. exact w.
Qed.

(** Both conditions of [≼꜀ₒ₋ₐₛ] restricted to the feedback-free co-traces hold
    for the pair [Pe], [Qe] -- the termination condition outright, since [Qe]
    converges everywhere -- and the acceptance condition fails on the co-trace
    [s_bad], which carries a feedback. *)
Theorem co_must_cond2_strictly_weaker :
  (forall s, ((Pe, mt) : st) ⇓ᶜᵒ s -> ((Qe, mt) : st) ⇓ᶜᵒ s)
  /\ (forall s q', ¬ has_fb s -> ((Qe, mt) : st) ⟹ᶜᵒ[s] q' -> q' ↛ ->
        exists p', ((Pe, mt) : st) ⟹ᶜᵒ[s] p' /\ p' ↛ /\ coR p' ⊆ coR q')
  /\ has_fb s_bad
  /\ ((Pe, mt) : st) ⇓ᶜᵒ s_bad
  /\ (exists q', ((Qe, mt) : st) ⟹ᶜᵒ[s_bad] q' /\ q' ↛)
  /\ ¬ (exists p', ((Pe, mt) : st) ⟹ᶜᵒ[s_bad] p').
Proof.
  split; [intros s _; eapply cocnv_iff_cnv, qe_cnv |].
  split; [exact pe_qe_co_cond2_ff |].
  split; [exact s_bad_has_fb |].
  split; [exact pe_cocnv_s_bad |].
  split; [| exact pe_no_co_s_bad].
  exists ((((g 𝟘) ‖ (g 𝟘)), mt) : st).
  split; [exact qe_co_reaches_stable | exact nilnil_e_stable].
Qed.

(** And the failure of the co-condition itself, for an arbitrary abstraction. *)
Section CoCond2GenericPe.

  Context {T FinA PreAct : Type}.
  Context {Φ : ExtAct TypeOfActions -> FinA} {𝝳P 𝝳Q : FinA -> PreAct}.
  Context {gLtsT : gLtsEq T VACCS_ExtAction}.
  Context (AbsP : @AbsAction st T FinA PreAct (ExtAct TypeOfActions) VACCS_ExtAction Φ 𝝳P _ gLtsT).
  Context (AbsQ : @AbsAction st T FinA PreAct (ExtAct TypeOfActions) VACCS_ExtAction Φ 𝝳Q _ gLtsT).

  Theorem co_must_cond2_false_Pe :
    ¬ @bhv_pre_co_cond2 st (ExtAct TypeOfActions) VACCS_ExtAction _ T FinA PreAct Φ 𝝳P gLtsT AbsP
        st _ 𝝳Q AbsQ ((Pe, mt) : st) ((Qe, mt) : st).
  Proof.
    intro h.
    destruct (h s_bad ((((g 𝟘) ‖ (g 𝟘)), mt) : st) pe_cocnv_s_bad qe_co_reaches_stable
                nilnil_e_stable) as (p' & w & _ & _).
    eapply pe_no_co_s_bad. exists p'. exact w.
  Qed.

  (** A fortiori the whole co-preorder fails, although its termination
      condition holds ([qe_cnv]) and its acceptance condition holds on every
      feedback-free co-trace ([pe_qe_co_cond2_ff]). *)
  Theorem co_must_false_Pe :
    ¬ @bhv_pre_co st (ExtAct TypeOfActions) VACCS_ExtAction _ T FinA PreAct Φ 𝝳P gLtsT AbsP
        st _ 𝝳Q AbsQ ((Pe, mt) : st) ((Qe, mt) : st).
  Proof. intros (_ & h2). eapply co_must_cond2_false_Pe, h2. Qed.

  (** The positive halves in the abstracted form, under the same shared-[𝝳]
      hypothesis as [pw_bp2_cond2_ff_abs]. *)
  Context (same_delta : forall x, 𝝳P x = 𝝳Q x).

  Lemma co_abs_of_coR_sub (p q : st) :
    coR p ⊆ coR q -> ⌈ (𝝳P ∘ Φ) ⌉ (coR p) ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q).
  Proof.
    intros hsub y hy.
    eapply (map_set_mono (𝝳P ∘ Φ) (coR p) (coR q) hsub) in hy as (μ & hμ & ->).
    exists μ. split; [exact hμ | eapply same_delta].
  Qed.

  Theorem pe_qe_cond2_ef_abs (s : trace (ExtAct TypeOfActions)) (q' : st) :
    ¬ has_echo s -> ((Qe, mt) : st) ⟹[s] q' -> q' ↛ ->
    exists p', ((Pe, mt) : st) ⟹[s] p' /\ p' ↛
               /\ ⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q').
  Proof.
    intros hec w hst. destruct (pe_qe_cond2_ef s q' hec w hst) as (p' & wp & hp & hsub).
    exists p'. split; [exact wp | split; [exact hp | eapply co_abs_of_coR_sub, hsub]].
  Qed.

  Theorem pe_qe_co_cond2_ff_abs (s : trace (ExtAct TypeOfActions)) (q' : st) :
    ¬ has_fb s -> ((Qe, mt) : st) ⟹ᶜᵒ[s] q' -> q' ↛ ->
    exists p', ((Pe, mt) : st) ⟹ᶜᵒ[s] p' /\ p' ↛
               /\ ⌈ (𝝳P ∘ Φ) ⌉ (coR p') ⊆ ⌈ (𝝳Q ∘ Φ) ⌉ (coR q').
  Proof.
    intros hfb w hst. destruct (pe_qe_co_cond2_ff s q' hfb w hst) as (p' & wp & hp & hsub).
    exists p'. split; [exact wp | split; [exact hp | eapply co_abs_of_coR_sub, hsub]].
  Qed.

End CoCond2GenericPe.
