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
     RestrictedSimulation RestrictedPreorders Subset_Act coConvergence
     DefinitionTI DefinitionTIco DefinitionAS DefinitionASco
     FeedbackNotReversible.

(** [NatVP] -- the instantiation of the VACCS parameters used by all the
    counterexamples -- is declared [#[local]] in [FeedbackNotReversible.v], so
    it has to be put back in the instance database here. *)
#[local] Existing Instance NatVP.

(** * None of the four feedback-free preorders implies its counterpart

    [FeedbackNotReversible.v] separates the alternative preorders of the
    development from their restrictions to the traces carrying no feedback, but
    states the separations in unfolded form, on [⟹[s]] and [⟹ᶜᵒ[s]].  This
    file restates them with the notations of [RestrictedPreorders.v], and
    settles the one case the big file leaves open, plain co-trace inclusion.

    The four pairs of VACCS processes, in the forwarder lifting with an empty
    mailbox:

      [≼ₜᵢⁿᶠᵇ]      [Bp2] against [Q0]      separated by the trace    [ā ; a ; b̄]
      [≼꜀ₒ₋ₜᵢⁿᶠᵇ]   [Qe]  against [Pe]      separated by the co-trace [ā ; a ; b]
      [≼ₐₛⁿᶠᵇ]      [Pw]  against [Bp2]     separated by the trace    [ā ; a ; b̄]
      [≼꜀ₒ₋ₐₛⁿᶠᵇ]   [Pe]  against [Qe]      separated by the co-trace [ā ; a ; b]

    with

      [Q0  = 𝛕•ā + 𝛕•b̄]
      [Bp2 = ā ‖ c1 ? Gd]                       where [Gd = If x = v0 Then b̄ Else 𝟘]
      [Pw  = 𝛕•(ā ‖ c1 ? 𝟘) + 𝛕•b̄ + c1 ? (ā ‖ Gd)]
      [Pe  = c1 ? (If x = v0 Then 𝛕•ā + 𝛕•b̄ Else 𝟘)]
      [Qe  = c1 ? (If x = v0 Then ā ‖ b̄ Else 𝟘)] *)

(** * co-Trace inclusion: the missing separation

    Everything here is read on co-traces, with [has_fb] taken literally on the
    co-trace, exactly as [pe_qe_co_cond2_ff] and [bhv_pre_co_cond2] do.  No
    detour through the dual trace and [has_echo] is needed: [easim] and the
    echo are what *proves* [pe_qe_co_cond2_ff] inside
    [FeedbackNotReversible.v], but its statement is already co-native, and it
    is the only thing used below.

    The negative half is immediate: [Qe] answers the co-trace [s_bad], which
    carries a feedback, and [Pe] does not ([qe_co_reaches_stable],
    [pe_no_co_s_bad]).

    The positive half is the inclusion of the feedback-free co-traces, and it
    does not follow from [pe_qe_co_cond2_ff] on the nose: that lemma only
    matches the states of [Qe] that are *stable*.  It does follow because [Qe]
    converges on every co-trace: the state reached terminates, so it can be
    driven silently to a stable one, which extends the co-weak transition
    without touching the co-trace read so far. *)

(** A silent computation is a co-weak transition on the empty co-trace: the
    empty co-trace is dual to the empty trace. *)
Lemma wt_nil_to_cowt_nil `{gLts P A} (p q : P) : p ⟹ q -> p ⟹ᶜᵒ q.
Proof. intro w. eapply (wt_to_cowt_dual p [] q w []). constructor. Qed.

(** [Qe] converges on every co-trace: it converges on every trace ([qe_cnv]),
    and a co-trace is answered along some dual trace ([cowt_to_wt_dual]). *)
Lemma qe_cocnv (s : trace (ExtAct TypeOfActions)) : ((Qe, mt) : st) ⇓ᶜᵒ s.
Proof.
  eapply cocnv_iff_prefix_terminate_r. intros t q _ w.
  destruct (cowt_to_wt_dual ((Qe, mt) : st) t q w) as (t' & _ & w').
  eapply (cnv_iff_prefix_terminate_l ((Qe, mt) : st) t' (qe_cnv t') t' q
            ltac:(reflexivity) w').
Qed.

(** Every feedback-free co-trace of [Qe] is a co-trace of [Pe]. *)
Theorem qe_pe_co_ti_nfb : ((Qe, mt) : st) ≼꜀ₒ₋ₜᵢⁿᶠᵇ ((Pe, mt) : st).
Proof.
  intros s hfb (q' & w).
  pose proof (cocnv_iff_prefix_terminate_l ((Qe, mt) : st) s (qe_cocnv s) s q'
                ltac:(reflexivity) w) as hterm.
  destruct (terminate_then_wt_refuses q' hterm) as (q'' & wn & hst).
  assert (((Qe, mt) : st) ⟹ᶜᵒ[s] q'') as w2
    by (eapply cowt_push_nil_right; [exact w | eapply wt_nil_to_cowt_nil, wn]).
  destruct (pe_qe_co_cond2_ff s q'' hfb w2 hst) as (p' & wp & _ & _).
  exists p'. exact wp.
Qed.

(** But the co-trace [s_bad = ā ; a ; b] carries a feedback ([s_bad_has_fb]),
    and separates them. *)
Theorem qe_pe_not_co_ti : ((Qe, mt) : st) ⋠꜀ₒ₋ₜᵢ ((Pe, mt) : st).
Proof.
  intro h. eapply pe_no_co_s_bad. eapply (h s_bad).
  exists ((((g 𝟘) ‖ (g 𝟘)), mt) : st). exact qe_co_reaches_stable.
Qed.

Theorem co_ti_nfb_not_co_ti :
  ((Qe, mt) : st) ≼꜀ₒ₋ₜᵢⁿᶠᵇ ((Pe, mt) : st) /\ ((Qe, mt) : st) ⋠꜀ₒ₋ₜᵢ ((Pe, mt) : st).
Proof. split; [exact qe_pe_co_ti_nfb | exact qe_pe_not_co_ti]. Qed.

(** * Trace inclusion *)

Theorem bp2_q0_ti_nfb : ((Bp2, mt) : st) ≼ₜᵢⁿᶠᵇ ((g Q0, mt) : st).
Proof. intros s hfb hs. eapply bp2_ff_included; eassumption. Qed.

Theorem bp2_q0_not_ti : ((Bp2, mt) : st) ⋠ₜᵢ ((g Q0, mt) : st).
Proof. intro h. eapply q_does_not. eapply (h s_cnd2). exact bp2_does. Qed.

Theorem ti_nfb_not_ti :
  ((Bp2, mt) : st) ≼ₜᵢⁿᶠᵇ ((g Q0, mt) : st) /\ ((Bp2, mt) : st) ⋠ₜᵢ ((g Q0, mt) : st).
Proof. split; [exact bp2_q0_ti_nfb | exact bp2_q0_not_ti]. Qed.

(** * The acceptance-set preorders

    Both read the acceptance sets through the image [⌈ 𝝳 ∘ Φ ⌉]; as in
    [SoundnessASco], the two sides are required to read the labels through the
    same abstraction ([same_delta]).  The negative halves hold for arbitrary
    [𝝳P], [𝝳Q] ([must_cond2_false_Pw], [co_must_false_Pe]). *)

Section NfbNotMust.

  Context {T FA PA : Type}.
  Context {Φ : ExtAct TypeOfActions -> FA} {𝝳P 𝝳Q : FA -> PA}.
  Context {gLtsT : gLtsEq T VACCS_ExtAction}.
  Context (AbsP : @AbsAction st T FA PA (ExtAct TypeOfActions) VACCS_ExtAction Φ 𝝳P _ gLtsT).
  Context (AbsQ : @AbsAction st T FA PA (ExtAct TypeOfActions) VACCS_ExtAction Φ 𝝳Q _ gLtsT).
  Context (same_delta : forall x, 𝝳P x = 𝝳Q x).

  (** ** Acceptance sets on traces: [Pw] against [Bp2] *)

  Theorem pw_bp2_as_nfb :
    @bhv_pre_nfb st (ExtAct TypeOfActions) VACCS_ExtAction _ T FA PA Φ 𝝳P gLtsT AbsP
      st _ 𝝳Q AbsQ ((Pw, mt) : st) ((Bp2, mt) : st).
  Proof.
    split.
    - intros s _ _. eapply bp2_cnv.
    - intros s q' hfb _ w hst.
      destruct (pw_bp2_cond2_ff s q' hfb w hst) as (p' & wp & hp & hsub).
      exists p'. split; [exact wp | split; [exact hp |]].
      eapply (abs_of_coR_sub Φ 𝝳P 𝝳Q same_delta); exact hsub.
  Qed.

  Theorem pw_bp2_not_as :
    ¬ @bhv_pre st (ExtAct TypeOfActions) VACCS_ExtAction _ T FA PA Φ 𝝳P gLtsT AbsP
        st _ 𝝳Q AbsQ ((Pw, mt) : st) ((Bp2, mt) : st).
  Proof. intros (_ & h2). exact (must_cond2_false_Pw AbsP AbsQ h2). Qed.

  Theorem as_nfb_not_as :
    @bhv_pre_nfb st (ExtAct TypeOfActions) VACCS_ExtAction _ T FA PA Φ 𝝳P gLtsT AbsP
      st _ 𝝳Q AbsQ ((Pw, mt) : st) ((Bp2, mt) : st)
    /\ ¬ @bhv_pre st (ExtAct TypeOfActions) VACCS_ExtAction _ T FA PA Φ 𝝳P gLtsT AbsP
         st _ 𝝳Q AbsQ ((Pw, mt) : st) ((Bp2, mt) : st).
  Proof. split; [exact pw_bp2_as_nfb | exact pw_bp2_not_as]. Qed.

  (** ** Acceptance sets on co-traces: [Pe] against [Qe] *)

  Theorem pe_qe_co_as_nfb :
    @bhv_pre_co_nfb st (ExtAct TypeOfActions) VACCS_ExtAction _ T FA PA Φ 𝝳P gLtsT AbsP
      st _ 𝝳Q AbsQ ((Pe, mt) : st) ((Qe, mt) : st).
  Proof.
    split.
    - intros s _ _. eapply cocnv_iff_cnv, qe_cnv.
    - intros s q' hfb _ w hst.
      destruct (pe_qe_co_cond2_ff s q' hfb w hst) as (p' & wp & hp & hsub).
      exists p'. split; [exact wp | split; [exact hp |]].
      eapply (abs_of_coR_sub Φ 𝝳P 𝝳Q same_delta); exact hsub.
  Qed.

  Theorem co_as_nfb_not_co_as :
    @bhv_pre_co_nfb st (ExtAct TypeOfActions) VACCS_ExtAction _ T FA PA Φ 𝝳P gLtsT AbsP
      st _ 𝝳Q AbsQ ((Pe, mt) : st) ((Qe, mt) : st)
    /\ ¬ @bhv_pre_co st (ExtAct TypeOfActions) VACCS_ExtAction _ T FA PA Φ 𝝳P gLtsT AbsP
         st _ 𝝳Q AbsQ ((Pe, mt) : st) ((Qe, mt) : st).
  Proof. split; [exact pe_qe_co_as_nfb | exact (co_must_false_Pe AbsP AbsQ)]. Qed.

End NfbNotMust.
