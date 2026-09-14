(*
   Copyright (c) 2026 Gaëtan Lopez <gaetanlopez.maths@gmail.com>

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

(** * Soundness of the VACCS proof system

        [p ᴠᴀᴄᴄꜱ⊑ₐₓ q -> p ⊑ₘᵤₛₜᵢ q]

    for **all** VACCS processes — no [Static] restriction, and no side
    condition on any rule.  That is a genuine simplification over VCCS,
    where the same theorem needs [Static p], [Static q] and an invariant
    lemma keeping the whole derivation inside the [Static] fragment.  The
    reason is the two bridges of [VACCS_Precongruence.v]: [‖]- and
    [ν]-precongruence hold with no hypothesis on the operands, because the
    argument moves the context into the *test* instead of analysing the
    context's effect on a behavioural characterisation.

    Every case is a single application of a lemma proved beforehand. *)

From stdpp Require Import base gmultiset.
From TestingTheory Require Import MultisetLTSConstruction.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Shift VACCS_Precongruence VACCS_Expansion VACCS_ResNormalize
  VACCS_Copycat VACCS_Absorb VACCS_Forwarder VACCS_Cond2 VACCS_Residues
  VACCS_GlbStable VACCS_DefinitionAxiomatic.

Section VACCS_SoundnessAx.

Context `{VP : VACCS_Parameters}.

Theorem soundness_ax : forall (p q : proc), p ᴠᴀᴄᴄꜱ⊑ₐₓ q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q.
Proof.
  intros p q Hax. induction Hax.
  (* ax_trans *)
  - intros t Hm. apply IHHax2. apply IHHax1. exact Hm.
  (* ax_cgr *)
  - apply must_i_cgr. assumption.
  (* ax_par *)
  - apply must_i_par_compat2; assumption.
  (* ax_res *)
  - apply must_i_res_compat; assumption.
  (* ax_tau_step *)
  - apply must_i_tau_below. assumption.
  (* ax_same_lts *)
  - intro t. apply (proj1 (must_same_lts p q
      (fun p' => conj (H τ p') (H0 τ p'))
      (fun mu p' => conj (H (ActExt mu) p') (H0 (ActExt mu) p')) t)).
  (* ax_glb_tau *)
  - apply must_i_glb_tau.
    + match goal with Hex : exists X, In (𝛕 • X) (summands M) |- _ =>
        destruct Hex as (X1 & HX1) end.
      exists X1. eapply summand_lts; [ exact HX1 | apply lts_tau ].
    + intros (c,v) q'' Hq''. eapply gsum_no_out. exact Hq''.
    + intros q' Hq'. match goal with
        IH : forall X, In (𝛕 • X) (summands M) -> _ ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ X |- _ =>
          apply IH; apply gsum_tau_summand; exact Hq' end.
    + intros c v q'' Hq''. destruct (gsum_in_summand _ _ _ _ Hq'') as (Q & HQ & ->).
      match goal with
        IH : forall c Q, In (c ? Q) (summands M) -> forall v, _ ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ _ |- _ =>
          apply IH; exact HQ end.
  (* ax_glb_settle *)
  - destruct (lts_dec ((g M) : proc) τ) as [ Hno | (X0 & HX0) ].
    + apply must_i_glb_stable; [ exact Hno | | ].
      * assumption.
      * intros c v q'' Hq''. destruct (gsum_in_summand _ _ _ _ Hq'') as (Q & HQ & ->).
        match goal with
          IH : forall c Q, In (c ? Q) (summands M) -> forall v, _ ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ _ |- _ =>
            apply IH; exact HQ end.
    + apply must_i_glb_tau.
      * exists X0. exact HX0.
      * intros (c,v) q'' Hq''. eapply gsum_no_out. exact Hq''.
      * intros q' Hq'. match goal with
          IH : forall X, In (𝛕 • X) (summands M) -> _ ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ X |- _ =>
            apply IH; apply gsum_tau_summand; exact Hq' end.
      * intros c v q'' Hq''. destruct (gsum_in_summand _ _ _ _ Hq'') as (Q & HQ & ->).
        match goal with
          IH : forall c Q, In (c ? Q) (summands M) -> forall v, _ ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ _ |- _ =>
            apply IH; exact HQ end.
  (* ax_share_msg *)
  - apply must_i_share_msg_pre.
Qed.

(** The equational form. *)
Corollary soundness_ax_eq : forall (p q : proc),
  p ᴠᴀᴄᴄꜱ⊑ₐₓ q -> q ᴠᴀᴄᴄꜱ⊑ₐₓ p -> p ≂ₘᵤₛₜᵢ q.
Proof.
  intros p q H1 H2. split; apply soundness_ax; assumption.
Qed.

End VACCS_SoundnessAx.
