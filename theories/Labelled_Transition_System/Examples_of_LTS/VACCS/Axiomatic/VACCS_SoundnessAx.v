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

        [ax_pre p q -> p ⊑ₘᵤₛₜᵢ q]

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
  VACCS_DefinitionAxiomatic.

Section VACCS_SoundnessAx.

Context `{VP : VACCS_Parameters}.

Theorem soundness_ax : forall (p q : proc), ax_pre p q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q.
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
  (* ax_input_ctx *)
  - eapply must_i_input_ctx; eassumption.
  (* ax_choice_input_ctx *)
  - eapply must_i_choice_input_ctx; eassumption.
  (* ax_choice_tau *)
  - apply must_i_choice_tau_compat. assumption.
  (* ax_tau_step *)
  - apply must_i_tau_below. assumption.
  (* ax_int_glb_ctx *)
  - eapply must_i_int_glb_ctx; eassumption.
  (* ax_tau_sep_l *)
  - apply must_i_tau_sep_pre_l.
  (* ax_tau_sep_r *)
  - apply must_i_tau_sep_pre_r.
  (* ax_tau_flatten_l *)
  - apply must_i_tau_flatten_pre_l. assumption.
  (* ax_tau_flatten_r *)
  - apply must_i_tau_flatten_pre_r. assumption.
  (* ax_convex *)
  - apply must_i_convex_pre.
  (* ax_share_in *)
  - apply must_i_share_in_pre.
  (* ax_success_l *)
  - apply must_i_success_ctx_l.
  (* ax_success_r *)
  - apply must_i_success_ctx_r.
  (* ax_input_distrib_l *)
  - intros t Hm. apply must_i_input_distrib_ctx_l. exact Hm.
  (* ax_expansion_l *)
  - apply must_i_expansion_l.
  (* ax_expansion_r *)
  - apply must_i_expansion_r.
  (* ax_res_normalize_l *)
  - apply must_i_res_normalize_l.
  (* ax_res_normalize_r *)
  - apply must_i_res_normalize_r.
  (* ax_input_drop *)
  - apply must_i_input_drop_bad. assumption.
  (* ax_ccat_r *)
  - apply must_i_nil_below_copycats. assumption.
  (* ax_settle_sim *)
  - eapply settle_sim_below_bag; eassumption.
  (* ax_restrict *)
  - apply must_i_restrict_badk; assumption.
  (* ax_glb_tau *)
  - eapply must_i_glb_gen; try eassumption.
    intros c v q'' Hq''.
    match goal with
    | Hex : forall c v q'', lts _ (ActExt (ActOut (c,v))) q'' -> exists _, _ |- _ =>
        destruct (Hex c v q'' Hq'') as (p'' & Hp'')
    end.
    exists p''. split; [ exact Hp'' | ].
    match goal with
    | Hall : forall c v p'' q'', lts _ (ActExt (ActOut (c,v))) p'' -> _ |- _ =>
        eapply Hall; [ exact Hp'' | exact Hq'' ]
    end.
  (* ax_sub_tau *)
  - apply must_i_sub_tau; assumption.
  (* ax_glb_weak *)
  - eapply must_i_glb_res; eassumption.
  (* ax_share_msg *)
  - apply must_i_share_msg_pre.
Qed.

(** The equational form. *)
Corollary soundness_ax_eq : forall (p q : proc),
  ax_pre p q -> ax_pre q p -> p ≂ₘᵤₛₜᵢ q.
Proof.
  intros p q H1 H2. split; apply soundness_ax; assumption.
Qed.

End VACCS_SoundnessAx.
