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

(** * Pushing [ν] into a guarded sum

    [Congruence.v] has no rule distributing [ν] over an arbitrary [+]
    (only [cgr_res_scope_step], for [‖]), so [resg] is built from scratch,
    directly off [lts_res_ext]'s own shape: a guard on the just-restricted
    channel (de Bruijn [bvar 0]) can *never* be exposed through [ν],
    because [VarC_action_add 1 μ] never produces [bvar 0] for any [μ] —
    [cst] channels are untouched and [bvar i] always shifts to
    [bvar (S i)].  Such a guard therefore becomes dead ([𝟘]); every other
    guard survives with its channel shifted down by one and [ν] moved to
    wrap the guard's *continuation*.

    That last move is legitimate because [ν] binds no value, so an
    input's continuation sits at the same [ν]-depth either way — which is
    exactly why [subst_in_proc]'s [ν] case is a transparent pass-through,
    i.e. [(ν p)^v = ν (p^v)] definitionally.

    Compared with VCCS this is one case shorter: [gproc] has no output
    constructor. *)

From stdpp Require Import base.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Expansion.

Section VACCS_ResNormalize.

Context `{VP : VACCS_Parameters}.

Fixpoint resg (M : gproc) : gproc :=
match M with
| ① => ①
| 𝟘 => 𝟘
| c ? p =>
    match c with
    | bvar 0 => 𝟘
    | cst c' => (cst c') ? (ν p)
    | bvar (S j) => (bvar j) ? (ν p)
    end
| 𝛕 • p => 𝛕 • (ν p)
| M1 + M2 => (resg M1) + (resg M2)
end.

Lemma resg_lts_iff : forall M a tgt, lts (ν (g M)) a tgt <-> lts (g (resg M)) a tgt.
Proof.
  induction M; intros a tgt; simpl.
  - split; intro H; inversion H; subst; inversion H1.
  - split; intro H; inversion H; subst; inversion H1.
  - destruct c as [c' | [|j]]; simpl.
    + split; intro H; inversion H; subst.
      inversion H1; subst; destruct μ as [[c0 v0]|[c0 v0]]; simpl in H4; inversion H4; subst;
        destruct c0 as [c0'|i0]; simpl in H2; try discriminate H2; inversion H2; subst;
        replace (ν p ^ v0) with ((ν p) ^ v0) by reflexivity; apply lts_input.
      -- inversion H1.
      -- apply lts_res_ext. apply lts_input.
    + split; intro H; inversion H; subst; inversion H1; subst;
        destruct μ as [[c0 v0]|[c0 v0]]; simpl in H4; destruct c0; simpl in H4; inversion H4.
    + split; intro H; inversion H; subst.
      inversion H1; subst; destruct μ as [[c0 v0]|[c0 v0]]; simpl in H4; inversion H4; subst;
        destruct c0 as [c0'|i0]; simpl in H2; try discriminate H2; inversion H2; subst;
        replace (ν p ^ v0) with ((ν p) ^ v0) by reflexivity; apply lts_input.
      -- inversion H1.
      -- apply lts_res_ext. apply lts_input.
  - split; intro H.
    + inversion H; subst; inversion H1; apply lts_tau.
    + inversion H; subst. apply lts_res_tau. apply lts_tau.
  - split; intro H.
    + inversion H; subst.
      * inversion H1; subst.
        -- apply lts_choiceL. apply IHM1. apply lts_res_ext. exact H5.
        -- apply lts_choiceR. apply IHM2. apply lts_res_ext. exact H5.
      * inversion H1; subst.
        -- apply lts_choiceL. apply IHM1. apply lts_res_tau. exact H5.
        -- apply lts_choiceR. apply IHM2. apply lts_res_tau. exact H5.
    + inversion H; subst.
      * apply IHM1 in H4.
        inversion H4; subst; [apply lts_res_ext | apply lts_res_tau]; apply lts_choiceL; assumption.
      * apply IHM2 in H4.
        inversion H4; subst; [apply lts_res_ext | apply lts_res_tau]; apply lts_choiceR; assumption.
Qed.

(** ** The normalisation law *)

Theorem must_i_res_normalize : forall M t, (ν (g M)) must_pass t <-> g (resg M) must_pass t.
Proof.
  intros M t.
  apply must_same_lts.
  - intro p'. apply resg_lts_iff.
  - intros mu p'. apply resg_lts_iff.
Qed.

Corollary must_i_res_normalize_l : forall M, (ν (g M)) ⊑ₘᵤₛₜᵢ g (resg M).
Proof. intros M t H. apply must_i_res_normalize. exact H. Qed.

Corollary must_i_res_normalize_r : forall M, g (resg M) ⊑ₘᵤₛₜᵢ (ν (g M)).
Proof. intros M t H. apply must_i_res_normalize. exact H. Qed.

Lemma resg_gStatic : forall M, gStatic M -> gStatic (resg M).
Proof.
  induction M; intro H; simpl; inversion H; subst.
  - constructor.
  - constructor.
  - destruct c as [c'|[|j]]; constructor; constructor; assumption.
  - constructor. constructor. assumption.
  - constructor; [ apply IHM1 | apply IHM2 ]; assumption.
Qed.

End VACCS_ResNormalize.
