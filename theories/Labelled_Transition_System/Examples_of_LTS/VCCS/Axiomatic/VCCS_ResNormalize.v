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

(** * Eliminating [ν] over a guarded sum: [ν (g M) ≂ₘᵤₛₜᵢ g (resg M)]

    The last piece [VCCS_NormalForm.v]'s normal-form theorem needs: once
    a [Static] process under a single [ν] has already been rewritten to
    a guarded sum [g M] (e.g. via the expansion law,
    [VCCS_Expansion.v]), [ν (g M)] is *itself* derivably a guarded sum
    — [resg M] below — obtained by pushing [ν] into each of [M]'s own
    guards individually (no existing structural-congruence rule does
    this for an arbitrary [+], only for [‖] via [cgr_res_scope_step]).

    The construction follows directly from [lts_res_ext]'s own shape
    (VCCS.v): a guard on the just-restricted channel (De Bruijn index
    [bvar 0], i.e. [M]'s reference to *this* [ν]'s own binder) can
    *never* be exposed through [ν] — [VarC_action_add 1 μ] (the shift
    [lts_res_ext] requires) never produces [bvar 0] for any [μ], since
    [cst] channels are left untouched and [bvar i] is shifted to
    [bvar (S i)] — so such a guard becomes dead ([𝟘]) once nothing else
    is composed under the same [ν] to synchronise with it. Every other
    guard survives, with its channel shifted down by one and [ν] moved
    to wrap its continuation directly instead of the whole guarded sum
    (justified since [ν] doesn't bind a *value*, so an input/output/tau
    guard's own continuation sits at exactly the same [ν]-depth whether
    [ν] wraps the guard or the guard wraps [ν]). *)

From stdpp Require Import base.
From TestingTheory Require Import VCCS VCCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation WeakTransitions Convergence VCCS_Static VCCS_Expansion.

Section VCCS_ResNormalize.

Context `{VP : VCCS_Parameters}.

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
| c ! v • p =>
    match c with
    | bvar 0 => 𝟘
    | cst c' => (cst c') ! v • (ν p)
    | bvar (S j) => (bvar j) ! v • (ν p)
    end
| 𝛕 • p => 𝛕 • (ν p)
| M1 + M2 => (resg M1) + (resg M2)
end.

(** ** [ν (g M)] and [g (resg M)] have exactly the same one-step transitions *)

Lemma resg_lts_iff : forall M a tgt, lts (ν (g M)) a tgt <-> lts (g (resg M)) a tgt.
Proof.
  induction M; intros a tgt; simpl.
  - split; intro H; inversion H; subst; inversion H1.
  - split; intro H; inversion H; subst; inversion H1.
  - destruct c as [c' | [|j]]; simpl.
    + split; intro H; inversion H; subst.
      inversion H1; subst; destruct μ as [[c0 v0]|[c0 v0]]; simpl in H4; inversion H4; subst; destruct c0 as [c0'|i0]; simpl in H2; try discriminate H2; inversion H2; subst; replace (ν p ^ v0) with ((ν p) ^ v0) by reflexivity; apply lts_input.
      -- inversion H1.
      -- apply lts_res_ext.
         apply lts_input.
    + split; intro H; inversion H; subst; inversion H1; subst; destruct μ as [[c0 v0]|[c0 v0]]; simpl in H4; destruct c0; simpl in H4; inversion H4.
    + split; intro H; inversion H; subst.
      inversion H1; subst; destruct μ as [[c0 v0]|[c0 v0]]; simpl in H4; inversion H4; subst; destruct c0 as [c0'|i0]; simpl in H2; try discriminate H2; inversion H2; subst; replace (ν p ^ v0) with ((ν p) ^ v0) by reflexivity; apply lts_input.
      -- inversion H1.
      -- apply lts_res_ext.
         apply lts_input.
  - destruct c as [c' | [|j]]; simpl.
    split; intro H; inversion H; subst.
    inversion H1; subst; destruct μ as [[c0 v0]|[c0 v0]]; simpl in H5; inversion H5; subst; destruct c0 as [c0'|i0]; simpl in H2; try discriminate H2; inversion H2; subst; apply lts_output.
    -- inversion H1.
    -- apply lts_res_ext.
       apply lts_output.
    -- split; intro H; inversion H; subst; inversion H1; subst; destruct μ as [[c0 v0]|[c0 v0]]; simpl in H5; destruct c0; simpl in H5; inversion H5.
    -- split; intro H; inversion H; subst.
       inversion H1; subst; destruct μ as [[c0 v0]|[c0 v0]]; simpl in H5; inversion H5; subst; destruct c0 as [c0'|i0]; simpl in H2; try discriminate H2; inversion H2; subst; apply lts_output.
       --- inversion H1.
       --- apply lts_res_ext.
           apply lts_output.
  - split; intro H.
    + inversion H; subst; inversion H1; apply lts_tau.
    + inversion H; subst.
      apply lts_res_tau.
      apply lts_tau.
  - split; intro H.
    + inversion H; subst.
      * inversion H1; subst.
        -- apply lts_choiceL.
           apply IHM1.
           apply lts_res_ext.
           exact H5.
        -- apply lts_choiceR.
           apply IHM2.
           apply lts_res_ext.
           exact H5.
      * inversion H1; subst.
        -- apply lts_choiceL.
           apply IHM1.
           apply lts_res_tau.
           exact H5.
        -- apply lts_choiceR.
           apply IHM2.
           apply lts_res_tau.
           exact H5.
    + inversion H; subst.
      * apply IHM1 in H4.
        inversion H4; subst; [apply lts_res_ext | apply lts_res_tau]; apply lts_choiceL; assumption.
      * apply IHM2 in H4.
        inversion H4; subst; [apply lts_res_ext | apply lts_res_tau]; apply lts_choiceR; assumption.
Qed.

(** ** The normalization law *)

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

(** ** [resg] preserves [gStatic] *)

Lemma resg_gStatic : forall M, gStatic M -> gStatic (resg M).
Proof.
  induction M; intro Hg; simpl; inversion Hg; subst.
  - constructor.
  - constructor.
  - destruct c as [c'|[|j]]; repeat constructor; assumption.
  - destruct c as [c'|[|j]]; repeat constructor; assumption.
  - repeat constructor. assumption.
  - constructor; [apply IHM1 | apply IHM2]; assumption.
Qed.

End VCCS_ResNormalize.
