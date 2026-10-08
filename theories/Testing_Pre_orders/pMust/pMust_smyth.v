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

(** * Probabilistic must, Smyth version

    Deng, van Glabbeek, Hennessy and Morgan compare the *sets* of success
    probabilities of [p ∥ t] by the Smyth order: below every value of
    [q ∥ t] there is a value of [p ∥ t] ([A ≤Sm B] iff for all [b ∈ B] there
    is [a ∈ A] with [a ≤ b]; for finite sets, [min A ≤ min B]).  Here the resolutions are the
    admissible runs of [pMust_almost_sure.v]: one scheduler for the whole
    distribution.

    The value of a run is the supremum of its successful mass.  Suprema are
    not asked of the probabilities; [sup r1 ≤ sup r2] is stated as "every
    probability strictly below a successful mass of [r1] is reached by
    [r2]", which needs density to be transitive.

    Following the definition, the Smyth order asks a dominating *run*, i.e.
    an attained infimum, which is the case for finite processes (Deng et
    al.); with infinitely many runs one would compare infima instead. *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base decidable list.
From TestingTheory Require Import pMust_almost_sure.

(** Density of the probabilities, and transitivity across [<ₚ] and [≤ₚ]. *)
Class DenseWeights `{Weights} := MkDenseWeights {
    prob_dense a b : a <ₚ b → ∃ c, a <ₚ c ∧ c <ₚ b;
  }.

Section Smyth.
  Context `{Weights} {P T C Sch : Type} `{!SchedSts C Sch}
    `{!pTesting P T C Sch}.

  (** [sup r1 ≤ sup r2] *)
  Definition run_le (r1 r2 : nat → dist C) : Prop :=
    ∀ n w, w <ₚ succ_mass r1 n → ∃ m, w ≤ₚ succ_mass r2 m.

  (** [A(Δ) ≤Sm A(Θ)] *)
  Definition smyth_le (Δ Θ : dist C) : Prop :=
    ∀ r2, is_run Θ r2 → ∃ r1, is_run Δ r1 ∧ run_le r1 r2.

  Definition ctx_pre_sm (p q : P) : Prop :=
    ∀ t : T, smyth_le (compose p t) (compose q t).

  Lemma prob_lt_le_trans a b c : a <ₚ b → b ≤ₚ c → a <ₚ c.
  Proof.
    intros [Hab Hba] Hbc. split; [by etrans|].
    intros Hca. apply Hba. by etrans.
  Qed.

  Lemma run_le_refl r : run_le r r.
  Proof. intros n w [Hle _]. by exists n. Qed.

  Lemma run_le_trans `{!DenseWeights} r1 r2 r3 :
    run_le r1 r2 → run_le r2 r3 → run_le r1 r3.
  Proof.
    intros H12 H23 n w Hw.
    destruct (prob_dense _ _ Hw) as (c & Hwc & Hc).
    destruct (H12 n c Hc) as (m & Hm).
    apply (H23 m). by eapply prob_lt_le_trans.
  Qed.

  #[global] Instance ctx_pre_sm_preorder `{!DenseWeights} : PreOrder ctx_pre_sm.
  Proof.
    split.
    - intros p t r Hr. exists r. split; [done|]. apply run_le_refl.
    - intros p q s Hpq Hqs t r3 Hr3.
      destruct (Hqs t r3 Hr3) as (r2 & Hr2 & H23).
      destruct (Hpq t r2 Hr2) as (r1 & Hr1 & H12).
      exists r1. split; [done|]. by eapply run_le_trans.
  Qed.
  (** ** The Smyth must is finer than the almost-sure must

      If below every run of [Θ] there is a run of [Δ], and [Δ] succeeds
      almost surely, so does [Θ] — provided [Θ] does not weigh more than
      [Δ]. *)
  Lemma smyth_le_pmust_as `{!DenseWeights} Δ Θ :
    (∀ w, w <ₚ dmass Θ → w <ₚ dmass Δ) → smyth_le Δ Θ → pmust_as Δ → pmust_as Θ.
  Proof.
    intros Hmass Hsm Has r2 Hr2 w Hw.
    destruct (Hsm r2 Hr2) as (r1 & Hr1 & Hle).
    assert (Hw' : w <ₚ dmass Δ) by (apply Hmass; by destruct Hr2 as [<- _]).
    destruct (prob_dense _ _ Hw') as (c & Hwc & Hc).
    assert (Hc' : c <ₚ dmass (r1 0)) by (by destruct Hr1 as [-> _]).
    destruct (Has r1 Hr1 c Hc') as (n & Hn).
    destruct (Hle n w (prob_lt_le_trans _ _ _ Hwc Hn)) as (m & Hm).
    by exists m.
  Qed.

  Lemma ctx_pre_sm_as `{!DenseWeights} p q :
    (∀ t w, w <ₚ dmass (compose q t) → w <ₚ dmass (compose p t)) →
    ctx_pre_sm p q → ctx_pre_as p q.
  Proof.
    intros Hmass Hpq t Hp. exact (smyth_le_pmust_as _ _ (Hmass t) (Hpq t) Hp).
  Qed.
  (** ** The Smyth must as a family of threshold musts

      [must_lt w Δ]: every run of [Δ] gets a successful mass arbitrarily
      close to [w] from below, i.e. its value is at least [w].  When [Δ] has
      a run of least value ([min_run], true for finite processes), [Δ] is
      below [Θ] for the Smyth order iff every threshold passed by [Δ] is
      passed by [Θ].  With [w] the whole mass, [must_lt] is the almost-sure
      must. *)
  Definition must_lt (w : prob) (Δ : dist C) : Prop :=
    ∀ r, is_run Δ r → ∀ w', w' <ₚ w → ∃ n, w' ≤ₚ succ_mass r n.

  Definition min_run (Δ : dist C) : Prop :=
    ∃ r, is_run Δ r ∧ ∀ r', is_run Δ r' → run_le r r'.

  Lemma smyth_le_must_lt `{!DenseWeights} Δ Θ w :
    smyth_le Δ Θ → must_lt w Δ → must_lt w Θ.
  Proof.
    intros Hsm Hw r2 Hr2 w' Hw'.
    destruct (Hsm r2 Hr2) as (r1 & Hr1 & Hle).
    destruct (prob_dense _ _ Hw') as (c & Hw'c & Hc).
    destruct (Hw r1 Hr1 c Hc) as (n & Hn).
    exact (Hle n w' (prob_lt_le_trans _ _ _ Hw'c Hn)).
  Qed.

  Lemma must_lt_smyth_le Δ Θ :
    min_run Δ → (∀ w, must_lt w Δ → must_lt w Θ) → smyth_le Δ Θ.
  Proof.
    intros (r & Hr & Hmin) Hth r2 Hr2. exists r. split; [done|].
    intros n w Hw. apply (Hth (succ_mass r n)); [|done|done].
    intros r' Hr' w' Hw'. exact (Hmin r' Hr' n w' Hw').
  Qed.

  Theorem smyth_le_iff_must_lt `{!DenseWeights} Δ Θ :
    min_run Δ → smyth_le Δ Θ ↔ ∀ w, must_lt w Δ → must_lt w Θ.
  Proof.
    intros Hmin. split.
    - intros Hsm w. by apply smyth_le_must_lt.
    - by apply must_lt_smyth_le.
  Qed.

  Corollary ctx_pre_sm_iff_must_lt `{!DenseWeights} p q :
    (∀ t, min_run (compose p t)) →
    ctx_pre_sm p q ↔ ∀ t w, must_lt w (compose p t) → must_lt w (compose q t).
  Proof.
    intros Hmin. split.
    - intros Hpq t w. exact (smyth_le_must_lt _ _ w (Hpq t)).
    - intros Hth t. apply must_lt_smyth_le; [apply Hmin|]. intros w. apply Hth.
  Qed.
End Smyth.

Notation "p ⊑ₛₘ q" := (ctx_pre_sm p q) (at level 70).
