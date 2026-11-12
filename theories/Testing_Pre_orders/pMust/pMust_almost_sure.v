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
(* begin hide *)
(* * Probabilistic must, almost-sure version

    The almost-sure must asks that along every maximal run the successful
    mass tends to the whole mass.  Probabilities only need to form a
    preordered monoid; with [[0,1]] this is "succeeds with probability 1".
    The Smyth version, comparing success probabilities, is in
    [pMust_smyth.v].  Both are parametrised by the lifting of
    [pMust_scheduled.v]; the notations are for [Stay]. *)
(* end hide *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base decidable list.
From TestingTheory Require Export pMust_scheduled.
(* begin hide *)
Section AlmostSure.
  Context `{Weights} {C Sch : Type} `{!SchedSts C Sch} (L : lifting).

  (* The successful mass tends to the whole mass. *)
  Definition almost_sure (r : nat → dist C) : Prop :=
    ∀ w, w <ₚ dmass (r 0) → ∃ n, w ≤ₚ succ_mass r n.

  Definition pmust_as (𝔇 : dist C) : Prop :=
    ∀ r, is_run L 𝔇 r → almost_sure r.
End AlmostSure.

Section Preorder.
  Context `{Weights} {P T C Sch : Type} `{!SchedSts C Sch}
    `{!pTesting P T C Sch} (L : lifting).

  Definition must_as (p : P) (t : T) : Prop := pmust_as L (compose p t).

  Definition ctx_pre_as (p q : P) : Prop := ∀ t : T, must_as p t → must_as q t.

  Definition ctx_pre_as_on (Ts : T → Prop) (p q : P) : Prop :=
    ∀ t : T, Ts t → must_as p t → must_as q t.

  Lemma ctx_pre_as_on_all p q : ctx_pre_as p q → ∀ Ts, ctx_pre_as_on Ts p q.
  Proof. intros Hpq Ts t _. apply Hpq. Qed.

  #[global] Instance ctx_pre_as_preorder : PreOrder ctx_pre_as.
  Proof. split; [by intros p t|]. intros p q r Hpq Hqr t Hp. by apply Hqr, Hpq. Qed.
End Preorder.

Notation "p 'must_as' t" := (must_as Stay p t) (at level 70).
Notation "p ⊑ₐₛ q" := (ctx_pre_as Stay p q) (at level 70).
Notation "p ⊑ₐₛ[ Ts ] q" := (ctx_pre_as_on Stay Ts p q) (at level 70, format "p  ⊑ₐₛ[ Ts ]  q").
Notation "p ⊑ₐₛᴰ q" := (ctx_pre_as Drop p q) (at level 70).
Notation "p ⊑ₐₛᴰ[ Ts ] q" := (ctx_pre_as_on Drop Ts p q) (at level 70, format "p  ⊑ₐₛᴰ[ Ts ]  q").
(* end hide *)
