(* begin hide *)
(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
   Copyright (c) 2025 Gaëtan Lopez <glopez@irif.fr>

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

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import countable.
From TestingTheory Require Import ActTau.



(** ** LTSs with non-blocking actions [gLts] *)


Class gLts (P : Type) {A : Type} (EA : ExtAction A) :=
  MkgLts {
      lts_step: P → Labels A → P → Prop;
      lts_state_eqdec: EqDecision P;

      lts_step_decidable a 𝜆 b : Decision (lts_step a 𝜆 b);

      lts_may_perform : P → Labels A → Prop;
      lts_may_perform_decidable p 𝜆 : Decision (lts_may_perform p 𝜆);
      lts_may_perform_spec1 p 𝜆 : lts_may_perform p 𝜆 → { q | lts_step p 𝜆 q };
      lts_may_perform_spec2 p 𝜆 : { q | lts_step p 𝜆 q } → lts_may_perform p 𝜆;
    }.

Arguments gLts P {_} EA.

#[global] Existing Instance lts_state_eqdec.
#[global] Existing Instance lts_step_decidable.
#[global] Existing Instance lts_may_perform_decidable.

Notation "p ⟶ q"      := (lts_step p τ q) (at level 30, format "p  ⟶  q").
Notation "p ⟶{ 𝜆 } q" := (lts_step p 𝜆 q) (at level 30, format "p  ⟶{ 𝜆 }  q").
Notation "p ⟶[ μ ] q" := (lts_step p (ActExt μ) q) (at level 30, format "p  ⟶[ μ ]  q").

Notation "p ⟶"      := (lts_may_perform p τ) (at level 30, format "p  ⟶").
Notation "p ⟶{ 𝜆 }" := (lts_may_perform p 𝜆) (at level 30, format "p  ⟶{ 𝜆 }").
Notation "p ⟶[ μ ]" := (lts_may_perform p (ActExt μ)) (at level 30, format "p  ⟶[ μ ]").

Notation "p ↛"      := (¬ lts_may_perform p τ) (at level 30, format "p  ↛").
Notation "p ↛{ 𝜆 }" := (¬ lts_may_perform p 𝜆) (at level 30, format "p  ↛{ 𝜆 }").
Notation "p ↛[ μ ]" := (¬ lts_may_perform p (ActExt μ)) (at level 30, format "p  ↛[ μ ]").