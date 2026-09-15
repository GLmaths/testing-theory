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
From stdpp Require Import base countable.
From TestingTheory Require Import gLts Bisimulation Testing_Predicate InteractionBetweenLts Must
  PAL_Syntax PAL_Template_LTS PAL_Template_Congruence PAL_Good.

(** * The Must preorder of PAL

    [Must.must] and [Must.ctx_pre] instantiated with the LTS with templates
    ([PAL_Template_LTS]) and the testing predicate [good_PAL]. *)

Section PAL_Must.
  Context (Val : Type) `{Countable Val}.

  Notation term := (term Val).

  (** [p] must pass the test [t]. *)
  Definition must_PAL (p t : term) : Prop :=
    must (gLtsP := PALT_gLts Val) (gLtsT := PALT_gLtsEq Val) (outcome := good_PAL Val) p t.

  (** The Must preorder: [q] passes every test that [p] must pass. *)
  Definition must_pre_PAL (p q : term) : Prop :=
    ctx_pre (gLtsP := PALT_gLts Val) (gLtsQ := PALT_gLts Val) (gLtsT := PALT_gLtsEq Val)
      (outcome := good_PAL Val) p q.

  Lemma must_pre_PAL_spec p q : must_pre_PAL p q ↔ ∀ t, must_PAL p t → must_PAL q t.
  Proof. done. Qed.
End PAL_Must.

Notation "p 'must_pass_PAL' t" := (must_PAL _ p t) (at level 70).
Notation "p ᴘᴀʟ⊑ₘᵤₛₜᵢ q" := (must_pre_PAL _ p q) (at level 70).
