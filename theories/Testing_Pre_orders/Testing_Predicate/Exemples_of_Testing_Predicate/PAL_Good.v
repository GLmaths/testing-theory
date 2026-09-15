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
From stdpp Require Import base decidable countable.
From TestingTheory Require Import gLts Bisimulation Testing_Predicate
  PAL_Syntax PAL_Template_LTS PAL_Template_Congruence.

(** * Testing predicate for PAL

    De Nicola–Pugliese (Section 5): an observer reports success when it can
    perform the action [ω] of its prefix [success]. [good_PAL E] holds when
    [✓] is in an active position of [E], i.e. when [E] can perform [ω] by
    rules AR4-AR8. *)

Section PAL_Good.
  Context (Val : Type) `{Countable Val}.

  Notation term := (term Val).

  Open Scope pal_scope.
  Inductive good_PAL : term → Prop :=
    | good_success : good_PAL ✓
    | good_echoice_l E1 E2 : good_PAL E1 → good_PAL (E1 □ E2)
    | good_echoice_r E1 E2 : good_PAL E2 → good_PAL (E1 □ E2)
    | good_par_l E1 E2 : good_PAL E1 → good_PAL (E1 ‖ E2)
    | good_par_r E1 E2 : good_PAL E2 → good_PAL (E1 ‖ E2)
    | good_lmerge E1 E2 : good_PAL E1 → good_PAL (E1 ⌊ E2)
    | good_if_true be E1 E2 : eval_bexp be = Some true → good_PAL E1 → good_PAL (IF be THEN E1 ELSE E2)
    | good_if_false be E1 E2 : eval_bexp be = Some false → good_PAL E2 → good_PAL (IF be THEN E1 ELSE E2).
  Close Scope pal_scope.

  #[global] Instance good_PAL_dec E : Decision (good_PAL E).
  Proof.
    induction E; try (right; inversion 1; fail).
    - destruct (eval_bexp be) as [[]|] eqn:hbe.
      + destruct IHE1 as [h|h]; [left; by apply good_if_true |].
        right. inversion 1; subst; first [congruence | contradiction].
      + destruct IHE2 as [h|h]; [left; by apply good_if_false |].
        right. inversion 1; subst; first [congruence | contradiction].
      + right. inversion 1; subst; congruence.
    - destruct IHE1 as [h1|h1]; [left; by apply good_echoice_l |].
      destruct IHE2 as [h2|h2]; [left; by apply good_echoice_r |].
      right. inversion 1; contradiction.
    - destruct IHE1 as [h1|h1]; [left; by apply good_par_l |].
      destruct IHE2 as [h2|h2]; [left; by apply good_par_r |].
      right. inversion 1; contradiction.
    - destruct IHE1 as [h1|h1]; [left; by apply good_lmerge |].
      right. inversion 1; contradiction.
    - left. apply good_success.
  Defined.

  (** [good_PAL] is preserved by the structural congruence. *)
  Lemma good_cgr_step p q : cgr_step Val p q → good_PAL p → good_PAL q.
  Proof.
    induction 1; intros hg; inversion hg; subst; try congruence;
      repeat match goal with
      | h : good_PAL (t_par _ _) |- _ => inversion h; subst; clear h
      | h : good_PAL (t_echoice _ _) |- _ => inversion h; subst; clear h
      | h : good_PAL t_nil |- _ => inversion h
      end;
      eauto using good_PAL.
  Qed.

  Lemma good_cgr p q : cgr Val p q → good_PAL p → good_PAL q.
  Proof. induction 1; eauto using good_cgr_step. Qed.

  (** For the LTS with templates, where [⋍] is the structural congruence. *)
  #[global] Instance PALT_Good : @Testing_Predicate term (PALT_Act Val) (PALT_ExtAction Val) good_PAL (PALT_gLtsEq Val).
  Proof.
    split.
    - apply _.
    - intros p q hp heq. exact (good_cgr p q heq hp).
    - intros p q η [].
    - intros p q η [].
  Defined.

End PAL_Good.
