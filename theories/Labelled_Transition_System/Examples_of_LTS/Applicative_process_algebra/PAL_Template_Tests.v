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
From stdpp Require Import base tactics decidable countable list gmap.
From TestingTheory Require Import ActTau gLts InputOutputActions
  PAL_Syntax PAL_Template_LTS PAL_Good.

(* * Tests for the completeness of the alternative LTS of PAL

   The observers of De Nicola–Pugliese (Definition 5.9), along a trace of
   actions of the test:
   - [isucc = eval(nil).✓] succeeds after an internal step;
   - for an input [ActIn ot], the test performs [in(ot)];
   - for an output [ActOut ot], the test emits [ot] with [out(ot).nil ⌊ _];
   - each step can also be abandoned by [isucc].
   [t_conv] ends with [isucc] (the paper's [con]), [ta E] ends with an external
   choice among the tests [ac β] for [β ∈ E] (the paper's [ac]). *)

Section PAL_T_Tests.
  Context (Val : Type) `{Countable Val}.

  Notation term := (term Val).
  Notation eot := (eot Val).
  Notation eit := (eit Val).
  Notation PALT_Act := (PALT_Act Val).

  (** Infer the action type of [⟶], [⟶[μ]], ... from the LTS on terms. *)
  #[local] Hint Mode ExtAction ! : typeclass_instances.

  (** ** The tests *)

  Open Scope pal_scope.

  (** [isucc = eval(nil).✓] *)
  Definition isucc : term := eval( 𝟘 ) • ✓.

  Fixpoint gen_test (s : list PALT_Act) (p : term) : term :=
    match s with
    | [] => p
    | ActIn ot :: s' => (in( eot_to_tuple ot ) • gen_test s' p) □ isucc
    | ActOut ot :: s' => ((out( eot_to_tuple ot ) • 𝟘) ⌊ gen_test s' p) □ isucc
    end.

  (** Tests for convergence: the paper's [con]. *)
  Definition t_conv (s : list PALT_Act) : term := gen_test s isucc.

  (** The test of one action: the paper's [ac]. *)
  Definition ac_t (β : PALT_Act) : term :=
    match β with
    | ActIn ot => in( eot_to_tuple ot ) • ✓
    | ActOut ot => (out( eot_to_tuple ot ) • 𝟘) ⌊ ✓
    end.

  Definition sum_ac (E : gset PALT_Act) : term :=
    foldr (λ β acc, ac_t β □ acc) 𝟘 (elements E).

  (** Tests for co-acceptance sets: the paper's [ac]. *)
  Definition ta (E : gset PALT_Act) (s : list PALT_Act) : term := gen_test s (sum_ac E).

  Close Scope pal_scope.

  (** ** Tuples as patterns *)

  Definition eot_to_eit (ot : eot) : eit :=
    map (λ of, match of with of_val v => if_val v | of_star => if_star end) ot.

  Lemma eval_in_eot_to_tuple_t (ot : eot) : eval_in_tuple (eot_to_tuple ot) = Some (eot_to_eit ot).
  Proof.
    induction ot as [|[|v] ot IH]; [done | |]; unfold eval_in_tuple in *; simpl; by rewrite IH.
  Qed.

  Lemma eval_out_eot_to_tuple_t (ot : eot) : eval_out_tuple (eot_to_tuple ot) = Some ot.
  Proof.
    induction ot as [|[|v] ot IH]; [done | |]; unfold eval_out_tuple in *; simpl; by rewrite IH.
  Qed.

  Lemma tuple_match_eot_to_eit_t (ot ot' : eot) : tuple_match (eot_to_eit ot) ot' ↔ ot' = ot.
  Proof.
    split.
    - revert ot'. induction ot as [|f ot IH]; intros ot' h; inversion h as [| f1 f2 it ot'' hf ht]; subst.
      + done.
      + f_equal; [| by apply IH].
        destruct f; simpl in hf; by inversion hf.
    - intros ->. induction ot as [|[|v] ot IH]; simpl; constructor; [constructor | done | constructor | done].
  Qed.

  (** ** Basic properties *)

  (** Inverts [good_PAL] hypotheses on terms whose head is not a success position. *)
  Local Ltac invert_good :=
    repeat match goal with h : good_PAL _ _ |- _ => inversion h; subst; clear h end.

  Lemma isucc_not_good : ¬ good_PAL Val isucc.
  Proof. inversion 1. Qed.

  Lemma isucc_tau : isucc ⟶ t_par t_nil t_success.
  Proof. apply tir6. Qed.

  Lemma isucc_tau_good q : isucc ⟶ q → good_PAL Val q.
  Proof. inversion 1; subst. apply good_par_r, good_success. Qed.

  Lemma gen_test_cons_not_good μ s p : ¬ good_PAL Val (gen_test (μ :: s) p).
  Proof. destruct μ; simpl; intros h; invert_good. Qed.

  Lemma ac_t_not_good β : ¬ good_PAL Val (ac_t β).
  Proof. destruct β; simpl; intros h; invert_good. Qed.

  Lemma sum_ac_not_good E : ¬ good_PAL Val (sum_ac E).
  Proof.
    unfold sum_ac. induction (elements E) as [|e l IH]; simpl.
    - inversion 1.
    - intros h. inversion h; subst; [by eapply ac_t_not_good | by apply IH].
  Qed.

  Lemma t_conv_not_good s : ¬ good_PAL Val (t_conv s).
  Proof. destruct s; [apply isucc_not_good | apply gen_test_cons_not_good]. Qed.

  Lemma ta_not_good E s : ¬ good_PAL Val (ta E s).
  Proof. destruct s; [apply sum_ac_not_good | apply gen_test_cons_not_good]. Qed.

  (** Each step of a trace can be abandoned by an internal step to success. *)
  Lemma gen_test_cons_tau_good μ s p : ∃ q, gen_test (μ :: s) p ⟶ q ∧ good_PAL Val q.
  Proof.
    destruct μ; simpl; eexists; split;
      [apply tir8_r, isucc_tau | apply good_echoice_r, good_par_r, good_success
      | apply tir8_r, isucc_tau | apply good_echoice_r, good_par_r, good_success].
  Qed.
End PAL_T_Tests.
