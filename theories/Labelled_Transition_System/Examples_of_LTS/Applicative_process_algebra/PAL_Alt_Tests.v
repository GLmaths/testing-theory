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
From TestingTheory Require Import ActTau gLts InputOutputActions Bisimulation
  PAL_Syntax PAL_Alt_LTS PAL_Alt_Phi PAL_Good.

(* * Tests for the completeness of the alternative LTS of PAL

   The observers of De Nicola–Pugliese (Definition 5.9), along a trace of
   actions of the test:
   - [isucc = eval(nil).✓] succeeds after an internal step;
   - for an input [AIn l], the test inputs with the pattern of template
     [ltemplate l], and goes on only if the received tuple is [ltuple l],
     otherwise it succeeds;
   - for an output [AOut ot], the test emits [ot] with [out(ot).nil ⌊ _];
   - each step can also be abandoned by [isucc].
   [t_conv] ends with [isucc] (the paper's [con]), [ta E] ends with an
   external choice among the tests [ac e] for the events [e ∈ E] (the
   paper's [ac]):
   - [ac (EvOut ot) = out(ot).nil ⌊ ✓];
   - [ac (EvIn tp) = in(pattern of tp).✓]. *)

Section PAL_Alt_Tests.
  Context (Val : Type) `{Countable Val} `{!Inhabited Val}.

  Notation term := (term Val).
  Notation bexp := (bexp Val).
  Notation eot := (eot Val).
  Notation label := (label Val).
  Notation ltemplate := (ltemplate Val).
  Notation ltuple := (ltuple Val).
  Notation PALA_Act := (PALA_Act Val).
  Notation Event := (Event Val).
  Notation pattern_from := (pattern_from Val).

  (** Infer the action type of [⟶], [⟶[μ]], ... from the LTS on terms. *)
  #[local] Hint Mode ExtAction ! : typeclass_instances.

  (** The received tuple is [ltuple l]: the formal fields [i], [i+1], ... got
      the values of [l]. *)
  Fixpoint guard_l (i : nat) (l : label) : bexp :=
    match l with
    | [] => b_true
    | lf_formal _ v :: l' => b_and (b_eq (ve_var i) (ve_val v)) (guard_l (S i) l')
    | _ :: l' => guard_l (S i) l'
    end.

  (** ** The tests *)

  Open Scope pal_scope.

  (** [isucc = eval(nil).✓] *)
  Definition isucc : term := eval( 𝟘 ) • ✓.

  Fixpoint gen_test (s : list PALA_Act) (p : term) : term :=
    match s with
    | [] => p
    | AIn _ l :: s' =>
        (in( pattern_from 0 (ltemplate l) ) • (IF guard_l 0 l THEN gen_test s' p ELSE ✓)) □ isucc
    | AOut _ ot :: s' =>
        ((out( eot_to_tuple ot ) • 𝟘) ⌊ gen_test s' p) □ isucc
    end.

  (** Tests for convergence: the paper's [con]. *)
  Definition t_conv (s : list PALA_Act) : term := gen_test s isucc.

  (** The test of one event: the paper's [ac e]. *)
  Definition ac_t (e : Event) : term :=
    match e with
    | EvOut _ ot => (out( eot_to_tuple ot ) • 𝟘) ⌊ ✓
    | EvIn _ tp => in( pattern_from 0 tp ) • ✓
    end.

  Definition sum_ac (E : gset Event) : term :=
    foldr (λ e acc, ac_t e □ acc) 𝟘 (elements E).

  (** Tests for co-acceptance sets: the paper's [ac]. *)
  Definition ta (E : gset Event) (s : list PALA_Act) : term := gen_test s (sum_ac E).

  (** ** Basic properties *)

  Local Ltac invert_good :=
    repeat match goal with h : good_PAL _ _ |- _ => inversion h; subst; clear h end.

  Lemma isucc_not_good : ¬ good_PAL Val isucc.
  Proof. inversion 1. Qed.

  Lemma isucc_tau : isucc ⟶ (𝟘 ‖ ✓).
  Proof. apply air6. Qed.

  Lemma isucc_tau_good q : isucc ⟶ q → good_PAL Val q.
  Proof. inversion 1; subst. apply good_par_r, good_success. Qed.

  Lemma gen_test_cons_not_good μ s p : ¬ good_PAL Val (gen_test (μ :: s) p).
  Proof. destruct μ; simpl; intros h; invert_good. Qed.

  Lemma ac_t_not_good e : ¬ good_PAL Val (ac_t e).
  Proof. destruct e; simpl; intros h; invert_good. Qed.

  Lemma sum_ac_not_good E : ¬ good_PAL Val (sum_ac E).
  Proof.
    unfold sum_ac. induction (elements E) as [|e l IH]; simpl.
    - inversion 1.
    - intros h. inversion h; subst; [by eapply ac_t_not_good | by apply IH].
  Qed.

  Lemma gen_test_cons_tau_good μ s p : ∃ q, gen_test (μ :: s) p ⟶ q ∧ good_PAL Val q.
  Proof.
    destruct μ; simpl; eexists; split;
      [apply air8_r, isucc_tau | apply good_echoice_r, good_par_r, good_success
      | apply air8_r, isucc_tau | apply good_echoice_r, good_par_r, good_success].
  Qed.
  Close Scope pal_scope.
End PAL_Alt_Tests.
