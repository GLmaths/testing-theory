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
From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable decidable.
From TestingTheory Require Import ActTau gLts.

Inductive MemAct (A : Type) :=
| msg (η : A)
| cobar (η : A).

Arguments msg {A} η.
Arguments cobar {A} η.

#[global] Instance MemAct_eqdec `{EqDecision A} : EqDecision (MemAct A).
Proof. solve_decision. Defined.

#[global] Instance MemAct_countable `{Countable A} : Countable (MemAct A).
Proof.
  apply (inj_countable'
           (λ a, match a with msg η => inl η | cobar η => inr η end)
           (λ s, match s with inl η => msg η | inr η => cobar η end)).
  by intros [].
Defined.

Section Mem.

Context `{H : ExtAction A}.

Definition mem_nb (a : MemAct A) : Prop :=
  match a with msg η => non_blocking η | cobar _ => False end.

Definition mem_dual (a b : MemAct A) : Prop :=
  match a, b with
  | msg η, cobar η' | cobar η, msg η' => η = η'
  | _, _ => False
  end.

#[local] Instance mem_nb_dec a : Decision (mem_nb a).
Proof. destruct a; simpl; apply _. Defined.

#[local] Instance mem_dual_dec a b : Decision (mem_dual a b).
Proof. destruct a, b; simpl; apply _. Defined.

Lemma mem_dual_blocks β η : mem_nb η → mem_dual β η → ¬ mem_nb β.
Proof. destruct β, η; simpl; tauto. Qed.

Lemma mem_dual_sym : Symmetric mem_dual.
Proof. intros [] [] h; simpl in *; by subst. Qed.

Definition mem_exists_dual (a : MemAct A) : { b | mem_dual a b } :=
  match a with
  | msg η => exist _ (cobar η) eq_refl
  | cobar η => exist _ (msg η) eq_refl
  end.

Definition ExtAction_mem : ExtAction (MemAct A) :=
  {| eqdec := _;
     countable := _;
     non_blocking := mem_nb;
     non_blocking_dec := mem_nb_dec;
     dual := mem_dual;
     dual_dec := mem_dual_dec;
     dual_blocks := mem_dual_blocks;
     duo_sym := mem_dual_sym;
     exists_dual := mem_exists_dual |}.

Lemma UniqueDual_mem : @UniqueDual (MemAct A) ExtAction_mem.
Proof. intros [] [] h; simpl in *; by subst. Qed.

End Mem.

#[global] Hint Extern 10 (ExtAction (MemAct ?A)) =>
  assert_fails (is_evar A); exact ExtAction_mem : typeclass_instances.

#[global] Hint Extern 10 (@UniqueDual (MemAct ?A) _) =>
  assert_fails (is_evar A); exact UniqueDual_mem : typeclass_instances.