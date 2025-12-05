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

From Coq Require ssreflect Setoid.
From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
Import ListNotations.
From Coq.Program Require Import Wf Equality.
From Coq.Wellfounded Require Import Inverse_Image.
From Coq.Logic Require Import JMeq ProofIrrelevance.

From stdpp Require Import base countable list decidable finite gmap.

From Must Require Import ActTau.
(** Actions  *)

Inductive ExtAct (A: Type) :=
| ActIn (a : A)
| ActOut (a : A)
.
Arguments ActIn {_} _.
Arguments ActOut {_} _.

Definition ext_act_match {A} (l1 l2: ExtAct A) :=
  match l1, l2 with
  | ActIn x, ActOut y => x = y
  | ActOut x, ActIn y => x = y
  | _, _ => False
  end.

Definition ActIO (A : Type) := Act (ExtAct A).

Notation "c '?'" := (ActExt (ActIn c)) (at level 50).
Notation "c '!'" := (ActExt (ActOut c)) (at level 50).

Definition act_match {A} (l1 l2: Act (ExtAct A)) :=
  match l1, l2 with
  | ActExt x, ActExt y => ext_act_match x y
  | _, _ => False
  end.

Definition co_act {A} (l: ExtAct A) :=
  match l with
  | ActIn x => ActOut x
  | ActOut x => ActIn x
  end.

(* fixme: Involution does not hold anymore in the context of pi-calculus. *)

Lemma co_involution {A} (l: ExtAct A) : co_act (co_act l) = l.
Proof. destruct l; eauto. Qed.

Lemma dual_co {A} (μ : ExtAct A)  : ext_act_match (co_act μ) μ.
Proof.
  destruct μ; simpl; eauto. 
Qed.

Definition act_match_commutative {A} (l1 l2: Act (ExtAct A)):
  act_match l1 l2 -> act_match l2 l1.
Proof. by destruct l1 as [[?|?]|], l2 as [[?|?]|]; eauto; intros ->. Qed.

#[global] Instance actext_eqdec `{EqDecision L} : EqDecision (ExtAct L).
Proof. solve_decision. Defined.
#[global] Instance act_eqdec `{EqDecision L} : EqDecision (Act L).
Proof. solve_decision. Defined.
#[global] Instance ext_act_match_dec `{EqDecision L} : ∀ (ℓ1 ℓ2: ExtAct L), Decision (ext_act_match ℓ1 ℓ2).
Proof.
  intros [l1|l1] [l2|l2]; [by right; intros ? | | | by right; intros ?];
    destruct (decide (l1 = l2)); eauto.
Defined.

#[global] Instance act_match_dec `{EqDecision L} : ∀ (ℓ1 ℓ2: Act (ExtAct L)), Decision (act_match ℓ1 ℓ2).
Proof. intros [l1|] [l2|]; try by (right; eauto). simpl. apply _. Defined.

Definition is_input {A} (μ : ExtAct A) := ∃ a, μ = ActIn a.

Definition are_inputs {A} (s : trace (ExtAct A)) := Forall is_input s.

Definition is_output {A} (μ : ExtAct A) := ∃ a, μ = ActOut a.

Definition are_outputs {A} (s : trace (ExtAct A)) := Forall is_output s.


#[global] Instance ext_act_match_sym `{A : Type} : Symmetric (@ext_act_match A).
Proof. 
  unfold ext_act_match.
  intros μ1 μ2 Hyp.
  destruct μ1; destruct μ2; eauto.
Qed.

Lemma simplify_match_output `{A : Type} a μ : @ext_act_match A (ActOut a) μ <-> μ = ActIn a.
Proof.
  split.
  + intros eq.
    unfold ext_act_match in eq.
    destruct μ; subst; eauto; try contradiction.
  + intro. subst. simpl. eauto.
Qed.

Lemma simplify_match_input `{A : Type} a μ : @ext_act_match A (ActIn a) μ <-> μ = ActOut a.
Proof.
  split.
  + intros eq.
    unfold ext_act_match in eq.
    destruct μ; subst; eauto; try contradiction.
  + intro. subst. simpl. eauto.
Qed.

Definition encode_ext_act `{A : Type} (μ : ExtAct A) : gen_tree (A + A) :=
match μ with
  | ActIn a => GenLeaf (inr a)
  | ActOut a => GenLeaf (inl a)
end.

Definition decode_ext_act `{A : Type} (tree : gen_tree (A + A)) : option (ExtAct A) :=
match tree with
  | GenLeaf (inr a) => Some (ActIn a)
  | GenLeaf (inl a) => Some (ActOut a)
  | _ => None
end.

Lemma encode_decide_ext_act `{EqDecision A , Countable A} μ : @decode_ext_act A (encode_ext_act μ) = Some μ.
Proof. case μ. 
* intros. simpl. reflexivity.
* intros. simpl. reflexivity.
Qed.


#[global] Instance ext_act_countable `{EqDecision A , Countable A} : Countable (ExtAct A).
Proof.
  refine (inj_countable encode_ext_act decode_ext_act encode_decide_ext_act).
Qed.




