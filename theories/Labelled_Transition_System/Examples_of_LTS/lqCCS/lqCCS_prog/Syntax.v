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

(* * Syntax of lqCCS programs

    Tagged lqCCS (Ceragioli, Gadducci, Lomurno, Tedeschi, arXiv:2604.23756),
    with asynchronous outputs, guarded sums, and recursion as in VACCS. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib Require Import Arith.Cantor.
From stdpp Require Import base countable decidable list numbers.

(* ** Names *)

Definition tag : Type := nat.
Definition qubit : Type := nat.
Definition unitary : Type := nat.
Definition meas : Type := nat.

(* ** Values and expressions *)

Inductive val : Type :=
| VBool (b : bool)
| VNat (n : nat)
| VQubit (q : qubit).

#[global] Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.

Declare Scope lqccs_scope.
Delimit Scope lqccs_scope with lq.
Bind Scope lqccs_scope with val.

Coercion VBool : bool >-> val.
Notation "$ n" := (VQubit n) (at level 1, n at level 0, format "$ n") : lqccs_scope.

Inductive exp : Type :=
| EVar (i : nat)
| EVal (v : val)
| ENot (e : exp)
| EOr (e1 e2 : exp)
| ELe (e1 e2 : exp)
| EEq (e1 e2 : exp).

Bind Scope lqccs_scope with exp.
Coercion EVal : val >-> exp.

Notation "# i" := (EVar i) (at level 1, i at level 1, format "# i") : lqccs_scope.
Notation "¬ₑ e" := (ENot e) (at level 35, right associativity) : lqccs_scope.
Notation "e1 ∨ₑ e2" := (EOr e1 e2) (at level 50, left associativity) : lqccs_scope.
Notation "e1 ≤ₑ e2" := (ELe e1 e2) (at level 40, no associativity) : lqccs_scope.
Notation "e1 =ₑ e2" := (EEq e1 e2) (at level 40, no associativity) : lqccs_scope.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Substitution in expressions *)

Fixpoint exp_subst (j : nat) (v : val) (e : exp) : exp :=
  match e with
  | #i => if decide (i = j) then v else if decide (i < j) then #i else #(pred i)
  | EVal w => w
  | ¬ₑ e => ¬ₑ exp_subst j v e
  | e1 ∨ₑ e2 => exp_subst j v e1 ∨ₑ exp_subst j v e2
  | e1 ≤ₑ e2 => exp_subst j v e1 ≤ₑ exp_subst j v e2
  | e1 =ₑ e2 => exp_subst j v e1 =ₑ exp_subst j v e2
  end.

Fixpoint exp_shift (j : nat) (e : exp) : exp :=
  match e with
  | #i => if decide (j ≤ i) then #(S i) else #i
  | EVal w => w
  | ¬ₑ e => ¬ₑ exp_shift j e
  | e1 ∨ₑ e2 => exp_shift j e1 ∨ₑ exp_shift j e2
  | e1 ≤ₑ e2 => exp_shift j e1 ≤ₑ exp_shift j e2
  | e1 =ₑ e2 => exp_shift j e1 =ₑ exp_shift j e2
  end.

(* ** Big-step evaluation〚 e 〛 = v, written [e ⇓ v] in the rules of Ceragioli, Gadducci, Lomurno and Tedeschi. *)

Definition val_le (v1 v2 : val) : option bool :=
  match v1, v2 with
  | VNat n1, VNat n2 => Some (bool_decide (n1 ≤ n2))
  | VBool b1, VBool b2 => Some (implb b1 b2)
  | _, _ => None
  end.

Fixpoint eval (e : exp) : option val :=
  match e with
  | #_ => None
  | EVal v => Some v
  | ¬ₑ e =>
      match eval e with Some (VBool b) => Some (VBool (negb b)) | _ => None end
  | e1 ∨ₑ e2 =>
      match eval e1, eval e2 with
      | Some (VBool b1), Some (VBool b2) => Some (VBool (b1 || b2))
      | _, _ => None
      end
  | e1 ≤ₑ e2 =>
      match eval e1, eval e2 with
      | Some v1, Some v2 => option_map VBool (val_le v1 v2)
      | _, _ => None
      end
  | e1 =ₑ e2 =>
      match eval e1, eval e2 with
      | Some v1, Some v2 => Some (VBool (bool_decide (v1 = v2)))
      | _, _ => None
      end
  end.

Notation "〚 e 〛 = v" := (eval e = @Some val v) (at level 70, no associativity) : lqccs_scope.

#[global] Instance exp_eq_dec : EqDecision exp.
Proof. solve_decision. Defined.


(* ** Parameters of the language *)

Class lqCCS_Parameters := {
  Chan : Type;
  Chan_eq_dec :: EqDecision Chan
}.

Section Prog_Syntax.
  Context `{lqP : lqCCS_Parameters}.

(* ** Channels: names and De Bruijn indices of restrictions *)

Inductive channel : Type :=
| CName (c : Chan)
| CIdx (i : nat).

#[global] Instance channel_eq_dec : EqDecision channel.
Proof. solve_decision. Defined.

(* ** Tagged prefixes and processes *)

Inductive prefix : Type :=
| PTau (t : tag)
| PRecv (t : tag) (c : channel)
| POp (t : tag) (U : unitary) (es : list exp)
| PMeas (t : tag) (M : meas) (es : list exp)
| PReinit (t : tag) (e : exp).

Inductive prog : Type :=
| PSend (t : tag) (c : channel) (e : exp)
| PIte (e : exp) (P Q : prog)
| PPar (P Q : prog)
| PRes (P : prog)
| PVar (i : nat)
| PRec (t : tag) (P : prog)
| PG (g : guard)
with guard : Type :=
| GNil (es : list exp)
| GSucc
| GPre (π : prefix) (P : prog)
| GSum (g1 g2 : guard).

Scheme prog_mut_ind := Induction for prog Sort Prop
  with guard_mut_ind := Induction for guard Sort Prop.
Combined Scheme prog_guard_ind from prog_mut_ind, guard_mut_ind.

Coercion PG : guard >-> prog.

Bind Scope lqccs_scope with prog guard.

Notation "𝟘{ es }" := (GNil es) (at level 1, format "𝟘{ es }") : lqccs_scope.
Notation "𝟘" := (PG (GNil [])) : lqccs_scope.
Notation "π ∙ P" := (GPre π P) (at level 46, right associativity) : lqccs_scope.
Notation "g + g'" := (GSum g g') (at level 50, left associativity) : lqccs_scope.
Notation "P ∥ Q" := (PPar P Q) (at level 60, right associativity) : lqccs_scope.
Notation "'ν' P" := (PRes P) (at level 36) : lqccs_scope.
Notation "𝟙" := GSucc : lqccs_scope.

Notation "t ∶ '𝛕'" := (PTau t) (at level 40) : lqccs_scope.
Notation "t ∶ c ?" := (PRecv t c) (at level 40, c at level 9) : lqccs_scope.
Notation "t ∶ U ⦅ es ⦆" := (POp t U es) (at level 40, U at level 9, format "t  ∶  U  ⦅ es ⦆") : lqccs_scope.
Notation "t ∶ M ⦅ es ▷⦆" := (PMeas t M es) (at level 40, M at level 9, format "t  ∶  M  ⦅ es  ▷⦆") : lqccs_scope.
Notation "t ∶ e ':=' '|0⟩'" := (PReinit t e) (at level 40, e at level 9) : lqccs_scope.
Notation "t ∶ c ! e" := (PSend t c e) (at level 40, c at level 9, e at level 9) : lqccs_scope.
Notation "t ∶ 'rec' ∙ P" := (PRec t P) (at level 40, P at level 40) : lqccs_scope.
Notation "'If' e 'Then' P 'Else' Q" := (PIte e P Q) (at level 55, e at level 9, P at level 54, Q at level 54) : lqccs_scope.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Substitution of a value [P[v/j]] and shift of the value indices

    [c?.P] and [M(ẽ ▷).P] bind the index [0] of [P]. *)

(* The number of value indices bound by a prefix. *)
Definition prefix_binds (π : prefix) : nat :=
  match π with
  | _ ∶ _ ? | _ ∶ _ ⦅_ ▷⦆ => 1
  | _ => 0
  end.

Definition prefix_subst (j : nat) (v : val) (π : prefix) : prefix :=
  match π with
  | t ∶ 𝛕 => t ∶ 𝛕
  | t ∶ c ? => t ∶ c ?
  | t ∶ U ⦅es⦆ => t ∶ U ⦅map (exp_subst j v) es⦆
  | t ∶ M ⦅es ▷⦆ => t ∶ M ⦅map (exp_subst j v) es ▷⦆
  | t ∶ e := |0⟩ => t ∶ (exp_subst j v e) := |0⟩
  end.

Reserved Notation "P ⁅ v // j ⁆ᵥ" (at level 20).

Fixpoint subst (j : nat) (v : val) (P : prog) : prog :=
  match P with
  | t ∶ c ! e => t ∶ c ! (exp_subst j v e)
  | If e Then P Else Q => If (exp_subst j v e) Then P ⁅ v // j ⁆ᵥ Else Q ⁅ v // j ⁆ᵥ
  | P ∥ Q => P ⁅ v // j ⁆ᵥ ∥ Q ⁅ v // j ⁆ᵥ
  | ν P => ν (P ⁅ v // j ⁆ᵥ)
  | PVar i => PVar i
  | t ∶ rec ∙ P => t ∶ rec ∙ P ⁅ v // j ⁆ᵥ
  | PG g => PG (gsubst j v g)
  end
where "P ⁅ v // j ⁆ᵥ" := (subst j v P) : lqccs_scope
with gsubst (j : nat) (v : val) (g : guard) : guard :=
  match g with
  | 𝟘{es} => 𝟘{map (exp_subst j v) es}
  | 𝟙 => 𝟙
  | π ∙ P => prefix_subst j v π ∙ P ⁅ v // prefix_binds π + j ⁆ᵥ
  | (g1 + g2)%lq => (gsubst j v g1 + gsubst j v g2)%lq
  end.

Notation "P ⁅ v ⁆ᵥ" := (subst 0 v P) (at level 20) : lqccs_scope.

Definition prefix_shift (j : nat) (π : prefix) : prefix :=
  match π with
  | t ∶ 𝛕 => t ∶ 𝛕
  | t ∶ c ? => t ∶ c ?
  | t ∶ U ⦅es⦆ => t ∶ U ⦅map (exp_shift j) es⦆
  | t ∶ M ⦅es ▷⦆ => t ∶ M ⦅map (exp_shift j) es ▷⦆
  | t ∶ e := |0⟩ => t ∶ (exp_shift j e) := |0⟩
  end.

Fixpoint shiftv (j : nat) (P : prog) : prog :=
  match P with
  | t ∶ c ! e => t ∶ c ! (exp_shift j e)
  | If e Then P Else Q => If (exp_shift j e) Then shiftv j P Else shiftv j Q
  | P ∥ Q => shiftv j P ∥ shiftv j Q
  | ν P => ν (shiftv j P)
  | PVar i => PVar i
  | t ∶ rec ∙ P => t ∶ rec ∙ shiftv j P
  | PG g => PG (gshiftv j g)
  end
with gshiftv (j : nat) (g : guard) : guard :=
  match g with
  | 𝟘{es} => 𝟘{map (exp_shift j) es}
  | 𝟙 => 𝟙
  | π ∙ P => prefix_shift j π ∙ shiftv (prefix_binds π + j) P
  | (g1 + g2)%lq => (gshiftv j g1 + gshiftv j g2)%lq
  end.

Notation "⇧ᵥ" := (shiftv 0) : lqccs_scope.

(* ** Renaming of the indices of restricted channels *)

Definition lift (f : nat → nat) (i : nat) : nat :=
  match i with 0 => 0 | S i => S (f i) end.

Definition swap01 (i : nat) : nat :=
  match i with 0 => 1 | 1 => 0 | _ => i end.

Definition ren_chan (f : nat → nat) (c : channel) : channel :=
  match c with CName c => CName c | CIdx i => CIdx (f i) end.

Definition prefix_ren (f : nat → nat) (π : prefix) : prefix :=
  match π with
  | t ∶ c ? => t ∶ (ren_chan f c) ?
  | _ => π
  end.

Fixpoint ren (f : nat → nat) (P : prog) : prog :=
  match P with
  | t ∶ c ! e => t ∶ (ren_chan f c) ! e
  | If e Then P Else Q => If e Then ren f P Else ren f Q
  | P ∥ Q => ren f P ∥ ren f Q
  | ν P => ν (ren (lift f) P)
  | PVar i => PVar i
  | t ∶ rec ∙ P => t ∶ rec ∙ ren f P
  | PG g => PG (gren f g)
  end
with gren (f : nat → nat) (g : guard) : guard :=
  match g with
  | 𝟘{es} => 𝟘{es}
  | 𝟙 => 𝟙
  | π ∙ P => prefix_ren f π ∙ ren f P
  | (g1 + g2)%lq => (gren f g1 + gren f g2)%lq
  end.

(* ** Shift of the recursion indices

    [rec.P] binds the recursion index [0] of [P]. *)

Fixpoint rshift (j : nat) (P : prog) : prog :=
  match P with
  | t ∶ c ! e => t ∶ c ! e
  | If e Then P1 Else P2 => If e Then rshift j P1 Else rshift j P2
  | P1 ∥ P2 => rshift j P1 ∥ rshift j P2
  | ν P1 => ν (rshift j P1)
  | PVar i => if decide (j ≤ i) then PVar (S i) else PVar i
  | t ∶ rec ∙ P1 => t ∶ rec ∙ rshift (S j) P1
  | PG g => PG (grshift j g)
  end
with grshift (j : nat) (g : guard) : guard :=
  match g with
  | 𝟘{es} => 𝟘{es}
  | 𝟙 => 𝟙
  | π ∙ P => π ∙ rshift j P
  | (g1 + g2)%lq => (grshift j g1 + grshift j g2)%lq
  end.

Notation "⇧ₚ" := (rshift 0) : lqccs_scope.

(* ** Substitution of a process for a recursion index [P[Q/j]] *)

Reserved Notation "P ⁅ Q // j ⁆ₚ" (at level 20).

Fixpoint pr_subst (j : nat) (P Q : prog) : prog :=
  match P with
  | t ∶ c ! e => t ∶ c ! e
  | If e Then P1 Else P2 => If e Then P1 ⁅ Q // j ⁆ₚ Else P2 ⁅ Q // j ⁆ₚ
  | P1 ∥ P2 => P1 ⁅ Q // j ⁆ₚ ∥ P2 ⁅ Q // j ⁆ₚ
  | ν P1 => ν (P1 ⁅ ren S Q // j ⁆ₚ)
  | PVar i => if decide (i = j) then Q else if decide (j < i) then PVar (pred i) else PVar i
  | t ∶ rec ∙ P1 => t ∶ rec ∙ P1 ⁅ ⇧ₚ Q // S j ⁆ₚ
  | PG g => PG (gpr_subst j g Q)
  end
where "P ⁅ Q // j ⁆ₚ" := (pr_subst j P Q) : lqccs_scope
with gpr_subst (j : nat) (g : guard) (Q : prog) : guard :=
  match g with
  | 𝟘{es} => 𝟘{es}
  | 𝟙 => 𝟙
  | π ∙ P => π ∙ P ⁅ Nat.iter (prefix_binds π) ⇧ᵥ Q // j ⁆ₚ
  | (g1 + g2)%lq => (gpr_subst j g1 Q + gpr_subst j g2 Q)%lq
  end.

Notation "P ⁅ Q ⁆ₚ" := (pr_subst 0 P Q) (at level 20) : lqccs_scope.

(* ** Iterated restrictions and lifts *)

Fixpoint Ѵ (n : nat) (P : prog) : prog :=
  match n with 0 => P | S n => ν (Ѵ n P) end.

Fixpoint liftn (n : nat) (f : nat → nat) : nat → nat :=
  match n with 0 => f | S n => liftn n (lift f) end.

(* ** Qubits named by expressions *)

Definition eval_qubit (e : exp) : option qubit :=
  match eval e with Some ($q) => Some q | _ => None end.

Definition eval_qubits (es : list exp) : option (list qubit) :=
  mapM eval_qubit es.

(* ** Size *)

Fixpoint size (P : prog) : nat :=
  match P with
  | PSend _ _ _ | PVar _ => 1
  | If _ Then P Else Q | P ∥ Q => S (size P + size Q)
  | ν P | _ ∶ rec ∙ P => S (size P)
  | PG g => S (gsize g)
  end
with gsize (g : guard) : nat :=
  match g with
  | 𝟘{_} | 𝟙 => 0
  | π ∙ P => S (size P)
  | (g1 + g2)%lq => S (gsize g1 + gsize g2)
  end.

(* ** Generations of tags

    A tag is a root with a generation, [⟨r, g⟩]; [tag_up] moves a tag to
    the next generation of the same root.  Unfolding a recursion moves the
    tags of the pending recursion to the next generation. *)

Definition tag_root (t : tag) : nat := (Cantor.of_nat t).1.

Definition tag_up (t : tag) : tag := Cantor.to_nat ((Cantor.of_nat t).1, S (Cantor.of_nat t).2).

Lemma tag_up_root t : tag_root (tag_up t) = tag_root t.
Proof. unfold tag_root, tag_up. by rewrite Cantor.cancel_of_to. Qed.

Lemma tag_up_inj t t' : tag_up t = tag_up t' → t = t'.
Proof.
  unfold tag_up. intros E. apply (f_equal Cantor.of_nat) in E. rewrite !Cantor.cancel_of_to in E.
  injection E as E1 E2. rewrite <- (Cantor.cancel_to_of t), <- (Cantor.cancel_to_of t').
  f_equal. destruct (Cantor.of_nat t), (Cantor.of_nat t'). simpl in *. congruence.
Qed.

Lemma tag_up_neq t : tag_up t ≠ t.
Proof.
  unfold tag_up. intros E. apply (f_equal Cantor.of_nat) in E. rewrite Cantor.cancel_of_to in E.
  destruct (Cantor.of_nat t) as [r g]. simpl in E. injection E as E. lia.
Qed.

Definition prefix_tren (f : tag → tag) (π : prefix) : prefix :=
  match π with
  | t ∶ 𝛕 => f t ∶ 𝛕
  | t ∶ c ? => f t ∶ c ?
  | t ∶ U ⦅es⦆ => f t ∶ U ⦅es⦆
  | t ∶ M ⦅es ▷⦆ => f t ∶ M ⦅es ▷⦆
  | t ∶ e := |0⟩ => f t ∶ e := |0⟩
  end.

Fixpoint tren (f : tag → tag) (P : prog) : prog :=
  match P with
  | t ∶ c ! e => f t ∶ c ! e
  | If e Then P Else Q => If e Then tren f P Else tren f Q
  | P ∥ Q => tren f P ∥ tren f Q
  | ν P => ν (tren f P)
  | PVar i => PVar i
  | t ∶ rec ∙ P => f t ∶ rec ∙ tren f P
  | PG g => PG (gtren f g)
  end
with gtren (f : tag → tag) (g : guard) : guard :=
  match g with
  | 𝟘{es} => 𝟘{es}
  | 𝟙 => 𝟙
  | π ∙ P => prefix_tren f π ∙ tren f P
  | (g1 + g2)%lq => (gtren f g1 + gtren f g2)%lq
  end.

Notation "P ↑" := (tren tag_up P) (at level 20, format "P ↑") : lqccs_scope.

Lemma prefix_tren_ext f g π : (∀ t, f t = g t) → prefix_tren f π = prefix_tren g π.
Proof. intros H. destruct π; simpl; by rewrite H. Qed.

Lemma tren_ext_all :
  (∀ P f g, (∀ t, f t = g t) → tren f P = tren g P)
  ∧ (∀ h f g, (∀ t, f t = g t) → gtren f h = gtren g h).
Proof.
  apply prog_guard_ind; simpl; intros; try (f_equal; auto; done).
  f_equal; [by apply prefix_tren_ext | by apply H].
Qed.

Lemma tren_ext f g P : (∀ t, f t = g t) → tren f P = tren g P.
Proof. apply (proj1 tren_ext_all). Qed.

Lemma prefix_tren_comp f g π : prefix_tren f (prefix_tren g π) = prefix_tren (f ∘ g) π.
Proof. by destruct π. Qed.

Lemma tren_comp_all :
  (∀ P f g, tren f (tren g P) = tren (f ∘ g) P) ∧ (∀ h f g, gtren f (gtren g h) = gtren (f ∘ g) h).
Proof.
  apply prog_guard_ind; simpl; intros; try (f_equal; auto; done).
  f_equal; [apply prefix_tren_comp | apply H].
Qed.

Lemma tren_comp f g P : tren f (tren g P) = tren (f ∘ g) P.
Proof. apply (proj1 tren_comp_all). Qed.

(* The first tag of a root. *)
Definition tag_base (t : tag) : tag := Cantor.to_nat (tag_root t, 0).

Lemma tag_base_up t : tag_base (tag_up t) = tag_base t.
Proof. unfold tag_base. by rewrite tag_up_root. Qed.

Lemma tren_base_up P : tren tag_base (P↑) = tren tag_base P.
Proof. rewrite tren_comp. apply tren_ext. intros t. apply tag_base_up. Qed.

Lemma size_tren : (∀ P f, size (tren f P) = size P) ∧ (∀ g f, gsize (gtren f g) = gsize g).
Proof. apply prog_guard_ind; simpl; intros; congruence. Qed.

End Prog_Syntax.

Bind Scope lqccs_scope with prog guard.
Notation "𝟘{ es }" := (GNil es) (at level 1, format "𝟘{ es }") : lqccs_scope.
Notation "𝟘" := (PG (GNil [])) : lqccs_scope.
Notation "π ∙ P" := (GPre π P) (at level 46, right associativity) : lqccs_scope.
Notation "g + g'" := (GSum g g') (at level 50, left associativity) : lqccs_scope.
Notation "P ∥ Q" := (PPar P Q) (at level 60, right associativity) : lqccs_scope.
Notation "'ν' P" := (PRes P) (at level 36) : lqccs_scope.
Notation "𝟙" := GSucc : lqccs_scope.
Notation "t ∶ '𝛕'" := (PTau t) (at level 40) : lqccs_scope.
Notation "t ∶ c ?" := (PRecv t c) (at level 40, c at level 9) : lqccs_scope.
Notation "t ∶ U ⦅ es ⦆" := (POp t U es) (at level 40, U at level 9, format "t  ∶  U  ⦅ es ⦆") : lqccs_scope.
Notation "t ∶ M ⦅ es ▷⦆" := (PMeas t M es) (at level 40, M at level 9, format "t  ∶  M  ⦅ es  ▷⦆") : lqccs_scope.
Notation "t ∶ e ':=' '|0⟩'" := (PReinit t e) (at level 40, e at level 9) : lqccs_scope.
Notation "t ∶ c ! e" := (PSend t c e) (at level 40, c at level 9, e at level 9) : lqccs_scope.
Notation "t ∶ 'rec' ∙ P" := (PRec t P) (at level 40, P at level 40) : lqccs_scope.
Notation "'If' e 'Then' P 'Else' Q" := (PIte e P Q) (at level 55, e at level 9, P at level 54, Q at level 54) : lqccs_scope.
Notation "P ⁅ v // j ⁆ᵥ" := (subst j v P) (at level 20) : lqccs_scope.
Notation "P ⁅ v ⁆ᵥ" := (subst 0 v P) (at level 20) : lqccs_scope.
Notation "P ⁅ Q // j ⁆ₚ" := (pr_subst j P Q) (at level 20) : lqccs_scope.
Notation "P ⁅ Q ⁆ₚ" := (pr_subst 0 P Q) (at level 20) : lqccs_scope.
Notation "P ↑" := (tren tag_up P) (at level 20, format "P ↑") : lqccs_scope.
Notation "⇧ᵥ" := (shiftv 0) : lqccs_scope.
Notation "⇧ₚ" := (rshift 0) : lqccs_scope.
