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

(* * lqCCS: syntax

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

Fixpoint exp_subst (k : nat) (v : val) (e : exp) : exp :=
  match e with
  | #i => if decide (i = k) then v else if decide (i < k) then #i else #(pred i)
  | EVal w => w
  | ¬ₑ e => ¬ₑ exp_subst k v e
  | e1 ∨ₑ e2 => exp_subst k v e1 ∨ₑ exp_subst k v e2
  | e1 ≤ₑ e2 => exp_subst k v e1 ≤ₑ exp_subst k v e2
  | e1 =ₑ e2 => exp_subst k v e1 =ₑ exp_subst k v e2
  end.

Fixpoint exp_shift (k : nat) (e : exp) : exp :=
  match e with
  | #i => if decide (k ≤ i) then #(S i) else #i
  | EVal w => w
  | ¬ₑ e => ¬ₑ exp_shift k e
  | e1 ∨ₑ e2 => exp_shift k e1 ∨ₑ exp_shift k e2
  | e1 ≤ₑ e2 => exp_shift k e1 ≤ₑ exp_shift k e2
  | e1 =ₑ e2 => exp_shift k e1 =ₑ exp_shift k e2
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

Section LqP.
  Context `{LP : lqCCS_Parameters}.

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

Inductive proc : Type :=
| PSend (t : tag) (c : channel) (e : exp)
| PIte (e : exp) (P Q : proc)
| PPar (P Q : proc)
| PRes (P : proc)
| PVar (i : nat)
| PRec (t : tag) (P : proc)
| PG (g : guard)
with guard : Type :=
| GNil (es : list exp)
| GSucc
| GPre (𝜆 : prefix) (P : proc)
| GSum (g1 g2 : guard).

Scheme proc_mut_ind := Induction for proc Sort Prop
  with guard_mut_ind := Induction for guard Sort Prop.
Combined Scheme proc_guard_ind from proc_mut_ind, guard_mut_ind.

Coercion PG : guard >-> proc.

Bind Scope lqccs_scope with proc guard.

Notation "𝟘{ es }" := (GNil es) (at level 1, format "𝟘{ es }") : lqccs_scope.
Notation "𝟘" := (PG (GNil [])) : lqccs_scope.
Notation "𝜆 ∙ P" := (GPre 𝜆 P) (at level 46, right associativity) : lqccs_scope.
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

(* ** Substitution of a value [P[v/k]] and shift of the value indices

    [c?.P] and [M(ẽ ▷).P] bind the index [0] of [P]. *)

(* The number of value indices bound by a prefix. *)
Definition prefix_binds (𝜆 : prefix) : nat :=
  match 𝜆 with
  | _ ∶ _ ? | _ ∶ _ ⦅_ ▷⦆ => 1
  | _ => 0
  end.

Definition prefix_subst (k : nat) (v : val) (𝜆 : prefix) : prefix :=
  match 𝜆 with
  | t ∶ 𝛕 => t ∶ 𝛕
  | t ∶ c ? => t ∶ c ?
  | t ∶ U ⦅es⦆ => t ∶ U ⦅map (exp_subst k v) es⦆
  | t ∶ M ⦅es ▷⦆ => t ∶ M ⦅map (exp_subst k v) es ▷⦆
  | t ∶ e := |0⟩ => t ∶ (exp_subst k v e) := |0⟩
  end.

Fixpoint subst (k : nat) (v : val) (P : proc) : proc :=
  match P with
  | t ∶ c ! e => t ∶ c ! (exp_subst k v e)
  | If e Then P Else Q => If (exp_subst k v e) Then subst k v P Else subst k v Q
  | P ∥ Q => subst k v P ∥ subst k v Q
  | ν P => ν (subst k v P)
  | PVar i => PVar i
  | t ∶ rec ∙ P => t ∶ rec ∙ subst k v P
  | PG g => PG (gsubst k v g)
  end
with gsubst (k : nat) (v : val) (g : guard) : guard :=
  match g with
  | 𝟘{es} => 𝟘{map (exp_subst k v) es}
  | 𝟙 => 𝟙
  | 𝜆 ∙ P => prefix_subst k v 𝜆 ∙ subst (prefix_binds 𝜆 + k) v P
  | (g1 + g2)%lq => (gsubst k v g1 + gsubst k v g2)%lq
  end.

Notation "P ⁅ v // k ⁆ᵥ" := (subst k v P) (at level 20) : lqccs_scope.
Notation "P ⁅ v ⁆ᵥ" := (subst 0 v P) (at level 20) : lqccs_scope.

Definition prefix_shift (k : nat) (𝜆 : prefix) : prefix :=
  match 𝜆 with
  | t ∶ 𝛕 => t ∶ 𝛕
  | t ∶ c ? => t ∶ c ?
  | t ∶ U ⦅es⦆ => t ∶ U ⦅map (exp_shift k) es⦆
  | t ∶ M ⦅es ▷⦆ => t ∶ M ⦅map (exp_shift k) es ▷⦆
  | t ∶ e := |0⟩ => t ∶ (exp_shift k e) := |0⟩
  end.

Fixpoint shiftv (k : nat) (P : proc) : proc :=
  match P with
  | t ∶ c ! e => t ∶ c ! (exp_shift k e)
  | If e Then P Else Q => If (exp_shift k e) Then shiftv k P Else shiftv k Q
  | P ∥ Q => shiftv k P ∥ shiftv k Q
  | ν P => ν (shiftv k P)
  | PVar i => PVar i
  | t ∶ rec ∙ P => t ∶ rec ∙ shiftv k P
  | PG g => PG (gshiftv k g)
  end
with gshiftv (k : nat) (g : guard) : guard :=
  match g with
  | 𝟘{es} => 𝟘{map (exp_shift k) es}
  | 𝟙 => 𝟙
  | 𝜆 ∙ P => prefix_shift k 𝜆 ∙ shiftv (prefix_binds 𝜆 + k) P
  | (g1 + g2)%lq => (gshiftv k g1 + gshiftv k g2)%lq
  end.

Notation "⇧ᵥ" := (shiftv 0) : lqccs_scope.

(* ** Renaming of the indices of restricted channels *)

Definition lift (f : nat → nat) (i : nat) : nat :=
  match i with 0 => 0 | S i => S (f i) end.

Definition swap01 (i : nat) : nat :=
  match i with 0 => 1 | 1 => 0 | _ => i end.

Definition ren_chan (f : nat → nat) (c : channel) : channel :=
  match c with CName c => CName c | CIdx i => CIdx (f i) end.

Definition prefix_ren (f : nat → nat) (𝜆 : prefix) : prefix :=
  match 𝜆 with
  | t ∶ c ? => t ∶ (ren_chan f c) ?
  | _ => 𝜆
  end.

Fixpoint ren (f : nat → nat) (P : proc) : proc :=
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
  | 𝜆 ∙ P => prefix_ren f 𝜆 ∙ ren f P
  | (g1 + g2)%lq => (gren f g1 + gren f g2)%lq
  end.

(* ** Shift of the recursion indices

    [rec.P] binds the recursion index [0] of [P]. *)

Fixpoint rshift (k : nat) (P : proc) : proc :=
  match P with
  | t ∶ c ! e => t ∶ c ! e
  | If e Then P1 Else P2 => If e Then rshift k P1 Else rshift k P2
  | P1 ∥ P2 => rshift k P1 ∥ rshift k P2
  | ν P1 => ν (rshift k P1)
  | PVar i => if decide (k ≤ i) then PVar (S i) else PVar i
  | t ∶ rec ∙ P1 => t ∶ rec ∙ rshift (S k) P1
  | PG g => PG (grshift k g)
  end
with grshift (k : nat) (g : guard) : guard :=
  match g with
  | 𝟘{es} => 𝟘{es}
  | 𝟙 => 𝟙
  | 𝜆 ∙ P => 𝜆 ∙ rshift k P
  | (g1 + g2)%lq => (grshift k g1 + grshift k g2)%lq
  end.

Notation "⇧ₚ" := (rshift 0) : lqccs_scope.

(* ** Substitution of a process for a recursion index [P[Q/k]] *)

Fixpoint pr_subst (k : nat) (P Q : proc) : proc :=
  match P with
  | t ∶ c ! e => t ∶ c ! e
  | If e Then P1 Else P2 => If e Then pr_subst k P1 Q Else pr_subst k P2 Q
  | P1 ∥ P2 => pr_subst k P1 Q ∥ pr_subst k P2 Q
  | ν P1 => ν (pr_subst k P1 (ren S Q))
  | PVar i => if decide (i = k) then Q else if decide (k < i) then PVar (pred i) else PVar i
  | t ∶ rec ∙ P1 => t ∶ rec ∙ pr_subst (S k) P1 (⇧ₚ Q)
  | PG g => PG (gpr_subst k g Q)
  end
with gpr_subst (k : nat) (g : guard) (Q : proc) : guard :=
  match g with
  | 𝟘{es} => 𝟘{es}
  | 𝟙 => 𝟙
  | 𝜆 ∙ P => 𝜆 ∙ pr_subst k P (Nat.iter (prefix_binds 𝜆) ⇧ᵥ Q)
  | (g1 + g2)%lq => (gpr_subst k g1 Q + gpr_subst k g2 Q)%lq
  end.

Notation "P ⁅ Q // k ⁆ₚ" := (pr_subst k P Q) (at level 20) : lqccs_scope.
Notation "P ⁅ Q ⁆ₚ" := (pr_subst 0 P Q) (at level 20) : lqccs_scope.

(* ** Iterated restrictions and lifts *)

Fixpoint Ѵ (n : nat) (P : proc) : proc :=
  match n with 0 => P | S n => ν (Ѵ n P) end.

Fixpoint liftn (n : nat) (f : nat → nat) : nat → nat :=
  match n with 0 => f | S n => liftn n (lift f) end.

(* ** Qubits named by expressions *)

Definition eval_qubit (e : exp) : option qubit :=
  match eval e with Some ($q) => Some q | _ => None end.

Definition eval_qubits (es : list exp) : option (list qubit) :=
  mapM eval_qubit es.

(* ** Size *)

Fixpoint size (P : proc) : nat :=
  match P with
  | PSend _ _ _ | PVar _ => 1
  | If _ Then P Else Q | P ∥ Q => S (size P + size Q)
  | ν P | _ ∶ rec ∙ P => S (size P)
  | PG g => S (gsize g)
  end
with gsize (g : guard) : nat :=
  match g with
  | 𝟘{_} | 𝟙 => 0
  | 𝜆 ∙ P => S (size P)
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

Lemma tag_up_inj t u : tag_up t = tag_up u → t = u.
Proof.
  unfold tag_up. intros E. apply (f_equal Cantor.of_nat) in E. rewrite !Cantor.cancel_of_to in E.
  injection E as E1 E2. rewrite <- (Cantor.cancel_to_of t), <- (Cantor.cancel_to_of u).
  f_equal. destruct (Cantor.of_nat t), (Cantor.of_nat u). simpl in *. congruence.
Qed.

Lemma tag_up_neq t : tag_up t ≠ t.
Proof.
  unfold tag_up. intros E. apply (f_equal Cantor.of_nat) in E. rewrite Cantor.cancel_of_to in E.
  destruct (Cantor.of_nat t) as [r g]. simpl in E. injection E as E. lia.
Qed.

Definition prefix_tren (f : tag → tag) (𝜆 : prefix) : prefix :=
  match 𝜆 with
  | t ∶ 𝛕 => f t ∶ 𝛕
  | t ∶ c ? => f t ∶ c ?
  | t ∶ U ⦅es⦆ => f t ∶ U ⦅es⦆
  | t ∶ M ⦅es ▷⦆ => f t ∶ M ⦅es ▷⦆
  | t ∶ e := |0⟩ => f t ∶ e := |0⟩
  end.

Fixpoint tren (f : tag → tag) (P : proc) : proc :=
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
  | 𝜆 ∙ P => prefix_tren f 𝜆 ∙ tren f P
  | (g1 + g2)%lq => (gtren f g1 + gtren f g2)%lq
  end.

Notation "P ↑" := (tren tag_up P) (at level 20, format "P ↑") : lqccs_scope.

Lemma prefix_tren_ext f g 𝜆 : (∀ t, f t = g t) → prefix_tren f 𝜆 = prefix_tren g 𝜆.
Proof. intros H. destruct 𝜆; simpl; by rewrite H. Qed.

Lemma tren_ext_all :
  (∀ P f g, (∀ t, f t = g t) → tren f P = tren g P)
  ∧ (∀ h f g, (∀ t, f t = g t) → gtren f h = gtren g h).
Proof.
  apply proc_guard_ind; simpl; intros; try (f_equal; auto; done).
  f_equal; [by apply prefix_tren_ext | by apply H].
Qed.

Lemma tren_ext f g P : (∀ t, f t = g t) → tren f P = tren g P.
Proof. apply (proj1 tren_ext_all). Qed.

Lemma prefix_tren_comp f g 𝜆 : prefix_tren f (prefix_tren g 𝜆) = prefix_tren (f ∘ g) 𝜆.
Proof. by destruct 𝜆. Qed.

Lemma tren_comp_all :
  (∀ P f g, tren f (tren g P) = tren (f ∘ g) P) ∧ (∀ h f g, gtren f (gtren g h) = gtren (f ∘ g) h).
Proof.
  apply proc_guard_ind; simpl; intros; try (f_equal; auto; done).
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
Proof. apply proc_guard_ind; simpl; intros; congruence. Qed.

End LqP.

Bind Scope lqccs_scope with proc guard.
Notation "𝟘{ es }" := (GNil es) (at level 1, format "𝟘{ es }") : lqccs_scope.
Notation "𝟘" := (PG (GNil [])) : lqccs_scope.
Notation "𝜆 ∙ P" := (GPre 𝜆 P) (at level 46, right associativity) : lqccs_scope.
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
Notation "P ⁅ v // k ⁆ᵥ" := (subst k v P) (at level 20) : lqccs_scope.
Notation "P ⁅ v ⁆ᵥ" := (subst 0 v P) (at level 20) : lqccs_scope.
Notation "P ⁅ Q // k ⁆ₚ" := (pr_subst k P Q) (at level 20) : lqccs_scope.
Notation "P ⁅ Q ⁆ₚ" := (pr_subst 0 P Q) (at level 20) : lqccs_scope.
Notation "P ↑" := (tren tag_up P) (at level 20, format "P ↑") : lqccs_scope.
Notation "⇧ᵥ" := (shiftv 0) : lqccs_scope.
Notation "⇧ₚ" := (rshift 0) : lqccs_scope.
