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
(* * lqCCS: syntax

    Tagged lqCCS (Ceragioli, Gadducci, Lomurno, Tedeschi, arXiv:2604.23756),
    with asynchronous outputs, guarded sums, and recursion as in VACCS.

    - Restricted channels are De Bruijn indices ([CIdx i]), as in VACCS:
      [ν P] binds the index [0] of [P].  Free channels are names ([CName c]).
      Processes are then identified up to α-conversion, and no side
      condition is needed for scope extrusion.
    - Variables of values are named, bound by [c?x] and [M(ẽ ▷ x)], and
      substituted by closed values.
    - [①] is an inert guard marking the success of an observer. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list numbers.

(* ** Names *)

Definition tag : Type := nat.
Definition qubit : Type := nat.
Definition sop : Type := nat.
Definition meas : Type := nat.
Definition chan : Type := nat.

(* ** Values and expressions *)

Inductive val : Type :=
| VBool (b : bool)
| VNat (n : nat)
| VQubit (q : qubit).

#[global] Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.

Inductive exp : Type :=
| EVar (i : nat)
| EVal (v : val)
| ENot (e : exp)
| EOr (e1 e2 : exp)
| ELe (e1 e2 : exp)
| EEq (e1 e2 : exp).

(* ** Substitution in expressions *)

(* [exp_subst k v e] substitutes [v] for the index [k] and lowers the
    indices above [k]; [exp_shift k e] makes room for a new index [k]. *)
Fixpoint exp_subst (k : nat) (v : val) (e : exp) : exp :=
  match e with
  | EVar i => if decide (i = k) then EVal v else if decide (i < k) then EVar i else EVar (pred i)
  | EVal w => EVal w
  | ENot e => ENot (exp_subst k v e)
  | EOr e1 e2 => EOr (exp_subst k v e1) (exp_subst k v e2)
  | ELe e1 e2 => ELe (exp_subst k v e1) (exp_subst k v e2)
  | EEq e1 e2 => EEq (exp_subst k v e1) (exp_subst k v e2)
  end.

Fixpoint exp_shift (k : nat) (e : exp) : exp :=
  match e with
  | EVar i => if decide (k ≤ i) then EVar (S i) else EVar i
  | EVal w => EVal w
  | ENot e => ENot (exp_shift k e)
  | EOr e1 e2 => EOr (exp_shift k e1) (exp_shift k e2)
  | ELe e1 e2 => ELe (exp_shift k e1) (exp_shift k e2)
  | EEq e1 e2 => EEq (exp_shift k e1) (exp_shift k e2)
  end.

(* ** Big-step evaluation [e ⇓ v] *)

Definition val_le (v1 v2 : val) : option bool :=
  match v1, v2 with
  | VNat n1, VNat n2 => Some (bool_decide (n1 ≤ n2))
  | VBool b1, VBool b2 => Some (implb b1 b2)
  | _, _ => None
  end.

Fixpoint eval (e : exp) : option val :=
  match e with
  | EVar _ => None
  | EVal v => Some v
  | ENot e =>
      match eval e with Some (VBool b) => Some (VBool (negb b)) | _ => None end
  | EOr e1 e2 =>
      match eval e1, eval e2 with
      | Some (VBool b1), Some (VBool b2) => Some (VBool (b1 || b2))
      | _, _ => None
      end
  | ELe e1 e2 =>
      match eval e1, eval e2 with
      | Some v1, Some v2 => option_map VBool (val_le v1 v2)
      | _, _ => None
      end
  | EEq e1 e2 =>
      match eval e1, eval e2 with
      | Some v1, Some v2 => Some (VBool (bool_decide (v1 = v2)))
      | _, _ => None
      end
  end.

#[global] Instance exp_eq_dec : EqDecision exp.
Proof. solve_decision. Defined.


(* ** Channels: names and De Bruijn indices of restrictions *)

Inductive channel : Type :=
| CName (c : chan)
| CIdx (i : nat).

#[global] Instance channel_eq_dec : EqDecision channel.
Proof. solve_decision. Defined.

(* ** Tagged prefixes and processes *)

Inductive prefix : Type :=
| PTau (t : tag)
| PRecv (t : tag) (c : channel)
| POp (t : tag) (E : sop) (es : list exp)
| PMeas (t : tag) (M : meas) (es : list exp)
| PInit (t : tag) (es : list exp).

Inductive proc : Type :=
| PSend (t : tag) (c : channel) (e : exp)
| PIte (e : exp) (P Q : proc)
| PPar (P Q : proc)
| PRes (P : proc)
| PVar (X : nat)
| PRec (t : tag) (X : nat) (P : proc)
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

Declare Scope lqccs_scope.
Delimit Scope lqccs_scope with lq.
Bind Scope lqccs_scope with proc guard.

Notation "𝟘" := (PG (GNil [])) : lqccs_scope.
Notation "𝜆 ∙ P" := (GPre 𝜆 P) (at level 46, right associativity) : lqccs_scope.
Notation "g + g'" := (GSum g g') (at level 50, left associativity) : lqccs_scope.
Notation "P ∥ Q" := (PPar P Q) (at level 60, right associativity) : lqccs_scope.
Notation "'ν' P" := (PRes P) (at level 36) : lqccs_scope.
Notation "①" := GSucc : lqccs_scope.

Notation "t ∶ '𝛕'" := (PTau t) (at level 40) : lqccs_scope.
Notation "t ∶ c ?" := (PRecv t c) (at level 40, c at level 9) : lqccs_scope.
Notation "t ∶ E ⦅ es ⦆" := (POp t E es) (at level 40, E at level 9) : lqccs_scope.
Notation "t ∶ M ⦅ es ▷⦆" := (PMeas t M es) (at level 40, M at level 9) : lqccs_scope.
Notation "t ∶ 'init' ⦅ es ⦆" := (PInit t es) (at level 40) : lqccs_scope.
Notation "t ∶ c ! e" := (PSend t c e) (at level 40, c at level 9, e at level 9) : lqccs_scope.
Notation "t ∶ 'rec' X ∙ P" := (PRec t X P) (at level 40, X at level 9, P at level 40) : lqccs_scope.
Notation "'If' e 'Then' P 'Else' Q" := (PIte e P Q) (at level 55, e at level 9, P at level 54, Q at level 54) : lqccs_scope.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Substitution of a value [P[v/k]] and shift of the value indices

    [c?.P] and [M(ẽ ▷).P] bind the index [0] of [P]. *)

(* The number of value indices bound by a prefix. *)
Definition prefix_binds (𝜆 : prefix) : nat :=
  match 𝜆 with
  | PRecv _ _ | PMeas _ _ _ => 1
  | _ => 0
  end.

Definition prefix_subst (k : nat) (v : val) (𝜆 : prefix) : prefix :=
  match 𝜆 with
  | PTau t => PTau t
  | PRecv t c => PRecv t c
  | POp t E es => POp t E (map (exp_subst k v) es)
  | PMeas t M es => PMeas t M (map (exp_subst k v) es)
  | PInit t es => PInit t (map (exp_subst k v) es)
  end.

Fixpoint subst (k : nat) (v : val) (P : proc) : proc :=
  match P with
  | PSend t c e => PSend t c (exp_subst k v e)
  | PIte e P Q => PIte (exp_subst k v e) (subst k v P) (subst k v Q)
  | P ∥ Q => subst k v P ∥ subst k v Q
  | ν P => ν (subst k v P)
  | PVar X => PVar X
  | PRec t X P => PRec t X (subst k v P)
  | PG g => PG (gsubst k v g)
  end
with gsubst (k : nat) (v : val) (g : guard) : guard :=
  match g with
  | GNil es => GNil (map (exp_subst k v) es)
  | ① => ①
  | 𝜆 ∙ P => prefix_subst k v 𝜆 ∙ subst (prefix_binds 𝜆 + k) v P
  | (g1 + g2)%lq => (gsubst k v g1 + gsubst k v g2)%lq
  end.

Notation "P ⟦ v ⟧" := (subst 0 v P) (at level 20) : lqccs_scope.

Definition prefix_shift (k : nat) (𝜆 : prefix) : prefix :=
  match 𝜆 with
  | PTau t => PTau t
  | PRecv t c => PRecv t c
  | POp t E es => POp t E (map (exp_shift k) es)
  | PMeas t M es => PMeas t M (map (exp_shift k) es)
  | PInit t es => PInit t (map (exp_shift k) es)
  end.

Fixpoint shiftv (k : nat) (P : proc) : proc :=
  match P with
  | PSend t c e => PSend t c (exp_shift k e)
  | PIte e P Q => PIte (exp_shift k e) (shiftv k P) (shiftv k Q)
  | P ∥ Q => shiftv k P ∥ shiftv k Q
  | ν P => ν (shiftv k P)
  | PVar X => PVar X
  | PRec t X P => PRec t X (shiftv k P)
  | PG g => PG (gshiftv k g)
  end
with gshiftv (k : nat) (g : guard) : guard :=
  match g with
  | GNil es => GNil (map (exp_shift k) es)
  | ① => ①
  | 𝜆 ∙ P => prefix_shift k 𝜆 ∙ shiftv (prefix_binds 𝜆 + k) P
  | (g1 + g2)%lq => (gshiftv k g1 + gshiftv k g2)%lq
  end.

(* ** Renaming of the indices of restricted channels

    [ren f P] applies [f] to the free indices of [P]; under a restriction,
    [f] is lifted.  [ren S] is the shift of VACCS ([NewVarC 0]), [ren swap01]
    exchanges the two innermost restrictions. *)

Definition lift (f : nat → nat) (i : nat) : nat :=
  match i with 0 => 0 | S i => S (f i) end.

Definition swap01 (i : nat) : nat :=
  match i with 0 => 1 | 1 => 0 | _ => i end.

Definition ren_chan (f : nat → nat) (c : channel) : channel :=
  match c with CName c => CName c | CIdx i => CIdx (f i) end.

Definition prefix_ren (f : nat → nat) (𝜆 : prefix) : prefix :=
  match 𝜆 with
  | PRecv t c => PRecv t (ren_chan f c)
  | _ => 𝜆
  end.

Fixpoint ren (f : nat → nat) (P : proc) : proc :=
  match P with
  | PSend t c e => PSend t (ren_chan f c) e
  | PIte e P Q => PIte e (ren f P) (ren f Q)
  | P ∥ Q => ren f P ∥ ren f Q
  | ν P => ν (ren (lift f) P)
  | PVar X => PVar X
  | PRec t X P => PRec t X (ren f P)
  | PG g => PG (gren f g)
  end
with gren (f : nat → nat) (g : guard) : guard :=
  match g with
  | GNil es => GNil es
  | ① => ①
  | 𝜆 ∙ P => prefix_ren f 𝜆 ∙ ren f P
  | (g1 + g2)%lq => (gren f g1 + gren f g2)%lq
  end.

(* ** Substitution of a process for a recursion variable [P[Q/X]] *)

Fixpoint pr_subst (X : nat) (P Q : proc) : proc :=
  match P with
  | PSend t c e => PSend t c e
  | PIte e P1 P2 => PIte e (pr_subst X P1 Q) (pr_subst X P2 Q)
  | P1 ∥ P2 => pr_subst X P1 Q ∥ pr_subst X P2 Q
  | ν P1 => ν (pr_subst X P1 (ren S Q))
  | PVar Y => if decide (X = Y) then Q else PVar Y
  | PRec t Y P1 => if decide (X = Y) then PRec t Y P1 else PRec t Y (pr_subst X P1 Q)
  | PG g => PG (gpr_subst X g Q)
  end
with gpr_subst (X : nat) (g : guard) (Q : proc) : guard :=
  match g with
  | GNil es => GNil es
  | ① => ①
  | 𝜆 ∙ P => 𝜆 ∙ pr_subst X P (Nat.iter (prefix_binds 𝜆) (shiftv 0) Q)
  | (g1 + g2)%lq => (gpr_subst X g1 Q + gpr_subst X g2 Q)%lq
  end.

Notation "P ⦃ Q // X ⦄" := (pr_subst X P Q) (at level 20) : lqccs_scope.

(* ** Qubits named by expressions *)

Definition eval_qubit (e : exp) : option qubit :=
  match eval e with Some (VQubit q) => Some q | _ => None end.

Definition eval_qubits (es : list exp) : option (list qubit) :=
  mapM eval_qubit es.

(* ** Size *)

Fixpoint size (P : proc) : nat :=
  match P with
  | PSend _ _ _ | PVar _ => 1
  | PIte _ P Q | P ∥ Q => S (size P + size Q)
  | ν P | PRec _ _ P => S (size P)
  | PG g => S (gsize g)
  end
with gsize (g : guard) : nat :=
  match g with
  | GNil _ | ① => 0
  | 𝜆 ∙ P => S (size P)
  | (g1 + g2)%lq => S (gsize g1 + gsize g2)
  end.

(* ** Facts on renamings *)

Lemma lift_ext f g : (∀ i, f i = g i) → ∀ i, lift f i = lift g i.
Proof. intros H [|i]; simpl; congruence. Qed.

Lemma lift_id i : lift id i = i.
Proof. by destruct i. Qed.

Lemma lift_comp f g i : lift f (lift g i) = lift (f ∘ g) i.
Proof. by destruct i. Qed.

Lemma lift_S f i : lift f (S i) = S (f i).
Proof. done. Qed.

Lemma lift_lift_swap01 f i : lift (lift f) (swap01 i) = swap01 (lift (lift f) i).
Proof. destruct i as [|[|i]]; done. Qed.

Lemma swap01_invol i : swap01 (swap01 i) = i.
Proof. destruct i as [|[|i]]; done. Qed.

Lemma swap01_SS i : swap01 (S (S i)) = S (S i).
Proof. done. Qed.

Lemma ren_chan_ext f g c : (∀ i, f i = g i) → ren_chan f c = ren_chan g c.
Proof. intros H. destruct c; simpl; congruence. Qed.

Lemma ren_chan_comp f g c : ren_chan f (ren_chan g c) = ren_chan (f ∘ g) c.
Proof. by destruct c. Qed.

Lemma ren_chan_id c : ren_chan id c = c.
Proof. by destruct c. Qed.

Lemma ren_chan_inj f : (∀ i j, f i = f j → i = j) → ∀ c c', ren_chan f c = ren_chan f c' → c = c'.
Proof. intros Hf [c|i] [c'|j]; simpl; intros [=]; subst; [done|]. f_equal. by apply Hf. Qed.

Lemma lift_inj f : (∀ i j, f i = f j → i = j) → ∀ i j, lift f i = lift f j → i = j.
Proof. intros Hf [|i] [|j]; simpl; intros [=]; subst; [done|]. f_equal. by apply Hf. Qed.

Lemma prefix_ren_ext f g 𝜆 : (∀ i, f i = g i) → prefix_ren f 𝜆 = prefix_ren g 𝜆.
Proof. intros H. destruct 𝜆; simpl; [done| |done|done|done]. by rewrite (ren_chan_ext f g). Qed.

Lemma ren_ext_all :
  (∀ P f g, (∀ i, f i = g i) → ren f P = ren g P)
  ∧ (∀ h f g, (∀ i, f i = g i) → gren f h = gren g h).
Proof.
  apply proc_guard_ind; simpl; intros; try (f_equal; auto; done).
  - by rewrite (ren_chan_ext f g).
  - f_equal. apply H. by apply lift_ext.
  - f_equal; [by apply prefix_ren_ext | by apply H].
Qed.

Lemma ren_ext f g P : (∀ i, f i = g i) → ren f P = ren g P.
Proof. apply (proj1 ren_ext_all). Qed.

Lemma prefix_ren_comp f g 𝜆 : prefix_ren f (prefix_ren g 𝜆) = prefix_ren (f ∘ g) 𝜆.
Proof. destruct 𝜆; simpl; [done| |done|done|done]. by rewrite ren_chan_comp. Qed.

Lemma ren_comp_all :
  (∀ P f g, ren f (ren g P) = ren (f ∘ g) P) ∧ (∀ h f g, gren f (gren g h) = gren (f ∘ g) h).
Proof.
  apply proc_guard_ind; simpl; intros; try (f_equal; auto; done).
  - by rewrite ren_chan_comp.
  - f_equal. rewrite H. apply ren_ext, lift_comp.
  - f_equal; [apply prefix_ren_comp | apply H].
Qed.

Lemma ren_comp f g P : ren f (ren g P) = ren (f ∘ g) P.
Proof. apply (proj1 ren_comp_all). Qed.

Lemma ren_id_all : (∀ P, ren id P = P) ∧ (∀ h, gren id h = h).
Proof.
  apply proc_guard_ind; simpl; intros; try (f_equal; auto; done).
  - by rewrite ren_chan_id.
  - f_equal. rewrite <- H at 2. apply ren_ext, lift_id.
  - f_equal; [|done]. destruct 𝜆; simpl; [done| |done|done|done]. by rewrite ren_chan_id.
Qed.

Lemma ren_id P : ren id P = P.
Proof. apply (proj1 ren_id_all). Qed.

(* [ren (lift f) (ren S P) = ren S (ren f P)] *)
Lemma ren_lift_S f P : ren (lift f) (ren S P) = ren S (ren f P).
Proof. rewrite !ren_comp. by apply ren_ext. Qed.

Lemma ren_swap01_invol P : ren swap01 (ren swap01 P) = P.
Proof.
  rewrite ren_comp. rewrite <- (ren_id P) at 2. apply ren_ext. intros i. apply swap01_invol.
Qed.

Lemma prefix_ren_subst f k v 𝜆 :
  prefix_ren f (prefix_subst k v 𝜆) = prefix_subst k v (prefix_ren f 𝜆).
Proof. by destruct 𝜆. Qed.

Lemma prefix_ren_shift f k 𝜆 : prefix_ren f (prefix_shift k 𝜆) = prefix_shift k (prefix_ren f 𝜆).
Proof. by destruct 𝜆. Qed.

Lemma prefix_ren_binds f 𝜆 : prefix_binds (prefix_ren f 𝜆) = prefix_binds 𝜆.
Proof. by destruct 𝜆. Qed.

Lemma ren_subst :
  (∀ P f k v, ren f (subst k v P) = subst k v (ren f P))
  ∧ (∀ g f k v, gren f (gsubst k v g) = gsubst k v (gren f g)).
Proof.
  apply proc_guard_ind; simpl; intros; try congruence.
  rewrite prefix_ren_subst, prefix_ren_binds. congruence.
Qed.

Lemma ren_shiftv :
  (∀ P f k, ren f (shiftv k P) = shiftv k (ren f P))
  ∧ (∀ g f k, gren f (gshiftv k g) = gshiftv k (gren f g)).
Proof.
  apply proc_guard_ind; simpl; intros; try congruence.
  rewrite prefix_ren_shift, prefix_ren_binds. congruence.
Qed.

Lemma ren_shiftv_iter n f Q : ren f (Nat.iter n (shiftv 0) Q) = Nat.iter n (shiftv 0) (ren f Q).
Proof. induction n; simpl; [done|]. by rewrite (proj1 ren_shiftv), IHn. Qed.

Lemma ren_pr_subst X :
  (∀ P f Q, ren f (P ⦃ Q // X ⦄) = (ren f P) ⦃ ren f Q // X ⦄)
  ∧ (∀ g f Q, gren f (gpr_subst X g Q) = gpr_subst X (gren f g) (ren f Q)).
Proof.
  apply proc_guard_ind; simpl; intros; try congruence.
  - f_equal. rewrite H. f_equal. apply ren_lift_S.
  - by case_decide.
  - case_decide; simpl; congruence.
  - rewrite H, prefix_ren_binds, ren_shiftv_iter. done.
Qed.

Lemma size_ren : (∀ P f, size (ren f P) = size P) ∧ (∀ g f, gsize (gren f g) = gsize g).
Proof. apply proc_guard_ind; simpl; intros; congruence. Qed.
(* end hide *)
