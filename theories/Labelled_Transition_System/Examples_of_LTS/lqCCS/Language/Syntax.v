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

    Tagged lqCCS, following Ceragioli, Gadducci, Lomurno and Tedeschi,
    /Verification of Quantum Protocols Adopting Physically Admissible
    Schedulers/ (arXiv:2604.23756, April 2026), Definition 2.1 and the tagged
    prefixes of Section 4.1.

    Deliberate differences with the paper.

    - Superoperators and measurements are *names* ([sop], [meas]).  Their
      meaning (Kraus operators, outcomes) is given by the semantics, which is
      parametric in a model of quantum states; the syntax does not depend on
      any matrix library.
    - Variables are bound by substitution of closed values, as in the paper
      ([P[v/x]]): the binders are [c?x] and [M(ẽ ▷ x)].
    - [①] ([GSucc]) is an inert guard saying that the observer is good, as
      in CCS testing ([①] of VACCS); it is used by the testing predicate only.
    - Sums are *guarded*, as in VACCS: a sum is made of guards ([guard]):
      [0_ẽ], [①], prefixes [𝜆.P], and sums of guards.  Outputs, parallel
      composition, restriction and conditionals are processes only, so that
      an output never stands under a sum.

    - Outputs are *asynchronous*: [t : c!e] is a process with no
      continuation ([PSend]), not a prefix, as in the lqCCS of POPL 2024
      (Ceragioli et al., /Quantum Bisimilarity via Barbs and Contexts/).  The
      2026 paper has a prefix [t : c!e.P]; [t : c!e.P] is recovered as
      [t : c!e ∥ P] up to the order of the output.  This is what makes outputs
      non-blocking in the sense of the output-buffered axioms ([Lts_OBA]). *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list numbers.
(* ** Names *)

Definition tag : Type := nat.
Definition qubit : Type := nat.
Definition var : Type := nat.
(* Names of trace-preserving superoperators [E : Op(n)] and of
    measurements [M : Meas(n)]. *)
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
| EVar (x : var)
| EVal (v : val)
| ENot (e : exp)
| EOr (e1 e2 : exp)
| ELe (e1 e2 : exp)
| EEq (e1 e2 : exp).

(* ** Tagged prefixes and processes *)

Inductive prefix : Type :=
(* [t : τ] *)
| PTau (t : tag)
(* [(t, t') : τ], a silent move standing for a synchronisation *)
| PTauPair (t t' : tag)
(* [t : c?x] *)
| PRecv (t : tag) (c : chan) (x : var)
(* [t : E(ẽ)] *)
| POp (t : tag) (E : sop) (es : list exp)
(* [t : M(ẽ ▷ x)] *)
| PMeas (t : tag) (M : meas) (es : list exp) (x : var).

Inductive proc : Type :=
(* [t : c!e], an asynchronous output: no continuation, never under a sum *)
| PSend (t : tag) (c : chan) (e : exp)
| PIte (e : exp) (P Q : proc)
| PPar (P Q : proc)
| PRes (P : proc) (c : chan)
(* a guarded sum *)
| PG (g : guard)
with guard : Type :=
(* [0_ẽ], deadlock discarding the qubits [ẽ] *)
| GNil (es : list exp)
| GSucc
| GPre (𝜆 : prefix) (P : proc)
| GSum (g1 g2 : guard).

Scheme proc_mut_ind := Induction for proc Sort Prop
  with guard_mut_ind := Induction for guard Sort Prop.
Combined Scheme proc_guard_ind from proc_mut_ind, guard_mut_ind.

Declare Scope lqccs_scope.
Delimit Scope lqccs_scope with lq.
Bind Scope lqccs_scope with proc.

Notation "𝟘" := (PG (GNil [])) : lqccs_scope.
Notation "𝜆 ∙ P" := (GPre 𝜆 P) (at level 46, right associativity) : lqccs_scope.
Notation "g ⊕ g'" := (GSum g g') (at level 50, left associativity) : lqccs_scope.
Notation "P ∥ Q" := (PPar P Q) (at level 60, right associativity) : lqccs_scope.
Notation "P \ c" := (PRes P c) (at level 36, left associativity) : lqccs_scope.
Notation "①" := GSucc : lqccs_scope.

#[local] Open Scope lqccs_scope.

(* ** Substitution [P[v/x]] *)

Fixpoint exp_subst (e : exp) (x : var) (v : val) : exp :=
  match e with
  | EVar y => if decide (x = y) then EVal v else EVar y
  | EVal w => EVal w
  | ENot e => ENot (exp_subst e x v)
  | EOr e1 e2 => EOr (exp_subst e1 x v) (exp_subst e2 x v)
  | ELe e1 e2 => ELe (exp_subst e1 x v) (exp_subst e2 x v)
  | EEq e1 e2 => EEq (exp_subst e1 x v) (exp_subst e2 x v)
  end.

Definition exps_subst (es : list exp) (x : var) (v : val) : list exp :=
  map (λ e, exp_subst e x v) es.

(* The variable bound by a prefix, if any. *)
Definition prefix_binder (𝜆 : prefix) : option var :=
  match 𝜆 with
  | PRecv _ _ x | PMeas _ _ _ x => Some x
  | _ => None
  end.

Definition prefix_subst (𝜆 : prefix) (x : var) (v : val) : prefix :=
  match 𝜆 with
  | PTau t => PTau t
  | PTauPair t t' => PTauPair t t'
  | PRecv t c y => PRecv t c y
  | POp t E es => POp t E (exps_subst es x v)
  | PMeas t M es y => PMeas t M (exps_subst es x v) y
  end.

Fixpoint subst (P : proc) (x : var) (v : val) : proc :=
  match P with
  | PSend t c e => PSend t c (exp_subst e x v)
  | PIte e P Q => PIte (exp_subst e x v) (subst P x v) (subst Q x v)
  | P ∥ Q => subst P x v ∥ subst Q x v
  | P \ c => subst P x v \ c
  | PG g => PG (gsubst g x v)
  end
with gsubst (g : guard) (x : var) (v : val) : guard :=
  match g with
  | GNil es => GNil (exps_subst es x v)
  | ① => ①
  | 𝜆 ∙ P =>
      prefix_subst 𝜆 x v ∙ (if decide (prefix_binder 𝜆 = Some x) then P else subst P x v)
  | g1 ⊕ g2 => gsubst g1 x v ⊕ gsubst g2 x v
  end.

Notation "P ⟦ v // x ⟧" := (subst P x v) (at level 20) : lqccs_scope.

(* ** Big-step evaluation [e ⇓ v]

    Only closed expressions evaluate.  Qubits are compared by name, never by
    value: [q = q'] says nothing about the quantum state. *)

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

(* ** Tags of a process ([Tag(P)] in the paper) *)

Definition prefix_tags (𝜆 : prefix) : list tag :=
  match 𝜆 with
  | PTau t | PRecv t _ _ | POp t _ _ | PMeas t _ _ _ => [t]
  | PTauPair t t' => [t; t']
  end.

Fixpoint tags (P : proc) : list tag :=
  match P with
  | PSend t _ _ => [t]
  | PIte _ P Q | P ∥ Q => tags P ++ tags Q
  | P \ _ => tags P
  | PG g => gtags g
  end
with gtags (g : guard) : list tag :=
  match g with
  | GNil _ | ① => []
  | 𝜆 ∙ P => prefix_tags 𝜆 ++ tags P
  | g1 ⊕ g2 => gtags g1 ++ gtags g2
  end.

(* ** Decidability and countability *)

#[global] Instance exp_eq_dec : EqDecision exp.
Proof. solve_decision. Defined.

#[global] Instance prefix_eq_dec : EqDecision prefix.
Proof. solve_decision. Defined.

Definition val_to_sum (v : val) : bool + nat + qubit :=
  match v with
  | VBool b => inl (inl b)
  | VNat n => inl (inr n)
  | VQubit q => inr q
  end.

Definition val_of_sum (s : bool + nat + qubit) : val :=
  match s with
  | inl (inl b) => VBool b
  | inl (inr n) => VNat n
  | inr q => VQubit q
  end.

#[global] Instance val_countable : Countable val.
Proof.
  refine (inj_countable' val_to_sum val_of_sum _). by intros [].
Defined.

(* Leaves of the encoding trees: values, and names (variables, tags,
    channels, superoperators and measurements are all [nat]). *)
Notation leaf := (val + nat)%type.

Fixpoint exp_encode (e : exp) : gen_tree leaf :=
  match e with
  | EVar x => GenLeaf (inr x)
  | EVal v => GenLeaf (inl v)
  | ENot e => GenNode 0 [exp_encode e]
  | EOr e1 e2 => GenNode 1 [exp_encode e1; exp_encode e2]
  | ELe e1 e2 => GenNode 2 [exp_encode e1; exp_encode e2]
  | EEq e1 e2 => GenNode 3 [exp_encode e1; exp_encode e2]
  end.

Fixpoint exp_decode (t : gen_tree leaf) : option exp :=
  match t with
  | GenLeaf (inr x) => Some (EVar x)
  | GenLeaf (inl v) => Some (EVal v)
  | GenNode 0 [t] => ENot <$> exp_decode t
  | GenNode 1 [t1; t2] => e1 ← exp_decode t1; e2 ← exp_decode t2; Some (EOr e1 e2)
  | GenNode 2 [t1; t2] => e1 ← exp_decode t1; e2 ← exp_decode t2; Some (ELe e1 e2)
  | GenNode 3 [t1; t2] => e1 ← exp_decode t1; e2 ← exp_decode t2; Some (EEq e1 e2)
  | GenNode _ _ => None
  end.

Lemma exp_decode_encode e : exp_decode (exp_encode e) = Some e.
Proof. induction e; simpl; try done; by rewrite ?IHe, ?IHe1, ?IHe2. Qed.

#[global] Instance exp_countable : Countable exp.
Proof. refine (inj_countable exp_encode exp_decode exp_decode_encode). Defined.

Definition prefix_to_sum (𝜆 : prefix) :
  tag + (tag * tag) + (tag * chan * var)
  + (tag * sop * list exp) + (tag * meas * list exp * var) :=
  match 𝜆 with
  | PTau t => inl (inl (inl (inl t)))
  | PTauPair t t' => inl (inl (inl (inr (t, t'))))
  | PRecv t c x => inl (inl (inr (t, c, x)))
  | POp t E es => inl (inr (t, E, es))
  | PMeas t M es x => inr (t, M, es, x)
  end.

Definition prefix_of_sum (s :
  tag + (tag * tag) + (tag * chan * var)
  + (tag * sop * list exp) + (tag * meas * list exp * var)) : prefix :=
  match s with
  | inl (inl (inl (inl t))) => PTau t
  | inl (inl (inl (inr (t, t')))) => PTauPair t t'
  | inl (inl (inr (t, c, x))) => PRecv t c x
  | inl (inr (t, E, es)) => POp t E es
  | inr (t, M, es, x) => PMeas t M es x
  end.

#[global] Instance prefix_countable : Countable prefix.
Proof.
  refine (inj_countable' prefix_to_sum prefix_of_sum _). by intros [].
Defined.

Notation pleaf := (list exp + prefix + exp + chan + (tag * chan * exp))%type.

Fixpoint proc_encode (P : proc) : gen_tree pleaf :=
  match P with
  | PSend t c e => GenLeaf (inr (t, c, e))
  | PIte e P Q => GenNode 1 [GenLeaf (inl (inl (inr e))); proc_encode P; proc_encode Q]
  | P ∥ Q => GenNode 3 [proc_encode P; proc_encode Q]
  | P \ c => GenNode 4 [proc_encode P; GenLeaf (inl (inr c))]
  | PG g => GenNode 6 [guard_encode g]
  end
with guard_encode (g : guard) : gen_tree pleaf :=
  match g with
  | GNil es => GenLeaf (inl (inl (inl (inl es))))
  | ① => GenNode 5 []
  | 𝜆 ∙ P => GenNode 0 [GenLeaf (inl (inl (inl (inr 𝜆)))); proc_encode P]
  | g1 ⊕ g2 => GenNode 2 [guard_encode g1; guard_encode g2]
  end.

Fixpoint proc_decode (t : gen_tree pleaf) : option proc :=
  match t with
  | GenLeaf (inr (t, c, e)) => Some (PSend t c e)
  | GenNode 1 [GenLeaf (inl (inl (inr e))); t1; t2] =>
      P ← proc_decode t1; Q ← proc_decode t2; Some (PIte e P Q)
  | GenNode 3 [t1; t2] => P ← proc_decode t1; Q ← proc_decode t2; Some (P ∥ Q)
  | GenNode 4 [t; GenLeaf (inl (inr c))] => (λ P, P \ c) <$> proc_decode t
  | GenNode 6 [t] => PG <$> guard_decode t
  | _ => None
  end
with guard_decode (t : gen_tree pleaf) : option guard :=
  match t with
  | GenLeaf (inl (inl (inl (inl es)))) => Some (GNil es)
  | GenNode 5 [] => Some ①
  | GenNode 0 [GenLeaf (inl (inl (inl (inr 𝜆)))); t] => GPre 𝜆 <$> proc_decode t
  | GenNode 2 [t1; t2] => g1 ← guard_decode t1; g2 ← guard_decode t2; Some (g1 ⊕ g2)
  | _ => None
  end.

Lemma proc_guard_decode_encode :
  (∀ P, proc_decode (proc_encode P) = Some P)
  ∧ (∀ g, guard_decode (guard_encode g) = Some g).
Proof.
  apply proc_guard_ind; intros; simpl; try done;
    repeat match goal with H : _ = Some _ |- _ => rewrite H end; done.
Qed.

Lemma proc_decode_encode P : proc_decode (proc_encode P) = Some P.
Proof. apply proc_guard_decode_encode. Qed.

Lemma guard_decode_encode g : guard_decode (guard_encode g) = Some g.
Proof. apply proc_guard_decode_encode. Qed.

#[global] Instance proc_eq_dec : EqDecision proc.
Proof.
  intros P Q. destruct (decide (proc_encode P = proc_encode Q)) as [E|E].
  - left. apply (f_equal proc_decode) in E. rewrite !proc_decode_encode in E. by simplify_eq.
  - right. by intros ->.
Defined.

#[global] Instance guard_eq_dec : EqDecision guard.
Proof.
  intros g h. destruct (decide (guard_encode g = guard_encode h)) as [E|E].
  - left. apply (f_equal guard_decode) in E. rewrite !guard_decode_encode in E. by simplify_eq.
  - right. by intros ->.
Defined.

#[global] Instance proc_countable : Countable proc.
Proof. refine (inj_countable proc_encode proc_decode proc_decode_encode). Defined.

#[global] Instance guard_countable : Countable guard.
Proof. refine (inj_countable guard_encode guard_decode guard_decode_encode). Defined.
(* end hide *)
