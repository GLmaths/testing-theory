(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
   Copyright (c) 2024 Gaëtan Lopez <gaetanlopez.maths@gmail.com>

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


Require Import Coq.Program.Equality Coq.Strings.String.
From stdpp Require Import base countable finite gmap list gmultiset strings.
Require Import Relations.
Require Import Coq.Wellfounded.Inverse_Image.

From stdpp Require Import base countable finite gmap list gmultiset strings.
From Must Require Import TransitionSystems Must Completeness.

(* ChannelType est le type des canaux, par exemple des chaînes de caractères*)
(* ValueType est le type des données transmises, par exemple des entiers, des chaînes de caractères, des programmes (?) *)

Coercion ActExt : ExtAct >-> Act.

Parameter (Channel Value : Type).
(*Exemple : Definition Channel := string.*)
(*Exemple : Definition Value := nat.*)

Inductive Data :=
| cst : Value -> Data
| bvar : nat -> Data. (* variable as De Bruijn indices *) 

Coercion cst : Value >-> Data.
Coercion bvar : nat >-> Data.

Inductive TypeOfActions := 
| act : Channel -> Data -> TypeOfActions.

Notation "c ⋉ v" := (act c v) (at level 50).


Inductive Equation (A : Type) : Type :=
| tt : Equation A
| ff : Equation A
| Inequality : A -> A -> Equation A
| Or : Equation A -> Equation A -> Equation A
| Not : Equation A -> Equation A.
(* I have a Type Of Equation and I know how to evaluate it *)

Arguments  tt  {_}.
Arguments  ff  {_} .
Arguments  Inequality  {_} _ _.
Arguments  Or  {_} _ _.
Arguments  Not  {_}  _.

Notation "'non' e" := (Not e) (at level 50).
Notation "x ∨ y" := (Or x y).
Notation "x ⩽ y" := (Inequality x y) (at level 50).

Parameter (Eval_Eq : Equation Data -> (option bool)).
Parameter (channel_eq_dec : EqDecision Channel). (* only here for the classes *)
#[global] Instance channel_eqdecision : EqDecision Channel. by exact channel_eq_dec. Defined.
Parameter (channel_is_countable : Countable Channel). (* only here for the classes *)
#[global] Instance channel_countable : Countable Channel. by exact channel_is_countable. Defined.
Parameter (value_eq_dec : EqDecision Value). (* only here for the classes *)
#[global] Instance value_eqdecision : EqDecision Value. by exact value_eq_dec. Defined.
Parameter (value_is_countable : Countable Value). (* only here for the classes *)
#[global] Instance value_countable : Countable Value. by exact value_is_countable. Defined.

(* Definition of processes*)
Inductive proc : Type :=
(* To parallele two processes*)
| pr_par : proc -> proc -> proc
(* Variable in a process, for recursion and substitution*)
| pr_var : nat -> proc
(* recursion for process*)
| pr_rec : nat -> proc -> proc
(* If test *NEW term in comparison of CCS* *)
| pr_if_then_else : Equation Data -> proc -> proc -> proc
(* The Process that does nothing without blocking state*)
| pr_nil : proc
(*The Guards*)
| g : gproc -> proc

with gproc : Type :=
(* Deadlock, no more computation *)
| gpr_deadlock : gproc
(* The Success operation*)
| gpr_success : gproc
(*An input is a name of a channel, an input variable, followed by a process*)
| gpr_input : Channel ->  proc -> gproc
(*An output is a name of a channel, an ouput value, followed by a process*)
| gpr_output : Channel -> Data -> proc -> gproc
(*A tau action : does nothing *)
| gpr_tau : proc -> gproc
(* To choose between two processes*)
| gpr_choice : gproc -> gproc -> gproc
(*Sequentiality for process*)
| gpr_seq : proc -> proc -> gproc
.


Coercion pr_var : nat >-> proc.
Coercion g : gproc >-> proc.

(*Some notation to simplify the view of the code*)
Notation "'δ'" := (gpr_deadlock).
Notation "①" := (gpr_success).
Notation "𝟘" := (pr_nil).
Notation "'rec' x '•' p" := (pr_rec x p) (at level 50).
Notation "P + Q" := (gpr_choice P Q).
Notation "P ‖ Q" := (pr_par P Q) (at level 50).
Notation "c ! v • P" := (gpr_output c v P) (at level 50).
Notation "c ? P" := (gpr_input c P) (at level 50).
Notation "'t' • P" := (gpr_tau P) (at level 50).
Notation "'If' C 'Then' P 'Else' Q" := (pr_if_then_else C P Q)
(at level 200, right associativity, format
"'[v   ' 'If'  C '/' '[' 'Then'  P  ']' '/' '[' 'Else'  Q ']' ']'").
Notation "P ; Q" := (gpr_seq P Q) (at level 50).


(*Notation with the De Brujin's indices for the variables*)
(* NewVar makes unrecognizable variable from the current environement*)
Definition NewVar_in_Data (k : nat) (Y : Data) : Data := 
match Y with
| cst v => cst v
| bvar i => if (decide(k < S i)) then bvar (S i) else bvar i
end.

Fixpoint NewVar_in_Equation (k : nat) (E : Equation Data) : Equation Data :=
match E with
| tt => tt
| ff => ff
| D1 ⩽ D2 => (NewVar_in_Data k D1) ⩽ (NewVar_in_Data k D2)
| e1 ∨ e2 => (NewVar_in_Equation k e1) ∨ (NewVar_in_Equation k e2)
| non e => non (NewVar_in_Equation k e)
end.

Fixpoint NewVar (k : nat) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (NewVar k P) ‖ (NewVar k Q)
| pr_var i => pr_var i
| rec x • P =>  rec x • (NewVar k P)
| If C Then P Else Q => If (NewVar_in_Equation k C) Then (NewVar k P) Else (NewVar k Q)
| 𝟘 => 𝟘
| g M => gNewVar k M
end

with gNewVar k M {struct M} : gproc :=
match M with
| δ => δ
| ① => ①
| c ? p => c ? (NewVar (S k) p)
| c ! v • p => c ! (NewVar_in_Data k v) • (NewVar k p)
| t • p => t • (NewVar k p)
| p1 + p2 => (gNewVar k p1) + (gNewVar k p2)
| P ; Q => (NewVar k P) ; (NewVar k Q)
end.



Definition Lift_in_Data (k : nat) (Y : Data) : Data := 
match Y with
| cst v => cst v
| bvar (S i) => if (decide(k < (S (S i)))) then bvar i else bvar (S i)
| bvar 0 => bvar 0
end.


(*Fixpoint Lift_in_Equation (k : nat) (E : Equation Data) : Equation Data :=
match E with
| tt => tt
| ff => ff
| D1 ⩽ D2 => (Lift_in_Data k D1) ⩽ (Lift_in_Data k D2)
| e1 ∨ e2 => (Lift_in_Equation k e1) ∨ (Lift_in_Equation k e2)
| non e => non (Lift_in_Equation k e)
end.

Fixpoint Lift (k : nat) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (Lift k P) ‖ (Lift k Q)
| pr_var i => pr_var i
| rec x • P =>  rec x • (Lift k P)
| If C Then P Else Q => If (Lift_in_Equation k C) Then (Lift k P) Else (Lift k Q)
| g M => gLift k M
end

with gLift k M {struct M} : gproc :=
match M with
| δ => δ
| ① => ①
| 𝟘 => 𝟘
| c ? p => c ? (Lift (S k) p)
| c ! v • p => c ! (Lift_in_Data k v) • (Lift k p)
| t • p => t • (Lift k p)
| p1 + p2 => (gLift k p1) + (gLift k p2)
| P ; Q => (Lift k P) ; (Lift k Q)
end.*)


(*Definition of the Substitution *)
Definition subst_Data (k : nat) (X : Data) (Y : Data) : Data := 
match Y with
| cst v => cst v
| bvar i => if (decide(i = k)) then X else if (decide(i < k)) then bvar i
                                                              else bvar (Nat.pred i)
end.

Definition Succ_bvar (X : Data) : Data :=
match X with
| cst v => cst v
| bvar i => bvar (S i)
end.

Fixpoint subst_in_Equation (k : nat) (X : Data) (E : Equation Data) : Equation Data :=
match E with
| tt => tt
| ff => ff
| D1 ⩽ D2 => (subst_Data k X D1) ⩽ (subst_Data k X D2)
| e1 ∨ e2 => (subst_in_Equation k X e1) ∨ (subst_in_Equation k X e2)
| non e => non (subst_in_Equation k X e)
end.

(* Important *)
Fixpoint subst_in_proc (k : nat) (X : Data) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (subst_in_proc k X P) ‖ (subst_in_proc k X Q)
| pr_var i => pr_var i
| rec x • P =>  rec x • (subst_in_proc k X P)
| If C Then P Else Q => If (subst_in_Equation k X C) Then (subst_in_proc k X P) Else (subst_in_proc k X Q)
| 𝟘 => 𝟘
| g M => subst_in_gproc k X M
end

with subst_in_gproc k X M {struct M} : gproc :=
match M with
| δ => δ
| ① => ①
| c ? p => c ? (subst_in_proc (S k) (NewVar_in_Data 0 X) p)
| c ! v • p => c ! (subst_Data k X v) • (subst_in_proc k X p)
| t • p => t • (subst_in_proc k X p)
| p1 + p2 => (subst_in_gproc k X p1) + (subst_in_gproc k X p2)
| P ; Q => (subst_in_proc k X P) ; (subst_in_proc k X Q)
end.

Notation "t1 ^ x1" := (subst_in_proc 0 x1 t1).

Fixpoint size (p : proc) := 
  match p with
  | p ‖ q  => S (size p + size q)
  | pr_var _ => 1
  | If C Then p Else q => S (size p + size q)
  | rec x • p => S (size p)
  | 𝟘 => 0
  | g p => gsize p
  end

with gsize p :=
  match p with
  | δ => 1
  | ① => 1
  | c ? p => S (size p)
  | c ! v • p => S (size p)
  | t • p => S (size p)
  | p + q => S (gsize p + gsize q)
  | p ; q => S (size p + size q)
end.


Lemma Succ_bvar_and_NewVar_in_Data_0 : forall v, NewVar_in_Data 0 v = Succ_bvar v.
Proof.
intros. induction v; simpl; reflexivity.
Qed.

Lemma All_According_To_Data : forall k v d, (subst_Data k v (NewVar_in_Data k d) = d).
Proof.
intros. destruct d. 
- simpl. auto.
- simpl. destruct (decide (k < S n)). (* case decide. *)
  * simpl. destruct (decide (S n = k)) as [e | e].
    ** exfalso. dependent destruction l. eapply Nat.neq_succ_diag_l. exact e. 
       rewrite <-e in l. lia.
    ** destruct (decide (S n < k)). 
       *** lia. (* pas top *)
       *** auto.
  * simpl. destruct (decide (n = k)).
    ** lia. (* pas top *)
    ** destruct n. 
      -- assert ( 0 < k). lia. destruct (decide (0 < k)). 
         *** auto. 
         *** exfalso. auto with arith.
      -- destruct (decide (S n < k)).
        *** auto.
        *** exfalso. lia. 
Qed.

Lemma All_According_To_Eq : forall e k v, (subst_in_Equation k v (NewVar_in_Equation k e) = e).
Proof.
intros E. dependent induction E; intros.
- simpl. reflexivity.
- simpl. reflexivity. 
- simpl. assert ((subst_Data k v (NewVar_in_Data k a)) = a).
  apply All_According_To_Data.
  assert (subst_Data k v (NewVar_in_Data k a0) = a0).
  apply All_According_To_Data.
  rewrite H, H0. auto.
- simpl. assert (subst_in_Equation k v (NewVar_in_Equation k E1) = E1). apply IHE1.
  assert (subst_in_Equation k v (NewVar_in_Equation k E2) = E2). apply IHE2.
  rewrite H, H0. auto.
- simpl. assert (subst_in_Equation k v (NewVar_in_Equation k E) = E). apply IHE.
  rewrite H. auto.
Qed.

(*Making a variable independent from the environment, makes the substitution non-effective *)
(* Important *)
Lemma All_According : forall p k v, subst_in_proc k v (NewVar k p) = p.
Proof.
intros. revert v. revert k.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros. 
* simpl. assert (subst_in_proc k v (NewVar k p1) = p1). apply Hp. simpl. auto with arith.
  assert (subst_in_proc k v (NewVar k p2) = p2). apply Hp. simpl. auto with arith.
  rewrite H, H0. auto.
* simpl. auto.
* simpl. assert (subst_in_proc k v (NewVar k p) = p). apply Hp. simpl. auto with arith.
  rewrite H. auto.
* simpl. assert (subst_in_Equation k v (NewVar_in_Equation k e) = e). apply All_According_To_Eq.
  assert (subst_in_proc k v (NewVar k p1) = p1). apply Hp. simpl. auto with arith.
  assert (subst_in_proc k v (NewVar k p2) = p2). apply Hp. simpl. auto with arith.
  rewrite H, H0, H1. auto.
* simpl. auto.
* destruct g0.
  - simpl. auto.
  - simpl. auto.
  - simpl. assert (subst_in_proc (S k) (NewVar_in_Data 0 v) (NewVar (S k) p) = p).
    apply Hp. simpl. auto with arith.
    rewrite H. auto.
  - simpl. assert (subst_Data k v (NewVar_in_Data k d) = d). apply All_According_To_Data.
    assert (subst_in_proc k v (NewVar k p) = p). apply Hp. simpl. auto with arith.
    rewrite H, H0. auto.
  - simpl. assert (subst_in_proc k v (NewVar k p) = p). apply Hp. simpl. auto with arith.
    rewrite H. auto.
  - simpl. assert (subst_in_proc k v (NewVar k (g g0_1)) = g g0_1). apply Hp. simpl. auto with arith.
    assert (subst_in_proc k v (NewVar k (g g0_2)) = g g0_2). apply Hp. simpl. auto with arith.
    dependent destruction H. dependent destruction H0. rewrite x0, x. auto.
  - simpl. assert (subst_in_proc k v (NewVar k p) = p). apply Hp. simpl. auto with arith.
    assert (subst_in_proc k v (NewVar k p0) = p0). apply Hp. simpl. auto with arith.
    rewrite H, H0. auto.
Qed.

(* Substitution for the Recursive Variable *)
Fixpoint pr_subst (id : nat) (p : proc) (q : proc) : proc :=
  match p with 
  | p1 ‖ p2 => (pr_subst id p1 q) ‖ (pr_subst id p2 q) 
  | pr_var id' => if decide (id = id') then q else p
  | rec id' • p => if decide (id = id') then p else rec id' • (pr_subst id p q)
  | If C Then P Else Q => If C Then (pr_subst id P q) Else (pr_subst id Q q)
  | 𝟘 => 𝟘
  | g gp => g (gpr_subst id gp q)
end

with gpr_subst id p q {struct p} := match p with
| δ => δ
| ① => ①
| c ? p => c ? (pr_subst id p (NewVar 0 q))
| c ! v • p => c ! v • (pr_subst id p q)
| t • p => t • (pr_subst id p q)
| p1 + p2 => (gpr_subst id p1 q) + (gpr_subst id p2 q)
| p1 ; p2 => (pr_subst id p1 q) ; (pr_subst id p2 q)
end.


Inductive SKIP_SEQ : proc -> Prop :=
| ZeroSkip : SKIP_SEQ (𝟘)
| ChoiceLSkip_Par : forall P Q, SKIP_SEQ (P) -> SKIP_SEQ (Q) -> SKIP_SEQ (P ‖ Q).


Lemma Data_dec : forall (x y : Data) , {x = y} + {x <> y}.
Proof.
decide equality. 
* destruct (decide(v = v0)). left. assumption. right. assumption.
* destruct (decide (n = n0)). left. assumption. right. assumption.
Qed.

#[global] Instance data_eqdecision : EqDecision Data. by exact Data_dec . Defined.

Definition encode_data (D : Data) : gen_tree (nat + Value) :=
match D with
  | cst v => GenLeaf (inr v)
  | bvar i => GenLeaf (inl i)
end.

Definition decode_data (tree : gen_tree (nat + Value)) : Data :=
match tree with
  | GenLeaf (inr v) => cst v
  | GenLeaf (inl i) => bvar i
  | _ => bvar 0
end.

Lemma encode_decide_datas d : decode_data (encode_data d) = d.
Proof. case d. 
* intros. simpl. reflexivity.
* intros. simpl. reflexivity.
Qed.

#[global] Instance data_countable : Countable Data.
Proof.
  refine (inj_countable' encode_data decode_data _).
  apply encode_decide_datas.
Qed.


Lemma TypeOfActions_dec : forall (x y : TypeOfActions) , {x = y} + {x <> y}.
Proof.
decide equality. 
* destruct (decide(d = d0)). left. assumption. right. assumption.
* destruct (decide (c = c0)). left. assumption. right. assumption.
Qed.

#[global] Instance TypeOfActions_eqdecision : EqDecision TypeOfActions. by exact TypeOfActions_dec . Defined.


Definition encode_TypeOfActions (a : TypeOfActions) : gen_tree (nat + (Channel + Data)) :=
match a with
  | act c v => GenNode 0 (GenLeaf (inr (inl c)):: [GenLeaf (inr (inr v))])
end.


Definition decode_TypeOfActions (tree :gen_tree (nat + (Channel + Data))) : option TypeOfActions :=
match tree with
  | GenNode 0 ((GenLeaf (inr (inl c))) :: [GenLeaf (inr (inr v))]) => Some (act c v)
  | _ => None
end.

Lemma encode_decide_TypeOfActions p : decode_TypeOfActions (encode_TypeOfActions  p) = Some p.
Proof. 
induction p. 
* simpl. reflexivity.
Qed.

#[global] Instance TypeOfActions_countable : Countable TypeOfActions.
Proof.
  eapply inj_countable with encode_TypeOfActions decode_TypeOfActions. 
  intro. apply encode_decide_TypeOfActions.
Qed.

Reserved Notation "p ≡ q" (at level 70).

(*Naïve definition of a relation ≡ that will become a congruence ≡* by transitivity*)
(* Important *)
Inductive cgr_step : proc -> proc -> Prop :=
(*  Reflexivity of the Relation ≡  *)
| cgr_refl_step : forall p, p ≡ p

(* Rules for the Parallèle *)
(* | cgr_par_nil_step : forall p, 
    p ‖ 𝟘 ≡ p
| cgr_par_nil_rev_step : forall p,
    p ≡ p ‖ 𝟘 *)
| cgr_par_com_step : forall p q,
    p ‖ q ≡ q ‖ p
| cgr_par_assoc_step : forall p q r,
    (p ‖ q) ‖ r ≡ p ‖ (q ‖ r)
| cgr_par_assoc_rev_step : forall p q r,
    p ‖ (q  ‖ r) ≡ (p ‖ q) ‖ r

(* Rules for the Summation *)
| cgr_choice_nil_step : forall p,
    cgr_step (p + δ) p
| cgr_choice_nil_rev_step : forall p,
    cgr_step (g p) (p + δ)
| cgr_choice_com_step : forall p q,
    cgr_step (p + q) (q + p)
| cgr_choice_assoc_step : forall p q r,
    cgr_step ((p + q) + r) (p + (q + r))
| cgr_choice_assoc_rev_step : forall p q r,
    cgr_step (p + (q + r)) ((p + q) + r)

(*The reduction is given to certain terms...*)
| cgr_recursion_step : forall x p q,
    cgr_step p q -> (rec x • p) ≡ (rec x • q)
| cgr_tau_step : forall p q,
    cgr_step p q ->
    cgr_step (t • p) (t • q)
| cgr_input_step : forall c p q,
    cgr_step p q ->
    cgr_step (c ? p) (c ? q)
| cgr_output_step : forall c v p q, 
    cgr_step p q -> 
    cgr_step (c ! v • p) (c ! v • q)
| cgr_par_step : forall p q r,
    cgr_step p q ->
    p ‖ r ≡ q ‖ r
| cgr_if_left_step : forall C p q q',
    cgr_step q q' ->
    (If C Then p Else q) ≡ (If C Then p Else q')
| cgr_if_right_step : forall C p p' q,
    cgr_step p p' ->
    (If C Then p Else q) ≡ (If C Then p' Else q)

(*...and sums (only for guards (by sanity))*)
| cgr_choice_step : forall p1 q1 p2,
    cgr_step (g p1) (g q1) -> 
    cgr_step (p1 + p2) (q1 + p2)
| cgr_seq_left_step : forall p q r,
    cgr_step p q ->
    (g (p ; r)) ≡ (g (q ; r ))
| cgr_seq_right_step : forall p q r,
    cgr_step p q ->
    (g (r ; p)) ≡ (g (r ; q))
    
(* Rules for sequentiation *)
(*| cgr_seq_nil_step : forall P, cgr_step (δ ; P) δ
| cgr_seq_nil_rev_step : forall P, cgr_step δ (δ ; P)*)
| cgr_seq_assoc_step : forall p q r,
    cgr_step ((p ; q) ; r) (p ; (q ; r))
| cgr_seq_assoc_rev_step : forall p q r,
    cgr_step (p ; (q ; r)) ((p ; q) ; r)

(* Rules for sequentiation-analysis *)
| cgr_seq_choice_step : forall G G' P, cgr_step ((G + G') ; P) ((G ; P) + (G'; P))
| cgr_seq_choice_rev_step : forall G G' P, cgr_step (((g G) ; P) + ((g G'); P)) ((G + G') ; P)
| cgr_seq_tau_step : forall P Q, cgr_step ((t • P) ; Q) (t • (P ; Q))
| cgr_seq_tau_rev_step : forall P Q, cgr_step (t • (P ; Q)) ((t • P) ; Q)
| cgr_seq_input_step : forall c P Q , cgr_step ((c ? P) ; Q) (c ? (P ; NewVar 0 Q))
| cgr_seq_input_rev_step : forall c P Q , cgr_step (c ? (P ; NewVar 0 Q)) ((c ? P) ; Q) 
| cgr_seq_output_step : forall c v P Q, cgr_step ((c ! v • P) ; Q) (c ! v • (P ; Q))
| cgr_seq_output_rev_step : forall c v P Q, cgr_step (c ! v • (P ; Q)) ((c ! v • P) ; Q)
.


#[global] Hint Constructors cgr_step:cgr_step_structure.

Infix "≡" := cgr_step (at level 70).


(* The relation ≡ is an reflexive*)
#[global] Instance cgr_refl_step_is_refl : Reflexive cgr_step.
Proof. intro. apply cgr_refl_step. Qed.
(* The relation ≡ is symmetric*)
#[global] Instance cgr_symm_step : Symmetric cgr_step.
Proof. intros p q hcgr. 
induction hcgr; try econstructor ; try eauto.
Qed.

(* Defining the transitive closure of ≡ *)
Infix "≡" := cgr_step (at level 70).
(* Defining the transitive closure of ≡ *)
Definition cgr := (clos_trans proc cgr_step).

Infix "≡*" := cgr (at level 70).


(* The relation ≡* is reflexive*)
#[global] Instance cgr_refl : Reflexive cgr.
Proof. intros. constructor. apply cgr_refl_step. Qed.
(* The relation ≡* is symmetric*)
#[global] Instance cgr_symm : Symmetric cgr.
Proof. intros p q hcgr. induction hcgr. constructor. apply cgr_symm_step. exact H. eapply t_trans; eauto. Qed.
(* The relation ≡* is transitive*)
#[global] Instance cgr_trans : Transitive cgr.
Proof. intros p q r hcgr1 hcgr2. eapply t_trans; eauto. Qed.

#[global] Hint Resolve cgr_refl cgr_symm cgr_trans:cgr_eq.

(* The relation ≡* is an equivence relation*)
(* Important *)
#[global] Instance cgr_is_eq_rel  : Equivalence cgr.
Proof. repeat split.
       + apply cgr_refl.
       + apply cgr_symm.
       + apply cgr_trans.
Qed.

(*the relation ≡* respects all the rules that ≡ respected*)
(*Lemma cgr_par_nil : forall p, p ‖ 𝟘 ≡* p.
Proof.
constructor.
apply cgr_par_nil_step.
Qed.
Lemma cgr_par_nil_rev : forall p, (g p) ≡* p ‖ 𝟘.
Proof.
constructor.
apply cgr_par_nil_rev_step.
Qed. *)
Lemma cgr_par_com : forall p q, p ‖ q ≡* q ‖ p.
Proof.
constructor.
apply cgr_par_com_step.
Qed.
Lemma cgr_par_assoc : forall p q r, (p ‖ q) ‖ r ≡* p ‖ (q ‖r).
Proof.
constructor.
apply cgr_par_assoc_step.
Qed.
Lemma cgr_par_assoc_rev : forall p q r, p ‖(q ‖ r) ≡* (p ‖ q) ‖ r.
Proof.
constructor.
apply cgr_par_assoc_rev_step.
Qed.
Lemma cgr_choice_nil : forall p, p + δ ≡* p.
Proof.
constructor.
apply cgr_choice_nil_step.
Qed.
Lemma cgr_choice_nil_rev : forall p, (g p) ≡* p + δ.
Proof.
constructor.
apply cgr_choice_nil_rev_step.
Qed.
Lemma cgr_choice_com : forall p q, p + q ≡* q + p.
Proof.
constructor.
apply cgr_choice_com_step.
Qed.
Lemma cgr_choice_assoc : forall p q r, (p + q) + r ≡* p + (q + r).
Proof.
constructor.
apply cgr_choice_assoc_step.
Qed.
Lemma cgr_choice_assoc_rev : forall p q r, p + (q + r) ≡* (p + q) + r.
Proof.
constructor.
apply cgr_choice_assoc_rev_step.
Qed.
Lemma cgr_recursion : forall x p q, p ≡* q -> (rec x • p) ≡* (rec x • q).
Proof.
intros. dependent induction H. 
constructor. 
apply cgr_recursion_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_tau : forall p q, p ≡* q -> (t • p) ≡* (t • q).
Proof.
intros. dependent induction H. 
constructor. 
apply cgr_tau_step. exact H. eauto with cgr_eq.
Qed. 
Lemma cgr_input : forall c p q, p ≡* q -> (c ? p) ≡* (c ? q).
Proof.
intros.
dependent induction H. 
* constructor. apply cgr_input_step. auto.
* eauto with cgr_eq.
Qed.
Lemma cgr_output : forall c v p q, p ≡* q -> (c ! v • p) ≡* (c ! v • q).
Proof.
intros.
dependent induction H. 
* constructor. apply cgr_output_step. auto.
* eauto with cgr_eq.
Qed.
Lemma cgr_par : forall p q r, p ≡* q-> p ‖ r ≡* q ‖ r.
Proof.
intros. dependent induction H. 
constructor.
apply cgr_par_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_if_left : forall C p q q', q ≡* q' -> (If C Then p Else q) ≡* (If C Then p Else q').
Proof.
intros. dependent induction H. 
constructor.
apply cgr_if_left_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_if_right : forall C p p' q, p ≡* p' -> (If C Then p Else q) ≡* (If C Then p' Else q).
Proof.
intros. dependent induction H. 
constructor.
apply cgr_if_right_step. exact H. eauto with cgr_eq.
Qed.
Lemma Guards_cong_with_Guards : forall p q, (g p) ≡* q -> exists q', q = g q'.
Proof.
intros. dependent induction H.
* inversion H; eauto.
* destruct (IHclos_trans1 p). auto. eapply IHclos_trans2 with x. assumption.
Qed.
Lemma cgr_choice : forall p q r, g p ≡* g q -> p + r ≡* q + r.
Proof.
intros. dependent induction H.
* constructor. constructor. assumption.
* assert (clos_trans proc cgr_step p y). assumption. apply Guards_cong_with_Guards in H1. destruct H1. subst.
  apply transitivity with (g (x + r)). eapply IHclos_trans1; auto. eapply IHclos_trans2; auto.
Qed.
Lemma cgr_seq_left : forall p q r, p ≡* q -> (g (p ; r)) ≡* (g (q ; r )).
Proof. intros. dependent induction H. constructor. apply cgr_seq_left_step. assumption. eauto with cgr_eq.
Qed.
Lemma cgr_seq_right : forall p q r, p ≡* q -> (g (r ; p)) ≡* (g (r ; q)).
Proof. intros. dependent induction H. constructor. apply cgr_seq_right_step. assumption. eauto with cgr_eq.
Qed.
Lemma cgr_seq_assoc : forall p q r, ((p ; q) ; r) ≡* (p ; (q ; r)).
Proof. intros. constructor. apply cgr_seq_assoc_step.
Qed.
Lemma cgr_seq_assoc_rev : forall p q r, (p ; (q ; r)) ≡* ((p ; q) ; r).
Proof. intros. constructor. apply cgr_seq_assoc_rev_step.
Qed.
(*Lemma cgr_seq_nil : forall P, (δ ; P) ≡* δ.
Proof. intros. constructor. apply cgr_seq_nil_step.
Qed.
Lemma cgr_seq_nil_rev : forall P, δ ≡* (δ ; P).
Proof. intros. constructor. apply cgr_seq_nil_rev_step.
Qed.*)
Lemma cgr_seq_choice : forall G G' P, ((G + G') ; P) ≡* ((G ; P) + (G'; P)).
Proof. intros. constructor. apply cgr_seq_choice_step.
Qed.
Lemma cgr_seq_choice_rev : forall G G' P, (((g G) ; P) + ((g G'); P)) ≡* ((G + G') ; P).
Proof. intros. constructor. apply cgr_seq_choice_rev_step.
Qed.
Lemma cgr_seq_tau : forall P Q, ((t • P) ; Q) ≡* (t • (P ; Q)).
Proof. intros. constructor. apply cgr_seq_tau_step.
Qed.
Lemma cgr_seq_tau_rev : forall P Q, (t • (P ; Q)) ≡* ((t • P) ; Q).
Proof. intros. constructor. apply cgr_seq_tau_rev_step.
Qed.
Lemma cgr_seq_input: forall c P Q , ((c ? P) ; Q) ≡* (c ? (P ; NewVar 0 Q)).
Proof. intros. constructor. apply cgr_seq_input_step.
Qed.
Lemma cgr_seq_input_rev : forall c P Q , (c ? (P ; NewVar 0 Q)) ≡* ((c ? P) ; Q).
Proof. intros. constructor. apply cgr_seq_input_rev_step.
Qed.
Lemma cgr_seq_output : forall c v P Q, ((c ! v • P) ; Q) ≡* (c ! v • (P ; Q)).
Proof. intros. constructor. apply cgr_seq_output_step.
Qed.
Lemma cgr_seq_output_rev : forall c v P Q, (c ! v • (P ; Q)) ≡* ((c ! v • P) ; Q).
Proof. intros. constructor. apply cgr_seq_output_rev_step.
Qed.

(* The 'if' process respects ≡* *)
Lemma cgr_full_if : forall C p p' q q', p ≡* p' -> q ≡* q' -> (If C Then p Else q) ≡* (If C Then p' Else q').
Proof.
intros.
apply transitivity with (If C Then p Else q'). apply cgr_if_left. exact H0. 
apply cgr_if_right. exact H. 
Qed.
(* The sum of guards respects ≡* *)
Lemma cgr_fullchoice : forall M1 M2 M3 M4, g M1 ≡* g M2 -> g M3 ≡* g M4 -> M1 + M3 ≡* M2 + M4.
Proof.
intros.
apply transitivity with (g (M2 + M3)). apply cgr_choice. exact H. apply transitivity with (g (M3 + M2)).
apply cgr_choice_com. apply transitivity with (g (M4 + M2)). apply cgr_choice. exact H0. apply cgr_choice_com.
Qed.
(* The parallele of process respects ≡* *)
Lemma cgr_fullpar : forall M1 M2 M3 M4, M1 ≡* M2 -> M3 ≡* M4 -> M1 ‖ M3 ≡* M2 ‖ M4.
Proof.
intros.
apply transitivity with (M2 ‖ M3). apply cgr_par. exact H. apply transitivity with (M3 ‖ M2).
apply cgr_par_com. apply transitivity with (M4 ‖ M2). apply cgr_par. exact H0. apply cgr_par_com.
Qed.
(* The sequentiation of process respects ≡* *)
Lemma cgr_fullseq : forall M1 M2 M3 M4, M1 ≡* M2 -> M3 ≡* M4 -> M1 ; M3 ≡* M2 ; M4.
Proof.
intros.
apply transitivity with (g (M2 ; M3)). apply cgr_seq_left. assumption. 
apply cgr_seq_right. assumption.
Qed.


#[global] Hint Resolve (* cgr_par_nil cgr_par_nil_rev*) cgr_par_com cgr_par_assoc cgr_par_assoc_rev 
cgr_choice_nil cgr_choice_nil_rev cgr_choice_com cgr_choice_assoc cgr_choice_assoc_rev 
cgr_recursion cgr_tau cgr_input cgr_output cgr_if_left cgr_if_right cgr_par cgr_choice 
cgr_seq_left cgr_seq_right cgr_seq_assoc cgr_seq_assoc_rev (* cgr_seq_nil cgr_seq_nil_rev *)
cgr_seq_choice cgr_seq_choice_rev cgr_seq_tau cgr_seq_tau_rev cgr_seq_input cgr_seq_input_rev 
cgr_seq_output cgr_seq_output_rev cgr_full_if cgr_fullchoice cgr_fullpar cgr_fullseq
cgr_refl cgr_symm cgr_trans:cgr.


Inductive States : Type :=
| pair : gmultiset TypeOfActions -> proc -> States.

Notation "'❲' M ',' P '❳'" := (pair M P).

Definition MailBox_of (S : States) : gmultiset TypeOfActions :=
match S with 
| ❲M ,P❳ => M
end.

Definition Process_of (S : States) : proc :=
match S with 
| ❲M ,P❳ => P
end.

(* The Labelled Transition System (LTS-transition) *)
(* Important *)
Inductive lts : proc -> (Act TypeOfActions) -> proc -> Prop :=
(*The Input and the Output*)
| lts_input : forall {c v P},
    lts (c ? P) (ActIn (c ⋉ v)) (P^v)
| lts_output : forall {c v P},
    lts (c ! v • P) (ActOut (c ⋉ v)) P

(*The actions Tau*)
| lts_tau : forall {P},
    lts (t • P) τ P
| lts_recursion : forall {x P},
    lts (rec x • P) τ (pr_subst x P (rec x • P))
| lts_ifOne : forall {p q E}, Eval_Eq E = Some true -> 
    lts (If E Then p Else q) τ p
| lts_ifZero : forall {p q E}, Eval_Eq E = Some false -> 
    lts (If E Then p Else q) τ q

(* Skip *)
| lts_skip : forall {P0 P}, SKIP_SEQ ( P0 )(* P0 ≡* 𝟘 *)-> lts (P0 ; P) τ P

(*The decoration for the transition system...*)
(*...for the parallele*)   
| lts_parL : forall {α p1 p2 q},
    lts p1 α p2 ->
    lts (p1 ‖ q) α (p2 ‖ q)
| lts_parR : forall {α q1 q2 p},
    lts q1 α q2 ->
    lts (p ‖ q1) α (p ‖ q2)
(*...for the sum*)
| lts_choiceL : forall {p1 p2 q α},
    lts (g p1) α q -> 
    lts (p1 + p2) α q
| lts_choiceR : forall {p1 p2 q α},
    lts (g p2) α q -> 
    lts (p1 + p2) α q
(*...for the sequentiation*)
| lts_seqL : forall {α p1 p2 q},
    lts p1 α p2 ->
    lts (p1 ; q) α (p2 ; q).

(* The Labelled Transition System (LTS-transition for states) *)
(* Important *)
Inductive ltsM : States -> (Act TypeOfActions) -> States -> Prop :=
(*The Input and the Output*)
| ltsM_input : forall {M p q c v}, lts p (ActIn (c ⋉ v)) q ->
    ltsM (❲M , p❳) (ActIn (c ⋉ v)) (❲M , q❳)
| ltsM_output : forall {M c v P},
    ltsM (❲M ⊎ {[+ c ⋉ v +]} , P❳) (ActOut (c ⋉ v)) (❲M , P❳)

| ltsM_tau : forall {M p q}, lts p τ q ->
    ltsM (❲M , p❳) τ (❲M , q❳)
| ltsM_send : forall {M c v p q}, lts p (ActOut (c ⋉ v)) q ->
    ltsM (❲M , p❳) τ (❲M ⊎ {[+ c ⋉ v +]}, q❳)

(* Communication of a channel output and input that have the same name*)
| ltsM_com : forall {M1 M2 M2' c v S1 S2 S2'},
    ltsM (❲M1, S1❳) (ActOut (c ⋉ v)) (❲ M2, S2' ❳) ->
    ltsM (❲ M1, S1❳) (ActIn (c ⋉ v)) (❲ M2', S2 ❳)->
    ltsM (❲M1 , S1❳) τ (❲M2 , S2❳).


#[global] Hint Constructors lts:ccs.



Lemma Subst_And_NewVar_in_Data : forall j k v d, (NewVar_in_Data j (subst_Data (j + k) v d))
                                        = subst_Data (j + S k) (NewVar_in_Data j v) (NewVar_in_Data j d).
Proof.
intros. revert k. revert v. revert j. dependent induction d.
* intros. simpl. reflexivity.
* intros. simpl. destruct (decide(n = (j+k)%nat)). 
  - destruct (decide (j < S n)).
     -- simpl. destruct (decide ((S n = (j + S k)%nat))). 
        --- auto.
        --- exfalso. lia. (* pas top *)
     -- simpl. destruct (decide (n = (j + S k)%nat)).
        --- auto.
        --- exfalso. lia. (* pas top *) 
  -  destruct (decide (n < j + k)).
     -- simpl. destruct (decide (j < S n)). 
        --- simpl. destruct (decide (S n = (j + S k)%nat)). 
            ** exfalso. lia. (* pas top *)
            ** destruct (decide (S n < j + S k)).
               *** auto.
               *** exfalso. lia. (* pas top *) 
        --- simpl. destruct (decide(n = (j + S k)%nat)). 
            ** lia.
            ** destruct (decide (n < j + S k)).
              ---- auto.
              ---- lia. (* pas top *) 
     -- simpl. destruct (decide (j < S (Nat.pred n))).
        --- destruct (decide (j < S n)).
            ** simpl. destruct (decide (S n = (j + S k)%nat)).
              *** lia. (* pas top *) 
              *** destruct (decide (S n < j + S k)). 
                **** lia. (* pas top *) 
                **** assert (n ≠ 0). lia. destruct n. lia. simpl. auto. (* pas top *) 
            ** simpl. destruct (decide (n = (j + S k)%nat)).
              *** lia.
              *** destruct (decide (n < j + S k)).
                **** lia.
                **** lia.
       --- destruct (decide (j < S n)).
          ** simpl. destruct (decide(S n = (j + S k)%nat)).
              *** lia.
              *** lia.
         ** lia.
Qed.


Lemma Subst_And_NewVar_in_Equation : forall j k v e, NewVar_in_Equation j (subst_in_Equation (j + k) v e) =
                                        subst_in_Equation (j + S k) (NewVar_in_Data j v) (NewVar_in_Equation j e).
Proof.
intros. induction e.
* simpl. auto.
* simpl. auto.
* simpl. 
  assert (NewVar_in_Data j (subst_Data (j + k) v a) = subst_Data (j + S k) (NewVar_in_Data j v) (NewVar_in_Data j a)). 
  eapply Subst_And_NewVar_in_Data. 
  assert (NewVar_in_Data j (subst_Data (j + k) v a0) = subst_Data (j + S k) (NewVar_in_Data j v) (NewVar_in_Data j a0)).
  eapply Subst_And_NewVar_in_Data. rewrite H. rewrite H0. auto.
* simpl. rewrite IHe1. rewrite IHe2. auto.
* simpl. rewrite IHe. auto.
Qed.

Lemma NewVarDataZero_and_NewVarData : forall j v, NewVar_in_Data 0 (NewVar_in_Data j v) = NewVar_in_Data (S j) (NewVar_in_Data 0 v).
Proof.
intros. revert j. induction v.
- intros. simpl. reflexivity.
- intros. simpl. destruct (decide (j < S n)); destruct (decide (S j < S (S n))); simpl; auto.
  exfalso. apply n0. auto with arith. exfalso. apply n0. auto with arith.
Qed.

Lemma Subst_And_NewVar : forall j k v P, NewVar j (subst_in_proc (j + k) v P) =
                                         subst_in_proc (j + S k) (NewVar_in_Data j v) (NewVar j P).
Proof.
intros. revert k. revert v. revert j. 
induction P as (P & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct P; simpl; intros.
* assert (NewVar j (subst_in_proc (j + k) v P1) = subst_in_proc (j + S k) (NewVar_in_Data j v) (NewVar j P1)). 
  apply Hp. simpl. auto with arith.
  assert (NewVar j (subst_in_proc (j + k) v P2) = subst_in_proc (j + (S k)) (NewVar_in_Data j v) (NewVar j P2)). 
  apply Hp. simpl. auto with arith.
  rewrite H. rewrite H0. auto.
* reflexivity.
* assert (NewVar j (subst_in_proc (j + k) v P) = subst_in_proc (j + (S k)) (NewVar_in_Data j v) (NewVar j P)). 
  apply Hp. simpl. auto with arith. rewrite H. auto.
* assert (NewVar j (subst_in_proc (j + k) v P1) = subst_in_proc (j + (S k)) (NewVar_in_Data j v) (NewVar j P1)). 
  apply Hp. simpl. auto with arith.
  assert (NewVar j (subst_in_proc (j + k) v P2) = subst_in_proc (j + (S k)) (NewVar_in_Data j v) (NewVar j P2)). 
  apply Hp. simpl. auto with arith.
  rewrite H. rewrite H0. auto. 
  assert (NewVar_in_Equation j (subst_in_Equation (j + k) v e) = subst_in_Equation (j + S k) (NewVar_in_Data j v) (NewVar_in_Equation j e)).
  apply Subst_And_NewVar_in_Equation. rewrite H1. auto.
* auto.
* destruct g0; simpl; auto.
  - assert ((NewVar (S j) (subst_in_proc (S (j + k)) (NewVar_in_Data 0 v) p)) = (subst_in_proc (S (j + S k)) (NewVar_in_Data (S j) (NewVar_in_Data 0 v)) (NewVar (S j) p))).
    assert (size p < size (gpr_input c p)). simpl. auto with arith. eapply (Hp p H (S j) (NewVar_in_Data 0 v) k).
    assert ((NewVar_in_Data 0 (NewVar_in_Data j v)) = NewVar_in_Data (S j) (NewVar_in_Data 0 v)). apply NewVarDataZero_and_NewVarData. 
    rewrite H0. rewrite H. auto.
  - assert (NewVar j (subst_in_proc (j + k) v p) = subst_in_proc (j + (S k)) (NewVar_in_Data j v) (NewVar j p)). 
    apply Hp. simpl. auto with arith.
    assert (NewVar_in_Data j (subst_Data (j + k) v d) =  subst_Data (j + S k) (NewVar_in_Data j v) (NewVar_in_Data j d)). 
    eapply Subst_And_NewVar_in_Data. 
    rewrite H. rewrite H0. auto.
  - assert (NewVar j (subst_in_proc (j + k) v p) = subst_in_proc (j + S k) (NewVar_in_Data j v) (NewVar j p)). eapply Hp. 
    simpl. auto with arith. rewrite H. auto.
  - assert (NewVar j (subst_in_proc (j + k) v (g g0_1)) = subst_in_proc (j + S k) (NewVar_in_Data j v) (NewVar j (g g0_1))). 
    apply Hp. simpl. auto with arith.
    assert (NewVar j (subst_in_proc (j + k) v (g g0_2)) = subst_in_proc (j + (S k)) (NewVar_in_Data j v) (NewVar j (g g0_2))). 
    apply Hp. simpl. auto with arith. simpl in H0. simpl in H. inversion H. inversion H0.
    rewrite H2. rewrite H3. auto.
  - assert (NewVar j (subst_in_proc (j + k) v p) = subst_in_proc (j + S k) (NewVar_in_Data j v) (NewVar j p)). 
    apply Hp. simpl. auto with arith.
    assert (NewVar j (subst_in_proc (j + k) v p0) = subst_in_proc (j + (S k)) (NewVar_in_Data j v) (NewVar j p0)). 
    apply Hp. simpl. auto with arith.
    rewrite H. rewrite H0. auto.
Qed.

(* Important *)
Lemma Congruence_Respects_Substitution : forall p q v k, p ≡* q -> (subst_in_proc k v p) ≡* (subst_in_proc k v q).
Proof.
intros. revert k. revert v. dependent induction H. 
* dependent induction H; simpl; eauto with cgr. intros.
assert (NewVar 0 (subst_in_proc k v Q) = subst_in_proc (S k) (NewVar_in_Data 0 v) (NewVar 0 Q)). eapply (Subst_And_NewVar 0). rewrite <-H. 
eauto with cgr. 
intros. 
assert (NewVar 0 (subst_in_proc k v Q) = subst_in_proc (S k) (NewVar_in_Data 0 v) (NewVar 0 Q)). eapply (Subst_And_NewVar 0). rewrite <-H. 
eauto with cgr. 
* eauto with cgr.
Qed.

Lemma New_Var_And_NewVar_in_Data : forall j i e, NewVar_in_Data (i + S j) (NewVar_in_Data i e) = NewVar_in_Data i (NewVar_in_Data (i + j) e).
Proof.
intros. revert j. induction e.
* intros. simpl. reflexivity.
* intros. simpl. destruct (decide (i < S n)); destruct (decide (i + j < S n)); simpl; auto.
  - destruct (decide (i + S j < S (S n))); destruct ((decide (i < S (S n)))); simpl; auto with arith. exfalso. apply n0. auto with arith.
    exfalso. apply n0. simpl. assert ((i + S j)%nat = S (i + j)%nat). auto with arith. rewrite H. auto with arith.
  - destruct (decide (i + S j < S (S n))); destruct (decide (i < S n)); simpl; auto with arith. exfalso. apply n0. 
    assert ((i + S j)%nat = S (i + j)%nat). auto with arith. rewrite H in l0. auto with arith. exfalso. apply n1. assumption. exfalso. apply n2.
    assumption.
  - exfalso. apply n0. assert (i <= i + j). auto with arith. destruct H. assumption. apply transitivity with (S m). auto with arith. assumption.
  - destruct (decide (i + S j < S n)); destruct (decide (i < S n)); simpl; auto with arith. exfalso. apply n2. eauto with arith.
    exfalso. apply n0. assumption.
Qed.

Lemma New_Var_And_NewVar_in_eq : forall j i e, NewVar_in_Equation (i + S j) (NewVar_in_Equation i e) 
                                  = NewVar_in_Equation i (NewVar_in_Equation (i + j) e).
Proof.
intros. induction e.
* simpl. auto.
* simpl. auto.
* simpl. assert (NewVar_in_Data (i + S j) (NewVar_in_Data i a) = NewVar_in_Data i (NewVar_in_Data (i + j) a)). apply New_Var_And_NewVar_in_Data.
  assert (NewVar_in_Data (i + S j) (NewVar_in_Data i a0) = NewVar_in_Data i (NewVar_in_Data (i + j) a0)). apply New_Var_And_NewVar_in_Data.
  rewrite H , H0. auto.
* simpl. rewrite IHe1 , IHe2 . auto.
* simpl. rewrite IHe. auto.
Qed.

Lemma New_Var_And_NewVar : forall j i p, NewVar (i + S j) (NewVar i p) = NewVar i (NewVar (i + j) p).
Proof.
intros. revert j i. induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; simpl; intros.
* assert (NewVar (i + S j) (NewVar i p1) = NewVar i (NewVar (i + j) p1)). apply Hp. simpl. auto with arith.
  assert (NewVar (i + S j) (NewVar i p2) = NewVar i (NewVar (i + j) p2)). apply Hp. simpl. auto with arith.
  rewrite H, H0. auto.
* reflexivity.
* assert (NewVar (i + S j) (NewVar i p) = NewVar i (NewVar (i + j) p)). apply Hp. simpl. auto with arith.
  rewrite H. auto.
* assert (NewVar_in_Equation (i + S j) (NewVar_in_Equation i e) = NewVar_in_Equation i (NewVar_in_Equation (i + j) e)). 
  apply New_Var_And_NewVar_in_eq.
  assert (NewVar (i + S j) (NewVar i p1) = NewVar i (NewVar (i + j) p1)). apply Hp. simpl. auto with arith.
  assert (NewVar (i + S j) (NewVar i p2) = NewVar i (NewVar (i + j) p2)). apply Hp. simpl. auto with arith.
  rewrite H, H0, H1. auto.
* reflexivity.
* destruct g0.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. assert (NewVar (S (i + S j)) (NewVar (S i) p) = NewVar (S i) (NewVar (S (i + j)) p)).
    assert (S (i + S j%nat) = ((S i) + (S j))%nat). auto with arith. rewrite H. assert (S (i + j) = (S i + j)%nat).
    auto with arith. rewrite H0. 
    apply Hp. simpl. auto with arith. rewrite H. auto.
  - simpl. assert (NewVar_in_Data (i + S j) (NewVar_in_Data i d) = NewVar_in_Data i (NewVar_in_Data (i + j) d)).
    apply New_Var_And_NewVar_in_Data. rewrite H. auto.
    assert (NewVar (i + S j) (NewVar i p) = NewVar i (NewVar (i + j) p)). apply Hp. simpl. auto with arith.
    rewrite H0. auto.
  - simpl. assert (NewVar (i + S j) (NewVar i p) = NewVar i (NewVar (i + j) p)).
    apply Hp. simpl. auto with arith. rewrite H. auto.
  - simpl. assert (NewVar (i + S j) (NewVar i (g g0_1)) = NewVar i (NewVar (i + j) (g g0_1))).
    apply Hp. simpl. auto with arith. 
    assert (NewVar (i + S j) (NewVar i (g g0_2)) = NewVar i (NewVar (i + j) (g g0_2))).
    apply Hp. simpl. auto with arith. simpl in H , H0. inversion H. inversion H0.
    rewrite H2 , H3. auto.
  - simpl. assert (NewVar (i + S j) (NewVar i p) = NewVar i (NewVar (i + j) p)). apply Hp. simpl. auto with arith. rewrite H.
    assert (NewVar (i + S j) (NewVar i p0) = NewVar i (NewVar (i + j) p0)). apply Hp. simpl. auto with arith. rewrite H0. auto.
Qed. 


(* Important *)
Lemma NewVar_Respects_Congruence : forall p p' j, p ≡* p' -> NewVar j p ≡* NewVar j p'.
Proof.
intros.  revert j.  dependent induction H. dependent induction H ; simpl ; auto with cgr.
* intros. apply cgr_choice. apply IHcgr_step. 
* intros. assert (NewVar (S j) (NewVar 0 Q) = NewVar 0 (NewVar j Q)). eapply (New_Var_And_NewVar j 0).
  rewrite H. auto with cgr.
* intros. assert (NewVar (S j) (NewVar 0 Q) = NewVar 0 (NewVar j Q)). eapply (New_Var_And_NewVar j 0).
  rewrite H. auto with cgr.
* eauto with cgr.
Qed.


(* Substition lemma, needed to contextualise the equivalence *)
(* Important *)
Lemma cgr_subst1 p q q' x : q ≡* q' → pr_subst x p q ≡* pr_subst x p q'.
Proof.
revert q q' x.
(* Induction on the size of p*)
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p.
  - simpl. intros. apply cgr_fullpar.
    apply Hp. simpl. auto with arith. assumption. 
    apply Hp. simpl. auto with arith. assumption. 
  - simpl. intros. destruct (decide (x = n)). assumption. reflexivity.
  - simpl. intros. destruct (decide (x = n)). reflexivity. apply cgr_recursion. apply Hp. simpl. auto. assumption.
  - simpl. intros. apply cgr_full_if.
    apply Hp. simpl. auto with arith. assumption. 
    apply Hp. simpl. auto with arith. assumption.  
  - intros. simpl. reflexivity.
  - destruct g0.
    * intros. simpl. reflexivity.
    * intros. simpl. reflexivity.
    * intros. simpl. apply cgr_input. apply Hp. simpl. auto. apply NewVar_Respects_Congruence. assumption.
    * simpl. intros. assert (pr_subst x p (NewVar 0 q) ≡* pr_subst x p (NewVar 0 q')).
      apply Hp. simpl. auto with arith. apply NewVar_Respects_Congruence. assumption.
      eauto with cgr.
    * intros. simpl. apply cgr_tau. apply Hp. simpl. auto. auto.
    * intros. simpl. apply cgr_fullchoice. 
      assert (pr_subst x (g g0_1) q ≡* pr_subst x (g g0_1) q'). apply Hp. simpl. auto with arith. assumption.
      auto. assert (pr_subst x (g g0_2) q ≡* pr_subst x (g g0_2) q'). apply Hp. simpl. auto with arith. assumption.
      auto.
    * intros. simpl. apply cgr_fullseq.
      apply Hp. simpl. auto with arith. assumption. 
      apply Hp. simpl. auto with arith. assumption. 
Qed.

Lemma PrSubst_NewVar : forall j n P p, pr_subst n (NewVar j P) (NewVar j p) = NewVar j (pr_subst n P p).
Proof.
intros. revert j n p. induction P as (P & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct P; intros.
* simpl. assert (pr_subst n (NewVar j P1) (NewVar j p) =  NewVar j (pr_subst n P1 p)). apply Hp. simpl. auto with arith.
  assert (pr_subst n (NewVar j P2) (NewVar j p) =  (NewVar j (pr_subst n P2 p))). apply Hp. simpl. auto with arith.
  rewrite H. rewrite H0. auto.
* simpl. destruct (decide (n0 = n)); simpl; auto.
* simpl. destruct (decide (n0 = n)); simpl ; auto. 
  assert (pr_subst n0 (NewVar j P) (NewVar j p) = NewVar j (pr_subst n0 P p)). apply Hp. simpl. auto with arith.
  rewrite H.  auto.
* simpl. assert (pr_subst n (NewVar j P1) (NewVar j p) = NewVar j (pr_subst n P1 p) ). apply Hp. simpl. auto with arith.
  assert (pr_subst n (NewVar j P2) (NewVar j p) = NewVar j (pr_subst n P2 p) ). apply Hp. simpl. auto with arith.
  rewrite H. rewrite H0. auto.
* simpl; auto.
* destruct g0; simpl; auto.
  - assert (NewVar (S j) (NewVar 0 p)= NewVar 0 (NewVar j p)). eapply (New_Var_And_NewVar j 0).
    rewrite <-H.
    assert (pr_subst n (NewVar (S j) p0) (NewVar (S j) (NewVar 0 p)) = NewVar (S j) (pr_subst n p0 (NewVar 0 p))).
    eapply (Hp p0). simpl. auto with arith. rewrite H0. auto.
  - assert (pr_subst n (NewVar j p0) (NewVar j p) = NewVar j (pr_subst n p0 p)).
    apply Hp. simpl. auto with arith. rewrite H. auto.
  - assert (pr_subst n (NewVar j p0) (NewVar j p) = NewVar j (pr_subst n p0 p)). apply Hp.
    simpl. auto with cgr. rewrite H. auto.
  - assert (pr_subst n (NewVar j (g g0_1)) (NewVar j p) = NewVar j (pr_subst n (g g0_1) p)).
    apply Hp. simpl. auto with arith.
    assert (pr_subst n (NewVar j (g g0_2)) (NewVar j p) = NewVar j (pr_subst n (g g0_2) p)).
    apply Hp. simpl. auto with arith.
    inversion H. inversion H0. auto.
  - assert (pr_subst n (NewVar j p0) (NewVar j p) = NewVar j (pr_subst n p0 p)). apply Hp. simpl. auto with arith.
    assert (pr_subst n (NewVar j p1) (NewVar j p) = NewVar j (pr_subst n p1 p)). apply Hp. simpl. auto with arith.
    rewrite H , H0. auto.
Qed.


(* ≡ respects the substitution of his variable*)
Lemma cgr_step_subst2 : forall p p' q x, p ≡ p' → pr_subst x p q ≡ pr_subst x p' q.
Proof.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros p' q n hcgr ; inversion hcgr; try auto; try (exact H); try (now constructor).
  - simpl. destruct (decide (n = x)). auto. constructor. apply Hp. subst. simpl. auto.  exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto with arith. assumption.
  - simpl. constructor. apply Hp. subst. simpl. auto with arith. assumption. 
  - simpl. constructor. apply Hp. subst. simpl. auto with arith. assumption. 
  - simpl. constructor. apply Hp. subst. simpl. auto with arith. assumption. 
  - simpl. constructor. apply Hp. subst. simpl. auto with arith. assumption.
  - simpl. constructor. apply Hp. subst. simpl. auto with arith. assumption.
  - simpl. apply cgr_choice_step. 
    assert (pr_subst n (g p1) q ≡ pr_subst n (g q1) q). apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. 
    apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H. exact H2.
  - simpl. constructor. apply Hp. subst. simpl. auto with arith. assumption.
  - simpl. constructor. apply Hp. subst. simpl. auto with arith. assumption.
  - simpl. subst. assert (pr_subst n (NewVar 0 Q) (NewVar 0 q) = NewVar 0 (pr_subst n Q q)).
    apply PrSubst_NewVar. rewrite H. constructor.
  - simpl. subst. assert (pr_subst n (NewVar 0 Q) (NewVar 0 q) = NewVar 0 (pr_subst n Q q)).
    apply PrSubst_NewVar. rewrite H. constructor.
Qed.

(* ≡* respects the substitution of his variable *)
(* Important *)
Lemma cgr_subst2 q p p' x : p ≡* p' → pr_subst x p q ≡* pr_subst x p' q.
Proof. 
intros hcgr. induction hcgr. constructor. now eapply cgr_step_subst2. apply transitivity with (pr_subst x y q).
exact IHhcgr1. exact IHhcgr2.
Qed.

(* ≡ respects the substitution / recursion *)
Lemma cgr_subst p q x : p ≡ q -> pr_subst x p (rec x • p) ≡* pr_subst x q (rec x • q).
Proof.
  intro heq.
  etrans.
  eapply cgr_subst2. constructor. eassumption.
  eapply cgr_subst1. constructor. apply cgr_recursion_step. exact heq.
Qed.

#[global] Hint Resolve cgr_is_eq_rel: ccs.
#[global] Hint Constructors clos_trans:ccs.
#[global] Hint Unfold cgr:ccs.


Inductive cgr_states : States -> States -> Prop :=
| cgr_prop : forall p p' M, p ≡* p' -> cgr_states (❲M , p ❳) (❲M , p' ❳).

Infix "≋" := cgr_states (at level 70).

Lemma cgr_states_simplified : forall S S', S ≋ S' -> Process_of S ≡* Process_of S'.
Proof.
intros. destruct H. simpl. assumption.
Qed.

(* State Transition System (STS-reduction) *)
(* Important *)
Inductive sts : States -> States -> Prop :=
(*The axiomes*)
(* Communication of channels output and input that have the same name *)
| sts_com : forall {c v M p g}, 
    sts (❲M ⊎ {[+ c ⋉ v +]}, ((c ? p) + g)❳) (❲M , (p ^ v)❳)
(* Send Output to Memory *)
| sts_send: forall {c v M p g}, 
    sts (❲M, ((c ! v • p) + g)❳) (❲M ⊎ {[+ c ⋉ v +]}, p❳)
(* Nothing more , something less *)
| sts_tau : forall {M p g}, 
    sts (❲M , (t • p) + g❳) (❲M , p❳)
(* Resursion *)
| sts_recursion : forall {M x p}, 
    sts (❲M , rec x • p❳) (❲M , pr_subst x p (rec x • p)❳)
(*If Yes*)
| sts_ifOne : forall {M p q E}, Eval_Eq E = Some true -> 
    sts (❲M , If E Then p Else q❳) (❲M , p❳)
(*If No*)
| sts_ifZero : forall {M p q E}, Eval_Eq E = Some false -> 
    sts (❲M , If E Then p Else q❳) (❲M , q❳)

(* The left parallele respect the Reduction *)
| sts_par : forall {M1 P1 M2 P2 P}, 
    sts ❲M1 , P1❳ ❲M2 ,P2❳ ->
    sts ❲M1 , P1 ‖ P❳ ❲M2 , P2 ‖ P❳

(* The left sequentiation respect the Reduction *)
| sts_seq : forall {M1 P1 M2 P2 P G}, 
    sts ❲M1 , P1❳ ❲M2 ,P2❳ ->
    sts ❲M1 , (P1 ; P) + G❳ ❲M2 , P2 ; P❳

(* Skip *)
| sts_skipSeq : forall {G M1 P Q}, SKIP_SEQ (P) -> sts ❲M1 , (P ; Q) + G❳ ❲M1 , Q❳

(*The Congruence respects the Reduction *)
| sts_cong : forall {S1 S2 S1' S2'},
    S1 ≋ S1' -> sts S1' S2' -> S2' ≋ S2 -> sts S1 S2
.

#[global] Hint Constructors sts:ccs.

Lemma MemoryOfInput : forall S S' c v , ltsM S (ActIn (c ⋉ v)) S' -> MailBox_of S = MailBox_of S'.
Proof.
intros. dependent induction H.
- simpl. reflexivity.
Qed.

Lemma MemoryOfInputDestruct : forall M1 M2 P1 P2 c v , ltsM ❲M1, P1❳ (ActIn (c ⋉ v)) ❲M2, P2❳ 
                                                        -> M1 = M2.
Proof.
intros. 
assert (M1 = MailBox_of ❲ M1, P1 ❳). simpl. reflexivity.
assert (M2 = MailBox_of ❲ M2, P2 ❳). simpl. reflexivity.
rewrite H0. rewrite H1.
eapply MemoryOfInput. exact H.
Qed.

(* p 'is equivalent some r 'and r performs α to q *)
Definition sc_then_lts p α q := exists r, p ≡* r /\ (lts r α q).

(* p performs α to some r and this is equivalent to q*)
Definition lts_then_sc p α q := exists r, ((lts p α r) /\ r ≡* q).

Lemma SKIP_SEQ_Respects_Congruence : forall p q, SKIP_SEQ p -> p ≡ q -> SKIP_SEQ q.
Proof.
intros. dependent induction H0; eauto; try inversion H.
- dependent destruction H; constructor ; assumption.
- dependent destruction H. dependent destruction H. constructor. assumption. constructor ; assumption.
- dependent destruction H. dependent destruction H0. constructor. constructor ; assumption. assumption.
- inversion H. subst. apply IHcgr_step in H3. constructor; assumption.
Qed.

(* p 'is equivalent some r 'and r performs α to q , the congruence and the Transition can be reversed : *)
(* Important *)
Lemma Congruence_Respects_Transition  : forall p q α, sc_then_lts p α q -> lts_then_sc p α q.
Proof. 
(* by induction on the congruence and the step then...*)
  intros p q α (p' & hcgr & l).
  revert q α l.
  dependent induction hcgr.
  - dependent induction H. 
(* reasonning about all possible cases due to the structure of terms *)
    + intros. exists q.  split.  exact l. eauto with cgr.
    + intros. dependent destruction l.
      -- exists (p ‖ p2). split. eapply lts_parR. assumption. eauto with cgr. 
      -- exists (q2 ‖ q). split. apply lts_parL. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- exists ((p2 ‖ q) ‖ r). split.
         * constructor. constructor. assumption.
         * eauto with cgr.
      -- dependent destruction l.
         * exists ((p ‖ p2) ‖ r). split.
           ** constructor. constructor. assumption.
           ** eauto with cgr.
         * exists ((p ‖ q) ‖ q2). split.
           ** constructor. assumption.
           ** eauto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l. 
         * exists (p2 ‖ (q ‖ r)). split.
           ** constructor. assumption.
           ** eauto with cgr.
         * exists (p ‖ (q2 ‖ r)). split.
           ** constructor. constructor. assumption.
           ** eauto with cgr.
      -- exists (p ‖ (q ‖ q2)). split.
        ** constructor. constructor. assumption.
        ** eauto with cgr.
    + intros. exists q. split. constructor. assumption. eauto with cgr.
    + intros. dependent destruction l.
      -- exists q. split. assumption. eauto with cgr.
      -- inversion l.
    + intros. exists q0. split.
      -- dependent destruction l.
         * apply lts_choiceR. assumption.
         * apply lts_choiceL. assumption.
      -- eauto with cgr.
    + intros. dependent destruction l.
      -- exists q0. split.
        ** apply lts_choiceL. apply lts_choiceL. assumption.
        ** eauto with cgr.
      -- exists q0. dependent destruction l.
        ** split. apply lts_choiceL. apply lts_choiceR. assumption. eauto with cgr.
        ** split. apply lts_choiceR. assumption. eauto with cgr.
    + intros. exists q0. dependent destruction l. dependent destruction l.
      -- split. apply lts_choiceL. assumption. eauto with cgr.
      -- split. apply lts_choiceR. apply lts_choiceL. assumption. eauto with cgr.
      -- split. apply lts_choiceR. apply lts_choiceR. assumption. eauto with cgr.
    + intros. dependent destruction l. exists (pr_subst x p (rec x • p)). split. apply lts_recursion. 
      apply cgr_subst. assumption.
    + intros. dependent destruction l. exists p.  split. apply lts_tau.
      constructor. assumption.
    + intros. dependent destruction l. exists (p^v). split. apply lts_input.
      apply Congruence_Respects_Substitution. constructor. apply H.
    + intros. inversion l. subst. exists p. split. constructor. constructor. assumption. 
    + intros. dependent destruction l. 
      -- destruct (IHcgr_step p2 α). assumption. destruct H0. exists (x ‖ r).
         split. constructor. assumption. eauto with cgr.
      -- exists (p ‖ q2). split. constructor. assumption. constructor. apply cgr_par_step. assumption.
    + intros. dependent destruction l.
      -- eexists. split. instantiate (1:= p). apply lts_ifOne. assumption. reflexivity. 
      -- eexists. split. instantiate (1:= q). apply lts_ifZero. assumption.
         constructor. assumption.
    + intros. dependent destruction l.
      -- eexists. split. instantiate (1:= p). apply lts_ifOne. assumption.
         constructor. assumption.
      -- eexists. split. instantiate (1:= q). apply lts_ifZero. assumption. 
         constructor. reflexivity.
    + intros. dependent destruction l.
      -- destruct (IHcgr_step q α). assumption. destruct H0. exists x.
         split. constructor. assumption. assumption.
      -- exists q. split. apply lts_choiceR. assumption. eauto with cgr.
    + intros. dependent destruction l.
      -- eapply (SKIP_SEQ_Respects_Congruence q p) in H0. exists r. split. constructor. assumption. eauto with cgr. symmetry.
         assumption.
      -- destruct (IHcgr_step p2 α). assumption. destruct H0. exists (x; r). split.
         ** constructor. assumption.
         ** eauto with cgr.
    + intros. dependent destruction l.
      -- exists p. split. 
         ** constructor. assumption.
         ** constructor. assumption.
      -- exists (p2; p). split. 
         ** constructor. assumption.
         ** apply cgr_fullseq. reflexivity. constructor. assumption.
    + intros. dependent destruction l. 
      -- exists (q; r). split. constructor. constructor. assumption. eauto with cgr.
      -- exists ((p2; q); r). split.
         ** constructor. constructor. assumption.
         ** eauto with cgr.
    + intros. dependent destruction l.
      -- inversion H. 
      -- dependent destruction l. 
         ** exists (q; r). split. constructor. assumption. eauto with cgr.
         ** exists (p2; (q; r)). split. constructor. assumption. eauto with cgr.
    + intros. dependent destruction l;dependent destruction l.
      -- inversion H.
      -- exists (p2; P). split. constructor. constructor. assumption. eauto with cgr.
      -- inversion H.
      -- exists (p2; P). split. constructor. apply lts_choiceR. assumption. eauto with cgr.
    + intros. dependent destruction l.
      -- inversion H.
      -- dependent destruction l.
        ** exists (q; P). constructor. constructor. constructor. assumption. eauto with cgr.
        ** exists (q; P). constructor. apply lts_choiceR. constructor. assumption. eauto with cgr.
    + intros. exists q. dependent destruction l.
      -- split. constructor. constructor. eauto with cgr.
    + intros. exists q. dependent destruction l.
      -- split.  inversion H. auto with cgr.
      -- dependent destruction l. split. constructor. eauto with cgr.
    + intros. dependent destruction l. simpl. exists (P ^ v; Q). split. constructor. constructor. 
      assert (NewVar 0 Q ^ v = Q). eapply All_According.
      rewrite H. eauto with cgr.
    + intros. dependent destruction l.
      * inversion H.
      * dependent destruction l. exists (P ^ v; NewVar 0 Q ^ v ). split. constructor. 
      assert (NewVar 0 Q ^ v = Q). eapply All_According.
      rewrite H. eauto with cgr.
    + intros. inversion l. subst. exists (P; Q). split. constructor. constructor. eauto with cgr.
    + intros. exists q. dependent destruction l. inversion H.
      -- inversion l. subst. split.
        ** constructor. 
        ** eauto with cgr.
  - intros. destruct (IHhcgr2 q α). assumption. destruct (IHhcgr1 x0 α). destruct H. assumption. exists x1. split. destruct H0. assumption.
    destruct H. destruct H0. eauto with cgr.
Qed.

(* p 'is equivalent some r 'and r performs α to q *)
Definition sc_then_ltsM S α S' := exists R, S ≋ R /\ (ltsM R α S').

(* p performs α to some r and this is equivalent to q*)
Definition ltsM_then_sc S α S' := exists R, ((ltsM S α R) /\ R ≋ S').

Lemma cgr_states_simplified_memory : forall M1 M2 p q, ❲ M1, p ❳ ≋ ❲ M2 , q ❳ ->  M1 = M2.
Proof.
intros. inversion H. subst. reflexivity.
Qed.

(* p 'is equivalent some r 'and r performs α to q , the congruence and the Transition can be reversed : *)
Lemma CongruenceStates_Respects_Transition : forall S S' α, sc_then_ltsM S α S' -> ltsM_then_sc S α S'.
Proof.
intros S S' α (R & hcgr & l).
destruct S. destruct R. destruct S'.
assert (g0 = g1). inversion hcgr. subst. reflexivity. subst.
  induction l.
* assert (p ≡* p2). apply cgr_states_simplified in hcgr. simpl in *. assumption.
  assert (lts_then_sc p (ActIn (c ⋉ v)) q). apply Congruence_Respects_Transition. exists p2. split. 
  assumption. assumption. destruct H1. destruct H1.
  exists ❲g1, x ❳. split. constructor. assumption. apply cgr_states_simplified_memory in hcgr. rewrite hcgr.
  constructor. assumption.
* exists (❲ M, p ❳). split. apply cgr_states_simplified_memory in hcgr. rewrite hcgr. constructor.
  constructor. apply cgr_states_simplified in hcgr. simpl in *. assumption.
* assert (p ≡* p2). apply cgr_states_simplified in hcgr. simpl in *. assumption.
  assert (lts_then_sc p τ q). apply Congruence_Respects_Transition. exists p2. split. 
  assumption. assumption. destruct H1. destruct H1.
  exists ❲g1, x ❳. split. constructor. assumption. apply cgr_states_simplified_memory in hcgr. rewrite hcgr.
  constructor. assumption.
* assert (p ≡* p2). apply cgr_states_simplified in hcgr. simpl in *. assumption.
  assert (lts_then_sc p (ActOut (c ⋉ v)) q). apply Congruence_Respects_Transition. exists p2. split. 
  assumption. assumption. destruct H1. destruct H1.
  exists ❲ M ⊎ {[+ c ⋉ v +]}, x ❳. split. assert (g1 = M). apply cgr_states_simplified_memory in hcgr.
  assumption. rewrite H3.
  apply ltsM_send. assumption. constructor. assumption.
* assert (g1 = M1). apply cgr_states_simplified_memory in hcgr. assumption.
  assert (S1 =  S2'). inversion l1. reflexivity. assert (M1 = M2'). inversion l2. reflexivity.
  subst.
  
  assert (sc_then_lts p (ActIn (c ⋉ v)) S2).
  exists S2'. split. inversion hcgr. subst. assumption. inversion l2. assumption.
  eapply Congruence_Respects_Transition in H. destruct H.
  destruct H. eapply ltsM_input in H. instantiate (1 := M2) in H.
  exists (❲ M2, x ❳). split. inversion l1. subst. eapply ltsM_com.
  instantiate (1 := p). econstructor.
  instantiate (1 := M2 ⊎ {[+ c ⋉ v +]}). constructor. inversion H. subst. exact H2.
  constructor. assumption.
Qed.

(* The relation ≋ is reflexive*)
#[global] Instance cgr_states_refl : Reflexive cgr_states.
Proof. intro. destruct x. constructor. reflexivity. Qed.
(* The relation ≋ is symmetric*)
#[global] Instance cgr_states_symm : Symmetric cgr_states.
Proof. intros p q hcgr. destruct p. destruct q. assert (g0 = g1). apply cgr_states_simplified_memory in hcgr. assumption.
rewrite H. constructor. inversion hcgr. subst. symmetry. assumption. Qed.
(* The relation ≋ is transitive*)
#[global] Instance cgr_states_trans : Transitive cgr_states.
Proof. intros p q r hcgr1 hcgr2. destruct p. destruct q. destruct r. 
inversion hcgr1. inversion hcgr2. subst. constructor. eauto with cgr. Qed.

#[global] Hint Resolve cgr_states_refl cgr_states_symm cgr_states_trans:cgr_states_eq.

(* The relation ≋ is an equivence relation*)
#[global] Instance cgr_states_is_eq_rel  : Equivalence cgr_states.
Proof. repeat split.
       + apply cgr_states_refl.
       + apply cgr_states_symm.
       + apply cgr_states_trans.
Qed.

Lemma Parallel_Respects_Transition : forall M1 P1 M2 P2 P a, ltsM ❲ M1, P1 ❳ a ❲ M2, P2 ❳ 
                                    -> ltsM ❲ M1, P1 ‖ P❳ a ❲ M2, P2 ‖ P❳.
Proof.
intros.
dependent induction H. 
- constructor. constructor. assumption.
- constructor.
- constructor. constructor. assumption.
- constructor. constructor. assumption.
- econstructor. instantiate (1 := P1 ‖ P). instantiate (1 := v). instantiate (1 := c).
  inversion H. subst. constructor.
  instantiate (1 := M1). inversion H0. subst. constructor. constructor. assumption. 
Qed.

Lemma Sequence_Respects_Transition : forall M1 P1 M2 P2 P a, ltsM ❲ M1, P1 ❳ a ❲ M2, P2 ❳ 
                                    -> ltsM ❲ M1, P1 ; P ❳ a ❲ M2, P2 ; P❳.
Proof.
intros.
dependent induction H. 
- constructor. constructor. assumption.
- constructor.
- constructor. constructor. assumption.
- constructor. constructor. assumption.
- econstructor. instantiate (1 := P1 ; P). instantiate (1 := v). instantiate (1 := c).
  inversion H. subst. constructor. inversion H0. subst. constructor. constructor. assumption. 
Qed.

Lemma Plus_Respects_Transition : forall M1 P1 M2 P2 P, ltsM ❲ M1, g P1 ❳ τ ❲ M2, P2 ❳ 
                                    -> ltsM ❲ M1, P1 + P ❳ τ ❲ M2, P2❳.
Proof.
intros.
dependent induction H. 
- constructor. constructor. assumption.
- constructor. constructor. assumption.
- inversion H0. subst. inversion H. subst.
  econstructor. instantiate (1:= P1 + P). constructor.
  instantiate (1:= M2 ⊎ {[+ c ⋉ v +]}). constructor. constructor.
  assumption.
Qed.


(* One side of the Harmony Lemma *)
(* Important *)
Lemma Reduction_Implies_TausAndCong : forall S S', (sts S S') -> (ltsM_then_sc S τ S').
Proof.
intros P Q Reduction. 
induction Reduction.
- exists  ❲ M, p ^ v ❳. split.
  econstructor. instantiate (1 := gpr_input c p + g0). instantiate (1 := v). instantiate (1 := c).
  constructor. constructor. constructor. constructor. constructor. eauto with cgr.
- exists ❲ M ⊎ {[+ c ⋉ v +]}, p ❳. split. constructor. constructor. constructor. reflexivity.
- exists ❲ M, p ❳. split. constructor. constructor. constructor. constructor. eauto with cgr.
- exists ❲ M, pr_subst x p (rec x • p) ❳. split. constructor. constructor. constructor. eauto with cgr.
- exists ❲ M, p ❳. split. constructor. constructor. assumption. constructor. eauto with cgr.
- exists ❲ M, q ❳. split. constructor. apply lts_ifZero. assumption. constructor. eauto with cgr.
- destruct IHReduction.  destruct H. destruct x.
  exists ❲ M2, p ‖ P ❳. split. apply Parallel_Respects_Transition. inversion H0. subst. 
  assumption. inversion H0.  subst. constructor. eauto with cgr.
- destruct IHReduction.  destruct H. destruct x.
  exists ❲ M2, p ; P ❳. split. inversion H0. subst. apply Plus_Respects_Transition.
  eapply Sequence_Respects_Transition. assumption. constructor. inversion H0. subst. eauto with cgr.
- exists ❲ M1, Q ❳. split. apply ltsM_tau. constructor. constructor. eauto with cgr. reflexivity.
- destruct IHReduction. destruct H1. 
  assert (ltsM_then_sc S1 τ x). apply CongruenceStates_Respects_Transition. exists S1'. split.
  assumption. assumption. destruct H3. destruct H3. exists x0. split.
  assumption. eauto with cgr_states_eq.
Qed.

(* The More Stronger Harmony Lemma (in one side) is more stronger *)
(* Important *)
Lemma Congruence_Simplicity : (forall α , ((forall P Q, (((ltsM P α Q) -> (sts P Q)))) 
-> (forall P Q, ((ltsM_then_sc P α Q) -> (sts P Q))))).
Proof.
intros. destruct H0. destruct H0. eapply sts_cong. instantiate (1:=P). apply cgr_states_refl. instantiate (1:=x). apply H. exact H0. 
exact H1.
Qed.

Lemma SumReduction_ForSTS : forall M1 M2 p1 p2 q, sts ❲ M1, g p1❳ ❲ M2, q ❳ -> sts ❲ M1, p1 + p2 ❳ ❲ M2, q ❳.
Proof.
intros. revert p2. dependent induction H;intros.
  * eapply sts_cong. 
    -- instantiate (1 := ❲ M2 ⊎ {[+ c ⋉ v +]}, gpr_input c p + (g0 + p2) ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M2, p ^ v ❳). constructor.
    -- constructor. eauto with cgr.
  * eapply sts_cong. 
    -- instantiate (1 := ❲ M1, c ! v • q + (g0 + p2) ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M1 ⊎ {[+ c ⋉ v +]}, q ❳). constructor.
    -- constructor. eauto with cgr.
  * eapply sts_cong. 
    -- instantiate (1 := ❲ M2, t • q + (g0 + p2) ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M2, q ❳). constructor.
    -- constructor. eauto with cgr.
  * eapply sts_cong. 
    -- instantiate (1 := ❲ M1, P1; P + (G + p2) ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M2, P2; P ❳). constructor. assumption.
    -- constructor. eauto with cgr.
  * eapply sts_cong. 
    -- instantiate (1 := ❲ M2, P; q + (G + p2) ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M2, q ❳). constructor. assumption. 
    -- constructor. eauto with cgr.
  * destruct S1'. destruct S2'. dependent destruction H. 
    assert (exists p', p = (g p')). eapply Guards_cong_with_Guards. eauto with cgr. destruct H2. subst. 
    eapply sts_cong.
    -- instantiate (1 := ❲ g0, x + p2 ❳). constructor. eauto with cgr.
    -- apply IHsts. auto. instantiate (1 := p0). instantiate (1 := g1). constructor.
    -- assumption.
Qed.

(* Important *)
Lemma Taus_Implies_Reduction : forall P Q, (ltsM P τ Q) -> (sts P Q).
Proof. 
intros.
dependent induction H.
- dependent induction H. 
  * eapply sts_cong. 
    -- instantiate (1 := ❲ M, t • P + δ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M, P ❳). constructor.
    -- constructor. eauto with cgr.
  * eapply sts_cong. 
    -- instantiate (1 := ❲ M, rec x • P ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M, pr_subst x P (rec x • P) ❳ ). constructor.
    -- constructor. eauto with cgr.
  * constructor. assumption.
  * constructor. assumption.
  * eapply sts_cong. 
    -- instantiate (1 := ❲ M, P0 ; P + δ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M, P ❳ ). econstructor. assumption.
    -- constructor. eauto with cgr.
  * constructor. apply IHlts. auto.
  * eapply sts_cong.
    -- instantiate (1 := ❲ M, q1 ‖ p ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M, q2 ‖ p ❳). constructor. apply IHlts. auto.
    -- constructor. eauto with cgr.
  * apply SumReduction_ForSTS. apply IHlts. auto. 
  * eapply sts_cong. 
    -- instantiate (1 := ❲ M, p2 + p1 ❳ ). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M, q ❳ ). apply SumReduction_ForSTS. apply IHlts. auto.
    -- constructor. eauto with cgr.
  * eapply sts_cong. 
    -- instantiate (1 := ❲ M, p1; q + δ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M, p2; q ❳ ). constructor. apply IHlts. auto.
    -- constructor. eauto with cgr.
- dependent induction H.
  * eapply sts_cong.
    -- instantiate (1 := ❲ M, c ! v • P + δ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M ⊎ {[+ c ⋉ v +]}, P ❳). constructor.
    -- constructor. eauto with cgr.
  * constructor. apply IHlts. auto.
  * eapply sts_cong.
    -- instantiate (1 := ❲ M, q1 ‖ p ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M ⊎ {[+ c ⋉ v +]}, q2 ‖ p ❳). constructor. apply IHlts. auto.
    -- constructor. eauto with cgr.
  * apply SumReduction_ForSTS. apply IHlts. auto.
  * eapply sts_cong. 
    -- instantiate (1 := ❲ M, p2 + p1 ❳ ). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M ⊎ {[+ c ⋉ v +]}, q ❳ ). apply SumReduction_ForSTS. apply IHlts. auto.
    -- constructor. eauto with cgr. 
  * eapply sts_cong. 
    -- instantiate (1 := ❲ M, p1; q + δ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M ⊎ {[+ c ⋉ v +]}, p2; q ❳ ). constructor. apply IHlts. auto.
    -- constructor. eauto with cgr.
- dependent destruction H. dependent destruction H0. dependent induction H.
  * eapply sts_cong.
    -- instantiate (1 := ❲ M2 ⊎ {[+ c ⋉ v +]}, gpr_input c P + δ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M2, P ^ v ❳). constructor.
    -- constructor. eauto with cgr.
  * constructor. apply IHlts. 
    -- auto.
    -- intros. inversion H0.
    -- intros. inversion H0. 
  * eapply sts_cong.
    -- instantiate (1 := ❲ M2 ⊎ {[+ c ⋉ v +]}, q1 ‖ p ❳). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M2, q2 ‖ p ❳). constructor. apply IHlts. 
        ** auto.
        ** intros. inversion H0. 
        ** intros. inversion H0. 
    -- constructor. eauto with cgr.
  * apply SumReduction_ForSTS. apply IHlts.
    -- auto.
    -- intros. inversion H0. 
    -- intros. inversion H0. 
  * eapply sts_cong. 
    -- instantiate (1 := ❲ M2 ⊎ {[+ c ⋉ v +]}, p2 + p1 ❳ ). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M2, q ❳ ). apply SumReduction_ForSTS. apply IHlts.
        ** auto.
        ** intros. inversion H0.
        ** intros. inversion H0.
    -- constructor. eauto with cgr.
  * eapply sts_cong. 
    -- instantiate (1 := ❲ M2 ⊎ {[+ c ⋉ v +]}, p1; q + δ❳  ). constructor. eauto with cgr.
    -- instantiate (1 := ❲ M2, p2; q ❳ ). constructor. apply IHlts.
        ** auto.
        ** intros. inversion H0.
        ** intros. inversion H0.
    -- constructor. eauto with cgr.
Qed.

(* One side of the Harmony Lemma*)
Lemma TausAndCong_Implies_Reduction: forall P Q, (ltsM_then_sc P τ Q) -> (sts P Q).
Proof.
intros P Q H.
apply Congruence_Simplicity with τ. exact Taus_Implies_Reduction. exact H.
Qed.

(* Important *)
Theorem HarmonyLemmaForCCSWithValuePassing : forall P Q, (ltsM_then_sc P τ Q) <-> (sts P Q).
Proof.
intros. split.
* apply TausAndCong_Implies_Reduction.
* apply Reduction_Implies_TausAndCong.
Qed.

(* Definition for Well Abstracted bvariable *)
Inductive Well_Defined_Data : nat -> Data -> Prop :=
| bvar_is_defined_up_to_k: forall k x, (x < k) -> Well_Defined_Data k (bvar x)
| cst_is_always_defined : forall k v, Well_Defined_Data k (cst v).

Inductive Well_Defined_Condition : nat -> Equation Data -> Prop :=
| tt_is_WD : forall k, Well_Defined_Condition k tt
| ff_is_WD : forall k, Well_Defined_Condition k ff
| Inequality_is_WD : forall k x y, Well_Defined_Data k x -> Well_Defined_Data k y -> Well_Defined_Condition k (x ⩽ y)
| Or_is_WD : forall k e e', Well_Defined_Condition k e -> Well_Defined_Condition k e' -> Well_Defined_Condition k (e ∨ e')
| Not_is_WD : forall k e, Well_Defined_Condition k e -> Well_Defined_Condition k (non e).

Inductive Well_Defined_Input_in : nat -> proc -> Prop :=
| WD_par : forall k p1 p2, Well_Defined_Input_in k p1 -> Well_Defined_Input_in k p2 
                -> Well_Defined_Input_in k (p1 ‖ p2)
| WD_var : forall k i, Well_Defined_Input_in k (pr_var i)
| WD_rec : forall k x p1, Well_Defined_Input_in k p1 -> Well_Defined_Input_in k (rec x • p1)
| WD_if_then_else : forall k p1 p2 C, Well_Defined_Condition k C -> Well_Defined_Input_in k p1 
                    -> Well_Defined_Input_in k p2 
                        -> Well_Defined_Input_in k (If C Then p1 Else p2)
| WD_deadlock : forall k, Well_Defined_Input_in k (δ)
| WD_success : forall k, Well_Defined_Input_in k (①)
| WD_nil : forall k, Well_Defined_Input_in k (𝟘)
| WD_input : forall k c p, Well_Defined_Input_in (S k) p
                  -> Well_Defined_Input_in k (c ? p)
| WD_output : forall k c v p, Well_Defined_Data k v -> Well_Defined_Input_in k p
                  -> Well_Defined_Input_in k (c ! v • p)
| WD_tau : forall k p,  Well_Defined_Input_in k p -> Well_Defined_Input_in k (t • p)
| WD_choice : forall k p1 p2,  Well_Defined_Input_in k (g p1) ->  Well_Defined_Input_in k (g p2) 
              ->  Well_Defined_Input_in k (p1 + p2)
| WD_seq : forall k p1 p2,  Well_Defined_Input_in k p1 ->  Well_Defined_Input_in k p2 
              ->  Well_Defined_Input_in k (p1 ; p2).
              
              
              
Inductive Well_Defined_Input_in_MultiSet : nat -> gmultiset TypeOfActions -> Prop :=
| WD_gmset_empty : forall k, Well_Defined_Input_in_MultiSet k ∅
| WD_gmset_base : forall k M d c, Well_Defined_Input_in_MultiSet k M -> Well_Defined_Data k d ->
            Well_Defined_Input_in_MultiSet k (M ⊎ {[+ c ⋉ d +]}).

Inductive Well_Defined_Input_in_State : nat -> States -> Prop :=
| WD_state_base : forall k M P, Well_Defined_Input_in_MultiSet k M -> Well_Defined_Input_in k P ->
            Well_Defined_Input_in_State k (❲ M, P ❳).

#[global] Hint Constructors Well_Defined_Input_in:ccs.

Lemma Inequation_k_data : forall k d, Well_Defined_Data k d -> Well_Defined_Data (S k) d.
Proof.
intros. dependent destruction d. constructor. dependent destruction H. constructor. auto with arith.
Qed.

Lemma Inequation_k_equation : forall k c, Well_Defined_Condition k c -> Well_Defined_Condition (S k) c.
Proof.
intros. dependent induction c.
* constructor.
* constructor.
* destruct a; destruct a0.
  - constructor; constructor.
  - dependent destruction H. constructor. constructor. apply Inequation_k_data. assumption.
  - dependent destruction H. constructor. apply Inequation_k_data. assumption. constructor. 
  - dependent destruction H. constructor; apply Inequation_k_data; assumption.
* dependent destruction H. constructor. apply IHc1. assumption. apply IHc2. assumption.
* dependent destruction H. constructor. apply IHc. assumption.
Qed.

Lemma Inequation_k_proc : forall k p, Well_Defined_Input_in k p -> Well_Defined_Input_in (S k) p.
Proof.
intros. revert H. revert k.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p.
- intros. dependent destruction H. constructor; apply Hp; simpl; auto with arith; assumption.
- intros. constructor.
- intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
- intros. dependent destruction H. constructor. 
  ** apply Inequation_k_equation. assumption.
  ** apply Hp. simpl; auto with arith. assumption.
  ** apply Hp. simpl; auto with arith. assumption.
- intros. constructor.
- destruct g0.
  ** intros. constructor.
  ** intros. constructor.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. constructor. dependent destruction H. apply Inequation_k_data.
     assumption. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. dependent destruction H. constructor.
    -- apply Hp. simpl; auto with arith. assumption.
    -- apply Hp. simpl; auto with arith. assumption.
  ** intros. dependent destruction H. constructor.     
    -- apply Hp. simpl; auto with arith. assumption.
    -- apply Hp. simpl; auto with arith. assumption.
Qed.

Lemma WD_data_and_NewVar : forall d k i, Well_Defined_Data (k + i) d 
                          <-> Well_Defined_Data (S (k + i)) (NewVar_in_Data i d).
Proof.
intros. split.
- intros. revert H. revert k i. dependent induction d.
  * intros. simpl. constructor.
  * intros. simpl. destruct (decide (i < S n)). inversion H. constructor. auto with arith.
    inversion H. constructor. auto with arith.
- intros. revert H. revert k i. dependent induction d.
  * intros. simpl. constructor.
  * intros. inversion H. destruct (decide (i < S n)). constructor. subst.
    inversion H0. rewrite H3 in H2. auto with arith. constructor. inversion H0.
    lia.
    subst. destruct (decide (i < S n)). constructor. inversion H2. inversion H2.
Qed.

Lemma WD_eq_and_NewVar : forall e k i, Well_Defined_Condition (k + i) e <-> 
                            Well_Defined_Condition (S (k + i)) (NewVar_in_Equation i e).
Proof.
intros. split.
- intros. revert H. revert k i. dependent induction e.
  * intros. constructor.
  * intros. constructor.
  * intros. dependent induction H. constructor.
    -- apply WD_data_and_NewVar. assumption.
    -- apply WD_data_and_NewVar. assumption.
  * intros. simpl. dependent destruction H. constructor. 
    -- apply IHe1. assumption. 
    -- apply IHe2. assumption.
  * intros. simpl. constructor. dependent destruction H. apply IHe. assumption.
- intros. revert H. revert k i. dependent induction e.
  * intros. constructor.
  * intros. constructor.
  * intros. dependent induction H. constructor.
    -- apply WD_data_and_NewVar. assumption.
    -- apply WD_data_and_NewVar. assumption.
  * intros. simpl. dependent destruction H. constructor. 
    -- apply IHe1. assumption. 
    -- apply IHe2. assumption.
  * intros. simpl. constructor. dependent destruction H. apply IHe. assumption.
Qed.

Lemma WD_and_NewVar : forall P k i, Well_Defined_Input_in (k + i) P <-> Well_Defined_Input_in (S k + i) (NewVar i P).
Proof.
intros. split.
- intros. revert H. revert k i. 
  induction P as (P & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct P; intros; simpl.
  * dependent destruction H. constructor. 
    ** apply Hp. simpl. auto with arith. assumption.
    ** apply Hp. simpl. auto with arith. assumption.
  * constructor.
  * dependent destruction H. constructor. apply Hp. simpl. auto with arith. assumption.
  * dependent destruction H. constructor. apply WD_eq_and_NewVar. assumption.
    ** apply Hp. simpl. auto with arith. assumption.
    ** apply Hp. simpl. auto with arith. assumption.
  * constructor.
  * destruct g0 ; simpl.
    -- constructor.
    -- constructor.
    -- constructor. assert (S (k + i) = (S k + i)%nat). auto with arith. 
      assert (S (S (k + i)) = (S k + S i)%nat). rewrite H0. apply plus_n_Sm. rewrite H1. apply Hp.
      simpl. auto with arith. dependent destruction H. assert (S (k + i) = (k + S i)%nat). auto with arith.
      rewrite <-H2. assumption.
    -- dependent destruction H. constructor. apply WD_data_and_NewVar. assumption.
        apply Hp. simpl. auto with arith. assumption.
    -- dependent destruction H. constructor. 
        apply Hp. simpl. auto with arith. assumption.
    -- dependent destruction H. constructor. assert (Well_Defined_Input_in (S (k + i)) (NewVar i (g g0_1))).
       apply Hp. simpl. auto with arith. assumption.
       assumption. assert (Well_Defined_Input_in (S (k + i)) (NewVar i (g g0_2))).
       apply Hp. simpl. auto with arith. assumption.
       assumption.
    -- dependent destruction H. constructor.
       ** apply Hp. simpl. auto with arith. assumption.
       ** apply Hp. simpl. auto with arith. assumption.
- intros. revert H. revert k i. 
  induction P as (P & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct P; intros; simpl.
  * dependent destruction H. constructor. 
    ** apply Hp. simpl. auto with arith. assumption.
    ** apply Hp. simpl. auto with arith. assumption.
  * constructor.
  * dependent destruction H. constructor. apply Hp. simpl. auto with arith. assumption.
  * dependent destruction H. constructor. apply WD_eq_and_NewVar. assumption.
    ** apply Hp. simpl. auto with arith. assumption.
    ** apply Hp. simpl. auto with arith. assumption.
  * constructor.
  * destruct g0 ; simpl.
    -- constructor.
    -- constructor.
    -- dependent destruction H. assert (S (k + i) = (S k + i)%nat). auto with arith. 
      assert (S (S (k + i)) = (S k + S i)%nat). rewrite H0. apply plus_n_Sm.
      assert (S (k + i) = (k + S i)%nat). auto with arith. 
      constructor. rewrite H2. apply Hp. simpl. auto with arith. rewrite <-H1. assumption.
    -- dependent destruction H. constructor. apply WD_data_and_NewVar. assumption.
        apply Hp. simpl. auto with arith. assumption.
    -- dependent destruction H. constructor. 
        apply Hp. simpl. auto with arith. assumption.
    -- dependent destruction H. constructor.
       apply Hp. simpl. auto with arith. assumption.
       apply Hp. simpl. auto with arith. assumption.
    -- dependent destruction H. constructor.
       ** apply Hp. simpl. auto with arith. assumption.
       ** apply Hp. simpl. auto with arith. assumption.
Qed.

Lemma Congruence_step_Respects_WD_k : forall p q k, Well_Defined_Input_in k p -> p ≡ q -> Well_Defined_Input_in k q. 
Proof.
intros. revert H. revert k. dependent induction H0 ; intros.
* auto.
* dependent destruction H;constructor; auto.
* dependent destruction H. dependent destruction H. constructor. auto. constructor;auto.
* dependent destruction H. dependent destruction H0. constructor;auto. constructor; auto.
* dependent destruction H; auto.
* constructor; auto. constructor.
* dependent destruction H. constructor; auto. 
* dependent destruction H. dependent destruction H. constructor; auto. constructor; auto.
* dependent destruction H. dependent destruction H0. constructor; auto. constructor; auto.
* dependent destruction H. constructor. apply IHcgr_step. auto.
* dependent destruction H. constructor. apply IHcgr_step. auto.
* constructor. dependent destruction H. apply IHcgr_step. auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto. 
* dependent destruction H. constructor; auto. 
* dependent destruction H. dependent destruction H. constructor; auto. constructor; auto.  
* dependent destruction H. dependent destruction H0. constructor; auto. constructor; auto.
* dependent destruction H. dependent destruction H. constructor. constructor; auto. constructor; auto.
* dependent destruction H. dependent destruction H. dependent destruction H1. 
  constructor. constructor; auto. assumption.
* dependent destruction H. dependent destruction H.
  constructor. constructor; auto.
* dependent destruction H. dependent destruction H.
  constructor;auto. constructor; auto.
* dependent destruction H. dependent destruction H.
  constructor;auto. constructor; auto. assert ((S k) = ((S k) + 0)%nat). auto with arith. rewrite H1. apply (WD_and_NewVar Q k 0).
  assert ((k + 0)%nat = k). auto with arith. rewrite H2. assumption.
* dependent destruction H. dependent destruction H.
  constructor;auto. constructor; auto. assert ((S k) = ((S k) + 0)%nat). auto with arith. 
  assert ((k + 0)%nat = k). auto with arith. rewrite <-H2. apply (WD_and_NewVar Q k 0). rewrite <-H1.  assumption.
* dependent destruction H. dependent destruction H.
  constructor;auto. constructor; auto. 
* dependent destruction H. dependent destruction H0.
  constructor;auto. constructor; auto. 
Qed.

Lemma Congruence_Respects_WD_k : forall p q k, Well_Defined_Input_in k p -> p ≡* q -> Well_Defined_Input_in k q. 
Proof.
intros. dependent induction H0.
- apply Congruence_step_Respects_WD_k with x; auto.
- eauto.
Qed.

Lemma Congruence_Respects_WD : forall p q, Well_Defined_Input_in 0 p -> p ≡* q -> Well_Defined_Input_in 0 q.
Proof.
intros. eapply Congruence_Respects_WD_k; eauto.
Qed.

Lemma CongruenceM_Respects_WD_k : forall S' S k, Well_Defined_Input_in_State k S' -> S' ≋ S -> Well_Defined_Input_in_State k S. 
Proof.
intros. dependent destruction H0. dependent destruction H.
constructor.
- assumption.
- eapply Congruence_Respects_WD_k; eauto.
Qed.

Lemma CongruenceM_Respects_WD : forall S' S, Well_Defined_Input_in_State 0 S' -> S' ≋ S -> Well_Defined_Input_in_State 0 S. 
Proof.
intros. eapply CongruenceM_Respects_WD_k; eauto.
Qed.


Lemma NotK : forall n k,  n < S k -> n ≠ k -> n < k.
Proof.
intros. assert (n ≤ k). auto with arith. destruct H1. exfalso. apply H0. reflexivity. auto with arith.
Qed.

Lemma ForData : forall k v d, Well_Defined_Data (S k) d -> Well_Defined_Data k (subst_Data k (cst v) d).
Proof.
intros. revert H. revert v. revert k. dependent induction d.
* intros. simpl. constructor.
* intros. simpl. destruct (decide (n = k )).
  - constructor. 
  - dependent destruction H. 
    destruct (decide (n < k)). 
    -- constructor. assumption.
    -- constructor. apply NotK. apply transitivity with n. lia. (* pas top *) assumption. lia.
Qed.

Lemma ForEquation : forall k v e, Well_Defined_Condition (S k) e 
                -> Well_Defined_Condition k (subst_in_Equation k (cst v) e).
Proof.
intros. revert H. revert v. revert k. 
- dependent induction e. 
-- intros. simpl. constructor.
-- intros. simpl. constructor.
-- dependent induction a; dependent induction a0.
  * intros. simpl. constructor; constructor.
  * intros. simpl. destruct (decide (n = k)).
    ** constructor; constructor.
    ** constructor. constructor. dependent destruction H. dependent destruction H0.
       destruct (decide(n < k)).
       --- constructor. assumption.
       --- constructor. lia. (* pas top *)
  * intros. simpl. constructor; try constructor. destruct (decide (n = k)). constructor. dependent destruction H.
    dependent destruction H.
    destruct (decide(n < k)).
       --- constructor. assumption.
       --- constructor. lia. (* pas top *) 
  * intros. simpl. constructor.
    ** destruct (decide (n = k)); try constructor. dependent destruction H. dependent destruction H.
       destruct (decide(n < k)).
       --- constructor. assumption.
       --- constructor. lia. (* pas top *)
    ** destruct (decide (n0 = k)); try constructor. dependent destruction H. dependent destruction H0. 
       destruct (decide (n0 < k)).
       --- constructor. assumption.
       --- constructor. lia. (* pas top *)
-- intros. dependent destruction H. simpl. constructor. apply IHe1. assumption. apply IHe2. assumption.
-- intros. dependent destruction H. simpl. constructor. apply IHe. assumption.
Qed.

Lemma ForSTS : forall k p v, Well_Defined_Input_in (S k) p -> Well_Defined_Input_in k (subst_in_proc k (cst v) p).
Proof.
intros. revert v. revert H. revert k.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p.
* intros. dependent destruction H. simpl. constructor. 
  - apply Hp. simpl. auto with arith. assumption.
  - apply Hp. simpl. auto with arith. assumption.
* intros. simpl. constructor.
* intros. simpl. dependent destruction H. constructor. apply Hp. simpl. auto with arith. assumption.
* intros. simpl. dependent destruction H. constructor.
  - apply ForEquation. assumption.
  - apply Hp. simpl. auto with arith. assumption.
  - apply Hp. simpl. auto with arith. assumption.
* intros. simpl. constructor.
* destruct g0.
  - intros. simpl. constructor.
  - intros. simpl. constructor.
  - intros. simpl. constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. dependent destruction H. constructor. apply ForData. assumption.
    apply Hp. simpl. auto with arith. assumption.
  - intros. simpl. constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. dependent destruction H. constructor.
    -- assert (Well_Defined_Input_in k (subst_in_proc k v (g0_1))). apply Hp.
      simpl.  auto with arith. assumption. assumption.
    -- assert (Well_Defined_Input_in k (subst_in_proc k v (g0_2))). apply Hp.
      simpl.  auto with arith. assumption. assumption.
  - intros. simpl. dependent destruction H. constructor.
    -- apply Hp. simpl. auto with arith. assumption.
    -- apply Hp. simpl. auto with arith. assumption.
Qed.



Lemma ForRecursionSanity : forall p' p x k, Well_Defined_Input_in k p' -> Well_Defined_Input_in k p 
            -> Well_Defined_Input_in k (pr_subst x p' p).
Proof.
intros. revert H. revert H0. revert k. revert x. revert p.
induction p' as (p' & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p'.
* intros. simpl. constructor. 
  ** apply Hp. simpl. auto with arith. assumption. dependent destruction H. assumption.
  ** apply Hp. simpl. auto with arith. assumption. dependent destruction H. assumption.
* intros. simpl. destruct (decide (x = n)). assumption. assumption.
* intros. simpl. destruct (decide (x=n)). 
  ** dependent destruction H. assumption.
  ** constructor. apply Hp. simpl; auto with arith. assumption. dependent destruction H. assumption.
* intros. simpl. dependent destruction H. constructor.
  ** assumption.
  ** apply Hp. simpl; auto with arith. assumption. assumption.
  ** apply Hp. simpl; auto with arith. assumption. assumption.
* intros. simpl. constructor.
* destruct g0. 
  ** intros. simpl. constructor.
  ** intros. simpl. constructor.
  ** intros. simpl. constructor. dependent destruction H. apply Hp. 
    - simpl;auto with arith.
    - assert ((S k) = ((S k) + 0)%nat). auto with arith. rewrite H1. apply (WD_and_NewVar p0 k 0).
      assert (k = (k + 0)%nat). auto with arith. rewrite <-H2. assumption. 
    - assumption.
  ** intros. simpl. dependent destruction H. constructor. assumption.
     apply Hp. simpl. auto with arith. assumption.  assumption.
  ** intros. simpl. constructor. apply Hp.
    - simpl; auto with arith.
    - assumption.
    - dependent destruction H. assumption.
  ** intros. simpl. dependent destruction H. constructor.
    - assert (Well_Defined_Input_in k (pr_subst x (g g0_1) p)). apply Hp. simpl; auto with arith. assumption.
      assumption. assumption.
    - assert (Well_Defined_Input_in k (pr_subst x (g g0_2) p)). apply Hp. simpl; auto with arith. assumption.
      assumption. assumption.
  ** intros. simpl. dependent destruction H. constructor.
    -- apply Hp. simpl. auto with arith. assumption. assumption.
    -- apply Hp. simpl. auto with arith. assumption. assumption.
Qed.

Lemma RecursionOverReduction_is_WD : forall k x p, Well_Defined_Input_in k (rec x • p) 
          -> Well_Defined_Input_in k (pr_subst x p (rec x • p)).
Proof.
intros. apply ForRecursionSanity. dependent destruction H. assumption. assumption.
Qed.

Lemma Well_Def_Data_Is_a_value : forall d, Well_Defined_Data 0 d <-> exists v, d = cst v.
Proof.
intros. split. 
- intro. dependent destruction H. exfalso. dependent induction H. exists v. reflexivity.
- intros. destruct H. subst. constructor.
Qed.



Lemma Well_Def_Subset : forall k M M0, Well_Defined_Input_in_MultiSet k M0 -> gmultiset_subseteq M M0 
                          -> Well_Defined_Input_in_MultiSet k M.
Proof.
intros. revert H0. revert M. dependent induction H; intros.
- assert (M = ∅). multiset_solver. subst. constructor.
- assert (0 < multiplicity (c ⋉ d) M0 \/ multiplicity (c ⋉ d) M0 = 0). multiset_solver.
  destruct H2.
  * assert (exists x, M0 = x ⊎ {[+ c ⋉ d +]}).
    exists (gmultiset_difference M0 ({[+ c ⋉ d +]})).
    multiset_solver. destruct H3. rewrite H3 in H1.
    assert (gmultiset_subseteq x M). multiset_solver.
    assert (Well_Defined_Input_in_MultiSet k x). eapply IHWell_Defined_Input_in_MultiSet.
    assumption.
    rewrite H3. constructor; assumption.
  * assert (gmultiset_subseteq M0 M). multiset_solver.
    eapply IHWell_Defined_Input_in_MultiSet. assumption.
Qed.

Lemma Well_Def_Singleton : forall k c d, Well_Defined_Input_in_MultiSet k {[+ c ⋉ d +]} ->  Well_Defined_Data k d.
Proof.
intros.
dependent destruction H. 
- assert (M = ∅). multiset_solver.
  rewrite H1 in x. assert (c = c0 /\ d0 = d). multiset_solver.
  destruct H2. subst. assumption.
Qed.

Lemma STS_Respects_WD : forall S S', Well_Defined_Input_in_State 0 S -> sts S S' -> Well_Defined_Input_in_State 0 S'.
Proof.
intros. revert H. rename H0 into Reduction. dependent induction Reduction.
* intros. dependent destruction H. 
  dependent destruction H0. dependent destruction H0_. 
  constructor. 
  - eapply Well_Def_Subset with (M ⊎ {[+ c ⋉ v +]}).  assumption. multiset_solver. 
  - assert (Well_Defined_Input_in_MultiSet 0 {[+ c ⋉ v +]}).
    eapply Well_Def_Subset with (M ⊎ {[+ c ⋉ v +]}). assumption. multiset_solver.
    eapply Well_Def_Singleton in H0.
    eapply Well_Def_Data_Is_a_value in H0.  destruct H0. subst.
    eapply ForSTS. assumption.
* intros. dependent destruction H. constructor.
  - constructor. assumption. dependent destruction H0. dependent destruction H0_. assumption. 
  - dependent destruction H0. dependent destruction H0_. assumption.
* intros. dependent destruction H. dependent destruction H0. dependent destruction H0_. constructor; assumption.
* intros. dependent destruction H. constructor. assumption. apply RecursionOverReduction_is_WD. assumption.
* intros. dependent destruction H0. dependent destruction H1. constructor; assumption.
* intros. dependent destruction H0. dependent destruction H1. constructor; assumption.
* intros. dependent destruction H. dependent destruction H0. assert (Well_Defined_Input_in_State 0 ❲ M1, P1 ❳). 
  constructor; assumption. apply IHReduction in H0. dependent destruction H0.
  constructor. assumption. constructor; assumption.
* intros. dependent destruction H. dependent destruction H0. dependent destruction H0_. 
  assert (Well_Defined_Input_in_State 0 ❲ M1, P1 ❳). 
  constructor; assumption. apply IHReduction in H0. dependent destruction H0.
  constructor. assumption. constructor; assumption.
* intros. dependent destruction H0. dependent destruction H1. dependent destruction H1_.
  constructor; assumption. 
* intros. apply CongruenceM_Respects_WD with S2'. apply IHReduction. eapply CongruenceM_Respects_WD with S1. 
  assumption. assumption. assumption. 
Qed.

Inductive Well_Defined_Action: (Act TypeOfActions) -> Prop :=
| ActionOuput_with_value_is_always_defined : forall c v, Well_Defined_Action (ActOut  (c ⋉ (cst v)))
| ActionInput_with_value_is_always_defined : forall c v, Well_Defined_Action (ActIn  (c ⋉ (cst v)))
| Tau_is_always_defined : Well_Defined_Action (τ).

Lemma Output_are_good : forall p1 p2 c d, Well_Defined_Input_in 0 p1 -> lts p1 (ActOut (c ⋉ d)) p2 
      -> exists v, d = cst v.
Proof.
intros. dependent induction H0. dependent destruction H. apply Well_Def_Data_Is_a_value in H. destruct H.
subst. exists x. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
Qed.

Lemma PreLTS_Respects_WD : forall p q α, Well_Defined_Input_in 0 p -> Well_Defined_Action α -> lts p α q 
            ->  Well_Defined_Input_in 0 q.
Proof.
intros. revert H. revert H0. rename H1 into Transition. dependent induction Transition.
* intros. dependent destruction H0.  apply ForSTS. dependent destruction H. assumption.
* intros. dependent destruction H. assumption.
* intros. dependent destruction H. assumption.
* intros. apply ForRecursionSanity. dependent destruction H. assumption. assumption.
* intros. dependent destruction H1. assumption.
* intros. dependent destruction H1. assumption.
* intros. dependent destruction H1. assumption.
* intros. dependent destruction H. constructor. apply IHTransition. assumption. assumption. assumption.
* intros. dependent destruction H. constructor. assumption. apply IHTransition. assumption. assumption.
* intros. dependent destruction H. apply IHTransition; assumption.
* intros. dependent destruction H. apply IHTransition; assumption.
* intros. dependent destruction H. constructor. apply IHTransition. assumption. assumption. assumption.
Qed.

Lemma LTS_Respects_WD : forall S S' α, Well_Defined_Input_in_State 0 S -> Well_Defined_Action α -> ltsM S α S' 
            ->  Well_Defined_Input_in_State 0 S'.
Proof.
intros. dependent induction H1.
- dependent destruction H.
  assert (Well_Defined_Input_in 0 q). eapply (PreLTS_Respects_WD p q (ActIn (c ⋉ v))); assumption.
  constructor; assumption.
- dependent destruction H. constructor.
  eapply Well_Def_Subset with (M ⊎ {[+ c ⋉ v +]}). assumption. multiset_solver.
  assumption.
- constructor.
  * dependent destruction H. assumption.
  * dependent destruction H. eapply (PreLTS_Respects_WD p q τ); assumption.
- dependent destruction H. constructor.
  * constructor. assumption. eapply Output_are_good in H0. instantiate (1 := v) in H0.
    destruct H0. subst. constructor. exact H2.
  * eapply (PreLTS_Respects_WD p q (ActOut (c ⋉ v))).
    assumption. eapply Output_are_good in H0. instantiate (1 := v) in H0. destruct H0. subst. econstructor.
    eassumption. exact H2.
- dependent destruction H1_. dependent destruction H1_0. dependent destruction H.
  constructor. 
  * eapply Well_Def_Subset with (M2 ⊎ {[+ c ⋉ v +]}). assumption. multiset_solver.
  * eapply PreLTS_Respects_WD. exact H0. 
    assert (Well_Defined_Data 0 v). eapply Well_Def_Singleton. eapply Well_Def_Subset. 
    instantiate (1 := (M2 ⊎ {[+ c ⋉ v +]})). assumption. 
    instantiate (1 := c). multiset_solver.
    instantiate (1 := ActExt (ActIn (c ⋉ v))). eapply Well_Def_Data_Is_a_value in H3.
    destruct H3. subst. constructor. assumption.
Qed.

(* Lemma to simplify the Data in Value for a transition *)
Lemma OutputWithValue : forall p q a, ltsM p (ActOut a) q -> exists c d, a = c ⋉ d.
Proof.
intros. dependent destruction a. dependent induction H.
- exists c. exists d. reflexivity.
Qed.

Lemma InputWithValue : forall p q a, ltsM p (ActIn a) q -> exists c v, a = c ⋉ v.
Proof.
intros. dependent destruction a. dependent induction H.
- exists c. exists d. reflexivity.
Qed.

Lemma ForallSets : forall M1 P1 α c d M2 P2,  ltsM ❲ M1, P1 ❳ α ❲ M2, P2 ❳ 
                    -> ltsM ❲ M1 ⊎ {[+ c ⋉ d +]}, P1 ❳ α ❲ M2 ⊎ {[+ c ⋉ d +]}, P2 ❳.
Proof.
intros. dependent destruction H.
- constructor. assumption.
- assert (M2 ⊎ {[+ c0 ⋉ v +]} ⊎ {[+ c ⋉ d +]} = M2 ⊎ {[+ c ⋉ d +]} ⊎ {[+ c0 ⋉ v +]}). multiset_solver.
  rewrite H. constructor.
- constructor. assumption.
- assert (M1 ⊎ {[+ c0 ⋉ v +]} ⊎ {[+ c ⋉ d +]} = M1 ⊎ {[+ c ⋉ d +]} ⊎ {[+ c0 ⋉ v +]}). multiset_solver.
  rewrite H0. econstructor. assumption.
- dependent destruction H. dependent destruction H0. econstructor. 
  * assert (M2 ⊎ {[+ c0 ⋉ v +]} ⊎ {[+ c ⋉ d +]} = M2 ⊎ {[+ c ⋉ d +]} ⊎ {[+ c0 ⋉ v +]}). multiset_solver. 
    rewrite H0. constructor.
  * econstructor. assumption.
Qed.



(* Peter Selinger Axioms (OutBuffered Agent with FeedBack) up to structural equivalence*)

Lemma OBA_with_FB_First_Axiom : forall p q r a α,
  ltsM p (ActOut a) q -> ltsM q α r ->
  (exists r', ltsM p α r' /\ ltsM_then_sc r' (ActOut a) r). (* output-commutativity *)
Proof.
intros. assert (ltsM p (ActOut a) q). assumption. apply OutputWithValue in H1.
decompose record H1. subst.
assert (ltsM p (ActOut (x ⋉ x0)) q). assumption. dependent destruction H. destruct r.
exists ❲ g0 ⊎ {[+ x ⋉ x0 +]}, p ❳. split.
* apply ForallSets. assumption.
* exists ❲ g0, p ❳. split. 
  - econstructor. 
  - constructor. eauto with cgr.
Qed.

Lemma OBA_with_FB_Second_Axiom : forall p q1 q2 a μ, 
  μ ≠ (ActOut a) ->
  ltsM p (ActOut a) q1 ->
  ltsM p (ActExt μ) q2 ->
  ∃ r : States, ltsM q1 (ActExt μ) r ∧ ltsM_then_sc q2 (ActOut a) r. (* output-confluence  *)
Proof.
intros. assert (ltsM p (ActOut a) q1).  assumption. dependent destruction H2.
inversion H1; subst.
- exists ❲ M , q ❳. split. 
  * constructor. assumption.
  * exists ❲ M, q ❳. split. constructor. constructor. eauto with cgr.
- (* replace M with (gmultiset_difference M0 {[+ c ⋉ v +]} ⊎ {[+ c0 ⋉ v0 +]}) by multiset_solver.*)
  assert (exists M', M = M' ⊎ {[+ c0 ⋉ v0 +]}). exists (gmultiset_difference M0 {[+ c ⋉ v +]}). 
  multiset_solver.
  assert (exists M0', M0 = M0' ⊎ {[+ c ⋉ v +]}). exists (gmultiset_difference M {[+ c0 ⋉ v0 +]}). 
  multiset_solver.
  destruct H2. rewrite H2. 
  exists ❲ x, P ❳. split.
  * constructor.
  * destruct H4. rewrite H4. exists ❲ x0 , P ❳. split. constructor. 
    assert (x0 = x). multiset_solver. rewrite H5. constructor. eauto with cgr.
Qed.

Lemma OBA_with_FB_Third_Axiom : forall p1 p2 p3 a, 
            ltsM p1 (ActOut a) p2 → ltsM p1 (ActOut a) p3 -> p2 ≋ p3. (* output-determinacy *)
Proof.
intros. assert (ltsM p1 (ActOut a) p2). assumption. dependent destruction H0.
dependent destruction H1. assert (M0 = M). multiset_solver. rewrite H0. 
constructor. eauto with cgr.
Qed.

Lemma OBA_with_FB_Fourth_Axiom : forall p1 p2 p3 a, ltsM p1 (ActOut a) p2 -> ltsM p2 (ActIn a) p3 
                              -> ltsM_then_sc p1 τ p3. (* feedback *)
Proof.
intros. dependent destruction H. dependent destruction H0. 
exists ❲ M, q ❳. split. econstructor.
- instantiate (1 := P). constructor.
- constructor. exact H.
- constructor. eauto with cgr.
Qed.

Lemma OBA_with_FB_Fifth_Axiom : forall p q1 q2 a,
  ltsM p (ActOut a) q1 -> ltsM p τ q2 ->
  (∃ q : States, ltsM q1 τ q /\ ltsM_then_sc q2 (ActOut a) q) \/ ltsM_then_sc q1 (ActIn a) q2. (* output-tau  *)
Proof.
intros. assert (ltsM p (ActOut a) q1). assumption. destruct a. 
dependent destruction H0. 
- dependent destruction H1. left. eexists. instantiate (1 := ❲ M0, q ❳). split.
  * constructor. assumption.
  * econstructor. split. constructor. constructor. eauto with cgr.
- dependent destruction H1. left. eexists.
  eexists. 
  * eapply ltsM_send. exact H0.
  * econstructor. assert (M0 ⊎ {[+ c ⋉ d +]} ⊎ {[+ c0 ⋉ v +]} = M0 ⊎ {[+ c0 ⋉ v +]} ⊎ {[+ c ⋉ d +]}). multiset_solver.
    split. rewrite H1. constructor. constructor. eauto with cgr. 
- destruct (decide ((c0 ⋉ v) = (c ⋉ d))). 
  * rewrite <-e in H1 , H. dependent destruction H1. inversion H0_; subst.
    assert (M2 = M). multiset_solver.
    rewrite H0 in H0_. 
    right. 
    eexists. instantiate (1 := ❲ M, S2 ❳). split. constructor. rewrite <-e. dependent destruction H0_0. assumption.
    rewrite H0. constructor. eauto with cgr.
  * dependent destruction H1. inversion H0_; subst. left.
    eexists. split. eapply ltsM_com.
    assert (ltsM ❲ M, S2' ❳ (ActOut (c0 ⋉ v)) ❲ (gmultiset_difference M2 ({[+ c ⋉ d +]})) , S2' ❳).
    assert (M = (gmultiset_difference M2 ({[+ c ⋉ d +]})) ⊎ {[+ c0 ⋉ v +]}).
    multiset_solver. rewrite H0. constructor. exact H0.
    dependent destruction H0_0. constructor. exact l.
    assert (M2 = (gmultiset_difference M2 {[+ c ⋉ d +]}) ⊎ {[+ c ⋉ d+]}). multiset_solver.
    exists (❲ gmultiset_difference M2 {[+ c ⋉ d +]}, S2 ❳). rewrite H0 at 1. split. 
      -- constructor.
      -- constructor. eauto with cgr.
Qed.

Lemma ExtraAxiom : forall p1 p2 q1 q2 a,
      ltsM p1 (ActOut a) q1 -> ltsM p2 (ActOut a) q2 -> q1 ≋ q2 -> p1 ≋ p2.
Proof.
intros. dependent destruction H1. dependent destruction H. dependent destruction H0.
constructor. assumption. 
Qed. 


Lemma Equation_dec : forall (x y : Equation Data) , {x = y} + {x <> y}.
Proof.
decide equality. apply Data_dec. apply Data_dec.
Qed.


#[global] Instance equation_dec : EqDecision (Equation Data). exact Equation_dec. Defined.


Fixpoint proc_dec (x y : proc) : { x = y } + { x <> y }
with gproc_dec (x y : gproc) : { x = y } + { x <> y }.
Proof.
decide equality. 
* destruct (decide(n = n0));eauto.
* destruct (decide(n = n0));eauto.
* destruct (decide(e = e0));eauto. 
* decide equality. destruct (decide(c = c0));eauto.
   destruct (decide(d = d0));eauto.
   destruct (decide(c = c0));eauto.
Qed.

#[global] Instance proc_eqdecision : EqDecision proc. by exact proc_dec. Defined.

#[global] Instance MailBox_eqdecision : EqDecision (gmultiset TypeOfActions). by exact gmultiset_eq_dec. Defined.

Fixpoint States_dec (x y : States) : { x = y } + { x <> y }.
Proof.
destruct x; destruct y.
decide equality. 
* destruct (decide(p1 = p2));eauto.
* destruct (decide(g2 = g3));eauto.
Qed.

#[global] Instance States_eqdecision : EqDecision States. by exact States_dec. Defined.

Fixpoint encode_equation (E : Equation Data) : gen_tree (nat + Data) :=
match E with
  | tt => GenLeaf (inl 1)
  | ff => GenLeaf (inl 0)
  | D1 ⩽ D2 => GenNode 2 (GenLeaf (inr D1) :: [GenLeaf (inr D2)])
  | e1 ∨ e2 => GenNode 3 (encode_equation e1 :: [encode_equation e2])
  | non e => GenNode 4 [encode_equation e] 
end.

Fixpoint decode_equation (tree : gen_tree (nat + Data)) : Equation Data :=
match tree with
  | GenLeaf (inl 1) => tt
  | GenLeaf (inl 0) => ff
  | GenNode 2 (GenLeaf (inr d) :: [GenLeaf (inr d')]) => d ⩽ d'
  | GenNode 3 (p :: [q]) => (decode_equation p) ∨ (decode_equation q)
  | GenNode 4 [t'] => non (decode_equation t')
  | _ => ff
end. 




Lemma encode_decide_equations p : decode_equation (encode_equation p) = p.
Proof. 
induction p.
* simpl. reflexivity.
* simpl. reflexivity.
* simpl. reflexivity.
* simpl. rewrite IHp1. rewrite IHp2. reflexivity.
* simpl. rewrite IHp. reflexivity.
Qed.

#[global] Instance equation_countable : Countable (Equation Data).
Proof.
  refine (inj_countable' encode_equation decode_equation _).
  apply encode_decide_equations.
Qed.




Fixpoint encode_proc (p: proc) : gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel)) :=
  match p with
  | p ‖ q  => GenNode 0 (encode_proc p :: [encode_proc q])
  | pr_var i => GenNode 2 [GenLeaf $ inl i]
  | rec x • P => GenNode 3 ((GenLeaf $ inl x) :: [encode_proc P])
  | If C Then A Else B => GenNode 4 (GenLeaf (inr ( inl (inl C))) :: encode_proc A :: [encode_proc B])
  | g gp => GenNode 1 [encode_gproc gp]
  | 𝟘 => GenNode 0 []
  end
with
encode_gproc (gp: gproc) : gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel)) :=
  match gp with
  | δ => GenNode 2 []
  | ① => GenNode 1 []
  | c ? p => GenNode 3 ((GenLeaf (inr $ inr c)) :: [encode_proc p])
  | c ! v • p => GenNode 4 ((GenLeaf (inr $ inl $ inr $ (c ⋉ v))) :: [encode_proc p])
  | t • p => GenNode 5 [encode_proc p]
  | gp + gq => GenNode 6 (encode_gproc gp :: [encode_gproc gq])
  | p ; q => GenNode 7 (encode_proc p :: [encode_proc q])
 end.
  
Definition Channel_of (a : TypeOfActions) : Channel := 
match a with 
| act c d => c
end.

Definition Data_of (a : TypeOfActions) : Data := 
match a with 
| act c d => d
end.

Fixpoint decode_proc (t': gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel))) : proc :=
  match t' with
  | GenNode 0 (ep :: [eq]) => (decode_proc ep) ‖ (decode_proc eq)
  | GenNode 2 [GenLeaf (inl i)] => pr_var i
  | GenNode 3 ((GenLeaf (inl i)) :: [egq]) => rec i • (decode_proc egq)
  | GenNode 4 ((GenLeaf (inr ( inl (inl C)))) :: A :: [B]) => If C Then (decode_proc A) Else (decode_proc B)
  | GenNode 0 [] => 𝟘
  | GenNode 1 [egp] => g (decode_gproc egp)
  | _ => ① 
  end
with
decode_gproc (t': gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel))): gproc :=
  match t' with
  | GenNode 2 [] => δ 
  | GenNode 1 [] => ①
  | GenNode 3 (GenLeaf (inr (inr c)) :: [ep]) => c ? (decode_proc ep) 
  | GenNode 4 (GenLeaf (inr ( inl (inr a))) :: [ep]) => (Channel_of a) ! (Data_of a) • (decode_proc ep) 
  | GenNode 5 [eq] => t • (decode_proc eq) 
  | GenNode 6 (egp :: [egq]) => (decode_gproc egp) + (decode_gproc egq) 
  | GenNode 7 (ep :: [eq]) => (decode_proc ep) ; (decode_proc eq) 
  | _ => ① 
  end.

Lemma encode_decide_procs p : decode_proc (encode_proc p) = p
with encode_decide_gprocs p : decode_gproc (encode_gproc p) = p.
Proof. all: case p. 
* intros. simpl. rewrite (encode_decide_procs p0). rewrite (encode_decide_procs p1). reflexivity.
* intros. simpl. reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). rewrite (encode_decide_procs p1). reflexivity.
* intros. simpl. reflexivity. 
* intros. simpl. rewrite (encode_decide_gprocs g0). reflexivity.
* intros. simpl. reflexivity.
* intros. simpl. reflexivity. 
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_gprocs g0). rewrite (encode_decide_gprocs g1). reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). rewrite (encode_decide_procs p1). reflexivity.
Qed.

#[global] Instance proc_count : Countable proc.
refine (inj_countable' encode_proc decode_proc _).
  apply encode_decide_procs.
Qed.

#[global] Instance mset_count : Countable (gmultiset TypeOfActions). by exact gmultiset_countable. Qed.

Definition encode_states (S : States) : gen_tree ((gmultiset TypeOfActions) + proc) :=
  match S with
  | ❲ M, P ❳ => GenNode 0 (GenLeaf (inl M) :: [GenLeaf (inr P)])
  end.

Definition decode_states (t': gen_tree ((gmultiset TypeOfActions) + proc)) : States :=
  match t' with
  | GenNode 0 (GenLeaf (inl M) :: [GenLeaf (inr P)]) => ❲ M , P ❳
  | _ => ❲ ∅ , ① ❳
  end.

Lemma encode_decide_states S : decode_states (encode_states S) = S.
Proof. case S.
* intros. simpl. reflexivity. 
Qed.

#[global] Instance States_count : Countable States.
refine (inj_countable' encode_states decode_states _).
  apply encode_decide_states.
Qed.

#[global] Instance Singletons_of_TypeOfActions : SingletonMS TypeOfActions (gmultiset TypeOfActions) 
:=gmultiset_singleton.
#[global] Instance Singleton_of_gproc : Singleton gproc (gset proc).
intro. exact {[(g X)]}. Qed.
#[global] Instance SingletonMS_of_States : SingletonMS States (gset States) 
:=gset_singleton.
#[global] Instance Singletons_of_States : Singleton States (gset States) := gset_singleton.
#[global] Instance Empty_of_States : Empty (gset States) := gset_empty.
#[global] Instance Union_of_States : Union (gset States) := gset_union.
#[global] Instance SemiSet_of_States : SemiSet States (gset States) := gset_semi_set.
#[global] Instance Singleton_of_TypeOfActions : Singleton TypeOfActions (gmultiset TypeOfActions) := gmultiset_singleton.
#[global] Instance SemiSet_of_TypeOfActions : SemiSet TypeOfActions (gmultiset TypeOfActions).
Proof. repeat split ;try now set_solver. Defined.

Definition moutputs_of_State p : gmultiset TypeOfActions := MailBox_of p.

Definition outputs_of_State p := dom (moutputs_of_State p).

Lemma mo_equiv_spec_step : forall {p q}, p ≋ q -> moutputs_of_State p = moutputs_of_State q.
Proof. intros. dependent induction H; multiset_solver. Qed.

Lemma mo_spec p a q : ltsM p (ActOut a) q -> moutputs_of_State p = {[+ a +]} ⊎ moutputs_of_State q.
Proof.
  intros l.
  dependent destruction l. multiset_solver. 
Qed.

Lemma mo_spec_l e a :
  a ∈ moutputs_of_State e -> {e' | ltsM e (ActExt $ ActOut a) e' /\ moutputs_of_State e' = moutputs_of_State e ∖ {[+ a +]}}.
Proof.
  intros mem.
  dependent induction e.
  cbn in mem.
  exists (❲ (gmultiset_difference g0 ({[+ a +]})), p ❳).
  assert (g0 = (gmultiset_difference g0 ({[+ a +]})) ⊎ ({[+ a +]})). multiset_solver.
  split.
  * rewrite H at 1. destruct a. constructor.
  * simpl. multiset_solver.
Qed.

Lemma mo_spec_r e a :
  {e' | ltsM e (ActExt $ ActOut a) e' /\ moutputs_of_State e' = moutputs_of_State e ∖ {[+ a +]}} -> a ∈ moutputs_of_State e.
Proof.
  dependent destruction e; intros (e' & l & mem).
  + cbn. dependent destruction l. multiset_solver.
Qed.

Lemma outputs_of_spec2 p a : a ∈ outputs_of_State p -> {q | ltsM p (ActExt (ActOut a)) q}.
Proof.
  intros mem.
  eapply gmultiset_elem_of_dom in mem.
  eapply mo_spec_l in mem.
  firstorder.
Qed.

Fixpoint moutputs_of p : gmultiset TypeOfActions := 
match p with
  | P ‖ Q => (moutputs_of P) ⊎ (moutputs_of Q)
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | If C Then P Else Q => ∅  
  | 𝟘 => ∅
  | g gp => moutputs_of_g gp
end
with 
moutputs_of_g (gp : gproc) : gmultiset TypeOfActions :=
match gp with
  | δ => ∅
  | ① => ∅
  | c ? p => ∅
  | c ! v • p => {[+ (c ⋉ v) +]}
  | t • p => ∅
  | gp1 + gp2 => moutputs_of_g gp1 ⊎ moutputs_of_g gp2
  | p1 ; p2 => moutputs_of p1
end.


Definition outputs_of p := dom (moutputs_of p).


#[global] Instance Elements_of_States : Elements (gmultiset TypeOfActions) (gmultiset TypeOfActions).
intro. exact [H].
Qed.

Lemma outputs_of_spec1_zero (p : proc ) (a : TypeOfActions) : {q | lts p (ActExt (ActOut a)) q} 
      -> a ∈ outputs_of p.
Proof.    
  intros (p' & lts__p). revert lts__p. revert a. revert p'.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros.
  + eapply gmultiset_elem_of_dom.
    cbn. inversion lts__p; subst. apply Hp in H3. eapply gmultiset_elem_of_dom in H3. multiset_solver.
    simpl. auto with arith.
    apply Hp in H3. eapply gmultiset_elem_of_dom in H3. multiset_solver.
    simpl. auto with arith.
  + inversion lts__p; subst.
  + inversion lts__p; subst.
  + inversion lts__p; subst.
  + inversion lts__p; subst.
  + assert (lts g0 (ActOut a) p'). assumption. destruct a.
    inversion lts__p; subst.
    * unfold outputs_of. multiset_solver.
    * unfold outputs_of. simpl. eapply gmultiset_elem_of_dom. eapply gmultiset_elem_of_disj_union. left.
      assert (c ⋉ d ∈ outputs_of (g p1)). eapply Hp. simpl. auto with arith. exact H1.
      unfold outputs_of in H0. eapply gmultiset_elem_of_dom in H0. exact H0.
    * unfold outputs_of. simpl. eapply gmultiset_elem_of_dom. eapply gmultiset_elem_of_disj_union. right.
      assert (c ⋉ d ∈ outputs_of (g p2)). eapply Hp. simpl. auto with arith. exact H1.
      unfold outputs_of in H0. eapply gmultiset_elem_of_dom in H0. exact H0.
    * unfold outputs_of. simpl. eapply gmultiset_elem_of_dom. 
      assert (c ⋉ d ∈ outputs_of (p1)). eapply Hp. simpl. auto with arith. exact H1.
      unfold outputs_of in H0. eapply gmultiset_elem_of_dom in H0. assumption.
Qed.

Lemma outputs_of_spec1 (p : proc) (a : TypeOfActions) (q : proc) : lts p (ActExt (ActOut a)) q
      -> a ∈ outputs_of p.
Proof.
intros. eapply outputs_of_spec1_zero. exists q. assumption.
Qed.

Lemma outputsM_of_spec1_zero (p : States ) (a : TypeOfActions) : {q | ltsM p (ActExt (ActOut a)) q} 
      -> a ∈ outputs_of_State p.
Proof.    
  intros (p' & lts__p).
  dependent destruction lts__p. eapply gmultiset_elem_of_dom. simpl.  multiset_solver.
Qed.

Lemma outputsM_of_spec1 (p : States) (a : TypeOfActions) (q : States) : ltsM p (ActExt (ActOut a)) q
      -> a ∈ outputs_of_State p.
Proof.
intros. eapply outputsM_of_spec1_zero. exists q. assumption.
Qed.

Definition ltsM_set_output (S : States) (a : TypeOfActions) : gset States:=
match S with
  | ❲ M  , P ❳ =>  if (decide (a ∈ M)) then {[ ❲ gmultiset_difference M {[+ a +]} , P ❳ ]} else ∅
end.


Fixpoint lts_set_input (p : proc) (a : TypeOfActions) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1 := lts_set_input p1 a in
      let ps2 := lts_set_input p2 a in
      list_to_set (map (fun p => p ‖ p2) (elements ps1)) ∪ list_to_set (map (fun p => p1 ‖ p) (elements ps2))
  | pr_var _ => ∅
  | rec _ • _ => ∅ 
  | If _ Then _ Else _ => ∅
  | 𝟘 => ∅
  | g gp => lts_set_input_g gp a  
  end
with
lts_set_input_g (g0 : gproc) (a : TypeOfActions) : gset proc :=
  match g0 with
  | δ => ∅
  | ① => ∅
  | c ? p => if decide(Channel_of a = c) then {[ p^(Data_of a) ]} else ∅
  | c ! v • p => ∅
  | t • p => ∅
  | g1 + g2 => lts_set_input_g g1 a ∪ lts_set_input_g g2 a
  | p1 ; p2 => 
      let ps1 := lts_set_input p1 a in
      list_to_set (map (fun p => (g (p ; p2))) (elements ps1))
  end.

Definition ltsM_set_input (S : States) (a : TypeOfActions) : gset States:=
match S with
  | ❲ M  , P ❳ =>  let ps1 := lts_set_input P a in
                    list_to_set (map (fun p => ❲ M  , p ❳) (elements ps1))
end.

Fixpoint lts_set_output (p : proc) (a : TypeOfActions) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1 := lts_set_output p1 a in
      let ps2 := lts_set_output p2 a in
      list_to_set (map (fun p => p ‖ p2) (elements ps1)) ∪ list_to_set (map (fun p => p1 ‖ p) (elements ps2))
  | pr_var _ => ∅
  | rec _ • _ => ∅ 
  | If _ Then _ Else _ => ∅
  | 𝟘 => ∅
  | g gp => lts_set_output_g gp a  
  end
with

lts_set_output_g (g0 : gproc) (a : TypeOfActions) : gset proc :=
  match g0 with
  | δ => ∅
  | ① => ∅
  | c ? p => ∅
  | c ! v • p => if decide(a = (c ⋉ v)) then {[ p ]} else ∅
  | t • p => ∅
  | g1 + g2 => lts_set_output_g g1 a ∪ lts_set_output_g g2 a
  | p1 ; p2 => 
      let ps1 := lts_set_output p1 a in
      list_to_set (map (fun p => ((g (p ; p2)))) (elements ps1))
  end.

#[global] Instance Skip_Seq_dec : forall p, Decision (SKIP_SEQ p).
Proof.
intros. 
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p.
- destruct (Hp p1). simpl. auto with arith. 
  destruct (Hp p2). simpl. auto with arith. constructor. constructor ; assumption.
  right. intro. dependent destruction H. contradiction.
  destruct (Hp p2). simpl. auto with arith. right. intro. dependent destruction H. contradiction.
  right. intro. dependent destruction H. contradiction.
- right. intro. inversion H.
- right. intro. inversion H.
- right. intro. inversion H.
- left. constructor.
- right. intro. inversion H.
Qed.

Fixpoint lts_set_tau (p : proc) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1 := lts_set_tau p1 in
      let ps2 := lts_set_tau p2 in
      list_to_set (map (fun p => p ‖ p2) (elements ps1)) ∪ list_to_set (map (fun p => p1 ‖ p) (elements ps2))
  | pr_var _ => ∅
  | rec x • p => {[ pr_subst x p (rec x • p) ]}
  | If C Then A Else B => match (Eval_Eq C) with 
                          | Some true => {[ A ]}
                          | Some false => {[ B ]}
                          | None => ∅
                          end
  | 𝟘 => ∅
  | g gp => lts_set_tau_g gp
end
with
lts_set_tau_g (gp : gproc) : gset proc :=
match gp with
  | δ => ∅
  | ① => ∅
  | c ? p => ∅
  | c ! v • p => ∅
  | t • p => {[ p ]}
  | gp1 + gp2 => lts_set_tau_g gp1 ∪ lts_set_tau_g gp2
  | p1 ; p2 => let ps1 := lts_set_tau p1 in 
               let lps1 := list_to_set (map (fun p => (g (p ; p2))) (elements ps1)) in
               if (decide (SKIP_SEQ p1)) then  {[ p2 ]} else lps1 
end.



Definition ltsM_set_tau (S : States) : gset States:=
match S with
  | ❲ M  , P ❳ =>  
      let ps_tau : gset States := list_to_set (map (fun p => ❲ M  , p ❳) (elements $ lts_set_tau P)) in
      (* let acts1 := outputs_of P in *)
      let ps1 :=
        flat_map (fun a =>
                    map
                      (fun p => ❲ M ⊎ {[+ a +]}  , p ❳)
                      (elements $ lts_set_output P a))
        (elements $ outputs_of P) in
      let ps2 :=
        flat_map (fun a =>
                    map
                      (fun p2 => ❲ (gmultiset_difference M {[+ a +]}) , p2 ❳)
                      ((elements $ lts_set_input P a)))
            (elements $ M)
         in
      list_to_set ps2 ∪ list_to_set ps1 ∪ ps_tau
end.

Lemma lts_set_tau_spec0 p q : q ∈ lts_set_tau p -> lts p τ q.
Proof.
  intro mem. revert mem. revert q. 
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intro p'; intro mem; simpl in mem; try set_solver.
  + eapply elem_of_union in mem. destruct mem.
    ++ eapply elem_of_list_to_set in H.
       eapply elem_of_list_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. constructor.
       apply Hp. simpl. auto with arith. assumption.
    ++ eapply elem_of_list_to_set in H.
       eapply elem_of_list_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. constructor.
       apply Hp. simpl. auto with arith. assumption.
  + assert (p' = pr_subst n p (rec n • p)). set_solver. subst.
    constructor.
  + destruct (decide (Eval_Eq e = Some true)).
      * rewrite e0 in mem. assert (p' = p1). set_solver. rewrite H. constructor. assumption.
      * destruct (decide (Eval_Eq e = Some false)). rewrite e0 in mem. 
        assert (p' = p2). set_solver. rewrite H. constructor. assumption.
        assert (Eval_Eq e = None). destruct (Eval_Eq e). destruct b. exfalso. apply n. reflexivity.
        exfalso. apply n0. reflexivity. reflexivity. rewrite H in mem. set_solver.
  + dependent destruction g0; simpl in mem; try set_solver.
      ++ assert (p' = p). set_solver. subst. constructor.
      ++ eapply elem_of_union in mem. destruct mem. 
        - constructor. apply Hp. simpl. auto with arith. assumption.
        - apply lts_choiceR. apply Hp. simpl. auto with arith. assumption.
      ++ destruct (decide ((SKIP_SEQ p))).
        - assert (p' = p0). set_solver. subst. constructor. assumption.
        - eapply elem_of_list_to_set in mem.
         eapply elem_of_list_fmap in mem as (q' & eq & mem). subst.
         rewrite elem_of_elements in mem. constructor. apply Hp. simpl. auto with arith.
         assumption.
Qed.

Lemma ltsM_set_output_spec0 p a q : q ∈ ltsM_set_output p a -> ltsM p (ActExt (ActOut a)) q.
Proof.
  intro mem.
  dependent destruction p; simpl in mem.
  destruct a.
  - destruct(decide (c ⋉ d ∈ g0)). assert (q = ❲ gmultiset_difference g0 {[+ c ⋉ d +]}, p ❳).
    set_solver. rewrite H. assert (g0 = gmultiset_difference g0 {[+ c ⋉ d +]} ⊎ {[+ c ⋉ d +]}).
    multiset_solver. rewrite H0 at 1. econstructor.
    inversion mem.
Qed.

Lemma ltsM_set_output_spec1 p a q : ltsM p (ActExt $ ActOut a) q -> q ∈ ltsM_set_output p a.
Proof.
  intro l. dependent destruction l. simpl.
  destruct (decide (c ⋉ v ∈ M ⊎ {[+ c ⋉ v +]})).
  assert (gmultiset_difference (M ⊎ {[+ c ⋉ v +]}) {[+ c ⋉ v +]} = M).
  multiset_solver. rewrite <-H at 1. set_solver.
  set_solver.
Qed.

Lemma lts_set_input_spec0 p a q : q ∈ lts_set_input p a -> lts p (ActExt $ ActIn a) q.
Proof.
  intro mem. revert mem. revert a. revert q. 
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intro p'; intro a; intro mem; simpl in mem; try set_solver.
  + eapply elem_of_union in mem. destruct mem.
    ++ eapply elem_of_list_to_set in H.
       eapply elem_of_list_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. constructor.
       apply Hp. simpl. auto with arith. assumption.
    ++ eapply elem_of_list_to_set in H.
       eapply elem_of_list_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. constructor.
       apply Hp. simpl. auto with arith. assumption.
  + dependent destruction g0; simpl in mem; try set_solver.
      ++ destruct (decide (Channel_of a = c)).
         +++ subst. eapply elem_of_singleton_1 in mem. subst. destruct a. simpl. apply lts_input.
         +++ inversion mem.
      ++ eapply elem_of_union in mem. destruct mem. 
        - constructor. apply Hp. simpl. auto with arith. assumption.
        - apply lts_choiceR. apply Hp. simpl. auto with arith. assumption.
      ++ eapply elem_of_list_to_set in mem.
         eapply elem_of_list_fmap in mem as (q' & eq & mem). subst.
         rewrite elem_of_elements in mem. constructor. apply Hp. simpl. auto with arith.
         assumption.
Qed.

Lemma Same_Memory_for_input : forall g0 g1 p p1 a, ❲ g1, p1 ❳ ∈ ltsM_set_input ❲ g0, p ❳ a -> g1 = g0.
Proof.
intros. simpl in H. 
eapply elem_of_list_to_set in H.
eapply elem_of_list_fmap in H as (q' & eq & H). dependent destruction eq.
auto.
Qed.

Lemma Simplification_for_input :  forall g0 g1 p p1 a, ❲ g1, p1 ❳ ∈ ltsM_set_input ❲ g0, p ❳ a 
                                  -> p1 ∈ lts_set_input p a.
Proof.
intros. simpl in H. 
eapply elem_of_list_to_set in H.
eapply elem_of_list_fmap in H as (q' & eq & H). dependent destruction eq.
rewrite elem_of_elements in H.
assumption. 
Qed.

Lemma ltsM_set_input_spec0 p a q : q ∈ ltsM_set_input p a -> ltsM p (ActExt $ ActIn a) q.
Proof.
  intro mem. 
  destruct p. destruct q.
  assert (g1 = g0). eapply Same_Memory_for_input. exact mem. rewrite H.
  apply Simplification_for_input in mem. destruct a.
  econstructor. apply lts_set_input_spec0. assumption.
Qed.

Lemma lts_set_input_spec1 p a q : lts p (ActExt $ ActIn a) q -> q ∈ lts_set_input p a.
Proof.
  intro l. dependent induction l; try set_solver.
  simpl. destruct (decide (c = c)). set_solver. exfalso. apply n. reflexivity.
Qed.

Lemma ltsM_set_input_spec1 p a q : ltsM p (ActExt $ ActIn a) q -> q ∈ ltsM_set_input p a.
Proof.
  intro l. dependent destruction l. apply lts_set_input_spec1 in H. 
  simpl. eapply elem_of_list_to_set. eapply elem_of_list_fmap. exists q. split. auto.
  eapply elem_of_elements. assumption.
Qed.

Lemma lts_set_output_spec0 p a q : q ∈ lts_set_output p a -> lts p (ActExt (ActOut a)) q.
Proof.
  revert a. revert q.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intro q; intro a; intro mem ; simpl in mem; try now inversion mem.
  - eapply elem_of_union in mem as [mem | mem]. 
    * eapply elem_of_list_to_set, elem_of_list_fmap in mem as (q' & eq & mem). subst.
    apply lts_parL. apply Hp. simpl. auto with arith. rewrite elem_of_elements in mem. assumption.
    * eapply elem_of_list_to_set, elem_of_list_fmap in mem as (q' & eq & mem). subst.
    apply lts_parR. apply Hp. simpl. auto with arith. rewrite elem_of_elements in mem. assumption.
  - dependent destruction g0; try now inversion mem; simpl in mem.
    case (TypeOfActions_dec a (c ⋉ d)) in mem.
    + rewrite e. rewrite e in mem. simpl in mem.
      destruct (decide (c ⋉ d = c ⋉ d)). subst. assert (q = p). set_solver.
      rewrite H. apply lts_output. exfalso. set_solver.
    + simpl in mem. destruct (decide (a = c ⋉ d)). exfalso. apply n. assumption. set_solver.
    + simpl in mem. eapply elem_of_union in mem. inversion mem. 
      * constructor.
        apply Hp. simpl. auto with arith. assumption.
      * eapply lts_choiceR.
        apply Hp. simpl. auto with arith. assumption.
    + simpl in mem. eapply elem_of_list_to_set, elem_of_list_fmap in mem as (q' & eq & mem).
      rewrite eq. constructor. apply Hp. simpl. auto with arith. set_solver.
Qed.

Lemma ltsM_set_tau_spec0 p q : q ∈ ltsM_set_tau p -> ltsM p τ q.
Proof.
  revert q. destruct p. revert g0.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  dependent destruction p; intro g' ; intro q ; intro mem ; simpl in mem.
  + eapply elem_of_union in mem. destruct mem as [mem1 | mem2].
    ++ eapply elem_of_union in mem1.
          destruct mem1 as [mem1 | mem2].
          eapply elem_of_list_to_set, elem_of_list_In, in_flat_map in mem1 as (t' & eq & mem1); subst.
          eapply elem_of_list_In, elem_of_list_fmap in mem1 as (t1 & eq' & mem1). subst.
          rewrite elem_of_elements in mem1. eapply elem_of_union in mem1.
          destruct mem1.
          - eapply elem_of_list_to_set in H. eapply elem_of_list_fmap in H. 
            destruct H. destruct H. rewrite elem_of_elements in H0.
            eapply lts_set_input_spec0 in H0. destruct t'. econstructor. 
            instantiate (1 := p1 ‖ p2). instantiate (1 := d). instantiate (1 := c).
            eapply elem_of_list_In in eq. 
            eapply gmultiset_elem_of_elements in eq.
            assert (g' = gmultiset_difference g' {[+ c ⋉ d +]} ⊎ {[+ c ⋉ d +]}).
            multiset_solver.
            rewrite H1 at 1. econstructor. instantiate (1 := g'). subst. constructor. constructor. assumption.
          - eapply elem_of_list_to_set in H. eapply elem_of_list_fmap in H. 
            destruct H. destruct H. rewrite elem_of_elements in H0.
            eapply lts_set_input_spec0 in H0. destruct t'. econstructor. 
            instantiate (1 := p1 ‖ p2). instantiate (1 := d). instantiate (1 := c).
            eapply elem_of_list_In in eq. 
            eapply gmultiset_elem_of_elements in eq.
            assert (g' = gmultiset_difference g' {[+ c ⋉ d +]} ⊎ {[+ c ⋉ d +]}).
            multiset_solver.
            rewrite H1 at 1. econstructor. instantiate (1 := g'). subst. constructor. constructor. assumption.
          - eapply elem_of_list_to_set, elem_of_list_In, in_flat_map in mem2 as (t' & eq & mem1); subst.
            eapply elem_of_list_In, elem_of_list_fmap in mem1 as (t1 & eq' & mem1). subst.
            rewrite elem_of_elements in mem1. eapply elem_of_union in mem1. destruct mem1.
              * rename H into mem1.
                eapply elem_of_list_to_set in mem1. eapply elem_of_list_fmap in mem1.
                destruct mem1. destruct H. rewrite elem_of_elements in H0.
                eapply lts_set_output_spec0 in H0.
                subst. destruct t'. eapply ltsM_send.
                constructor. assumption.
              * rename H into mem1.
                eapply elem_of_list_to_set in mem1. eapply elem_of_list_fmap in mem1.
                destruct mem1. destruct H. rewrite elem_of_elements in H0.
                eapply lts_set_output_spec0 in H0.
                subst. destruct t'. eapply ltsM_send.
                constructor. assumption.
     ++ eapply elem_of_list_to_set, elem_of_list_fmap in mem2 as (p' & eq & mem2); subst.
        rewrite elem_of_elements in mem2. eapply elem_of_union in mem2. destruct mem2.
        * rename H into mem1. eapply elem_of_list_to_set, elem_of_list_fmap in mem1 as (p & eq & mem1); subst.
          rewrite elem_of_elements in mem1. eapply lts_set_tau_spec0 in mem1.
          constructor. constructor. assumption.
        * rename H into mem2. eapply elem_of_list_to_set, elem_of_list_fmap in mem2 as (p & eq & mem2); subst.
          rewrite elem_of_elements in mem2. eapply lts_set_tau_spec0 in mem2.
          constructor. constructor. assumption.
   + set_solver.
   + eapply elem_of_union in mem. destruct mem. 
      ++ set_solver.
      ++ rename H into mem. eapply elem_of_list_to_set, elem_of_list_fmap in mem as (p' & eq & mem); subst.
         rewrite elem_of_elements in mem. assert (p' = pr_subst n p (rec n • p)).
         set_solver. subst. constructor. constructor.
   + eapply elem_of_union in mem. destruct mem. 
      ++ set_solver.
      ++ rename H into mem. eapply elem_of_list_to_set , elem_of_list_fmap in mem as (p' & eq & mem); subst.
         rewrite elem_of_elements in mem. 
         destruct (decide (Eval_Eq e = Some true)). 
         rewrite e0 in mem. assert (p' = p1). 
         set_solver. subst. constructor. constructor.  assumption. 
         destruct (decide (Eval_Eq e = Some false)).
         rewrite e0 in mem. assert (p' = p2). 
         set_solver. subst. constructor. constructor.  assumption. 
         assert (Eval_Eq e = None). destruct (Eval_Eq e). destruct b. exfalso. apply n. reflexivity.
         exfalso. apply n0. reflexivity. reflexivity. rewrite H in mem. set_solver.
    + set_solver.
    + eapply elem_of_union in mem. destruct mem as [mem1 | mem3].
      eapply elem_of_union in mem1. destruct mem1 as [mem1 | mem2].
      * eapply elem_of_list_to_set, elem_of_list_In, in_flat_map in mem1 as (t' & eq & mem1); subst.
        eapply elem_of_list_In, elem_of_list_fmap in mem1 as (t1 & eq' & mem1). subst.
        rewrite elem_of_elements in mem1. eapply (lts_set_input_spec0 g0 t')  in mem1.
        destruct t'.
        econstructor. instantiate (1 := g0). instantiate (1 := d). instantiate (1 := c).
        assert (g' = gmultiset_difference g' {[+ c ⋉ d +]} ⊎  {[+ c ⋉ d +]}).
        eapply elem_of_list_In in eq. rewrite gmultiset_elem_of_elements in eq.
        multiset_solver. rewrite H at 1. econstructor. econstructor.
        assumption.
      * eapply elem_of_list_to_set, elem_of_list_In, in_flat_map in mem2 as (t' & eq & mem2); subst.
        eapply elem_of_list_In, elem_of_list_fmap in mem2 as (t1 & eq' & mem2). subst.
        rewrite elem_of_elements in mem2. eapply (lts_set_output_spec0 g0 t') in mem2.
        destruct t'.
        econstructor. assumption.
      * eapply elem_of_list_to_set, elem_of_list_fmap in mem3 as (t' & eq & mem3); subst.
        rewrite elem_of_elements in mem3. eapply (lts_set_tau_spec0 g0) in mem3.
        econstructor. assumption.
Qed.

Lemma Transition_and_SKIP : forall p a q, lts p a q -> ~ SKIP_SEQ p.
Proof.
intros. dependent induction H ; intro; try now inversion H.
* inversion H0. subst. contradiction.
* inversion H0. subst. contradiction.
Qed.

Lemma lts_set_tau_spec1 p q : lts p τ q -> q ∈ lts_set_tau p.
Proof.
  intro l. dependent induction l; simpl; try set_solver.
  - rewrite H. set_solver. 
  - rewrite H. set_solver. 
  - eapply decide_True in H.  rewrite H. set_solver. 
  - eapply Transition_and_SKIP in l. eapply decide_False in l.  rewrite l. set_solver. 
Qed.

Lemma lts_set_output_spec1 p a q : lts p (ActExt $ ActOut a) q -> q ∈ lts_set_output p a.
Proof.
  intro l. dependent induction l; try set_solver.
  simpl. destruct (decide (c ⋉ v = c ⋉ v)). set_solver. exfalso. apply n. reflexivity.
Qed.

Lemma ltsM_set_tau_spec1 p q : ltsM p τ q -> q ∈ ltsM_set_tau p.
Proof. 
  intro l. dependent induction l ; simpl. 
  - eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    eapply elem_of_list_fmap. exists q. split. auto.
    apply elem_of_elements. eapply lts_set_tau_spec1. assumption.
  - eapply elem_of_union. left.
    eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    
    rewrite elem_of_list_In. rewrite in_flat_map. exists (c ⋉ v).
    split. 
    + eapply elem_of_list_In, elem_of_elements.
      eapply (outputs_of_spec1 p (c ⋉ v)). eauto.
    + eapply elem_of_list_In. eapply elem_of_list_fmap. exists q.
      split. auto. eapply elem_of_elements.
      eapply lts_set_output_spec1. assumption.
  - eapply elem_of_union. left.
    eapply elem_of_union. left.
    eapply elem_of_list_to_set.
    rewrite elem_of_list_In. rewrite in_flat_map. exists ((c ⋉ v)). 
    split. eapply elem_of_list_In. eapply gmultiset_elem_of_elements. 
    dependent destruction l1. multiset_solver.
    eapply elem_of_list_In. eapply elem_of_list_fmap.
    exists (S2). split.
    dependent destruction l1. 
    assert (gmultiset_difference (M2 ⊎ {[+ c ⋉ v +]}) {[+ c ⋉ v +]} = M2). multiset_solver.
    rewrite H at 1. auto.
    eapply elem_of_elements.
    dependent destruction l2.
    eapply lts_set_input_spec1. assumption. 
Qed.

Definition ltsM_set (S : States) (α : Act TypeOfActions): gset States :=
  match α with
  | τ => ltsM_set_tau S
  | ActExt (ActIn a) => ltsM_set_input S a
  | ActExt (ActOut a) => ltsM_set_output S a
  end.

Lemma ltsM_set_spec0 p α q : q ∈ ltsM_set p α -> ltsM p α q.
Proof.
  destruct α as [[a|a]|].
  - now eapply ltsM_set_input_spec0.
  - now eapply ltsM_set_output_spec0.
  - now eapply ltsM_set_tau_spec0.
Qed.

Lemma ltsM_set_spec1 p α q : ltsM p α q -> q ∈ ltsM_set p α.
Proof.
  destruct α as [[a|a]|].
  - now eapply ltsM_set_input_spec1.
  - now eapply ltsM_set_output_spec1.
  - now eapply ltsM_set_tau_spec1.
Qed.

Definition states_stable p α := ltsM_set p α = ∅.

Lemma ltsM_dec p α q : { ltsM p α q } + { ~ ltsM p α q }.
Proof.
  destruct (decide (q ∈ ltsM_set p α)).
  - eapply ltsM_set_spec0 in e. eauto.
  - right. intro l. now eapply ltsM_set_spec1 in l.
Qed.

Lemma states_stable_dec p α : Decision (states_stable p α).
Proof. destruct (decide (ltsM_set p α = ∅)); [ left | right ]; eauto. Qed.

Lemma gset_nempty_ex (g : gset States) : g ≠ ∅ -> {p | p ∈ g}.
Proof.
  intro n. destruct (elements g) eqn:eq.
  + destruct n. eapply elements_empty_iff in eq. set_solver.
  + exists s. eapply elem_of_elements. rewrite eq. set_solver.
Qed.

(* Making VACCS Instance of each class *)

#[global] Program Instance VACCS_Label : Label TypeOfActions.
  (* {| label_eqdec := TypeOfActions_dec ;
     label_countable := TypeOfActions_countable 
  |}. *)

#[global] Program Instance VACCS_Lts : Lts States TypeOfActions. 
Next Obligation. intros. exact (ltsM X X0 X1). Defined. (* lts_step x ℓ y  := ltsM x ℓ y *)
Next Obligation. intros. exact (ltsM_dec a α b). Defined. (* lts_state_eqdec := proc_dec *)
Next Obligation. intros. exact (outputs_of_State X). Defined. (* lts_outputs S := outputs_of_State S *)
Next Obligation. intros. apply (outputsM_of_spec1 p1 x p2). apply H. Defined. (* lts_outputsM_spec1 p1 x p2 := outputs_of_spec1 p1 x p2 *)
Next Obligation. intros. apply (outputs_of_spec2 p1 x). assumption. Defined. (* lts_outputs_spec2 p1 x := outputs_of_spec2 p1 x *)
Next Obligation. intros. exact (states_stable X X0). Defined. (* lts_stable p α := states_stable p α *)
Next Obligation. intros. exact (states_stable_dec p α). Defined. (* lts_stable_decidable p α := states_stable_dec p α *)
Next Obligation. intros p [[a|a]|]; unfold VACCS_Lts_obligation_6 in *; unfold VACCS_Lts_obligation_1 in *;
        intro hs;eapply gset_nempty_ex in hs as (r & l); eapply ltsM_set_spec0 in l; 
        exists r; assumption. Defined.
Next Obligation.  
        intros p [[a|a]|]; intros (q & mem); intro eq; eapply ltsM_set_spec1 in mem; set_solver.
Qed.

#[global] Program Instance VACCS_LtsEq : LtsEq States TypeOfActions. 
Next Obligation. exact cgr_states. Defined. (* eq_rel x y  := cgr x y *)
Next Obligation. apply cgr_states_refl. Qed. (* eq_rel_refl p := cgr_refl p *)
Next Obligation. apply cgr_states_symm. Qed. (* eq_symm p q := cgr_symm p q *)
Next Obligation. eapply cgr_states_trans. Qed. (* eq_trans x y z:= cgr_trans x y z *)
Next Obligation. eapply CongruenceStates_Respects_Transition. Qed. (* eq_spec p q α := CongruenceStates_Respects_Transition p q α *)

#[global] Program Instance VACCS_LtsOba : LtsOba States TypeOfActions.
Next Obligation. exact moutputs_of_State. Defined. (* lts_oba_mo p := moutputs_of p  *)
Next Obligation.
    intros. simpl. unfold VACCS_LtsOba_obligation_1. unfold VACCS_Lts_obligation_3. unfold outputs_of_State.
    now rewrite gmultiset_elem_of_dom.
  Qed.
Next Obligation.
    intros. unfold VACCS_LtsOba_obligation_1. simpl. unfold outputs_of_State.
    now eapply mo_spec.
  Qed.
Next Obligation. exact OBA_with_FB_First_Axiom. Qed. (* lts_oba_output_commutativity p q r a α := OBA_with_FB_First_Axiom p q r a α *)
Next Obligation. exact OBA_with_FB_Second_Axiom. Qed. (* lts_oba_output_confluence p q1 q2 a μ := OBA_with_FB_Second_Axiom p q1 q2 a μ *)
Next Obligation. exact OBA_with_FB_Fifth_Axiom. Qed. (* lts_oba_output_tau p q1 q2 a := OBA_with_FB_Fifth_Axiom p q1 q2 a *)
Next Obligation. exact OBA_with_FB_Third_Axiom. Qed. (* lts_oba_output_deter p1 p2 p3 a := OBA_with_FB_Third_Axiom p1 p2 p3 a *)
Next Obligation. exact ExtraAxiom. Qed. (* lts_oba_output_deter_inv p1 p2 q1 q2 a := ExtraAxiom p1 p2 q1 q2 a *)

#[global] Program Instance VACCS_LtsObaFB : LtsObaFB States TypeOfActions :=
  {| lts_oba_fb_feedback p1 p2 p3 a := OBA_with_FB_Fourth_Axiom p1 p2 p3 a |}.

