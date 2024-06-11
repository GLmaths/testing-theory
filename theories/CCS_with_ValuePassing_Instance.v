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

(* ChannelType est le type des canaux, par exemple des chaînes de caractères*)
(* ValueType est le type des données transmises, par exemple des entiers, des chaînes de caractères, des programmes (?) *)
Inductive ExtAct (Channel Data : Type) :=
| ActIn : Channel -> Data -> ExtAct Channel Data
| ActOut : Channel -> Data -> ExtAct Channel Data
.

Arguments ActIn {_} {_} _ _.
Arguments ActOut {_} {_} _ _.

Inductive Act (Channel Data : Type) :=
| ActExt (μ: ExtAct Channel Data)
| τ
.
Arguments ActExt {_} {_} _.
Arguments τ {_} {_}.


Coercion ActExt : ExtAct >-> Act.

Context (Channel Value : Type).
(*Exemple : Definition Channel := string.*)
(*Exemple : Definition Value := nat.*)


Inductive Data :=
| cst : Value -> Data
| bvar : nat -> Data. (* variable as De Bruijn indices *) 

Coercion cst : Value >-> Data.
Coercion bvar : nat >-> Data.


Inductive Equation (A : Type) : Type :=
| Equality : A -> A -> Equation A.

Arguments  Equality {_} _ _.

Notation "x == y" := (Equality x y) (at level 50).


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
(*The Guards*)
| g : gproc -> proc

with gproc : Type :=
(* The Success operation*)
| gpr_success : gproc
(* The Process that does nothing*)
| gpr_nil : gproc
(*An input is a name of a channel, an input variable, followed by a process*)
| gpr_input : Channel ->  proc -> gproc
(*An output is a name of a channel, an ouput value, followed by a process*)
| gpr_output : Channel -> Data -> proc -> gproc
(*A tau action : does nothing *)
| gpr_tau : proc -> gproc
(* To choose between two processes*)
| gpr_choice : gproc -> gproc -> gproc
.

Coercion pr_var : nat >-> proc.
Coercion g : gproc >-> proc.


(*Some notation to simplify the view of the code*)

Notation "①" := (gpr_success).
Notation "⓪" := (gpr_nil).
Notation "'rec' x '•' p" := (pr_rec x p) (at level 50).
Notation "P + Q" := (gpr_choice P Q).
Notation "P ‖ Q" := (pr_par P Q) (at level 50).
Notation "c ! v • P" := (gpr_output c v P) (at level 50).
Notation "c ? x • P" := (gpr_input c P) (at level 50).
Notation "'t' • P" := (gpr_tau P) (at level 50).
Notation "'If' C 'Then' P 'Else' Q" := (pr_if_then_else C P Q)
(at level 200, right associativity, format
"'[v   ' 'If'  C '/' '[' 'Then'  P  ']' '/' '[' 'Else'  Q ']' ']'").

(*Definition of the Substitution *)
Definition subst_Data (k : nat) (X : Data) (Y : Data) : Data := 
match Y with
| cst v => cst v
(*| fvarV i => fvarV i*)
| bvar i => if (decide(i = k)) then X else bvar i
end.

Definition subst_in_Equation (k : nat) (X : Data) (E : Equation Data) : Equation Data :=
match E with 
| D1 == D2 => (subst_Data k X D1) == (subst_Data k X D2)
end.


Fixpoint subst_in_proc (k : nat) (X : Data) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (subst_in_proc k X P) ‖ (subst_in_proc k X Q)
| pr_var i => pr_var i
| rec x • P =>  rec x • (subst_in_proc k X P)
| If C Then P Else Q => If (subst_in_Equation k X C) Then (subst_in_proc k X P) Else (subst_in_proc k X Q)
| g M => subst_in_gproc k X M
end

with subst_in_gproc k X M {struct M} : gproc :=
match M with 
| ① => ①
| ⓪ => ⓪
| c ? x • p => c ? x • (subst_in_proc (S k) X p)
| c ! v • p => c ! (subst_Data k X v) • (subst_in_proc k X p)
| t • p => t • (subst_in_proc k X p)
| p1 + p2 => (subst_in_gproc k X p1) + (subst_in_gproc k X p2)
end.


Notation "t1 ^ x1" := (subst_in_proc 0 x1 t1).

(* Substitution for the Recursive Variable *)
Fixpoint pr_subst (id : nat) (p : proc) (q : proc) : proc :=
  match p with 
  | p1 ‖ p2 => (pr_subst id p1 q) ‖ (pr_subst id p2 q) 
  | pr_var id' => if decide (id = id') then q else p
  | rec id' • p => if decide (id = id') then p else rec id' • (pr_subst id p q)
  | If C Then P Else Q => If C Then (pr_subst id P q) Else (pr_subst id Q q)
  | g gp => g (gpr_subst id gp q)
end

with gpr_subst id p q {struct p} := match p with
| ① => ①
| ⓪ => ⓪
| c ? x • p => c ? x • (pr_subst id p q)
| c ! v • p => c ! v • (pr_subst id p q)
| t • p => t • (pr_subst id p q)
| p1 + p2 => (gpr_subst id p1 q) + (gpr_subst id p2 q)
end.


(* The Labelled Transition System (LTS-transition) *)
Inductive lts : proc-> (Act Channel Data) -> proc -> Prop :=
(*The Input and the Output*)
| lts_input : forall {c v P},
    lts (c ? x • P) (ActIn c (cst v)) (P^v)
| lts_output : forall {c v P},
    lts (c ! (cst v) • P) (ActOut c (cst v)) P

(*The actions Tau*)
| lts_tau : forall {P},
    lts (t • P) τ P 
| lts_recursion : forall {x P},
    lts (rec x • P) τ (pr_subst x P (rec x • P))
| lts_ifOne : forall p q x y, x = y -> 
    lts (If (x == y) Then p Else q) τ p
| lts_ifZero : forall {p q x y}, ~(x = y) -> 
    lts (If (x == y) Then p Else q) τ q

(* Communication of a channel output and input that have the same name*)
| lts_comL : forall {c v p1 p2 q1 q2},
    lts p1 (ActOut c (cst v)) p2 ->
    lts q1 (ActIn c (cst v)) q2 ->
    lts (p1 ‖ q1) τ (p2 ‖ q2) 
| lts_comR : forall {c v p1 p2 q1 q2},
    lts p1 (ActOut c (cst v)) p2 ->
    lts q1 (ActIn c (cst v)) q2 ->
    lts (q1 ‖ p1) τ (q2 ‖ p2)

(*The decoration for the transition system...*)
(*...for the parallele*)   
| lts_parL : forall {α p1 p2 q},
    lts p1 α p2 ->
    lts (p1 ‖ q) α (p2 ‖ q)
| lts_parR : forall {α p q1 q2}, 
    lts q1 α q2 ->
    lts (p ‖ q1) α (p ‖ q2)
(*...for the sum*)
| lts_choiceL : forall {p1 p2 q α},
    lts (g p1) α q -> 
    lts (p1 + p2) α q
| lts_choiceR : forall {p1 p2 q α},
    lts (g p2) α q -> 
    lts (p1 + p2) α q
.

Fixpoint size (p : proc) := 
  match p with
  | p ‖ q  => S (size p + size q)
  | pr_var _ => 1
  | If C Then p Else q => S (size p + size q)
  | rec x • p => S (size p)
  | g p => gsize p
  end

with gsize p :=
  match p with
  | ① => 1
  | ⓪ => 0
  | c ? x • p => S (size p)
  | c ! v • p => S (size p)
  | t • p => S (size p)
  | p + q => S (gsize p + gsize q)
end.

#[global] Hint Constructors lts:ccs.

Reserved Notation "p ≡ q" (at level 70).

(*Naïve definition of a relation ≡ that will become a congruence ≡* by transitivity*)
Inductive cgr_step : proc -> proc -> Prop :=
(*  Reflexivity of the Relation ≡  *)
| cgr_refl_step : forall p, p ≡ p

(* Rules for the Parallèle *)
| cgr_par_nil_step : forall p, 
    p ‖ ⓪ ≡ p
| cgr_par_nil_rev_step : forall p,
    p ≡ p ‖ ⓪
| cgr_par_com_step : forall p q,
    p ‖ q ≡ q ‖ p
| cgr_par_assoc_step : forall p q r,
    (p ‖ q) ‖ r ≡ p ‖ (q ‖ r)
| cgr_par_assoc_rev_step : forall p q r,
    p ‖ (q  ‖ r) ≡ (p ‖ q) ‖ r

(* Rules for the Summation *)
| cgr_choice_nil_step : forall p,
    cgr_step (p + ⓪) p
| cgr_choice_nil_rev_step : forall p,
    cgr_step (g p) (p + ⓪)
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
    cgr_step (c ? x • p) (c ? x • q)
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
.


#[global] Hint Constructors cgr_step:cgr_step_structure.

Infix "≡" := cgr_step (at level 70).


(* The relation ≡ is an reflexive*)
#[global] Instance cgr_refl_step_is_refl : Reflexive cgr_step.
Proof. intro. apply cgr_refl_step. Qed.
(* The relation ≡ is symmetric*)
#[global] Instance cgr_symm_step : Symmetric cgr_step.
Proof. intros p q hcgr. induction hcgr; econstructor ; eauto.
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
#[global] Instance cgr_is_eq_rel  : Equivalence cgr.
Proof. repeat split.
       + apply cgr_refl.
       + apply cgr_symm.
       + apply cgr_trans.
Qed.


(*the relation ≡* respects all the rules that ≡ respected*)
Lemma cgr_par_nil : forall p, p ‖ ⓪ ≡* p.
Proof.
constructor.
apply cgr_par_nil_step.
Qed.
Lemma cgr_par_nil_rev : forall p, p ≡* p ‖ ⓪.
Proof.
constructor.
apply cgr_par_nil_rev_step.
Qed.
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
Lemma cgr_choice_nil : forall p, p + ⓪ ≡* p.
Proof.
constructor.
apply cgr_choice_nil_step.
Qed.
Lemma cgr_choice_nil_rev : forall p, (g p) ≡* p + ⓪.
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
Lemma cgr_input : forall c p q, p ≡* q -> (c ? x • p) ≡* (c ? x • q).
Proof.
intros.
dependent induction H. 
* constructor. apply cgr_input_step. auto.
* eauto with cgr_eq.
Qed.
Lemma cgr_output : forall c v p q, p ≡* q -> (c ! v • p) ≡* (c ! v • q).
Proof.
intros. dependent induction H. 
constructor.
apply cgr_output_step. exact H. eauto with cgr_eq.
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
Lemma cgr_choice : forall p q r, g p ≡* g q -> p + r ≡* q + r.
Proof.
intros. dependent induction H. 
constructor.
apply cgr_choice_step. exact H. admit. (* again and again *)
Admitted.


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


#[global] Hint Resolve cgr_par_nil cgr_par_nil_rev cgr_par_nil_rev cgr_par_com cgr_par_assoc 
cgr_par_assoc_rev cgr_choice_nil cgr_choice_nil_rev cgr_choice_com cgr_choice_assoc 
cgr_choice_assoc_rev cgr_recursion cgr_tau cgr_input cgr_output cgr_par cgr_choice 
cgr_refl cgr_symm cgr_trans:cgr.


Lemma Congruence_Respects_Substitution : forall p q v k, p ≡* q -> (subst_in_proc k v p) ≡* (subst_in_proc k v q).
Proof.
intros. revert k. revert v. dependent induction H. 
* dependent induction H.
  - reflexivity.
  - eauto with cgr.
  - eauto with cgr.
  - simpl. eauto with cgr.
  - simpl. eauto with cgr.
  - simpl. eauto with cgr.
  - simpl. eauto with cgr.
  - simpl. eauto with cgr.
  - simpl. eauto with cgr.
  - simpl. eauto with cgr.
  - simpl. eauto with cgr.
  - simpl. eauto with cgr.
  - simpl. eauto with cgr.
  - simpl. intros. apply cgr_input. apply IHcgr_step. 
  - simpl. eauto with cgr.
  - simpl. eauto with cgr.
  - simpl. intros. apply cgr_if_left.  auto. 
  - simpl. intros. apply cgr_if_right. auto.
  - simpl. eauto with cgr.
* eauto with cgr.
Qed.


(* Substition lemma, needed to contextualise the equivalence *)
Lemma cgr_subst1 p q q' x : q ≡* q' → pr_subst x p q ≡* pr_subst x p q'.
Proof.
(* Induction on the size of p*)
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p.
  - simpl. intro. apply cgr_fullpar.
    apply Hp. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ. exact H. 
    apply Hp. simpl. rewrite <-Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply Nat.lt_0_succ. exact H.
  - simpl. intro. destruct (decide (x = n)). exact H. reflexivity.
  - simpl. intro. destruct (decide (x = n)). reflexivity. apply cgr_recursion. apply Hp. simpl. auto. exact H.
  - simpl. intro. apply cgr_full_if.
    apply Hp. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ. exact H. 
    apply Hp. simpl. rewrite <-Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply Nat.lt_0_succ. exact H.  
  - destruct g0.
    * intros. simpl. reflexivity.
    * intros. simpl. reflexivity.
    * intros. simpl. apply cgr_input. apply Hp. simpl. auto. auto.
    * intros. simpl. apply cgr_output. apply Hp. simpl. auto. auto.
    * intros. simpl. apply cgr_tau. apply Hp. simpl. auto. auto.
    * intros. simpl. apply cgr_fullchoice. 
      assert (pr_subst x (g g0_1) q ≡* pr_subst x (g g0_1) q'). apply Hp. simpl. auto with arith. auto.
      auto. assert (pr_subst x (g g0_2) q ≡* pr_subst x (g g0_2) q'). apply Hp. simpl. auto with arith. auto.
      auto. 
Qed.
(* ≡ respects the substitution of his variable*)
Lemma cgr_step_subst2 : forall p p' q x, p ≡ p' → pr_subst x p q ≡ pr_subst x p' q.
Proof.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros p' q n hcgr ; inversion hcgr; try auto; try (exact H).
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - simpl. destruct (decide (n = x)). auto. constructor. apply Hp. subst. simpl. auto.  exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H. 
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H. 
  - simpl. constructor. apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H.
  - simpl. constructor. apply Hp. subst. simpl. rewrite <-Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply Nat.lt_0_succ.
    exact H.
  - simpl. constructor. apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H.
  - simpl. apply cgr_choice_step. 
    assert (pr_subst n (g p1) q ≡ pr_subst n (g q1) q). apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. 
    apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H. exact H2.
Qed.

(* ≡* respects the substitution of his variable *)
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


(* State Transition System (STS-reduction) *)
Inductive sts : proc -> proc -> Prop :=
(*The axiomes*)
(* Communication of channels output and input that have the same name *)
| sts_com : forall {c v p1 g1 p2 g2}, (*Well_Defined_Input_in 0 (((c ! (cst v) • p1) + g1) ‖ ((c ? x • p2) + g2)) ->*)
    sts (((c ! (cst v) • p1) + g1) ‖ ((c ? x • p2) + g2)) (p1 ‖ (p2 ^ v))
(* Nothing more , something less *)
| sts_tau : forall {p g}, (* Well_Defined_Input_in 0 (((t • p) + g)) -> *)
    sts ((t • p) + g) p
(* Resursion *)
| sts_recursion : forall {x p}, (* Well_Defined_Input_in 0 (rec x • p) -> *)
    sts (rec x • p) (pr_subst x p (rec x • p))
(*If Yes*)
| sts_ifOne : forall {p q v v'}, v = v' -> (*Well_Defined_Input_in 0 (If (v == v') Then p Else q) ->*)
    sts (If (v == v') Then p Else q) p
(*If No*)
| sts_ifZero : forall {p q v v'}, ~(v = v') -> (*Well_Defined_Input_in 0 (If (v == v') Then p Else q) ->*)
    sts (If (v == v') Then p Else q) q

(* The left parallele respect the Reduction *)
| sts_par : forall {p1 p2 q}, (* Well_Defined_Input_in 0 q ->*)
    sts p1 p2 ->
    sts (p1 ‖ q) (p2 ‖ q)

(*The Congruence respects the Reduction *)
| sts_cong : forall {p1 p2 q2 q1},
    p1 ≡* p2 -> sts p2 q2 -> q2 ≡* q1 -> sts p1 q1
.

#[global] Hint Constructors sts:ccs.


(* For the (STS-reduction), the reductible terms and reducted terms are pretty all the same, up to ≡* *)
Lemma ReductionShape : forall P Q, sts P Q ->
((exists c v P1 P2 G1 G2 S, ((P ≡* (((c ! (cst v) • P1) + G1) ‖ ((c ? x • P2) + G2)) ‖ S)) /\ (Q ≡*((P1 ‖ (P2^v)) ‖ S)))
\/ (exists P1 G1 S, (P ≡* (((t • P1) + G1) ‖ S)) /\ (Q ≡* (P1 ‖ S)))
\/ (exists n P1 S, (P ≡* ((rec n • P1) ‖ S)) /\ (Q ≡* (pr_subst n P1 (rec n • P1) ‖ S)))
\/ (exists P1 P0 S v, (P ≡* ((If (v == v) Then P1 Else P0) ‖ S)) /\ (Q ≡* P1 ‖ S))
\/ (exists P1 P0 S v v', (P ≡* ((If (v == v') Then P1 Else P0) ‖ S)) /\ (Q ≡* P0 ‖ S) /\ ~(v = v'))
).
Proof.
intros P Q Transition.
induction Transition.
  - left. exists c. exists v. exists p1. exists p2. exists g1. exists g2. exists (⓪). split; apply cgr_par_nil_rev.
  - right. left. exists p. exists g0. exists ⓪. split; apply cgr_par_nil_rev.
  - right. right. left. exists x. exists p. exists ⓪. split; apply cgr_par_nil_rev.
  - right. right. right. left. exists p. exists q. exists ⓪. exists v. rewrite H.  split;apply cgr_par_nil_rev.
  - right. right. right. right. exists p. exists q. exists ⓪. exists v. exists v'. split. apply cgr_par_nil_rev.
    split. apply cgr_par_nil_rev. auto.
  - destruct IHTransition as [IH|[IH|[IH|[IH |IH]]]];  decompose record IH. 
    * left. exists x. exists x0. exists x1. exists x2. exists x3. exists x4. exists (x5 ‖ q). split.
        ** apply transitivity with (((((x ! x0 • x1) + x3) ‖ ((x ? l • x2) + x4)) ‖ x5) ‖ q). apply cgr_par. auto. apply cgr_par_assoc.
        ** apply transitivity with (((x1 ‖ x2^x0) ‖ x5) ‖ q). apply cgr_par. auto.  apply cgr_par_assoc. 
    * right. left. exists x. exists x0. exists (x1 ‖ q). split.
        ** apply transitivity with (((t • x + x0) ‖ x1) ‖ q). apply cgr_par. auto. apply cgr_par_assoc.
        ** apply transitivity with (x ‖ (x1) ‖ q). apply cgr_par. auto. apply cgr_par_assoc.
    * right. right. left. exists x. exists x0. exists (x1 ‖ q). split. 
        ** apply transitivity with ((rec x • x0 ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
        ** apply transitivity with ((pr_subst x x0 (rec x • x0) ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
    * right. right. right. left. exists x. exists x0. exists (x1 ‖ q). exists x2. split.
        ** apply transitivity with (((If (x2 == x2) Then x Else x0) ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
        ** apply transitivity with ((x ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
    * right. right. right. right. exists x. exists x0. exists (x1 ‖ q). exists x2. exists x3. split.
        ** apply transitivity with (((If (x2 == x3) Then x Else x0) ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
        ** split. apply transitivity with ((x0 ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc. auto.
  - destruct IHTransition as [IH|[IH|[IH|[IH |IH]]]]; decompose record IH. 
    * left. exists x. exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. split. apply cgr_trans with p2. exact H. exact H2.
      apply cgr_trans with q2. apply cgr_symm. exact H0. exact H3.
    * right. left. exists x. exists x0. exists x1. split. apply cgr_trans with p2. exact H. exact H2. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
    * right. right. left. exists x. exists x0. exists x1. split. apply cgr_trans with p2. exact H. exact H2. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
    * right. right. right. left. exists x. exists x0. exists x1. exists x2. split. apply cgr_trans with p2. exact H. exact H1. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
    * right. right. right. right. exists x. exists x0. exists x1. exists x2. exists x3. split. apply cgr_trans with p2. exact H. exact H2. split. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H1. auto.
Qed.

(* For the (LTS-transition), the transitable terms and transitted terms, that performs a INPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForInput : forall P Q c v, (lts P (ActIn c v)) Q -> 
(exists P1 G R, ((P ≡* ((c ? x • P1 + G) ‖ R)) /\ (Q ≡* (P1^v ‖ R)) /\ ((exists L,P = (g L)) -> R = ⓪))).
Proof.
intros P Q c v Transition.
 dependent induction Transition.
- exists P. exists ⓪. exists ⓪. split ; try split.
  * apply cgr_trans with ((c ? x • P) + ⓪). apply cgr_trans with (c ? x • P). apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
  * reflexivity.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ q). split; try split.
  * apply cgr_trans with ((((c ? l • x) + x0) ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
  * apply cgr_trans with ((x^v ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ p). split; try split.
  * apply cgr_trans with ((((c ? l • x) + x0) ‖ x1) ‖ p). apply cgr_trans with (q1 ‖ p). apply cgr_par_com. apply cgr_par. assumption. apply cgr_par_assoc.
  * apply cgr_trans with ((x^v ‖ x1) ‖ p). apply cgr_trans with (q2 ‖ p). apply cgr_par_com. apply cgr_par. assumption. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p2). exists ⓪. split ; try split.
  * apply cgr_trans with ((c ? l • x) + (x0 + p2)). apply cgr_trans with (((c ? l • x) + x0) + p2).
    apply cgr_choice. assert (x1 = ⓪). apply H3. exists p1. reflexivity. rewrite H2 in H0. apply transitivity with (((c ? l • x) + x0) ‖ ⓪).
    assumption. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x1 = ⓪). apply H3. exists p1. reflexivity. rewrite H2 in H1. assumption.
  * reflexivity.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p1). exists ⓪. split; try split.
  * apply cgr_trans with ((c ? l • x) + (x0 + p1)). apply cgr_trans with (((c ? l • x) + x0) + p1).
    apply cgr_trans with (p2 + p1). apply cgr_choice_com. apply cgr_choice. assert (x1 = ⓪). apply H3. exists p2. reflexivity.
    apply cgr_trans with (((c ? l • x) + x0) ‖ x1). assumption. rewrite H2. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x1 = ⓪). apply H3. exists p2. reflexivity. rewrite <-H2. assumption. 
  * reflexivity.
Qed.

(* For the (LTS-transition), the transitable terms and transitted terms, that performs a OUPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForOutput : forall P Q c v, (lts P (ActOut c v)) Q -> 
(exists P1 G R, ((P ≡* ((c ! v • P1 + G) ‖ R)) /\ (Q ≡* (P1 ‖ R)) /\ ((exists L,P = (g L)) -> R = ⓪))).
Proof.
intros P Q c v Transition.
 dependent induction Transition.
- exists P. exists ⓪. exists ⓪. split ; try split.
  * apply cgr_trans with ((c ! v0 • P) + ⓪). apply cgr_trans with (c ! v0 • P). apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
  * reflexivity.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ q). split; try split.
  * apply cgr_trans with ((((c ! v • x) + x0) ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
  * apply cgr_trans with ((x ‖ x1) ‖ q). apply cgr_par. assumption. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ p). split; try split.
  * apply cgr_trans with ((((c ! v • x) + x0) ‖ x1) ‖ p). apply cgr_trans with (q1 ‖ p). apply cgr_par_com. apply cgr_par. assumption. apply cgr_par_assoc.
  * apply cgr_trans with ((x ‖ x1) ‖ p). apply cgr_trans with (q2 ‖ p). apply cgr_par_com. apply cgr_par. assumption. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p2). exists ⓪. split ; try split.
  * apply cgr_trans with ((c ! v • x) + (x0 + p2)). apply cgr_trans with (((c ! v • x) + x0) + p2).
    apply cgr_choice. assert (x1 = ⓪). apply H3. exists p1. reflexivity. rewrite H2 in H0. apply transitivity with (((c ! v • x) + x0) ‖ ⓪).
    assumption. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x1 = ⓪). apply H3. exists p1. reflexivity. rewrite H2 in H1. assumption.
  * reflexivity.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p1). exists ⓪. split; try split.
  * apply cgr_trans with ((c ! v • x) + (x0 + p1)). apply cgr_trans with (((c ! v • x) + x0) + p1).
    apply cgr_trans with (p2 + p1). apply cgr_choice_com. apply cgr_choice. assert (x1 = ⓪). apply H3. exists p2. reflexivity.
    apply cgr_trans with (((c ! v • x) + x0) ‖ x1). assumption. rewrite H2. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x1 = ⓪). apply H3. exists p2. reflexivity. rewrite <-H2. assumption.
  * reflexivity.
Qed.



(* For the (LTS-transition), the transitable Guards and transitted terms, that performs a Tau ,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForTauAndGuard : forall P V, ((lts P τ V) /\ (exists L, P = (g L))) -> 
(exists Q M, ((P ≡* ((t • Q) + M))) /\ (V ≡* (Q))).
Proof.
intros P V Hyp. 
destruct Hyp. rename H into Transition. dependent induction Transition.
- exists P. exists ⓪. split. 
  * apply cgr_choice_nil_rev.
  * apply cgr_refl.
- inversion H0. inversion H.
- inversion H0. inversion H1.
- inversion H0. inversion H1.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- destruct (IHTransition (reflexivity τ)). exists p1. reflexivity. destruct H. destruct H.  exists x. 
  exists (x0 + p2). split. apply cgr_trans with (((t • x) + x0) + p2).
  apply cgr_choice. assumption.
  apply cgr_choice_assoc. assumption.
- destruct (IHTransition (reflexivity τ)). exists p2. reflexivity. destruct H. destruct H.  exists x. 
  exists (x0 + p1). split. apply cgr_trans with (((t • x) + x0) + p1). apply cgr_trans with (p2 + p1). 
  apply cgr_choice_com. apply cgr_choice. assumption. apply cgr_choice_assoc. assumption.
Qed.

(* p 'is equivalent some r 'and r performs α to q *)
Definition sc_then_lts p α q := exists r, p ≡* r /\ (lts r α q).

(* p performs α to some r and this is equivalent to q*)
Definition lts_then_sc p α q := exists r, ((lts p α r) /\ r ≡* q).


(* p 'is equivalent some r 'and r performs α to q , the congruence and the Transition can be reversed : *)
Lemma Congruence_Respects_Transition  : forall p q α, sc_then_lts p α q -> lts_then_sc p α q.
Proof. 
(* by induction on the congruence and the step then...*)
  intros p q α (p' & hcgr & l).
  revert q α l.
  dependent induction hcgr.
  - dependent induction H. 
(* reasonning about all possible cases due to the structure of terms *)
    + intros. exists q.  split.  exact l. reflexivity. 
    + intros. exists (q ‖ ⓪). split. apply lts_parL. assumption. auto with cgr (*par contexte parallele*). 
    + intros. dependent destruction l. inversion l2. inversion l1. exists p2. split. exact l. auto with cgr. 
      inversion l.
    + intros. dependent destruction l.
      -- exists (q2 ‖ p2). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). exact l1. exact l2. auto with cgr.
      -- exists (p2 ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). exact l1. exact l2. auto with cgr.
      -- exists (p ‖ p2). split. apply lts_parR. assumption. auto with cgr.
      -- exists (q2 ‖ q). split. apply lts_parL. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l2. 
         * exists ((p2 ‖ p0) ‖ r). split.
           apply lts_parL. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). assumption. assumption. auto with cgr.
         * exists ((p2 ‖ q) ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). apply lts_parL. assumption. assumption.
           apply cgr_par_assoc.
      -- dependent destruction l1. 
         * exists ((q2 ‖ p2) ‖ r). split. apply lts_parL. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption.
           assumption. auto with cgr.
         * exists ((q2 ‖ q) ‖ q0). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption. apply lts_parL.
           assumption. auto with cgr.
      -- exists ((p2 ‖ q) ‖ r). split. apply lts_parL. apply lts_parL. assumption. auto with cgr.
      -- dependent destruction l.
         * exists ((p ‖ p2) ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). apply lts_parR. assumption. assumption.
           auto with cgr.
         * exists ((p ‖ q2) ‖ p2). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption. apply lts_parR.
           assumption. auto with cgr.
         * exists ((p ‖ p2) ‖ r). split. apply lts_parL. apply lts_parR. assumption. auto with cgr.
         * exists ((p ‖ q) ‖ q2). split. apply lts_parR. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l1. 
         * exists (p2 ‖ (q ‖ q2)). split.
           eapply lts_comL. instantiate (1:= v). instantiate (1:= c). assumption. apply lts_parR. assumption. auto with cgr.
         * exists (p ‖ (q0 ‖ q2)). split. apply lts_parR. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). assumption.
           assumption. auto with cgr.
      -- dependent destruction l2. 
         * exists (p0 ‖ (q ‖ p2)). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). apply lts_parR. assumption.
           assumption. auto with cgr.
         * exists (p ‖ (q2 ‖ p2)). split. apply lts_parR.  eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption.
           assumption. auto with cgr.
      -- dependent destruction l.
         * exists (p2 ‖ (q2 ‖ r)). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c).  assumption. apply lts_parL.
           assumption. auto with cgr.
         * exists (q2 ‖ (p2 ‖ r)). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). apply lts_parL. assumption.
           assumption. auto with cgr.
         * exists (p2 ‖ ( q ‖ r)). split. apply lts_parL. assumption. auto with cgr.
         * exists (p ‖ (q2 ‖ r)). split. apply lts_parR. apply lts_parL. assumption. auto with cgr.
      -- exists (p ‖ (q ‖ q2)). split. apply lts_parR.  auto. apply lts_parR. assumption. auto with cgr.
    + intros. exists q.  split. apply lts_choiceL.  assumption. auto with cgr.
    + intros. dependent destruction l.
      -- exists q. split. assumption. auto with cgr.
      -- inversion l.
    + intros. dependent destruction l.
      -- exists q0. split. apply lts_choiceR. assumption. auto with cgr.
      -- exists q0. split. apply lts_choiceL. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- exists q0. split. apply lts_choiceL. apply lts_choiceL. assumption. auto with cgr.
      -- dependent destruction l.
         * exists q0. split. apply lts_choiceL. apply lts_choiceR. assumption. auto with cgr.
         * exists q0. split. apply lts_choiceR. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l.
         * exists q0. split. apply lts_choiceL. assumption. auto with cgr.
         * exists q0. split. apply lts_choiceR. apply lts_choiceL. assumption. auto with cgr.
      -- exists q0. split. apply lts_choiceR. apply lts_choiceR. assumption. auto with cgr.
    + intros. dependent destruction l. exists (pr_subst x p (rec x • p)). split. apply lts_recursion. 
      apply cgr_subst. assumption.
    + intros. dependent destruction l. exists p.  split. apply lts_tau.
      constructor. assumption.
    + intros. dependent destruction l. exists (p^v). split. apply lts_input.
      apply Congruence_Respects_Substitution. constructor. apply H.
    + intros. dependent destruction l. exists p. split. apply lts_output. 
      constructor. assumption.
    + intros. dependent destruction l.
      -- destruct (IHcgr_step p2 (ActOut c (cst v))).  exact l1. destruct H0. exists (x ‖ q2).
          split. eapply lts_comL. exact H0. assumption.
          apply cgr_fullpar. assumption. reflexivity.
      -- destruct (IHcgr_step q2 (ActIn c (cst v))). assumption. destruct H0. exists (x ‖ p2).
          split.  eapply lts_comR. exact l1. assumption.
          apply cgr_fullpar. assumption. reflexivity.
      -- destruct (IHcgr_step p2 α). assumption. destruct H0. eexists.
          split. instantiate (1:= (x ‖ r)). apply lts_parL. assumption. apply cgr_fullpar.
          assumption. reflexivity.
      -- eexists. split. instantiate (1:= (p ‖ q2)). apply lts_parR.
          assumption. apply cgr_par.
          constructor. assumption.
    + intros. dependent destruction l.
      -- eexists. split. instantiate (1:= p). apply lts_ifOne. reflexivity. 
         constructor. reflexivity.
      -- eexists. split. instantiate (1:= q). apply lts_ifZero. assumption.
         constructor. assumption.
    + intros. dependent destruction l.
      -- eexists. split. instantiate (1:= p). apply lts_ifOne. auto. 
         constructor. assumption.
      -- eexists. split. instantiate (1:= q). apply lts_ifZero. assumption. 
         constructor. reflexivity.
    + intros. dependent destruction l. 
      -- destruct (IHcgr_step q α). assumption. destruct H0. exists x. split. apply lts_choiceL. assumption. assumption.
      -- eexists. instantiate (1:= q). split. apply lts_choiceR. assumption. reflexivity.
  - intros. destruct (IHhcgr2 q α). assumption. destruct (IHhcgr1 x0 α). destruct H. assumption. exists x1. split. destruct H0. assumption.
    destruct H. destruct H0. eauto with cgr.
Qed.



(* One side of the Harmony Lemma *)
Lemma Reduction_Implies_TausAndCong : forall P Q, (sts P Q) -> (lts_then_sc P τ Q).
Proof. 
intros P Q Reduction. 
assert ((exists c v P1 P2 G1 G2 S, ((P ≡* (((c ! (cst v) • P1) + G1) ‖ ((c ? x • P2) + G2)) ‖ S)) /\ (Q ≡*((P1 ‖ (P2^v)) ‖ S)))
\/ (exists P1 G1 S, (P ≡* (((t • P1) + G1) ‖ S)) /\ (Q ≡* (P1 ‖ S)))
\/ (exists n P1 S, (P ≡* ((rec n • P1) ‖ S)) /\ (Q ≡* (pr_subst n P1 (rec n • P1) ‖ S)))
\/ (exists P1 P0 S v, (P ≡* ((If (v == v) Then P1 Else P0) ‖ S)) /\ (Q ≡* P1 ‖ S))
\/ (exists P1 P0 S v v', (P ≡* ((If (v == v') Then P1 Else P0) ‖ S)) /\ (Q ≡* P0 ‖ S) /\ ~(v = v'))
). 
apply ReductionShape. exact Reduction.
destruct H as [IH|[IH|[IH|[IH |IH]]]];  decompose record IH. 

(*First case τ by communication *)

- assert (lts (((x ! x0 • x1) + x3) ‖ ((x ? l • x2) + x4) ‖ x5) τ (x1 ‖ (x2^x0) ‖ x5)).
  * apply lts_parL.   
    eapply lts_comL. apply lts_choiceL. instantiate (2:= x). instantiate (1:= x0).
    apply lts_output. apply lts_choiceL. apply lts_input.
  * assert (sc_then_lts P τ ((x1 ‖ x2^x0) ‖ x5)). exists ((((x ! x0 • x1) + x3) ‖ ((x ? l • x2) + x4)) ‖ x5). split. assumption. assumption.
    assert (lts_then_sc P τ ((x1 ‖ x2^x0) ‖ x5)). apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3.
    exists x6. split. assumption. apply transitivity with ((x1 ‖ x2^x0) ‖ x5). assumption. symmetry. assumption.

(*Second case τ by Tau Action *)

- assert (lts ((t • x + x0) ‖ x1) τ (x ‖ x1)). constructor.
  apply lts_choiceL. apply lts_tau.
  assert (sc_then_lts P τ (x ‖ x1)). exists ((t • x + x0) ‖ x1). split. assumption. apply lts_parL.
  apply lts_choiceL. apply lts_tau.
  assert (lts_then_sc P τ (x ‖ x1)). apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3. 
  exists x2. split. assumption. apply transitivity with (x ‖ x1). assumption. symmetry. assumption.

(*Third case τ by recursion *)

- assert (lts (rec x • x0 ‖ x1) τ (pr_subst x x0 (rec x • x0) ‖ x1)). 
  constructor. apply lts_recursion. assert (sc_then_lts P τ ((pr_subst x x0 (rec x • x0) ‖ x1))). 
  exists (rec x • x0 ‖ x1). split. assumption. assumption. assert (lts_then_sc P τ (pr_subst x x0 (rec x • x0) ‖ x1)). 
  apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3. 
  exists x2. split. assumption. apply transitivity with (pr_subst x x0 (rec x • x0) ‖ x1). assumption.
  symmetry. assumption.

(*Fourth case τ by If ONE*)

- assert (lts ((If x2 == x2 Then x Else x0) ‖ x1) τ (x ‖ x1)). constructor. apply lts_ifOne. auto.
  assert (sc_then_lts P τ (x ‖ x1)). exists ((If x2 == x2 Then x Else x0) ‖ x1). split. assumption.
  constructor. constructor. auto. 
  assert (lts_then_sc P τ (x ‖ x1)). apply Congruence_Respects_Transition. 
  exists ((If x2 == x2 Then x Else x0) ‖ x1). split. assumption. assumption. destruct H3. destruct H3.
  exists x3. split. assumption. apply transitivity with (x ‖ x1). assumption. 
  symmetry. exact H1. 

(*Fifth case τ by If ZERO*)

- assert (lts ((If x2 == x3 Then x Else x0) ‖ x1) τ (x0 ‖ x1)). constructor. apply lts_ifZero. assumption.
  assert (sc_then_lts P τ (x0 ‖ x1)). exists ((If x2 == x3 Then x Else x0) ‖ x1). split. assumption.
  apply lts_parL. apply lts_ifZero. assumption.
  assert (lts_then_sc P τ (x0 ‖ x1)). apply Congruence_Respects_Transition. 
  exists ((If x2 == x3 Then x Else x0) ‖ x1). split.  assumption. assumption. destruct H4. destruct H4.
  exists x4. split. assumption. apply transitivity with (x0 ‖ x1). assumption.
  symmetry. assumption. 
Qed.


(* Some lemmas for multiple parallele processes to simplify the statements of proof*)
Lemma InversionParallele : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (P ‖ R) ‖ (Q ‖ S) . 
Proof. 
intros.
apply transitivity with (((P ‖ Q) ‖ R) ‖ S). apply cgr_par_assoc_rev.
apply transitivity with ((P ‖ (Q ‖ R)) ‖ S). apply cgr_par. apply cgr_par_assoc.
apply transitivity with (((Q ‖ R) ‖ P) ‖ S). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ‖ R) ‖ (P ‖ S)). apply cgr_par_assoc.
apply transitivity with ((R ‖ Q) ‖ (P ‖ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with (((R ‖ Q) ‖ P) ‖ S). apply cgr_par_assoc_rev.
apply transitivity with ((P ‖ (R ‖ Q)) ‖ S). apply cgr_par. apply cgr_par_com.
apply transitivity with (((P ‖ R) ‖ Q) ‖ S). apply cgr_par. apply cgr_par_assoc_rev.
apply transitivity with ((P ‖ R) ‖ (Q ‖ S)). apply cgr_par_assoc.
reflexivity. 
Qed.
Lemma InversionParallele2 : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (R ‖ P) ‖ (S ‖ Q).
Proof.
intros. 
apply transitivity with ((P ‖ R) ‖ (Q ‖ S)). apply InversionParallele.
apply transitivity with ((R ‖ P) ‖ (Q ‖ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ‖ S) ‖ (R ‖ P)). apply cgr_par_com.
apply transitivity with ((S ‖ Q) ‖ (R ‖ P)). apply cgr_par. apply cgr_par_com.
apply cgr_par_com.
Qed.
Lemma InversionParallele3 : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (R ‖ Q) ‖ (P ‖ S).
Proof.
intros.
apply transitivity with ((Q ‖ P) ‖ (R ‖ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ‖ R) ‖ (P ‖ S)). apply InversionParallele. apply cgr_par. apply cgr_par_com.
Qed.

(* The More Stronger Harmony Lemma (in one side) is more stronger *)
Lemma Congruence_Simplicity : (forall α , ((forall P Q, (((lts P α Q) -> (sts P Q)))) 
-> (forall P Q, ((lts_then_sc P α Q) -> (sts P Q))))).
Proof.
intros. destruct H0. destruct H0. eapply sts_cong. instantiate (1:=P). apply cgr_refl. instantiate (1:=x). apply H. exact H0. 
exact H1.
Qed.

Lemma Taus_Implies_Reduction : forall P Q, (lts P τ Q) -> (sts P Q).
Proof. 
intros.
dependent induction H.
  - eapply sts_cong.  instantiate (1:=  ((t • P) + ⓪)). apply cgr_choice_nil_rev. instantiate (1:=P).
    apply sts_tau. constructor. constructor.
  - apply sts_recursion.
  - apply sts_ifOne. assumption.
  - apply sts_ifZero. assumption.
  - destruct (TransitionShapeForOutput p1 p2 c v). assumption.  decompose record H1.
    destruct (TransitionShapeForInput q1 q2 c v). assumption. decompose record H4.
    eapply sts_cong. instantiate (1:=(((c ! v • x) + x0) ‖ ((c ? l • x2) + x3)) ‖ (x1 ‖ x4)).
    apply cgr_trans with ((((c ! v • x) + x0) ‖ x1) ‖ (((c ? l • x2) + x3) ‖ x4)). apply cgr_fullpar. assumption. assumption.
    apply InversionParallele. 
    instantiate (1 := (x ‖ (x2^v)) ‖ (x1 ‖ x4)). apply sts_par.
    apply sts_com. 
    apply transitivity with ((x ‖ x1) ‖ ((x2^v) ‖ x4)). apply InversionParallele. apply cgr_fullpar. 
    symmetry. assumption. symmetry. assumption.
  - destruct (TransitionShapeForOutput p1 p2 c v). assumption. decompose record H1.
    destruct (TransitionShapeForInput q1 q2 c v). assumption. decompose record H4.
    eapply sts_cong. instantiate (1:=(((c ! v • x) + x0) ‖ ((c ? l • x2) + x3)) ‖ (x1 ‖ x4)).
    apply transitivity with (p1 ‖ q1). apply cgr_par_com.
    apply transitivity with ((((c ! v • x) + x0) ‖ x1) ‖ (((c ? l • x2) + x3) ‖ x4)).
    apply cgr_fullpar. assumption. assumption. apply InversionParallele. 
    instantiate (1 := (x ‖ (x2^v)) ‖ (x1 ‖ x4)). apply sts_par. apply sts_com.
    apply transitivity with ((x ‖ x1) ‖ ((x2^v) ‖ x4)). apply InversionParallele. apply transitivity with (p2 ‖ q2). apply cgr_fullpar. 
    symmetry. assumption. symmetry. assumption. apply cgr_par_com.
- apply sts_par. apply IHlts. reflexivity.
- eapply sts_cong. instantiate (1:= q1 ‖ p). apply cgr_par_com. instantiate (1:= q2 ‖ p).
  apply sts_par. apply IHlts. reflexivity. apply cgr_par_com.
- destruct (TransitionShapeForTauAndGuard (g p1) q). split. assumption. exists p1. reflexivity.
  decompose record H0.
  eapply sts_cong. instantiate (1:= ((t • x) + (x0 + p2))).
  apply transitivity with (g (((t • x) + x0) + p2)). apply cgr_choice. assumption. apply cgr_choice_assoc.
  instantiate (1:= x). apply sts_tau. symmetry. assumption.
- destruct (TransitionShapeForTauAndGuard (g p2) q). split. assumption. exists p2. reflexivity.
  decompose record H0. eapply sts_cong. instantiate (1:= ((t • x) + (x0 + p1))).
  apply transitivity with (g (((t • x) + x0 ) + p1)). apply transitivity with (g (p2 + p1)). apply cgr_choice_com.
  apply cgr_choice. assumption. apply cgr_choice_assoc. instantiate (1:= x). apply sts_tau.
  symmetry. assumption.
Qed.

(* One side of the Harmony Lemma*)
Lemma TausAndCong_Implies_Reduction: forall P Q, (lts_then_sc P τ Q) -> (sts P Q).
Proof.
intros P Q H.
apply Congruence_Simplicity with τ. exact Taus_Implies_Reduction. exact H.
Qed.

Theorem HarmonyLemmaForCCSWithValuePassing : forall P Q, (lts_then_sc P τ Q) <-> (sts P Q).
Proof.
intros. split.
* apply TausAndCong_Implies_Reduction.
* apply Reduction_Implies_TausAndCong.
Qed.

(* Definition for Well Abstracted bvariable *)
Inductive Well_Defined_Data : nat -> Data -> Prop :=
| bvar_is_defined_up_to_k: forall k x, (x < k) -> Well_Defined_Data k (bvar x)
| cst_is_always_defined : forall k x, Well_Defined_Data k (cst x).

Inductive Well_Defined_Condition : nat -> Equation Data -> Prop :=
| equationOnValueXX : forall k x y, Well_Defined_Data k x -> Well_Defined_Data k y -> Well_Defined_Condition k (x == y).

Inductive Well_Defined_Input_in : nat -> proc -> Prop :=
| WD_par : forall k p1 p2, Well_Defined_Input_in k p1 -> Well_Defined_Input_in k p2 
                -> Well_Defined_Input_in k (p1 ‖ p2)
| WD_var : forall k i, Well_Defined_Input_in k (pr_var i)
| WD_rec : forall k x p1, Well_Defined_Input_in k p1 -> Well_Defined_Input_in k (rec x • p1)
| WD_if_then_else : forall k p1 p2 C, Well_Defined_Condition k C -> Well_Defined_Input_in k p1 
                    -> Well_Defined_Input_in k p2 
                        -> Well_Defined_Input_in k (If C Then p1 Else p2)
| WD_success : forall k, Well_Defined_Input_in k (①)
| WD_nil : forall k, Well_Defined_Input_in k (⓪)
| WD_input : forall k c p, Well_Defined_Input_in (S k) p
                  -> Well_Defined_Input_in k (c ? x • p)
| WD_output : forall k c v p, Well_Defined_Data k v 
                    -> Well_Defined_Input_in k p -> Well_Defined_Input_in k (c ! v • p)
| WD_tau : forall k p,  Well_Defined_Input_in k p -> Well_Defined_Input_in k (t • p)
| WD_choice : forall k p1 p2,  Well_Defined_Input_in k (g p1) ->  Well_Defined_Input_in k (g p2) 
              ->  Well_Defined_Input_in k (p1 + p2).

#[global] Hint Constructors Well_Defined_Input_in:ccs.

Lemma Inequation_k_data : forall k d, Well_Defined_Data k d -> Well_Defined_Data (S k) d.
Proof.
intros. dependent destruction d. constructor. dependent destruction H. constructor. auto with arith.
Qed.

Lemma Inequation_k_equation : forall k c, Well_Defined_Condition k c -> Well_Defined_Condition (S k) c.
Proof.
intros. dependent destruction c. destruct d; destruct d0.
- constructor; constructor.
- dependent destruction H. constructor. constructor. apply Inequation_k_data. assumption.
- dependent destruction H. constructor. apply Inequation_k_data. assumption. constructor. 
- dependent destruction H. constructor; apply Inequation_k_data; assumption.
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
- destruct g0.
  ** intros. constructor.
  ** intros. constructor.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. constructor. apply Inequation_k_data. dependent destruction H. assumption.
     apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. dependent destruction H. constructor.
    -- apply Hp. simpl; auto with arith. assumption.
    -- apply Hp. simpl; auto with arith. assumption.
Qed.


Lemma Congruence_step_Respects_WD_k : forall p q k, Well_Defined_Input_in k p -> p ≡ q -> Well_Defined_Input_in k q. 
Proof.
intros. revert H. revert k. dependent induction H0 ; intros.
* auto.
* dependent destruction H; auto.
* constructor; auto. constructor.
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
  - dependent destruction H. constructor. apply NotK; assumption.
Qed.

Lemma ForEquation : forall k v e, Well_Defined_Condition (S k) e 
                -> Well_Defined_Condition k (subst_in_Equation k (cst v) e).
Proof.
intros. revert H. revert v. revert k. 
- dependent destruction e. dependent induction d; dependent induction d0.
  * intros. simpl. constructor; constructor.
  * intros. simpl. destruct (decide (n = k)).
    ** constructor; constructor.
    ** constructor. constructor. dependent destruction H. dependent destruction H0. constructor. apply NotK; assumption.
  * intros. simpl. constructor; try constructor. destruct (decide (n = k)). constructor. dependent destruction H.
    dependent destruction H. constructor. apply NotK; assumption.
  * intros. simpl. constructor.
    ** destruct (decide (n = k)); try constructor. dependent destruction H. dependent destruction H. 
    apply NotK; assumption.
    ** destruct (decide (n0 = k)); try constructor. dependent destruction H. dependent destruction H0. 
    apply NotK; assumption.
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
* destruct g0.
  - intros. simpl. constructor.
  - intros. simpl. constructor.
  - intros. simpl. constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. constructor.
    -- eapply ForData. dependent destruction H. assumption.
    -- apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. dependent destruction H. constructor.
    -- assert (Well_Defined_Input_in k (subst_in_proc k v (g0_1))). apply Hp.
      simpl.  auto with arith. assumption. assumption.
    -- assert (Well_Defined_Input_in k (subst_in_proc k v (g0_2))). apply Hp.
      simpl.  auto with arith. assumption. assumption.
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
* destruct g0. 
  ** intros. simpl. constructor.
  ** intros. simpl. constructor.
  ** intros. simpl. constructor. dependent destruction H. apply Hp. 
    - simpl;auto with arith.
    - apply Inequation_k_proc. assumption.
    - assumption.
  ** intros. simpl. constructor. dependent destruction H. assumption. apply Hp.
    - simpl; auto with arith.
    - assumption.
    - dependent destruction H. assumption.
  ** intros. simpl. constructor. apply Hp.
    - simpl; auto with arith.
    - assumption.
    - dependent destruction H. assumption.
  ** intros. simpl. dependent destruction H. constructor.
    - assert (Well_Defined_Input_in k (pr_subst x (g g0_1) p)). apply Hp. simpl; auto with arith. assumption.
      assumption. assumption.
    - assert (Well_Defined_Input_in k (pr_subst x (g g0_2) p)). apply Hp. simpl; auto with arith. assumption.
      assumption. assumption.
Qed.

Lemma RecursionOverReduction_is_WD : forall k x p, Well_Defined_Input_in k (rec x • p) -> Well_Defined_Input_in k (pr_subst x p (rec x • p)).
Proof.
intros. apply ForRecursionSanity. dependent destruction H. assumption. assumption.
Qed.


Lemma STS_Respects_WD : forall p q, Well_Defined_Input_in 0 p -> sts p q -> Well_Defined_Input_in 0 q.
Proof.
intros. revert H. rename H0 into Reduction. dependent induction Reduction.
* intros. constructor.
  - dependent destruction H. dependent destruction H. dependent destruction H. assumption.
  - dependent destruction H. dependent destruction H0. dependent destruction H0_. apply ForSTS. assumption. 
* intros. dependent destruction H. dependent destruction H. assumption.
* intros. dependent destruction H. apply RecursionOverReduction_is_WD. constructor. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H. constructor. apply IHReduction. assumption. assumption.
* intros. apply Congruence_Respects_WD with q2. apply IHReduction. apply Congruence_Respects_WD with p1. 
  assumption. assumption. assumption.
Qed.

Lemma LTS_Respects_WD : forall p q α, Well_Defined_Input_in 0 p -> lts p α q ->  Well_Defined_Input_in 0 q.
Proof.
intros. revert H. rename H0 into Transition. dependent induction Transition.
* intros. apply ForSTS. dependent destruction H. assumption.
* intros. dependent destruction H. assumption.
* intros. dependent destruction H. assumption.
* intros. apply ForRecursionSanity. dependent destruction H. assumption. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H. constructor. 
  ** apply IHTransition1. assumption.
  ** apply IHTransition2. assumption.
* intros. dependent destruction H. constructor.
  ** apply IHTransition2. assumption.
  ** apply IHTransition1. assumption.
* intros. dependent destruction H. constructor. apply IHTransition. assumption. assumption.
* intros. dependent destruction H. constructor. assumption. apply IHTransition. assumption.
* intros. dependent destruction H. apply IHTransition. assumption.
* intros. dependent destruction H. apply IHTransition. assumption.
Qed.

