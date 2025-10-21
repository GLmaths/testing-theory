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
Require Import RelationClasses.
From stdpp Require base countable finite gmap list gmultiset strings.
Require Import Relations Morphisms.
Require Import Coq.Wellfounded.Inverse_Image.


Require Import signatures.pi.
Require Import signatures.unscoped.

Notation "tm <[ s ]" :=
  (subst2 s ids tm) (at level 10, right associativity) : subst_scope.
Notation "tm [ s ]" :=
  (subst2 ids s tm) (at level 10, right associativity) : subst_scope.
Notation "a ⋅ x" :=
  (ren1 a x) (at level 20, right associativity) : subst_scope.
Notation "↑" := (shift) : subst_scope.
Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.
Notation "f >> g" := (fun x => g (f x)) (at level 50) : subst_scope.
Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at next level, right associativity) : subst_scope.
Open Scope subst_scope.
Notation "↑↑" := (shift >> var_Data).

(* Notation "p [ x ← v ]" := (subst_proc id (fun y => if (base.decide (y = x)) then v else y) p).
Notation "p [ x ⇐ q ]" := (subst_proc (fun y => if (base.decide (y = x)) then q else y) id p). *)

(*Coercion makes the specification of 'cst' and 'bvar' useless, then simplify the notation *)
Coercion cst : Value >-> Data.
Coercion var_Data : nat >-> Data.
Coercion var_proc : nat >-> proc.

(* Arguments  tt  {_}.
Arguments  ff  {_} .
Arguments  Inequality  {_} _ _.
Arguments  Or  {_} _ _.
Arguments  Not  {_}  _. *)

Notation "'non' e" := (Not e) (at level 50).
Notation "x ∨ y" := (Or x y) (at level 50).
Notation "x ⩽ y" := (Inequality x y) (at level 50).

(* From Must Require Import TransitionSystems Must Completeness. *)
(* We need to distinguish actions for bound/free input now, so we don't use
   the types in TransitionSystems. *)
(* Label of action (other than tau), here it is a channel's name with a data transmitted *)
Inductive ExternalAction := 
| act : Data -> Data -> ExternalAction.

Inductive Act :=
| ActIn (a : ExternalAction)
| FreeOut (a : ExternalAction)
| BoundOut (a : ExternalAction)
| τ
.

Notation "c ⋉ v" := (act c v) (at level 50).

Parameter (Eval_Eq : Equation -> (option bool)).
Parameter (channel_eq_dec : base.EqDecision Value). (* only here for the classes *)
#[global] Instance channel_eqdecision : base.EqDecision Value. Proof. exact channel_eq_dec. Defined.
Parameter (channel_is_countable : countable.Countable Value). (* only here for the classes *)
#[global] Instance channel_countable : countable.Countable Value. Proof. exact channel_is_countable. Defined.
Parameter (value_eq_dec : base.EqDecision Value). (* only here for the classes *)
#[global] Instance value_eqdecision : base.EqDecision Value. Proof. exact value_eq_dec. Defined.
Parameter (value_is_countable : countable.Countable Value). (* only here for the classes *)
#[global] Instance value_countable : countable.Countable Value. Proof. exact value_is_countable. Defined.

(*Some notation to simplify the view of the code*)
Notation "①" := (pr_success).
Notation "𝟘" := (pr_nil).
Notation "'rec' p" := (pr_rec p) (at level 50).
Notation "P + Q" := (pr_choice P Q).
Notation "P ‖ Q" := (pr_par P Q) (at level 50).
Notation "c ! v • P" := (pr_output c v P) (at level 50).
Notation "'ν' P" := (pr_res P) (at level 50).
Notation "c ? P" := (pr_input c P) (at level 50).
Notation "'t' • P" := (pr_tau P) (at level 50).
Notation "'If' C 'Then' P 'Else' Q" := (pr_if_then_else C P Q)
(at level 200, right associativity, format
"'[v   ' 'If'  C '/' '[' 'Then'  P  ']' '/' '[' 'Else'  Q ']' ']'").

Definition swap_two p :=
  ren_proc ids (fun x => match x with 0 => S 0 | S 0 => 0 | n => n end) p.
(* have this automatically unfold *)
Arguments swap_two / _.

(* Lemma swap_two_example : exists p, p =
  swap_two
   (0 ? (0 ! var_Data 0 • ①) ‖ (1 ! var_Data 1 • (1 ? (1 ! var_Data 1 • ①)))).
   unfold swap_two. asimpl. unfold core.funcomp. *)

Reserved Notation "p ≡ q" (at level 70).
Inductive cgr_step : proc -> proc -> Prop :=
(*  Reflexivity of the Relation ≡  *)
| cgr_refl_step : forall p, p ≡ p

| cgr_par_nil_step : forall p, 
    (p ‖ 𝟘) ≡ p
| cgr_par_nil_rev_step : forall p,
    p ≡ (p ‖ 𝟘)
| cgr_par_com_step : forall p q,
    (p ‖ q) ≡ (q ‖ p)
| cgr_par_assoc_step : forall p q r,
    ((p ‖ q) ‖ r) ≡ (p ‖ (q ‖ r))
| cgr_par_assoc_rev_step : forall p q r,
    (p ‖ (q  ‖ r)) ≡ ((p ‖ q) ‖ r)

(* Rules for the Summation *)
| cgr_choice_nil_step : forall p,
    (p + 𝟘) ≡ p
| cgr_choice_nil_rev_step : forall p,
    p ≡ (p + 𝟘)
| cgr_choice_com_step : forall p q,
    (p + q) ≡ (q + p)
| cgr_choice_assoc_step : forall p q r,
    ((p + q) + r) ≡ (p + (q + r))
| cgr_choice_assoc_rev_step : forall p q r,
    (p + (q + r)) ≡ ((p + q) + r)

(*The reduction is given to certain terms...*)
| cgr_recursion_step : forall p q,
    p ≡ q -> (rec p) ≡ (rec q)
| cgr_tau_step : forall p q,
    p ≡ q ->
    (t • p) ≡ (t • q)
| cgr_input_step : forall c p q,
    p ≡ q ->
    (c ? p) ≡ (c ? q)
| cgr_par_step : forall p q r,
    p ≡ q ->
    (p ‖ r) ≡ (q ‖ r)
| cgr_if_left_step : forall C p q q',
    q ≡ q' ->
    (If C Then p Else q) ≡ (If C Then p Else q')
| cgr_if_right_step : forall C p p' q,
    p ≡ p' ->
    (If C Then p Else q) ≡ (If C Then p' Else q)

(*...and sums (only for guards (by sanity))*)
(* this rule is in the corrected book of Sangiorgi, see his typos *)
| cgr_choice_step : forall p1 q1 p2,
    p1 ≡ q1 -> 
    (p1 + p2) ≡ (q1 + p2)

(* | cgr_nu_nu_step : forall p,
    (ν ν p) ≡ (ν ν (swap_two p)) *)
| cgr_res_nil_step :
    (ν 𝟘) ≡ 𝟘
| cgr_res_nil_rev_step :
    𝟘 ≡ (ν 𝟘)
| cgr_res_step : forall p q,
    p ≡ q ->
    (ν p) ≡ (ν q)
| cgr_scope_step: forall (P Q:proc),
    (ν (P ‖ Q [↑↑])) ≡ ((ν P) ‖ Q)
| cgr_scope_rev_step: forall (P Q:proc),
    ((ν P) ‖ Q) ≡ (ν (P ‖ (Q [↑↑])))
where "p ≡ q" := (cgr_step p q).

#[global] Hint Constructors cgr_step:cgr_step_structure.

(* /!\ for induction principle to make coq understand that guards are sub-terms of proc *)
Fixpoint size (p : proc) := 
  match p with
  | ① => 1
  | 𝟘 => 0
  | p ‖ q  => S (size p + size q)
  | rec p => S (size p)
  | var_proc _ => 1
  | c ! v • p => S (size p)
  | c ? p => S (size p)
  | ν p => S (size p)
  | t • p => S (size p)
  | p + q => S (size p + size q)
  | If C Then p Else q => S (size p + size q)
end.

(* The relation ≡ is an reflexive*)
#[global] Instance cgr_refl_step_is_refl : Reflexive cgr_step.
Proof. intro. apply cgr_refl_step. Qed.
(* The relation ≡ is symmetric*)
#[global] Instance cgr_symm_step : Symmetric cgr_step.
Proof. intros p q hcgr. induction hcgr; try solve [constructor; try exact IHhcgr].
Qed.
(* - assert (swap_two (swap_two p) = p).
  + unfold swap_two. admit.
  + replace (ν p) with (ν (swap_two (swap_two p))). apply cgr_nu_nu_step. now rewrite H. *)
(* Admitted. *)

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
Lemma cgr_par_nil : forall p, p ‖ 𝟘 ≡* p.
Proof.
constructor.
apply cgr_par_nil_step.
Qed.
Lemma cgr_par_nil_rev : forall p, p ≡* p ‖ 𝟘.
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
Lemma cgr_choice_nil : forall p, p + 𝟘 ≡* p.
Proof.
constructor.
apply cgr_choice_nil_step.
Qed.
Lemma cgr_choice_nil_rev : forall p, p ≡* p + 𝟘.
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
Lemma cgr_recursion : forall p q, p ≡* q -> (rec p) ≡* (rec q).
Proof.
intros. dependent induction H. 
constructor. 
apply cgr_recursion_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_tau : forall p q, p ≡* q -> (t • p) ≡* (t • q).
Proof.
intros. dependent induction H. 
constructor. 
apply cgr_tau_step. exact H.
simple eapply cgr_trans. exact IHclos_trans1. assumption.
Qed. 
Lemma cgr_input : forall c p q, p ≡* q -> (c ? p) ≡* (c ? q).
Proof.
intros.
dependent induction H. 
* constructor. now apply cgr_input_step.
* simple eapply cgr_trans. exact IHclos_trans1. assumption.
Qed.
Lemma cgr_res : forall p q, p ≡* q -> (ν p) ≡* (ν q).
Proof.
intros. dependent induction H.
- constructor. apply cgr_res_step. exact H.
- eauto with cgr_eq.
Qed.
Lemma cgr_res_nil : 𝟘 ≡* (ν 𝟘).
Proof.
constructor. exact cgr_res_nil_rev_step.
Qed.
Lemma cgr_scope : forall P Q, 
  ν (P ‖ Q [↑↑]) ≡* (ν P) ‖ Q.
Proof.
intros P Q.  constructor. apply cgr_scope_step.
Qed.
Lemma cgr_scope_rev : forall P Q, 
  (ν P ‖ Q) ≡* ν (P ‖ Q[↑↑]).
Proof.
intros P Q. constructor. apply cgr_scope_rev_step.
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
- constructor.  apply cgr_if_right_step. exact H.
- eauto with cgr_eq.
Qed.
Lemma cgr_choice : forall p q r, p ≡* q -> p + r ≡* q + r.
Proof.
intros. dependent induction H. 
- constructor.  apply cgr_choice_step. exact H.
- eauto with cgr_eq.
Qed.

(* The if of processes respects ≡* *)
Lemma cgr_full_if : forall C p p' q q', p ≡* p' -> q ≡* q' -> (If C Then p Else q) ≡* (If C Then p' Else q').
Proof.
intros.
apply transitivity with (If C Then p Else q'). apply cgr_if_left. exact H0. 
apply cgr_if_right. exact H. 
Qed.
(* The sum of guards respects ≡* *)
Lemma cgr_fullchoice : forall M1 M2 M3 M4, M1 ≡* M2 -> M3 ≡* M4 -> M1 + M3 ≡* M2 + M4.
Proof.
intros.
apply transitivity with (M2 + M3). apply cgr_choice. exact H. apply transitivity with (M3 + M2).
apply cgr_choice_com. apply transitivity with (M4 + M2). apply cgr_choice. exact H0. apply cgr_choice_com.
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
cgr_choice_assoc_rev cgr_recursion cgr_tau cgr_input cgr_if_left cgr_if_right cgr_par cgr_choice 
cgr_refl cgr_symm cgr_res cgr_scope cgr_scope_rev cgr_res_nil cgr_trans : cgr.

#[global] Instance pr_par_proper : Proper (cgr ==> cgr ==> cgr) pr_par.
Proof. intros p p' Hp q q' Hq.
apply transitivity with (p' ‖ q).
- now apply cgr_par.
- apply transitivity with (q ‖ p').
  + now apply cgr_par_com.
  + apply transitivity with (q' ‖ p').
    * now apply cgr_par. 
    * apply cgr_par_com.
Qed.

#[global] Instance pr_choice_proper : Proper (cgr ==> cgr ==> cgr) pr_choice.
Proof. intros p p' Hp q q' Hq. apply cgr_fullchoice; assumption. Qed.

#[global] Instance pr_res_proper : Proper (cgr ==> cgr) pr_res.
Proof. intros p p' Hp. apply cgr_res; assumption. Qed.

#[global] Instance pr_rec_proper : Proper (cgr ==> cgr) pr_rec.
Proof. intros p p' Hp. apply cgr_recursion; assumption. Qed.

#[global] Instance pr_tau_proper : Proper (cgr ==> cgr) pr_tau.
Proof. intros p p' Hp. apply cgr_tau; assumption. Qed.

(* Lemma Congruence_Respects_Substitution : forall p q s,
p ≡* q -> p [s] ≡* q [s].
Proof.
intros p q s congruence_hyp. revert s.
induction congruence_hyp as [p q base_case | p r q transitivity_case]. 
+ induction base_case; intros; asimpl; auto with cgr.
- apply cgr_recursion. unfold core.funcomp. apply IHbase_case. admit.
- setoid_rewrite (subst_in_succ_new Q v k 0). apply cgr_scope.
- simpl. setoid_rewrite (subst_in_succ_new Q v k 0). apply cgr_scope_rev.
+ eauto with cgr.
Qed. *)

(* The old Congruence lemmas can now be restated using Autosubst's help.
   This still requires some technical work and lemmas on substitutions. *)
Arguments core.funcomp _ _ _/.

Lemma permute_subst : forall sp s Q,
  (subst2 (up_Data_proc sp) (up_Data_Data s) (Q [↑↑]))
  =
  (subst2 sp s Q) [↑↑].
Proof.
intros.
asimpl.
simpl. substify. 
reflexivity.
Qed.

(* Lemma subst_and_ren :
forall p sp s,
  subst_proc (up_Data_proc (up_Data_proc sp)) (up_Data_Data (up_Data_Data s)) p
=
subst_proc (up_Data_proc (up_Data_proc sp)) (up_Data_Data (up_Data_Data s))
(subst_proc
 (fun x : nat => var_proc (idsRen x))
 (fun x : nat => var_Data
  match x return nat with
| O => S O
| S n0 => match n0 return nat with
| O => O
| S _ => x
end
end) p).
Proof.
intro p sp s. *)

Instance SubstProper : Proper (eq ==> eq ==> cgr ==> cgr) subst2.
Proof.
intros sp' sp Hp s' s Hs q1 q2 Hq.
induction Hq as [p q base_case | p r q transitivity_case].
- subst. revert sp s. induction base_case; intros; try solve [asimpl; auto with cgr].
  (* + simpl. unfold subst2. simpl. substify. simpl. Set Printing All. *)
  + unfold subst2. simpl. rewrite permute_subst. exact (cgr_scope _ _).
  + unfold subst2. simpl. rewrite permute_subst. exact (cgr_scope_rev _ _).
- subst. now rewrite IHtransitivity_case.
Qed.

Definition νs n q := Nat.iter n (fun p => ν p) q.

Instance NewsProper : Proper (eq ==> cgr ==> cgr) νs.
Proof.
intros n ? <- p1 p2 Heq. induction n.
- now simpl.
- simpl. now apply cgr_res.
Qed.

Definition nvars (n : nat) (p: proc) := Nat.iter n (fun p => p [↑↑]) p.
Instance nvars_proper : Proper (eq ==> cgr ==> cgr) nvars.
Proof.
intros n ? <- p1 p2 Heq. induction n.
- now simpl.
- simpl. now rewrite IHn.
Qed.

Lemma shift_in_nvars : forall n q, nvars n q [↑↑] = nvars n (q [↑↑]).
Proof.
induction n.
- now simpl.
- intros. simpl. now rewrite IHn.
Qed.

Lemma n_extrusion : forall n p q, (νs n p) ‖ q ≡* νs n (p ‖ nvars n q).
Proof.
induction n.
- now simpl.
- intros p q. simpl. rewrite <- cgr_scope. rewrite IHn. now rewrite shift_in_nvars.
Qed.

(* Lemma Congruence_Respects_Substitution : forall p q (v:Data) k,
p ≡* q -> p [k ←  v] ≡* q [k ← v]. *)
(* Lemma Congruence_Respects_Substitution : forall p q s,
p ≡* q -> p [s] ≡* q [s].
Proof.
intros p q s congruence_hyp. revert s.
induction congruence_hyp as [p q base_case | p r q transitivity_case]. 
+ induction base_case; intros; asimpl; auto with cgr.
(* auto's simple apply is not sufficient, so we still need to apply the lemmas *)
- apply cgr_recursion. apply IHbase_case. admit.
- setoid_rewrite (subst_in_succ_new Q v k 0). apply cgr_scope.
- simpl. setoid_rewrite (subst_in_succ_new Q v k 0). apply cgr_scope_rev.
+ eauto with cgr.
Qed. *)

(* Lemma NewVar_Respects_Congruence : forall p q n, p ≡* q -> n ↑ p ≡* n ↑ q.
Proof.
intros p q n congruence_hyp. revert n.
induction congruence_hyp as [p q base_case | p r q transitivity_case]. 
+ induction base_case; simpl; auto with cgr.
  - intro n. simpl. rewrite lift_of_lift_proc. apply cgr_scope. lia.
  - intro n. simpl. rewrite lift_of_lift_proc. apply cgr_scope_rev. lia.
+ eauto with cgr.
Qed. *)


(* Substition lemma for the substitution in recursive processes *)
(* Lemma cgr_subst1 (p:proc) (q:proc) q' x : q ≡* q' → p [x ← q] ≡* p [x ← q'].
Proof.
(* Induction on the size of q*)
revert q q' x.
 induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image proc nat lt size Nat.lt_wf_0)).
destruct p; intros.
  - reflexivity.
  - reflexivity.
  - simpl. simple apply cgr_recursion, Hp. unfold lt. simple apply le_n. assumption.
  - simpl. destruct decide. assumption. simple apply cgr_refl.
  - apply cgr_fullchoice.
    * apply Hp. simpl. lia. assumption.
    * apply Hp. simpl. auto with arith. assumption.
  - apply cgr_fullpar.
    * apply Hp. simpl. auto with arith. assumption. 
    * apply Hp. simpl. auto with arith. assumption.
  - simple apply cgr_refl.
  - simpl. simple apply cgr_res. apply Hp. simpl. unfold lt. apply le_n. by apply NewVar_Respects_Congruence.
  - simpl. simple apply cgr_input. apply Hp. auto with arith. by apply NewVar_Respects_Congruence.
  - simpl. auto with cgr.
  - apply cgr_full_if.
    * apply Hp. simpl. auto with arith. assumption.
    * apply Hp. simpl. auto with arith. assumption.
Qed. *)

(* Substitution lemma for the substitution in recursive processes *)
(* Lemma cgr_step_subst2 : forall p p' q x, p ≡ p' → p [x ← q] ≡ p' [x ← q].
Proof.
  induction p
  as (p & Hp) using (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros p' q n hcgr.
  inversion hcgr; try (now constructor).
  - apply cgr_recursion_step. apply Hp. subst. unfold lt. simple apply le_n. assumption.
  - constructor. apply Hp. subst. unfold lt. simple apply le_n. assumption.
  - constructor. apply Hp. subst. unfold lt. simple apply le_n. assumption. 
  - constructor. apply Hp. subst. simpl. auto with arith. assumption. 
  - constructor. apply Hp. subst. simpl. auto with arith. assumption. 
  - constructor. apply Hp. subst. simpl. auto with arith. assumption. 
  - constructor. apply Hp; subst. simpl. auto with arith. assumption.
  - constructor. apply Hp. subst. unfold lt. simple apply le_n. assumption.
  - simpl. rewrite pr_subst_through_lift. constructor.
  - simpl. rewrite pr_subst_through_lift. constructor.
Qed. *)

(* ≡* respects the substitution of his variable *)
(* Lemma cgr_subst2 q p p' x : p ≡* p' → p [x ← q] ≡* p' [x ← q].
Proof. 
intros congruence_hyp. induction congruence_hyp as [p p' base_case | p p' p'' transitivity_case]. 
  + constructor. now eapply cgr_step_subst2.
  + apply transitivity with p' [x ← q].
    * assumption.
    * assumption.
Qed. *)

(* ≡ respects the substitution / recursion *)
(* Lemma cgr_subst p q x : p ≡ q -> p [x ← rec p] ≡* q [x ← rec q].
Proof.
  intro congruence_hyp.
  etrans.
  * eapply cgr_subst2. constructor. eassumption.
  * eapply cgr_subst1. constructor. apply cgr_recursion_step. exact congruence_hyp.
Qed. *)

#[global] Hint Resolve cgr_is_eq_rel: ccs.
#[global] Hint Constructors clos_trans:ccs.
#[global] Hint Unfold cgr:ccs.


(* State Transition System (STS-reduction), reduction semantic *)
Inductive sts : proc -> proc -> Prop :=
(*The axiomes*)
(* Communication of channels output and input that have the same name *)
| sts_com : forall {c v p1 p2 g1 g2}, 
    sts ((c ! v • p1) + g1 ‖ ((c ? p2) + g2)) (p1 ‖ p2 [v..])
(* Nothing more , something less *)
| sts_tau : forall {p g}, 
    sts ((t • p) + g) p
(* Resursion *)
| sts_recursion : forall {p}, 
    sts (rec p) (p <[(rec p)..])
(*If Yes*)
| sts_ifOne : forall {p q E}, Eval_Eq E = Some true -> 
    sts (If E Then p Else q) p
(*If No*)
| sts_ifZero : forall {p q E}, Eval_Eq E = Some false -> 
    sts (If E Then p Else q) q

(* The left parallele respect the Reduction *)
| sts_par : forall {p1 p2 q}, 
    sts p1 p2 ->
    sts (p1 ‖ q) (p2 ‖ q)

(*The Congruence respects the Reduction *)
| sts_cong : forall {p1 p2 q2 q1},
    p1 ≡* p2 -> sts p2 q2 -> q2 ≡* q1 -> sts p1 q1

| sts_res : forall {p q},
    sts p q -> sts (ν p) (ν q)
.

#[global] Hint Constructors sts:ccs.

Ltac finish_zero H := rewrite H, <- cgr_par_assoc.
Ltac finish_Sn H := simpl; rewrite H, <- cgr_par_assoc, <- n_extrusion, cgr_scope.

(* Lemma 1.2.20 from Sangiorgi and Walker *)
Lemma ReductionShape : forall P Q, sts P Q ->
((exists c v P1 P2 G1 G2 s n, (P ≡* νs n (((c ! v • P1) + G1 ‖ ((c ? P2) + G2)) ‖ s)) /\ (Q ≡* νs n ((P1 ‖ (P2[v..])) ‖ s)))
\/ (exists P1 G1 s n, (P ≡* νs n (((t • P1) + G1) ‖ s)) /\ (Q ≡* νs n (P1 ‖ s)))
\/ (exists P1 s n, (P ≡* νs n ((rec P1) ‖ s)) /\ (Q ≡* νs n (P1 <[(rec P1)..] ‖ s)))
\/ (exists P1 P0 s E n, (P ≡* νs n ((If E Then P1 Else P0) ‖ s)) /\ (Q ≡* νs n (P1 ‖ s)) /\ (Eval_Eq E = Some true))
\/ (exists P1 P0 s E n, (P ≡* νs n ((If E Then P1 Else P0) ‖ s)) /\ (Q ≡* νs n (P0 ‖ s)) /\ (Eval_Eq E = Some false))
).
Proof.
intros P Q Transition.
induction Transition.
  - left. exists c, v, p1, p2, g1, g2, 𝟘, 0. split; apply cgr_par_nil_rev.
  - right. left. exists p, g, 𝟘, 0. split; apply cgr_par_nil_rev.
  - right. right. left. exists p, 𝟘, 0. split; apply cgr_par_nil_rev.
  - right. right. right. left. exists p, q, 𝟘, E, 0.
    repeat split. apply cgr_par_nil_rev. apply cgr_par_nil_rev.  assumption.
  - right. right. right. right. exists p, q, 𝟘, E, 0.
    repeat split. apply cgr_par_nil_rev. apply cgr_par_nil_rev. assumption.
  - destruct IHTransition as [IH|[IH|[IH|[IH |IH]]]].
    + destruct IH as [c [v [P1 [P2 [g1 [g2 [s [n [H1 H2]]]]]]]]]. left. intros. simpl in H1, H2.
      destruct n.
      * exists c, v, P1, P2, g1,g2, (s ‖ q), 0. simpl. split; [ now finish_zero H1 | now finish_zero H2 ].
      * exists c, v, P1, P2, g1,g2, (s ‖ nvars n (q [↑↑])), (S n). split; [ now finish_Sn H1 | now finish_Sn H2 ].
    + destruct IH as (P1 & P2 & s & n & [H1 H2]). right. left. destruct n; intros; simpl in H1, H2.
      * exists P1, P2, (s ‖ q), 0. split; [ now finish_zero H1 | now finish_zero H2 ].
      * exists P1, P2, (s ‖ nvars n (q [↑↑])), (S n). split; [ now finish_Sn H1 | now finish_Sn H2 ].
    + destruct IH as (P1 & s & n & [H1 H2]). right. right. left. destruct n; simpl in H1, H2.
      * exists P1, (s ‖ q), 0. split; [ now finish_zero H1 | now finish_zero H2 ].
      * exists P1, (s ‖ nvars n (q [↑↑])), (S n). split; [ now finish_Sn H1 | now finish_Sn H2 ].
    + destruct IH as (P1 & P0 & s & E & n & [H1 [H2 H3]]).  right. right. right. left. destruct n; simpl in H1, H2.
      * exists P1, P0, (s ‖ q), E, 0. split; [ now finish_zero H1 | now finish_zero H2 ].
      * exists P1, P0, (s ‖ nvars n (q [↑↑])), E, (S n). repeat split; [ now finish_Sn H1 | now finish_Sn H2 | assumption ].
    + destruct IH as (P1 & P0 & s & E & n & [H1 [H2 H3]]). right. right. right. right. destruct n; simpl in H1, H2.
      * exists P1, P0, (s ‖ q), E, 0. split; [ now finish_zero H1 | now finish_zero H2 ].
      * exists P1, P0, (s ‖ nvars n (q [↑↑])), E, (S n). repeat split; [ now finish_Sn H1 | now finish_Sn H2 | assumption ].
  - destruct IHTransition as [IH|[IH|[IH|[IH |IH]]]].
    + destruct IH as [c [v [P1 [P2 [g1 [g2 [s [n [H1 H2]]]]]]]]].
      left. exists c, v, P1, P2, g1, g2, s, n. split; [ now rewrite <- H1 | now rewrite <- H2 ].
    + destruct IH as [P1 [P2 [s [n [H1 H2]]]]].
      right. left. exists P1, P2, s, n. split; [ now rewrite <- H1 | now rewrite <- H2 ].
    + destruct IH as [P1 [s [n [H1 H2]]]].
      right. right. left. exists P1, s, n. split; [ now rewrite <- H1 | now rewrite <- H2 ].
    + destruct IH as [P1 [P0 [s [E [n [H1 [H2 H3]]]]]]].
      right. right. right. left. exists P1, P0, s, E, n. repeat split; [ now rewrite <- H1 | now rewrite <- H2 | assumption ].
    + destruct IH as [P1 [P0 [s [E [n [H1 [H2 H3]]]]]]].
      right. right. right. right. exists P1, P0, s, E, n. repeat split; [ now rewrite <- H1 | now rewrite <- H2 | assumption ].
  - destruct IHTransition as [IH|[IH|[IH|[IH |IH]]]].
    + destruct IH as [c [v [P1 [P2 [g1 [g2 [s [n [H1 H2]]]]]]]]].
      left. exists c, v, P1, P2, g1, g2, s, (S n). split; [now rewrite H1 | now rewrite H2 ].
    + destruct IH as [P1 [P2 [s [n [H1 H2]]]]].
      right. left. exists P1, P2, s, (S n). split; [ now rewrite H1 | now rewrite H2 ].
    + destruct IH as [P1 [s [n [H1 H2]]]].
      right. right. left. exists P1, s, (S n). split; [ now rewrite H1 | now rewrite H2 ].
    + destruct IH as [P1 [P0 [s [E [n [H1 [H2 H3]]]]]]].
      right. right. right. left. exists P1, P0, s, E, (S n). repeat split; [ now rewrite H1 | now rewrite H2 | assumption ].
    + destruct IH as [P1 [P0 [s [E [n [H1 [H2 H3]]]]]]].
      right. right. right. right. exists P1, P0, s, E, (S n). repeat split; [ now rewrite H1 | now rewrite H2 | assumption ].
Qed.


(* The Labelled Transition System (LTS-transition) *)
Inductive lts : proc-> Act -> proc -> Prop :=
(*The Input and the Output*)
| lts_input : forall {c v P},
    lts (c ? P) (ActIn (c ⋉ v)) (P [v ..])
| lts_output : forall {c v P},
    lts (c ! v • P) (FreeOut (c ⋉ v)) P

(*The actions Tau*)
| lts_tau : forall {P},
    lts (t • P) τ P
| lts_recursion : forall {P},
    lts (rec P) τ ((rec P) <[P ..])
| lts_ifOne : forall {p q E}, Eval_Eq E = Some true -> 
    lts (If E Then p Else q) τ p
| lts_ifZero : forall {p q E}, Eval_Eq E = Some false -> 
    lts (If E Then p Else q) τ q

(* Communication of a channel output and input that have the same name*)
| lts_comL : forall {c v p1 p2 q1 q2},
    lts p1 (FreeOut (c ⋉ v)) p2 ->
    lts q1 (ActIn (c ⋉ v)) q2 ->
    lts (p1 ‖ q1) τ (p2 ‖ q2) 
| lts_comR : forall {c v p1 p2 q1 q2},
    lts p1 (FreeOut (c ⋉ v)) p2 ->
    lts q1 (ActIn (c ⋉ v)) q2 ->
    lts (q1 ‖ p1) τ (q2 ‖ p2)

(* Scoped rules *)
| lts_close_l : forall {c v p1 p2 q1 q2},
    lts p1 (BoundOut (c ⋉ v)) p2 ->      (* this term is an "open" term, (see the lts_open rule) *)
    lts q1 (ActIn (c ⋉ v)) q2 ->         (* while this one is a "closed" term *)
    lts (p1 ‖ q1) τ (ν (p2 ‖ (q2 [↑↑]))) (* so whe should shift q2 here. This corresponds to cgr_scope (scope extrusion) *)
| lts_close_r : forall {c v p1 p2 q1 q2},
    lts q1 (BoundOut (c ⋉ v)) q2 ->
    lts p1 (ActIn (c ⋉ v)) p2 ->
    lts (p1 ‖ q1) τ (ν (p2 ‖ q2))
| lts_res : forall {p q α},
    lts p α q ->
    lts (ν p) α (ν q) (* only α needs to shift here!! (both chan and value).
                         as a consequence, the channel in α can never be 0 (giving the condition in paper)
                         as in onther places: we started with an "open" value, that's why we add a flat ν *)
| lts_open : forall {c p1 p2}, (** remark: we are adding a ν but we are not shifting. this corresponds to the intuition in momigliano&cecilia that free rules handle open terms *)
    c <> var_Data 0 ->
    lts p1 (FreeOut (c ⋉ (var_Data 0))) p2 ->       (** condition: c must not be 0 ! *)
    lts (ν p1) (BoundOut (c ⋉ (var_Data 0))) p2     (* this should happen only when v = 0 *)
                                                    (* note that p2 is now an open term. its scope is going to be closed in the close rule *)

| lts_parL : forall {α p1 p2 q},
    lts p1 α p2 ->
    lts (p1 ‖ q) α (p2 ‖ q)
| lts_parR : forall {α p q1 q2}, 
    lts q1 α q2 ->
    lts (p ‖ q1) α (p ‖ q2)
| lts_choiceL : forall {p1 p2 q α},
    lts p1 α q -> 
    lts (p1 + p2) α q
| lts_choiceR : forall {p1 p2 q α},
    lts p2 α q -> 
    lts (p1 + p2) α q
.

(* observations: a closed term does no visible actions (only τ) *)

#[global] Hint Constructors lts:ccs.

(* For the (LTS-transition), the transitable terms and transitted terms, that performs a INPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForInput : forall P Q c v, (lts P (ActIn (c ⋉ v))) Q -> 
exists P1 G R n, (P ≡* νs n ((c ? P1 + G) ‖ R)) /\ (Q ≡* νs n (P1[v..] ‖ R)).
(* /\ ((exists L,P = (g L)) -> R = 𝟘))). *)
Proof.
intros P Q c v Transition.
 dependent induction Transition.
- exists P, 𝟘, 𝟘, 0. split; eauto with cgr.
- destruct (IHTransition c v eq_refl) as [P1 [G [R [n [H0 H1]]]]]. exists P1, G, R, (S n). split.
  + now rewrite H0.
  + now rewrite H1.
- destruct (IHTransition c v eq_refl) as [P1 [G [R [n [H0 H1]]]]]. destruct n; intros; simpl in H0, H1.
  + exists P1, G, (R ‖ q), 0. simpl. split; [now finish_zero H0 | now finish_zero H1 ].
  + exists P1, G, (R ‖ nvars n (q [↑↑])), (S n). split; [ now finish_Sn H0 | now finish_Sn H1 ].
- destruct (IHTransition c v eq_refl) as [P1 [G [R [n [H0 H1]]]]]. destruct n; intros; simpl in H0, H1.
  + exists P1, G, (R ‖ p), 0. simpl. split; [rewrite H0|rewrite H1]; now rewrite cgr_par_com, cgr_par_assoc.
  + exists P1, G, (R ‖ nvars n (p [↑↑])), (S n). simpl. split; [finish_Sn H0| finish_Sn H1]; now rewrite cgr_par_com.
- destruct (IHTransition c v eq_refl) as [P1 [G [R [n [H0 H1]]]]]. destruct n; intros; simpl in H0, H1.
  + exists P1, G, R, 0. simpl. split.
    * rewrite H0. admit.
    * now rewrite H1.
  + exists P1, G, R, (S n). simpl. split.
    * rewrite H0. admit.
    * now rewrite H1.
- destruct (IHTransition c v eq_refl) as [P1 [G [R [n [H0 H1]]]]]. destruct n; intros; simpl in H0, H1.
  + exists P1, G, (R ‖ q), 0. simpl. split.
    * rewrite H0. rewrite cgr_par_com. now rewrite cgr_par_assoc.
    * rewrite H1. rewrite cgr_par_com. now rewrite cgr_par_assoc.
  + exists P1, G, (R ‖ nvars n (p [↑↑])), (S n). simpl. split; [finish_Sn H0| finish_Sn H1]; now rewrite cgr_par_com.

(* - destruct (IHTransition c v eq_refl). decompose record H.
  exists x. exists (x0 + p2). exists 𝟘. split.
  * rewrite cgr_par_nil. rewrite <- cgr_choice_assoc. apply cgr_choice.
  * transitivity ((c ? x) + (x0 + p2)).
    ** apply cgr_trans with (((c ? x) + x0) + p2).
      *** apply cgr_choice. assert (x1 = 𝟘).
          **** apply H3. exists p1. reflexivity. admit.
          **** rewrite H1 in H0. apply transitivity with (((c ? x) + x0) ‖ 𝟘).
               ***** assumption.
               ***** apply cgr_par_nil.
      *** apply cgr_choice_assoc.
    ** apply cgr_par_nil_rev.
  * assert (x1 = 𝟘). apply H3. exists p1. reflexivity. rewrite H2 in H1. assumption.
  * reflexivity. *)
Qed.


(* Lemma guarded_does_no_output : forall p c v q, ¬ lts (g p) (ActOut (c ⋉ v)) q.
Proof. 
intros. intro Transition. 
dependent induction Transition;eapply IHTransition; eauto.
Qed. *)

(* For the (LTS-transition), the transitable terms and transitted terms, that performs a OUPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForOutput : forall P Q c v, (lts P (FreeOut (c ⋉ v)) Q) ->
exists G R n, P ≡* νs n (c ! v • G ‖ R) /\ Q ≡* νs n (G ‖ R).
Proof.
intros P Q c v Transition.
dependent induction Transition; try destruct (IHTransition c v eq_refl) as [G [R [n [H0 H1]]]].
- exists P, 𝟘, 0. split; apply cgr_par_nil_rev.
- exists G, R, (S n). split; simpl; [now rewrite H0 | now rewrite H1].
- destruct n.
  + exists G, (R ‖ q), 0. split; [ now finish_zero H0 | now finish_zero H1 ].
  + exists G, (R ‖ nvars n (q [↑↑])), (S n). split; [now finish_Sn H0 | now finish_Sn H1].
- destruct n; simpl in H0, H1.
  + exists G, (R ‖ p), 0. simpl. split; [rewrite H0|rewrite H1]; now rewrite cgr_par_com, cgr_par_assoc.
  + exists G, (R ‖ nvars n (p [↑↑])), (S n). simpl. split; [finish_Sn H0| finish_Sn H1]; now rewrite cgr_par_com.
- destruct n; simpl in H0, H1.
  + exists G, R, 0. simpl. split.
    * rewrite H0. admit.
    * now rewrite H1.
  + exists G, R, (S n). simpl. split.
    * rewrite H0. admit.
    * now rewrite H1.
- destruct n; simpl in H0, H1.
  + exists G, R, 0. simpl. split.
    * rewrite H0. rewrite cgr_par_com. now rewrite cgr_par_assoc. admit.
    * now rewrite H1.
  + exists G, R, (S n). simpl. split.
    * admit.
    * now rewrite H1.
(* - edestruct guarded_does_no_output. eauto. *)
Admitted.


(* Lemma TransitionShapeForOutputSimplified : forall P Q c v, (lts P (FreeOut (c ⋉ v)) Q) 
                                        -> (P ≡* ((c ! v • 𝟘) ‖ Q)).
Proof.
intros. 
destruct (TransitionShapeForOutput P Q c v H) as [G [R [n [H0 H1]]]].

apply transitivity with (((c ! v • 𝟘) ‖ x) ‖ 𝟘). apply transitivity with ((c ! v • 𝟘) ‖ x); eauto.
auto with cgr. apply transitivity with ((c ! v • 𝟘) ‖ (x ‖ 𝟘)). auto with cgr. apply cgr_fullpar. auto with cgr.
eauto with cgr. 
Qed.  *)


(* For the (LTS-transition), the transitable Guards and transitted terms, that performs a Tau ,
are pretty all the same, up to ≡* *)
(* Lemma TransitionShapeForTauAndGuard : forall P V, lts P τ V -> 
exists M, P ≡* (t • V) + M.
Proof.
intros P V (Transition & guard_witness). 
dependent induction Transition.
  - exists P. exists 𝟘. split. 
    * apply cgr_choice_nil_rev.
    * apply cgr_refl.
  - inversion guard_witness as (g & impossible_hyp). inversion impossible_hyp.
  - inversion guard_witness as (g & impossible_hyp). inversion impossible_hyp.
  - inversion guard_witness as (g & impossible_hyp). inversion impossible_hyp.
  - inversion guard_witness as (g & impossible_hyp). inversion impossible_hyp.
  - inversion guard_witness as (g & impossible_hyp). inversion impossible_hyp.
  - inversion guard_witness as (g & impossible_hyp). inversion impossible_hyp.
  - inversion guard_witness as (g & impossible_hyp). inversion impossible_hyp.
  - destruct (IHTransition (reflexivity τ)).
    * exists p1. reflexivity.
    * destruct H. destruct H.  exists x. 
      exists (x0 + p2). split; eauto. apply cgr_trans with (((t • x) + x0) + p2).
      apply cgr_choice. assumption.
      apply cgr_choice_assoc. 
  - destruct (IHTransition (reflexivity τ)).
    * exists p2. reflexivity.
    * destruct H. destruct H.  exists x. 
      exists (x0 + p1). split; eauto. apply cgr_trans with (((t • x) + x0) + p1). apply cgr_trans with (p2 + p1). 
      apply cgr_choice_com. apply cgr_choice. assumption. apply cgr_choice_assoc.
Qed. *)

(* p 'is equivalent some r 'and r performs α to q *)
Definition sc_then_lts p α q := exists r, p ≡* r /\ (lts r α q).

(* p performs α to some r and this is equivalent to q*)
Definition lts_then_sc p α q := exists r, ((lts p α r) /\ r ≡* q).


(* p 'is equivalent some r 'and r performs α to q , the congruence and the Transition can be reversed : *)
(* fact 1.4.16 in Sangiorgi&Walker *)
Lemma Congruence_Respects_Transition  : forall p q α, sc_then_lts p α q -> lts_then_sc p α q.
Proof. 
(* by induction on the congruence and the step then...*)
  intros p q α (p' & hcgr & l).
  revert q α l.
  dependent induction hcgr.
  - dependent induction H.
    + intros q α l. exists q. split. exact l. reflexivity.
    + intros q α l. exists (q ‖ 𝟘). split. apply lts_parL. assumption. apply cgr_par_nil.
    + intros q α l. dependent destruction l.
      * inversion l2.
      * inversion l1.
      * inversion l2.
      * inversion l1.
      * exists p2. split. assumption. apply cgr_par_nil_rev.
      * inversion l.
    + intros r α l. dependent destruction l.
      * exists (q2 ‖ p2). split; [apply (@lts_comR c v _ _ _ _ l1 l2) | apply cgr_par_com].
      * exists (p2 ‖ q2). split; [apply (@lts_comL c v _ _ _ _ l1 l2) | apply cgr_par_com].
      * eexists. split. apply (lts_close_r l1 l2). apply cgr_res. apply cgr_par_com. 
      * eexists. split. apply (lts_close_l l1 l2). apply cgr_res. apply cgr_par_com.
      * exists (p ‖ p2). split. apply (lts_parR l). apply cgr_par_com.
      * exists (q2 ‖ q). split. apply (lts_parL l). apply cgr_par_com.
    + intros. dependent destruction l.
      * dependent destruction l2. 
         ** exists ((p2 ‖ p0) ‖ r). split.
           apply lts_parL. apply (@lts_comL c v _ _ _ _ l1 l2). apply cgr_par_assoc.
         ** exists ((p2 ‖ q) ‖ q2). split. apply (@lts_comL c v). apply (lts_parL l1). assumption.
           apply cgr_par_assoc.
      * dependent destruction l1. 
         ** exists ((q2 ‖ p2) ‖ r). split. apply lts_parL. apply (@lts_comR c v). assumption.
           assumption. auto with cgr.
         ** exists ((q2 ‖ q) ‖ q0). split. apply (@lts_comR c v). assumption. apply lts_parL.
           assumption. auto with cgr.
      * admit. (* bound *)
      * admit. (* bound*)
      * exists ((p2 ‖ q) ‖ r). split. apply lts_parL. apply lts_parL. assumption. auto with cgr.
      * dependent destruction l.
         ** exists ((p ‖ p2) ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). apply lts_parR. assumption. assumption.
           auto with cgr.
         ** exists ((p ‖ q2) ‖ p2). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption. apply lts_parR.
           assumption. auto with cgr.
         ** admit. (* bound *)
         ** admit. (* bound *)
         ** exists ((p ‖ p2) ‖ r). split. apply lts_parL. apply lts_parR. assumption. auto with cgr.
         ** exists ((p ‖ q) ‖ q2). split. apply lts_parR. assumption. auto with cgr.
    + intros. dependent destruction l.
      * dependent destruction l1. 
         ** exists (p2 ‖ (q ‖ q2)). split.
           eapply lts_comL. instantiate (1:= v). instantiate (1:= c). assumption. apply lts_parR. assumption. auto with cgr.
         ** exists (p ‖ (q0 ‖ q2)). split. apply lts_parR. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). assumption.
           assumption. auto with cgr.
      * dependent destruction l2. 
         ** exists (p0 ‖ (q ‖ p2)). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). apply lts_parR. assumption.
           assumption. auto with cgr.
         ** exists (p ‖ (q2 ‖ p2)). split. apply lts_parR.  eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption.
           assumption. auto with cgr.
      * admit. (* bound *)
      * admit. (* bound *)
      * dependent destruction l.
         ** exists (p2 ‖ (q2 ‖ r)). split. apply (@lts_comL c v). assumption. apply lts_parL.
           assumption. auto with cgr.
         ** exists (q2 ‖ (p2 ‖ r)). split. apply (@lts_comR c v). apply lts_parL. assumption.
           assumption. auto with cgr.
         ** admit. (* bound *)
         ** admit. (* bound *)
         ** exists (p2 ‖ ( q ‖ r)). split. apply lts_parL. assumption. auto with cgr.
         ** exists (p ‖ (q2 ‖ r)). split. apply lts_parR. apply lts_parL. assumption. auto with cgr.
      * exists (p ‖ (q ‖ q2)). split. apply lts_parR.  auto. apply lts_parR. assumption. auto with cgr.
    + intros. exists q.  split. apply lts_choiceL. assumption. auto with cgr.
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
    + intros. dependent destruction l. eexists. split. apply lts_recursion.
       assert (p ≡* q) by now constructor. rewrite H0. admit. (** substitution in recursion? *)
    + intros. dependent destruction l. exists p.  split. apply lts_tau.
      constructor. assumption.
    + intros. dependent destruction l. exists (p [v..]). split. apply lts_input.
      assert (p ≡* q) by now constructor. now rewrite H0.
    + intros. dependent destruction l.
      * destruct (IHcgr_step p2 (FreeOut (c ⋉ v))).  exact l1. destruct H0. exists (x ‖ q2).
        split. eapply lts_comL. exact H0. assumption.
        apply cgr_fullpar. assumption. reflexivity.
      * destruct (IHcgr_step q2 (ActIn (c ⋉ v))). assumption. destruct H0. exists (x ‖ p2).
        split.  eapply lts_comR. exact l1. assumption.
        apply cgr_fullpar. assumption. reflexivity.
      * admit. (* bound *)
      * admit. (* bound *)
      * destruct (IHcgr_step p2 α). assumption. destruct H0. eexists.
        split. instantiate (1:= (x ‖ r)). apply lts_parL. assumption. apply cgr_fullpar.
        assumption. reflexivity.
      * eexists. split. instantiate (1:= (p ‖ q2)). apply lts_parR.
        assumption. apply cgr_par. now constructor.
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
      -- destruct (IHcgr_step q α). assumption. destruct H0. exists x. split. apply lts_choiceL. assumption. assumption.
      -- eexists. instantiate (1:= q). split. apply lts_choiceR. assumption. reflexivity.
    + intros. dependent destruction l.
    + intros. repeat dependent destruction l.
    + admit. (* res *)
    + admit. (* res *)
    + admit. (* res *)
  - intros. destruct (IHhcgr2 q α). assumption. destruct (IHhcgr1 x0 α). destruct H. assumption. exists x1. split. destruct H0. assumption.
    destruct H. destruct H0. eauto with cgr.
Qed.



(* One side of the Harmony Lemma *)
Lemma Reduction_Implies_TausAndCong : forall P Q, (sts P Q) -> (lts_then_sc P τ Q).
Proof. 
intros P Q Reduction. 
assert ((exists c v P2 G2 S, ((P ≡* ((c ! v • 𝟘) ‖ ((c ? P2) + G2)) ‖ S)) /\ (Q ≡*((𝟘 ‖ (P2^v)) ‖ S)))
\/ (exists P1 G1 S, (P ≡* (((t • P1) + G1) ‖ S)) /\ (Q ≡* (P1 ‖ S)))
\/ (exists n P1 S, (P ≡* ((rec n • P1) ‖ S)) /\ (Q ≡* (pr_subst n P1 (rec n • P1) ‖ S)))
\/ (exists P1 P0 S E, (P ≡* ((If E Then P1 Else P0) ‖ S)) /\ (Q ≡* P1 ‖ S) /\ (Eval_Eq E = Some true))
\/ (exists P1 P0 S E, (P ≡* ((If E Then P1 Else P0) ‖ S)) /\ (Q ≡* P0 ‖ S) /\ (Eval_Eq E = Some false))
). 
apply ReductionShape. exact Reduction.
destruct H as [IH|[IH|[IH|[IH |IH]]]]. 

(*First case τ by communication *)

- decompose record IH.
  assert (lts ((x ! x0 • 𝟘) ‖ ((x ? x1) + x2) ‖ x3) τ (𝟘 ‖ (x1^x0) ‖ x3)).
  * apply lts_parL.   
    eapply lts_comL. instantiate (2:= x). instantiate (1:= x0).
    apply lts_output. apply lts_choiceL. apply lts_input.
  * assert (sc_then_lts P τ ((𝟘 ‖ x1^x0) ‖ x3)). exists (((x ! x0 • 𝟘) ‖ ((x ? x1) + x2)) ‖ x3). split. assumption. assumption.
    assert (lts_then_sc P τ ((𝟘 ‖ x1^x0) ‖ x3)). apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3.
    exists x4. split. assumption. apply transitivity with ((𝟘 ‖ x1^x0) ‖ x3). assumption. symmetry. assumption.

(*Second case τ by Tau Action *)

- decompose record IH.
  assert (lts ((t • x + x0) ‖ x1) τ (x ‖ x1)). constructor.
  apply lts_choiceL. apply lts_tau.
  assert (sc_then_lts P τ (x ‖ x1)). exists ((t • x + x0) ‖ x1). split. assumption. apply lts_parL.
  apply lts_choiceL. apply lts_tau.
  assert (lts_then_sc P τ (x ‖ x1)). apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3. 
  exists x2. split. assumption. apply transitivity with (x ‖ x1). assumption. symmetry. assumption.

(*Third case τ by recursion *)

- decompose record IH.
  assert (lts (rec x • x0 ‖ x1) τ (pr_subst x x0 (rec x • x0) ‖ x1)). 
  constructor. apply lts_recursion. assert (sc_then_lts P τ ((pr_subst x x0 (rec x • x0) ‖ x1))). 
  exists (rec x • x0 ‖ x1). split. assumption. assumption. assert (lts_then_sc P τ (pr_subst x x0 (rec x • x0) ‖ x1)). 
  apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3. 
  exists x2. split. assumption. apply transitivity with (pr_subst x x0 (rec x • x0) ‖ x1). assumption.
  symmetry. assumption.

(*Fourth case τ by If ONE*)

- destruct IH. destruct H. destruct H. destruct H. destruct H. destruct H0. 
  assert (lts ((If x2 Then x Else x0) ‖ x1) τ (x ‖ x1)). constructor. apply lts_ifOne. assumption.
  assert (sc_then_lts P τ (x ‖ x1)). exists ((If x2 Then x Else x0) ‖ x1). split. assumption.
  constructor. constructor. assumption. 
  assert (lts_then_sc P τ (x ‖ x1)). apply Congruence_Respects_Transition. 
  exists ((If x2 Then x Else x0) ‖ x1). split. assumption. assumption. destruct H4. destruct H4.
  exists x3. split. assumption. apply transitivity with (x ‖ x1). assumption. 
  symmetry. assumption.

(*Fifth case τ by If ZERO*)

- destruct IH. destruct H. destruct H. destruct H. destruct H. destruct H0. 
  assert (lts ((If x2 Then x Else x0) ‖ x1) τ (x0 ‖ x1)). constructor. apply lts_ifZero. assumption.
  assert (sc_then_lts P τ (x0 ‖ x1)). exists ((If x2 Then x Else x0) ‖ x1). split. assumption.
  apply lts_parL. apply lts_ifZero. assumption.
  assert (lts_then_sc P τ (x0 ‖ x1)). apply Congruence_Respects_Transition. 
  exists ((If x2 Then x Else x0) ‖ x1). split.  assumption. assumption. destruct H4. destruct H4.
  exists x3. split. assumption. apply transitivity with (x0 ‖ x1). assumption.
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
intros ? Hyp ? ? transition_then_congruence_hyp. 
destruct transition_then_congruence_hyp as (R & transition & cong).
eapply sts_cong. 
* apply cgr_refl. 
* apply Hyp. exact transition.
* exact cong.
Qed.

Lemma Taus_Implies_Reduction : forall P Q, (lts P τ Q) -> (sts P Q).
Proof. 
intros P Q Transition.
dependent induction Transition.
  - eapply sts_cong.  instantiate (1:=  ((t • P) + 𝟘)). apply cgr_choice_nil_rev. eapply sts_tau. reflexivity.
  - apply sts_recursion.
  - apply sts_ifOne. assumption.
  - apply sts_ifZero. assumption.
  - destruct (TransitionShapeForOutput p1 p2 c v). assumption.  decompose record H.
    destruct (TransitionShapeForInput q1 q2 c v). assumption. decompose record H2.
    eapply sts_cong. instantiate (1:=((c ! v • 𝟘) ‖ ((c ? x0) + x1)) ‖ (x ‖ x2)).
    apply cgr_trans with ((c ! v • 𝟘 ‖ x) ‖ (((c ? x0) + x1) ‖ x2)). apply cgr_fullpar. assumption. assumption.
    apply InversionParallele. 
    instantiate (1 := (𝟘 ‖ (x0^v)) ‖ (x ‖ x2)). apply sts_par.
    apply sts_com. 
    apply transitivity with ((𝟘 ‖ x) ‖ ((x0^v) ‖ x2)). apply InversionParallele. apply cgr_fullpar. 
    symmetry. assumption. symmetry. assumption.
  - destruct (TransitionShapeForOutput p1 p2 c v). assumption. decompose record H.
    destruct (TransitionShapeForInput q1 q2 c v). assumption. decompose record H2.
    eapply sts_cong. instantiate (1:=((c ! v • 𝟘) ‖ ((c ? x0) + x1)) ‖ (x ‖ x2)).
    apply transitivity with (p1 ‖ q1). apply cgr_par_com.
    apply transitivity with (((c ! v • 𝟘) ‖ x) ‖ (((c ? x0) + x1) ‖ x2)).
    apply cgr_fullpar. assumption. assumption. apply InversionParallele. 
    instantiate (1 := (𝟘 ‖ (x0^v)) ‖ (x ‖ x2)). apply sts_par. apply sts_com.
    apply transitivity with ((𝟘 ‖ x) ‖ ((x0^v) ‖ x2)). apply InversionParallele. apply transitivity with (p2 ‖ q2). apply cgr_fullpar. 
    symmetry. assumption. symmetry. assumption. apply cgr_par_com.
- apply sts_par. apply IHTransition. reflexivity.
- eapply sts_cong. instantiate (1:= q1 ‖ p). apply cgr_par_com. instantiate (1:= q2 ‖ p).
  apply sts_par. apply IHTransition. reflexivity. apply cgr_par_com.
- destruct (TransitionShapeForTauAndGuard (g p1) q). split. assumption. exists p1. reflexivity.
  decompose record H.
  eapply sts_cong. instantiate (1:= ((t • x) + (x0 + p2))).
  apply transitivity with (g (((t • x) + x0) + p2)). apply cgr_choice. assumption. apply cgr_choice_assoc.
  instantiate (1:= x). apply sts_tau. symmetry. assumption.
- destruct (TransitionShapeForTauAndGuard (g p2) q). split. assumption. exists p2. reflexivity.
  decompose record H. eapply sts_cong. instantiate (1:= ((t • x) + (x0 + p1))).
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

(*The next work is for making 'bvar' always relates to an input*) 

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

(* the 'bvar' always relates to a input *)
Inductive Well_Defined_Input_in : nat -> proc -> Prop :=
| WD_par : forall k p1 p2, Well_Defined_Input_in k p1 -> Well_Defined_Input_in k p2 
                -> Well_Defined_Input_in k (p1 ‖ p2)
| WD_var : forall k i, Well_Defined_Input_in k (pr_var i)
| WD_rec : forall k x p1, Well_Defined_Input_in k p1 -> Well_Defined_Input_in k (rec x • p1)
| WD_if_then_else : forall k p1 p2 C, Well_Defined_Condition k C -> Well_Defined_Input_in k p1 
                    -> Well_Defined_Input_in k p2 
                        -> Well_Defined_Input_in k (If C Then p1 Else p2)
| WD_success : forall k, Well_Defined_Input_in k (①)
| WD_nil : forall k, Well_Defined_Input_in k (𝟘)
| WD_input : forall k c p, Well_Defined_Input_in (S k) p
                  -> Well_Defined_Input_in k (c ? p)
| WD_output : forall k c v, Well_Defined_Data k v 
                  -> Well_Defined_Input_in k (c ! v • 𝟘)
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
- intros. constructor. dependent destruction H. apply Inequation_k_data. assumption.
- destruct g0.
  ** intros. constructor.
  ** intros. constructor.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
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
- dependent induction e. 
-- intros. simpl. constructor.
-- intros. simpl. constructor.
-- dependent induction a; dependent induction a0.
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
-- intros. dependent destruction H. simpl. constructor. apply IHe1. assumption. apply IHe2. assumption.
-- intros. dependent destruction H. simpl. constructor. apply IHe. assumption.
Qed.

Lemma WD_and_subst_rec : forall k p v, Well_Defined_Input_in (S k) p -> Well_Defined_Input_in k (subst_in_proc k (cst v) p).
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
* intros. simpl. dependent destruction H. constructor. apply ForData. assumption.
* destruct g0.
  - intros. simpl. constructor.
  - intros. simpl. constructor.
  - intros. simpl. constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. dependent destruction H. constructor.
    -- assert (Well_Defined_Input_in k (subst_in_proc k v (g0_1))). apply Hp.
      simpl.  auto with arith. assumption. assumption.
    -- assert (Well_Defined_Input_in k (subst_in_proc k v (g0_2))). apply Hp.
      simpl.  auto with arith. assumption. assumption.
Qed.

Lemma WD_data_and_NewVar : forall d k i, Well_Defined_Data (k + i) d 
                          -> Well_Defined_Data (S (k + i)) (NewVar_in_Data i d).
Proof.
dependent induction d; intros.
- simpl. constructor.
- simpl. destruct (decide (i < S n)).
  * constructor. simpl. dependent destruction H. auto with arith.
  * constructor. dependent destruction H. apply transitivity with i.
    apply Nat.nlt_succ_r. assumption.
    auto with arith. 
Qed.

Lemma WD_eq_and_NewVar : forall e k i, Well_Defined_Condition (k + i) e 
                          -> Well_Defined_Condition (S (k + i)) (NewVar_in_Equation i e).
Proof.
intro. dependent induction e; intros; simpl. 
* constructor.
* constructor.
* dependent destruction H.  constructor; apply WD_data_and_NewVar ; assumption.
* dependent destruction H. constructor. 
  - apply IHe1. assumption.
  - apply IHe2. assumption.
* dependent destruction H. constructor. apply IHe. assumption.
Qed.

Lemma WD_and_NewVar : forall k i p, Well_Defined_Input_in (k + i) p -> Well_Defined_Input_in ((S k) + i) (NewVar i p).
Proof.
intros. revert H. revert k i.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros; simpl.
* dependent destruction H. constructor.
   - apply Hp. simpl. auto with arith. assumption.
   - apply Hp. simpl. auto with arith. assumption.
* constructor.
* constructor. dependent destruction H. apply Hp. simpl. auto with arith. assumption.
* dependent destruction H. constructor. apply  WD_eq_and_NewVar. assumption.
   - apply Hp. simpl. auto with arith. assumption.
   - apply Hp. simpl. auto with arith. assumption.
* constructor. dependent destruction H. apply WD_data_and_NewVar. assumption.
* destruct g0; intros; simpl.
  - constructor.
  - constructor.
  - dependent destruction H. constructor. 
    assert (S (S (k + i)) = (S k + S i)%nat). simpl. auto with arith.
    rewrite H0. apply Hp. simpl. auto with arith. assert ((k + S i)%nat = S (k + i)).  auto with arith. rewrite H1. assumption.
  - constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - dependent destruction H. constructor.
    -- assert (S (k + i) = (S k + i)%nat). auto with arith. rewrite H1.
       assert (Well_Defined_Input_in (S k + i) (NewVar i (g g0_1))).
       apply Hp. simpl. auto with arith. assumption. assumption.
    -- assert (S (k + i) = (S k + i)%nat). auto with arith. rewrite H1.
       assert (Well_Defined_Input_in (S k + i) (NewVar i (g g0_2))).
       apply Hp. simpl. auto with arith. assumption. assumption.
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
* intros. simpl. assumption.
* destruct g0. 
  ** intros. simpl. constructor.
  ** intros. simpl. constructor.
  ** intros. simpl. constructor. dependent destruction H. apply Hp. 
    - simpl;auto with arith.
    - assert ((S k) = ((S k) + 0)%nat). auto with arith. rewrite H1. apply (WD_and_NewVar k 0 p0).
      assert (k = (k + 0)%nat). auto with arith. rewrite <-H2. assumption. 
    - assumption.
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

Lemma STS_Respects_WD : forall p q, Well_Defined_Input_in 0 p -> sts p q -> Well_Defined_Input_in 0 q.
Proof.
intros. revert H. rename H0 into Reduction. dependent induction Reduction.
* intros. constructor.
  - constructor.
  - dependent destruction H. dependent destruction H0. dependent destruction H0_. 
    dependent destruction H. apply Well_Def_Data_Is_a_value in H. destruct H. subst.  apply WD_and_subst_rec. assumption. 
* intros. dependent destruction H. dependent destruction H. assumption.
* intros. dependent destruction H. apply RecursionOverReduction_is_WD. constructor. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H. constructor. apply IHReduction. assumption. assumption.
* intros. apply Congruence_Respects_WD with q2. apply IHReduction. apply Congruence_Respects_WD with p1. 
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
Qed.

Lemma LTS_Respects_WD : forall p q α, Well_Defined_Input_in 0 p -> Well_Defined_Action α -> lts p α q 
            ->  Well_Defined_Input_in 0 q.
Proof.
intros. revert H. revert H0. rename H1 into Transition. dependent induction Transition.
* intros. dependent destruction H0.  apply WD_and_subst_rec. dependent destruction H. assumption.
* intros. constructor.
* intros. dependent destruction H. assumption.
* intros. apply ForRecursionSanity. dependent destruction H. assumption. assumption.
* intros. dependent destruction H1. assumption.
* intros. dependent destruction H1. assumption.
* intros. dependent destruction H. constructor. 
  ** apply IHTransition1. assert (exists v', v = cst v'). eapply Output_are_good. exact H.
     exact Transition1. destruct H2. subst. constructor. assumption.
  ** apply IHTransition2. assert (exists v', v = cst v'). eapply Output_are_good. exact H.
     exact Transition1. destruct H2. subst. constructor. assumption.
* intros. dependent destruction H. constructor.
  ** apply IHTransition2. assert (exists v', v = cst v'). eapply Output_are_good. exact H1.
     exact Transition1. destruct H2. subst. constructor. assumption.
  ** apply IHTransition1. assert (exists v', v = cst v'). eapply Output_are_good. exact H1.
     exact Transition1. destruct H2. subst. constructor. assumption.
* intros. dependent destruction H. constructor. apply IHTransition. assumption. assumption. assumption.
* intros. dependent destruction H. constructor. assumption. apply IHTransition. assumption. assumption.
* intros. dependent destruction H. apply IHTransition. assumption. assumption.
* intros. dependent destruction H. apply IHTransition. assumption. assumption.
Qed.


(* Lemma to simplify the Data in Value for a transition *)
Lemma OutputWithValue : forall p q a, lts p (ActOut a) q -> exists c d, a = c ⋉ d.
Proof.
intros. dependent destruction a. dependent induction H.
- exists c. exists d. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
Qed.

Lemma InputWithValue : forall p q a, lts p (ActIn a) q -> exists c v, a = c ⋉ v.
Proof.
intros. dependent destruction a. dependent induction H.
- exists c. exists d. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
- destruct (IHlts c d). reflexivity. destruct H0. dependent destruction H0. exists x. exists x0. reflexivity.
Qed.


(* Peter Selinger Axioms (OutBuffered Agent with FeedBack) up to structural equivalence*)

Lemma OBA_with_FB_First_Axiom : forall p q r a α,
  lts p (ActOut a) q -> lts q α r ->
  (exists r', lts p α r' /\ lts_then_sc r' (ActOut a) r). (* output-commutativity *)
Proof.
intros. assert (lts p (ActOut a) q). assumption. apply OutputWithValue in H1.
decompose record H1. subst. eapply TransitionShapeForOutputSimplified in H.
eapply lts_parR in H0. instantiate (1 := (x ! x0 • 𝟘)) in H0.
edestruct (Congruence_Respects_Transition p ((x ! x0 • 𝟘) ‖ r) α).
exists ((x ! x0 • 𝟘) ‖ q). split; assumption. destruct H2.
assert (lts ((x ! x0 • 𝟘) ‖ r) (ActOut (x ⋉ x0)) (𝟘 ‖ r)). constructor. constructor.
edestruct (Congruence_Respects_Transition x1 (𝟘 ‖ r) (ActOut (x ⋉ x0))).
exists ((x ! x0 • 𝟘) ‖ r). split ; assumption. destruct H5.
assert (x2 ≡* r). eauto with cgr.
exists x1. split. assumption. exists x2. split; assumption.
Qed.

Lemma OBA_with_FB_Second_Axiom : forall p q1 q2 a μ, 
  μ ≠ (ActOut a) ->
  lts p (ActOut a) q1 ->
  lts p (ActExt μ) q2 ->
  ∃ r : proc, lts q1 (ActExt μ) r ∧ lts_then_sc q2 (ActOut a) r. (* output-confluence  *)
Proof.
intros. assert (lts p (ActOut a) q1). assumption. apply OutputWithValue in H2.
decompose record H2. subst. rename x into c. rename x0 into v.
eapply TransitionShapeForOutputSimplified in H0.
edestruct (Congruence_Respects_Transition ((c ! v • 𝟘) ‖ q1) q2 μ).
exists p. split. symmetry. assumption. assumption.
destruct H3. inversion H3; subst.
inversion H9. subst. now destruct H. 
exists q3. split. assumption.
assert (lts ((c ! v • 𝟘) ‖ q3) (ActOut (c ⋉ v)) (𝟘 ‖ q3)). constructor. constructor.
edestruct (Congruence_Respects_Transition q2 (𝟘 ‖ q3) (ActOut (c ⋉ v))).
exists ((c ! v • 𝟘) ‖ q3). split. eauto with cgr. assumption. destruct H6. exists x. split. assumption.
eauto with cgr.
Qed.

Lemma OBA_with_FB_Third_Axiom : forall p1 p2 p3 a, 
            lts p1 (ActOut a) p2 → lts p1 (ActOut a) p3 -> p2 ≡* p3. (* output-determinacy *)
Proof.
intros. assert (lts p1 (ActOut a) p2). assumption. apply OutputWithValue in H1.
decompose record H1. subst. rename x into c. rename x0 into v.
revert H0. revert p3. dependent induction H.
- intros. inversion H0. subst. eauto with cgr.
- intros. inversion H0;subst. 
  * apply cgr_fullpar. eapply IHlts. eauto. eauto. assumption. eauto with cgr.
  * apply TransitionShapeForOutputSimplified in H.
    apply TransitionShapeForOutputSimplified in H6.
    apply transitivity with (p2 ‖ ((c ! v • 𝟘) ‖ q2)). eauto with cgr. 
    apply transitivity with ((p2 ‖ (c ! v • 𝟘)) ‖ q2). eauto with cgr. apply cgr_par.
    eauto with cgr.
- intros. inversion H0 ; subst.
  * apply TransitionShapeForOutputSimplified in H.
    apply TransitionShapeForOutputSimplified in H6.
    apply transitivity with (((c ! v • 𝟘) ‖ p2) ‖ q2). eauto with cgr.
    apply transitivity with (( p2 ‖ (c ! v • 𝟘)) ‖ q2). eauto with cgr.
    apply transitivity with ( p2 ‖ ((c ! v • 𝟘) ‖ q2)). eauto with cgr. apply cgr_fullpar. reflexivity.
    eauto with cgr.
  * apply cgr_fullpar. reflexivity. eapply IHlts. eauto. eauto. assumption.
- intros. exfalso. eapply guarded_does_no_output. eassumption.
- intros. exfalso. eapply guarded_does_no_output. eassumption.
Qed.

Lemma OBA_with_FB_Fourth_Axiom : forall p1 p2 p3 a, lts p1 (ActOut a) p2 -> lts p2 (ActIn a) p3 
                              -> lts_then_sc p1 τ p3. (* feedback *)
Proof.
intros. assert (lts p1 (ActOut a) p2). assumption. apply OutputWithValue in H1.
decompose record H1. subst. rename x into c. rename x0 into v.
eapply TransitionShapeForOutputSimplified in H.
assert (lts (c ! v • 𝟘) (ActOut (c ⋉ v)) 𝟘). constructor.
assert (lts ((c ! v • 𝟘) ‖ p2) τ  (𝟘 ‖ p3)). econstructor; eassumption.
edestruct (Congruence_Respects_Transition p1 (𝟘 ‖ p3) τ). exists ((c ! v • 𝟘) ‖ p2).
split; assumption. destruct H4. exists x. split. assumption. eauto with cgr.
Qed.

Lemma OBA_with_FB_Fifth_Axiom : forall p q1 q2 a,
  lts p (ActOut a) q1 -> lts p τ q2 ->
  (∃ q : proc, lts q1 τ q /\ lts_then_sc q2 (ActOut a) q) \/ lts_then_sc q1 (ActIn a) q2. (* output-tau  *)
Proof.
intros. assert (lts p (ActOut a) q1). assumption. apply OutputWithValue in H1.
decompose record H1. subst. rename x into c. rename x0 into v.
eapply TransitionShapeForOutputSimplified in H.
edestruct (Congruence_Respects_Transition ((c ! v • 𝟘) ‖ q1) q2 τ). exists p. split. eauto with cgr. assumption.
destruct H2. dependent induction H2.
- inversion H2_; subst. right. exists q0. split. assumption. eauto with cgr. 
- inversion H2_0.
- inversion H2.
- left. exists q0. split. assumption. 
  assert (lts ((c ! v • 𝟘) ‖ q0) (ActOut (c ⋉ v)) (𝟘 ‖ q0)). constructor. constructor.
  edestruct (Congruence_Respects_Transition q2 (𝟘 ‖ q0) (ActOut (c ⋉ v))). exists ((c ! v • 𝟘) ‖ q0).
  split. eauto with cgr. assumption. destruct H5. exists x. split. assumption. eauto with cgr.
Qed.


Lemma ExtraAxiom : forall p1 p2 q1 q2 a,
      lts p1 (ActOut a) q1 -> lts p2 (ActOut a) q2 -> q1 ≡* q2 -> p1 ≡* p2.
Proof.
intros. assert (lts p1 (ActOut a) q1). assumption. apply OutputWithValue in H2.
decompose record H2. subst. rename x into c. rename x0 into v.
eapply TransitionShapeForOutputSimplified in H0.
eapply TransitionShapeForOutputSimplified in H.
apply transitivity with ((c ! v • 𝟘) ‖ q1). assumption.
apply transitivity with ((c ! v • 𝟘) ‖ q2). eauto with cgr. eauto with cgr.
Qed. 

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


Fixpoint encode_equation (E : Equation Data) : gen_tree (nat + Data) :=
match E with
  | tt => GenLeaf (inl 1)
  | ff => GenLeaf (inl 0)
  | D1 ⩽ D2 => GenNode 2 [GenLeaf (inr D1) ; GenLeaf (inr D2)]
  | e1 ∨ e2 => GenNode 3 [encode_equation e1 ; encode_equation e2]
  | non e => GenNode 4 [encode_equation e] 
end.

Fixpoint decode_equation (tree : gen_tree (nat + Data)) : Equation Data :=
match tree with
  | GenLeaf (inl 1) => tt
  | GenLeaf (inl 0) => ff
  | GenNode 2 [GenLeaf (inr d); GenLeaf (inr d')] => d ⩽ d'
  | GenNode 3 [p ; q] => (decode_equation p) ∨ (decode_equation q)
  | GenNode 4 [t'] => non (decode_equation t')
  | _ => ff
end. 

Lemma Equation_dec : forall (x y : Equation Data) , {x = y} + {x <> y}.
Proof.
decide equality. apply Data_dec. apply Data_dec.
Qed.

#[global] Instance equation_dec : EqDecision (Equation Data). exact Equation_dec. Defined.

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

Lemma TypeOfActions_dec : forall (x y : TypeOfActions) , {x = y} + {x <> y}.
Proof.
decide equality. 
* destruct (decide(d = d0)). left. assumption. right. assumption.
* destruct (decide (c = c0)). left. assumption. right. assumption.
Qed.

#[global] Instance TypeOfActions_eqdecision : EqDecision TypeOfActions. by exact TypeOfActions_dec . Defined.

Fixpoint proc_dec (x y : proc) : { x = y } + { x <> y }
with gproc_dec (x y : gproc) : { x = y } + { x <> y }.
Proof.
decide equality. 
* destruct (decide(n = n0));eauto.
* destruct (decide(n = n0));eauto.
* destruct (decide(e = e0));eauto. 
* destruct (decide(d = d0));eauto.
* destruct (decide(c = c0));eauto.
* decide equality. destruct (decide(c = c0));eauto.
Qed.

#[global] Instance proc_eqdecision : EqDecision proc. by exact proc_dec. Defined.

Definition encode_TypeOfActions (a : TypeOfActions) : gen_tree (nat + (Channel + Data)) :=
match a with
  | act c v => GenNode 0 [GenLeaf (inr (inl c)) ; GenLeaf (inr (inr v))]
end.

Definition decode_TypeOfActions (tree :gen_tree (nat + (Channel + Data))) : option TypeOfActions :=
match tree with
  | GenNode 0 [GenLeaf (inr (inl c)); GenLeaf (inr (inr v))] => Some (act c v)
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

Fixpoint encode_proc (p: proc) : gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel)) :=
  match p with
  | p ‖ q  => GenNode 0 [encode_proc p; encode_proc q]
  | c ! v • 𝟘  => GenLeaf (inr $ inl $ inr $ (c ⋉ v))
  | pr_var i => GenNode 2 [GenLeaf $ inl i]
  | rec x • P => GenNode 3 [GenLeaf $ inl x; encode_proc P]
  | If C Then A Else B => GenNode 4 [GenLeaf (inr ( inl (inl C))) ; encode_proc A; encode_proc B]
  | g gp => GenNode 1 [encode_gproc gp]
  end
with
encode_gproc (gp: gproc) : gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel)) :=
  match gp with
  | ① => GenNode 1 []
  | 𝟘 => GenNode 0 []
  | c ? p => GenNode 2 [GenLeaf (inr $ inr c); encode_proc p]
  | t • p => GenNode 3 [encode_proc p]
  | gp + gq => GenNode 4 [encode_gproc gp; encode_gproc gq]
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
  | GenNode 0 [ep; eq] => (decode_proc ep) ‖ (decode_proc eq)
  | GenLeaf (inr ( inl (inr a))) => (Channel_of a) ! (Data_of a) • 𝟘
  | GenNode 2 [GenLeaf (inl i)] => pr_var i
  | GenNode 3 [GenLeaf (inl i); egq] => rec i • (decode_proc egq)
  | GenNode 4 [GenLeaf (inr ( inl (inl C))); A; B] => If C Then (decode_proc A) Else (decode_proc B)
  | GenNode 1 [egp] => g (decode_gproc egp)
  | _ => ① 
  end
with
decode_gproc (t': gen_tree (nat + (((Equation Data ) + TypeOfActions) + Channel))): gproc :=
  match t' with
  | GenNode 1 [] => ①
  | GenNode 0 [] => 𝟘
  | GenNode 2 [GenLeaf (inr (inr c)); ep] => c ? (decode_proc ep)
  | GenNode 3 [eq] => t • (decode_proc eq)
  | GenNode 4 [egp; egq] => (decode_gproc egp) + (decode_gproc egq)
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
* intros. simpl. rewrite (encode_decide_gprocs g0). rewrite (encode_decide_gprocs g1). reflexivity.
Qed.

#[global] Instance proc_count : Countable proc.
refine (inj_countable' encode_proc decode_proc _).
  apply encode_decide_procs.
Qed.
#[global] Instance Singletons_of_TypeOfActions : SingletonMS TypeOfActions (gmultiset TypeOfActions) 
:=gmultiset_singleton.
#[global] Instance Singletons_of_proc : Singleton proc (gset proc) := gset_singleton.
#[global] Instance Empty_of_proc : Empty (gset proc) := gset_empty.
#[global] Instance Union_of_proc : Union (gset proc) := gset_union.
#[global] Instance SemiSet_of_proc : SemiSet proc (gset proc) := gset_semi_set.

(* Next Obligations *)
Fixpoint moutputs_of p : gmultiset TypeOfActions := 
match p with
  | P ‖ Q => (moutputs_of P) ⊎ (moutputs_of Q)
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | If C Then P Else Q => ∅
  | c ! v • 𝟘 => {[+ c ⋉ v +]}
  | g _ => ∅
end.  
Definition outputs_of p := dom (moutputs_of p).

Lemma mo_equiv_spec_step : forall {p q}, p ≡ q -> moutputs_of p = moutputs_of q.
Proof. intros. dependent induction H; multiset_solver. Qed.

Lemma mo_equiv_spec : forall {p q}, p ≡* q -> moutputs_of p = moutputs_of q.
Proof.
  intros p q hcgr.
  induction hcgr. now eapply mo_equiv_spec_step.
  etrans; eauto.
Qed.

Lemma mo_spec p a q : lts p (ActOut a) q -> moutputs_of p = {[+ a +]} ⊎ moutputs_of q.
Proof.
  intros l. assert (lts p (ActOut a) q). assumption. apply OutputWithValue in H.
  decompose record H. subst. rename x into c. rename x0 into v.
  eapply TransitionShapeForOutputSimplified, mo_equiv_spec in l. simpl in l. eauto.
Qed.

Lemma mo_spec_l e a :
  a ∈ moutputs_of e -> {e' | lts e (ActExt $ ActOut a) e' /\ moutputs_of e' = moutputs_of e ∖ {[+ a +]}}.
Proof.
  intros mem.
  dependent induction e.
  + cbn in mem.
    destruct (decide (a ∈ moutputs_of e1)).
    destruct (IHe1 a e) as (e1' & lts__e1 & eq).
    exists (pr_par e1' e2). repeat split; eauto with ccs.
    multiset_solver.
    destruct (decide (a ∈ moutputs_of e2)).
    destruct (IHe2 a e) as (e2' & lts__e2 & eq).
    exists (pr_par e1 e2'). repeat split; eauto with ccs.
    multiset_solver.
    contradict mem. intro mem. multiset_solver.
    + exfalso. multiset_solver.
    + exfalso. multiset_solver.
    + exfalso. multiset_solver.
  + exists (g 𝟘).
    assert (a = c ⋉ d). multiset_solver. subst.
    repeat split; eauto with ccs. multiset_solver.
  + simpl in mem. exfalso. set_solver. 
Qed.

Lemma mo_spec_r e a :
  {e' | lts e (ActExt $ ActOut a) e' /\ moutputs_of e' = moutputs_of e ∖ {[+ a +]}} -> a ∈ moutputs_of e.
Proof.
  dependent induction e; intros (e' & l & mem).
  + cbn.
    inversion l; subst.
    eapply gmultiset_elem_of_disj_union. left.
    eapply IHe1. exists p2. split.
    eassumption. cbn in mem. multiset_solver.
    eapply gmultiset_elem_of_disj_union. right.
    eapply IHe2. exists q2. split.
    eassumption. cbn in mem. multiset_solver.
  + inversion l.
  + inversion l.
  + inversion l.    
  + inversion l; subst. set_solver.
  + destruct a. now eapply guarded_does_no_output in l.
Qed.


Lemma outputs_of_spec2 p a : a ∈ outputs_of p -> {q | lts p (ActExt (ActOut a)) q}.
Proof.
  intros mem.
  eapply gmultiset_elem_of_dom in mem.
  eapply mo_spec_l in mem.
  firstorder.
Qed.

Lemma outputs_of_spec1_zero (p : proc) (a : TypeOfActions) : {q | lts p (ActExt (ActOut a)) q} 
      -> a ∈ outputs_of p.
Proof.    
  intros (p' & lts__p).
  dependent induction p.
  + eapply gmultiset_elem_of_dom.
    cbn. inversion lts__p; subst. apply IHp1 in H3. eapply gmultiset_elem_of_dom in H3. multiset_solver.
     apply IHp2 in H3. eapply gmultiset_elem_of_dom in H3. multiset_solver.
  + inversion lts__p; subst.
  + inversion lts__p; subst.
  + inversion lts__p; subst.
  + inversion lts__p; subst. unfold outputs_of. multiset_solver.
  + assert (lts g0 (ActOut a) p'). assumption. apply OutputWithValue in H.
    decompose record H. subst. rename x into c. rename x0 into v.
    now eapply guarded_does_no_output in lts__p.
Qed.

Lemma outputs_of_spec1 (p : proc) (a : TypeOfActions) (q : proc) : lts p (ActExt (ActOut a)) q
      -> a ∈ outputs_of p.
Proof.
intros. eapply outputs_of_spec1_zero. exists q. assumption.
Qed.

Fixpoint lts_set_output (p : proc) (a : TypeOfActions) : gset proc:=
match p with
  | p1 ‖ p2 => 
      let ps1 := lts_set_output p1 a in
      let ps2 := lts_set_output p2 a in
      (* fixme: find a way to map over sets. *)
      list_to_set (map (fun p => p ‖ p2) (elements ps1)) ∪ list_to_set (map (fun p => p1 ‖ p) (elements ps2))
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | If _ Then _ Else _ => ∅
  | c ! v • 𝟘 => if decide(a = (c ⋉ v)) then {[ (g 𝟘) ]} else ∅
  | g _  => ∅
end.

Fixpoint lts_set_input_g (g : gproc) (a : TypeOfActions) : gset proc :=
  match g with
  | c ? p => if decide(Channel_of a = c) then {[ p^(Data_of a) ]} else ∅
  | g1 + g2 => lts_set_input_g g1 a ∪ lts_set_input_g g2 a
  | ① => ∅
  | 𝟘 => ∅
  | t • p => ∅
  end.
  
Fixpoint lts_set_input (p : proc) (a : TypeOfActions) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1 := lts_set_input p1 a in
      let ps2 := lts_set_input p2 a in
      list_to_set (map (fun p => p ‖ p2) (elements ps1)) ∪ list_to_set (map (fun p => p1 ‖ p) (elements ps2))
  | pr_var _ => ∅
  | rec _ • _ => ∅ 
  | c ! v • 𝟘 => ∅
  | If _ Then _ Else _ => ∅
  | g gp => lts_set_input_g gp a  
  end.
  
Fixpoint lts_set_tau_g (gp : gproc) : gset proc :=
match gp with
  | c ? p => ∅
  | ① => ∅
  | 𝟘 => ∅
  | t • p => {[ p ]}
  | gp1 + gp2 => lts_set_tau_g gp1 ∪ lts_set_tau_g gp2
end.



Fixpoint lts_set_tau (p : proc) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1_tau : gset proc := list_to_set (map (fun p => p ‖ p2) (elements $ lts_set_tau p1)) in
      let ps2_tau : gset proc := list_to_set (map (fun p => p1 ‖ p) (elements $ lts_set_tau p2)) in
      let ps_tau := ps1_tau ∪ ps2_tau in
      let acts1 := outputs_of p1 in
      let acts2 := outputs_of p2 in
      let ps1 :=
        flat_map (fun a =>
                    map
                      (fun '(p1 , p2) => p1 ‖ p2)
                      (list_prod (elements $ lts_set_output p1 a) (elements $ lts_set_input p2 a)))
        (elements $ outputs_of p1) in
      let ps2 :=
        flat_map
          (fun a =>
             map
               (fun '(p1 , p2) => p1 ‖ p2)
               (list_prod (elements $ lts_set_input p1 a) (elements $ lts_set_output p2 a)))
          (elements $ outputs_of p2)
      in
      ps_tau ∪ list_to_set ps1 ∪ list_to_set ps2
  | c ! v • 𝟘 => ∅
  | pr_var _ => ∅
  | rec x • p => {[ pr_subst x p (rec x • p) ]}
  | If C Then A Else B => match (Eval_Eq C) with 
                          | Some true => {[ A ]}
                          | Some false => {[ B ]}
                          | None => ∅
                          end
  | g gp => lts_set_tau_g gp
end.

Lemma lts_set_output_spec0 p a q : q ∈ lts_set_output p a -> lts p (ActExt (ActOut a)) q.
Proof.
  intro mem.
  dependent induction p; simpl in mem; try now inversion mem.
  - eapply elem_of_union in mem as [mem | mem]. 
    * eapply elem_of_list_to_set, elem_of_list_fmap in mem as (q' & eq & mem). subst.
    apply lts_parL. apply IHp1. rewrite elem_of_elements in mem. set_solver.
    * eapply elem_of_list_to_set, elem_of_list_fmap in mem as (q' & eq & mem). subst.
    apply lts_parR. apply IHp2. rewrite elem_of_elements in mem. exact mem.
  -  case (TypeOfActions_dec a (c ⋉ d)) in mem.
    + rewrite e. rewrite e in mem.
      destruct (decide (c ⋉ d = c ⋉ d)). subst. assert (q = (g 𝟘)). set_solver.
      rewrite H. apply lts_output. exfalso. set_solver.
    + destruct (decide (a = c ⋉ d)). exfalso. apply n. assumption. set_solver.
Qed.

Lemma lts_set_output_spec1 p a q : lts p (ActExt $ ActOut a) q -> q ∈ lts_set_output p a.
Proof.
  intro l. dependent induction l; try set_solver.
  simpl. destruct (decide (c ⋉ v = c ⋉ v)). set_solver. exfalso. apply n. reflexivity.
Qed.

Lemma lts_set_input_spec0 p a q : q ∈ lts_set_input p a -> lts p (ActExt $ ActIn a) q.
Proof.
  intro mem.
  dependent induction p; simpl in mem; try set_solver.
  + eapply elem_of_union in mem. destruct mem.
    ++ eapply elem_of_list_to_set in H.
       eapply elem_of_list_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. eauto with ccs.
    ++ eapply elem_of_list_to_set in H.
       eapply elem_of_list_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. eauto with ccs.
  + dependent induction g0; simpl in mem; try set_solver.
      ++ destruct (decide (Channel_of a = c)).
         +++ subst. eapply elem_of_singleton_1 in mem. subst. destruct a. simpl. apply lts_input.
         +++ destruct a. simpl in *. inversion mem.
      ++ eapply elem_of_union in mem. destruct mem; eauto with ccs.
Qed.

Lemma lts_set_input_spec1 p a q : lts p (ActExt $ ActIn a) q -> q ∈ lts_set_input p a.
Proof.
  intro l. dependent induction l; try set_solver.
  simpl. destruct (decide (c = c)). set_solver. exfalso. apply n. reflexivity.
Qed.


Lemma lts_set_tau_spec0 p q : q ∈ lts_set_tau p -> lts p τ q.
Proof.
  - intro mem.
    dependent induction p; simpl in mem.
    + eapply elem_of_union in mem. destruct mem as [mem1 | mem2].
      ++ eapply elem_of_union in mem1.
         destruct mem1.
         eapply elem_of_union in H as [mem1 | mem2]. 
         eapply elem_of_list_to_set, elem_of_list_fmap in mem1 as (t' & eq & h); subst.
         rewrite elem_of_elements in h. eauto with ccs.
         eapply elem_of_list_to_set, elem_of_list_fmap in mem2 as (t' & eq & h); subst.
         rewrite elem_of_elements in h. eauto with ccs.
         eapply elem_of_list_to_set, elem_of_list_In, in_flat_map in H as (t' & eq & h); subst.
         eapply elem_of_list_In, elem_of_list_fmap in h as ((t1 & t2) & eq' & h'). subst.
         eapply elem_of_list_In, in_prod_iff in h' as (mem1 & mem2).
         eapply elem_of_list_In in mem1. rewrite elem_of_elements in mem1.
         eapply elem_of_list_In in mem2. rewrite elem_of_elements in mem2.
         eapply lts_set_output_spec0 in mem1.
         eapply lts_set_input_spec0 in mem2. destruct t'. eapply lts_comL. exact mem1. exact mem2.
      ++ eapply elem_of_list_to_set, elem_of_list_In, in_flat_map in mem2 as (t' & eq & h); subst.
         eapply elem_of_list_In, elem_of_list_fmap in h as ((t1 & t2) & eq' & h'). subst.
         eapply elem_of_list_In, in_prod_iff in h' as (mem1 & mem2).
         eapply elem_of_list_In in mem1. rewrite elem_of_elements in mem1.
         eapply elem_of_list_In in mem2. rewrite elem_of_elements in mem2.
         eapply lts_set_input_spec0 in mem1.
         eapply lts_set_output_spec0 in mem2. destruct t'. eapply lts_comR. exact mem2. exact mem1.
    + inversion mem.
    + eapply elem_of_singleton_1 in mem. subst; eauto with ccs.
    + destruct (decide (Eval_Eq e = Some true)).
      * rewrite e0 in mem. assert (q = p1). set_solver. rewrite H. constructor. assumption.
      * destruct (decide (Eval_Eq e = Some false)). rewrite e0 in mem. 
        assert (q = p2). set_solver. rewrite H. constructor. assumption.
        assert (Eval_Eq e = None). destruct (Eval_Eq e). destruct b. exfalso. apply n. reflexivity.
        exfalso. apply n0. reflexivity. reflexivity. rewrite H in mem. set_solver.
    + inversion mem.
    + dependent induction g0; simpl in mem; try set_solver;
        try eapply elem_of_singleton_1 in mem; subst; eauto with ccs.
      eapply elem_of_union in mem as [mem1 | mem2]; eauto with ccs.
Qed.

Lemma lts_set_tau_spec1 p q : lts p τ q -> q ∈ lts_set_tau p.
Proof. 
  intro l. dependent induction l; simpl; try set_solver.
  - rewrite H. set_solver. 
  - rewrite H. set_solver. 
  - eapply elem_of_union. left.
    eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    rewrite elem_of_list_In. rewrite in_flat_map.
    exists (c ⋉ v). split.
    + eapply elem_of_list_In, elem_of_elements.
      eapply outputs_of_spec1_zero. eauto.
    + eapply elem_of_list_In, elem_of_list_fmap.
      exists (p2 , q2). split.
      ++ reflexivity.
      ++ eapply elem_of_list_In, in_prod_iff; split; eapply elem_of_list_In, elem_of_elements.
         eapply lts_set_output_spec1; eauto with ccs.
         eapply lts_set_input_spec1; eauto with ccs.
  - eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    rewrite elem_of_list_In. rewrite in_flat_map.
    exists (c ⋉ v). split.
    + eapply elem_of_list_In, elem_of_elements.
      eapply outputs_of_spec1_zero. exists p2. exact l1.
    + eapply elem_of_list_In, elem_of_list_fmap.
      exists (q2 , p2). split.
      ++ reflexivity.
      ++ eapply elem_of_list_In, in_prod_iff; split; eapply elem_of_list_In, elem_of_elements.
         eapply lts_set_input_spec1; eauto with ccs.
         eapply lts_set_output_spec1; eauto with ccs.
Qed.


Definition lts_set (p : proc) (α : Act TypeOfActions): gset proc :=
  match α with
  | τ => lts_set_tau p
  | ActExt (ActIn a) => lts_set_input p a
  | ActExt (ActOut a) => lts_set_output p a
  end.

Lemma lts_set_spec0 p α q : q ∈ lts_set p α -> lts p α q.
Proof.
  destruct α as [[a|a]|].
  - now eapply lts_set_input_spec0.
  - now eapply lts_set_output_spec0.
  - now eapply lts_set_tau_spec0.
Qed.

Lemma lts_set_spec1 p α q : lts p α q -> q ∈ lts_set p α.
Proof.
  destruct α as [[a|a]|].
  - now eapply lts_set_input_spec1.
  - now eapply lts_set_output_spec1.
  - now eapply lts_set_tau_spec1.
Qed.

Definition proc_stable p α := lts_set p α = ∅.

Lemma lts_dec p α q : { lts p α q } + { ~ lts p α q }.
Proof.
  destruct (decide (q ∈ lts_set p α)).
  - eapply lts_set_spec0 in e. eauto.
  - right. intro l. now eapply lts_set_spec1 in l.
Qed.

Lemma proc_stable_dec p α : Decision (proc_stable p α).
Proof. destruct (decide (lts_set p α = ∅)); [ left | right ]; eauto. Qed.

Lemma gset_nempty_ex (g : gset proc) : g ≠ ∅ -> {p | p ∈ g}.
Proof.
  intro n. destruct (elements g) eqn:eq.
  + destruct n. eapply elements_empty_iff in eq. set_solver.
  + exists p. eapply elem_of_elements. rewrite eq. set_solver.
Qed.

(* Making VACCS Instance of each class *)

#[global] Program Instance VACCS_Label : Label TypeOfActions := 
  {| label_eqdec := TypeOfActions_dec ;
  label_countable := TypeOfActions_countable |}. (* useless, already said it, it is just a reminder *)

#[global] Program Instance VACCS_Lts : Lts proc TypeOfActions := 
  {| lts_step x ℓ y  := lts x ℓ y ;
     lts_state_eqdec := proc_dec ;
     lts_step_decidable p α q := lts_dec p α q ;
     lts_outputs := outputs_of ;
     lts_outputs_spec1 p1 x p2 := outputs_of_spec1 p1 x p2;
     lts_outputs_spec2 p1 x := outputs_of_spec2 p1 x;
     lts_stable p := proc_stable p;
     lts_stable_decidable p α := proc_stable_dec p α 
    |}.
    Next Obligation.
        intros p [[a|a]|]; intro hs;eapply gset_nempty_ex in hs as (r & l); eapply lts_set_spec0 in l; 
        exists r; assumption.
    Qed.
    Next Obligation.  
        intros p [[a|a]|]; intros (q & mem); intro eq; eapply lts_set_spec1 in mem; set_solver.
    Qed.

#[global] Program Instance VACCS_LtsEq : LtsEq proc TypeOfActions := 
  {| eq_rel x y  := cgr x y;
     eq_rel_refl p := cgr_refl p;
     eq_symm p q := cgr_symm p q;
     eq_trans x y z:= cgr_trans x y z;
     eq_spec p q α := Congruence_Respects_Transition p q α |}.

#[global] Program Instance VACCS_LtsOba : LtsOba proc TypeOfActions :=
  {| lts_oba_output_commutativity p q r a α := OBA_with_FB_First_Axiom p q r a α;
     lts_oba_output_confluence p q1 q2 a μ := OBA_with_FB_Second_Axiom p q1 q2 a μ;
     lts_oba_output_deter p1 p2 p3 a := OBA_with_FB_Third_Axiom p1 p2 p3 a;
     lts_oba_output_tau p q1 q2 a := OBA_with_FB_Fifth_Axiom p q1 q2 a;
     lts_oba_output_deter_inv p1 p2 q1 q2 a := ExtraAxiom p1 p2 q1 q2 a;
     lts_oba_mo p := moutputs_of p 
  |}.
  Next Obligation.
    intros. simpl. unfold outputs_of.
    now rewrite gmultiset_elem_of_dom.
  Qed.
  Next Obligation.
    intros. simpl. unfold outputs_of.
    now eapply mo_spec.
  Qed.
  

#[global] Program Instance VACCS_LtsObaFB : LtsObaFB proc TypeOfActions :=
  {| lts_oba_fb_feedback p1 p2 p3 a := OBA_with_FB_Fourth_Axiom p1 p2 p3 a |}.

