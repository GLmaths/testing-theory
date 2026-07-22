(*
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


From stdpp Require Import base countable.
From TestingTheory Require Import VCCS Clos_n.
From Stdlib Require Import Relations Program.Equality Wellfounded.Inverse_Image.


Section VCCS_congruence.

Context `{VP : VCCS_Parameters}.

(*Naïve definition of a relation ≡ that will become a congruence ≡* by transitivity*)
(* reference : communicating and mobile systems :
  the π-calculus, Robin MILNER, definition 4.7 page 31 *)
Inductive cgr_step : nat -> proc -> proc -> Prop :=
(*  Reflexivity of the Relation ≡  *)
| cgr_refl_step : forall n p, cgr_step n p p
| cgr_if_true_step : forall n p q E, Eval_Eq n E = Some true -> cgr_step n (If E Then p Else q) p
| cgr_if_true_rev_step  : forall n p q E, Eval_Eq n E = Some true -> cgr_step n p (If E Then p Else q)
| cgr_if_false_step  : forall n p q E, Eval_Eq n E = Some false -> cgr_step n (If E Then p Else q) q
| cgr_if_false_rev_step  : forall n p q E, Eval_Eq n E = Some false -> cgr_step n q (If E Then p Else q)

(* Rules for the Parallèle *)
| cgr_par_nil_step : forall n p,
    cgr_step n (p ‖ (g 𝟘)) p
| cgr_par_nil_rev_step : forall n p,
    cgr_step n p (p ‖ (g 𝟘))
| cgr_par_com_step : forall n p q,
    cgr_step n (p ‖ q) (q ‖ p)
| cgr_par_assoc_step : forall n p q r,
    cgr_step n ((p ‖ q) ‖ r) (p ‖ (q ‖ r))
| cgr_par_assoc_rev_step : forall n p q r,
    cgr_step n (p ‖ (q  ‖ r)) ((p ‖ q) ‖ r)

(* Rules for the Restriction *)
| cgr_res_nil_step : forall n,
   cgr_step n (ν (g 𝟘)) (g 𝟘)
| cgr_res_nil_rev_step : forall n,
   cgr_step n (g 𝟘) (ν (g 𝟘))
| cgr_res_swap_step : forall n p,
    cgr_step n (ν (ν p)) (ν (ν (VarSwap_in_proc 0 p)))
| cgr_res_swap_rev_step : forall n p,
    cgr_step n (ν (ν (VarSwap_in_proc 0 p))) (ν (ν p))
| cgr_res_scope_step : forall n p q,
    cgr_step n (ν (p ‖ (NewVarC 0 q))) ((ν p) ‖ q)
| cgr_res_scope_rev_step : forall n p q,
    cgr_step n ((ν p) ‖ q) (ν (p ‖ (NewVarC 0 q)))

(* Rules for the Summation *)
| cgr_choice_nil_step : forall n p,
    cgr_step n (p + 𝟘) p
| cgr_choice_nil_rev_step : forall n p,
    cgr_step n (g p) (p + 𝟘)
| cgr_choice_com_step : forall n p q,
    cgr_step n (p + q) (q + p)
| cgr_choice_assoc_step : forall n p q r,
    cgr_step n ((p + q) + r) (p + (q + r))
| cgr_choice_assoc_rev_step : forall n p q r,
    cgr_step n (p + (q + r)) ((p + q) + r)

(* Congruence through contexts to certain terms...*)
| cgr_recursion_step : forall n x p q,
    cgr_step n p q -> cgr_step n (rec x • p) (rec x • q)
| cgr_tau_step : forall n p q,
    cgr_step n p q ->
    cgr_step n (𝛕 • p) (𝛕 • q)
| cgr_input_step : forall n c p q,
    cgr_step (S n) p q ->
    cgr_step n (c ? p) (c ? q)
| cgr_output_step : forall n c v p q,
    cgr_step n p q ->
    cgr_step n (c ! v • p) (c ! v • q)
| cgr_par_step : forall n p q r,
    cgr_step n p q ->
    cgr_step n (p ‖ r) (q ‖ r)
| cgr_res_step : forall n p q,
    cgr_step n p q ->
    cgr_step n (ν p) (ν q)
| cgr_if_left_step : forall n C p q q',
    cgr_step n q q' ->
    cgr_step n (If C Then p Else q) (If C Then p Else q')
| cgr_if_right_step : forall n C p p' q,
    cgr_step n p p' ->
    cgr_step n (If C Then p Else q) (If C Then p' Else q)

(*...and sums (only for guards (by sanity))*)
| cgr_choice_step : forall n p1 q1 p2,
    cgr_step n (g p1) (g q1) ->
    cgr_step n (p1 + p2) (q1 + p2)
.

Hint Constructors cgr_step:cgr_step_structure.

Notation "p ≡ q" := (cgr_step 0 p q) (at level 70).
Notation "p ≡[ n ] q" := (cgr_step n p q) (at level 70).

(* The relation ≡[n] is an reflexive*)
#[global] Instance cgr_refl_step_is_refl n : Reflexive (cgr_step n).
Proof. intro. apply cgr_refl_step. Qed.
(* The relation ≡[n] is symmetric*)
#[global] Instance cgr_symm_step n : Symmetric (cgr_step n).
Proof. intros p q hcgr. induction hcgr; econstructor ; eauto.
Qed.

(* Defining the transitive closure of ≡[n] *)
Definition cgr (n : nat) := (clos_trans proc (cgr_step n)).

Notation "p ≡* q" := (cgr 0 p q) (at level 70).
Notation "p ≡*[ n ] q" := (cgr n p q) (at level 70).

(* The relation ≡*[n] is reflexive*)
#[global] Instance cgr_refl n : Reflexive (cgr n).
Proof. intros. constructor. apply cgr_refl_step. Qed.
(* The relation ≡*[n] is symmetric*)
#[global] Instance cgr_symm n : Symmetric (cgr n).
Proof. intros p q hcgr. induction hcgr. constructor. apply cgr_symm_step. exact H. eapply t_trans; eauto. Qed.
(* The relation ≡*[n] is transitive*)
#[global] Instance cgr_trans n : Transitive (cgr n).
Proof. intros p q r hcgr1 hcgr2. eapply t_trans; eauto. Qed.

Hint Resolve cgr_refl cgr_symm cgr_trans:cgr_eq.

(* The relation ≡*[n] is an equivence relation*)
#[global] Instance cgr_is_eq_rel n : Equivalence (cgr n).
Proof. repeat split.
       + apply cgr_refl.
       + apply cgr_symm.
       + apply cgr_trans.
Qed.

(*the relation ≡*[n] respects all the rules that ≡[n] respected*)
Lemma cgr_if_true : forall n p q E, Eval_Eq n E = Some true -> (If E Then p Else q) ≡*[n] p.
Proof.
constructor.
apply cgr_if_true_step; eauto.
Qed.
Lemma cgr_if_true_rev : forall n p q E, Eval_Eq n E = Some true -> p ≡*[n] (If E Then p Else q).
Proof.
constructor.
apply cgr_if_true_rev_step; eauto.
Qed.
Lemma cgr_if_false : forall n p q E, Eval_Eq n E = Some false -> (If E Then p Else q) ≡*[n] q.
Proof.
constructor.
apply cgr_if_false_step; eauto.
Qed.
Lemma cgr_if_false_rev : forall n p q E, Eval_Eq n E = Some false -> q ≡*[n] (If E Then p Else q).
Proof.
constructor.
apply cgr_if_false_rev_step; eauto.
Qed.
Lemma cgr_par_nil : forall n p, p ‖ 𝟘 ≡*[n] p.
Proof.
constructor.
apply cgr_par_nil_step.
Qed.
Lemma cgr_par_nil_rev : forall n p, p ≡*[n] p ‖ 𝟘.
Proof.
constructor.
apply cgr_par_nil_rev_step.
Qed.
Lemma cgr_par_com : forall n p q, p ‖ q ≡*[n] q ‖ p.
Proof.
constructor.
apply cgr_par_com_step.
Qed.
Lemma cgr_par_assoc : forall n p q r, (p ‖ q) ‖ r ≡*[n] p ‖ (q ‖r).
Proof.
constructor.
apply cgr_par_assoc_step.
Qed.
Lemma cgr_par_assoc_rev : forall n p q r, p ‖(q ‖ r) ≡*[n] (p ‖ q) ‖ r.
Proof.
constructor.
apply cgr_par_assoc_rev_step.
Qed.
Lemma cgr_res_nil : forall n, ν (g 𝟘) ≡*[n] (g 𝟘).
Proof.
constructor.
apply cgr_res_nil_step.
Qed.
Lemma cgr_res_nil_rev : forall n, (g 𝟘) ≡*[n] ν (g 𝟘).
Proof.
constructor.
apply cgr_res_nil_rev_step.
Qed.
Lemma cgr_res_swap : forall n p, ν (ν p) ≡*[n] ν (ν (VarSwap_in_proc 0 p)).
Proof.
constructor.
apply cgr_res_swap_step.
Qed.
Lemma cgr_res_swap_rev : forall n p, ν (ν (VarSwap_in_proc 0 p)) ≡*[n] ν (ν p).
Proof.
constructor.
apply cgr_res_swap_rev_step.
Qed.
Lemma cgr_res_scope : forall n p q, ν (p ‖ (NewVarC 0 q)) ≡*[n] (ν p) ‖ q.
Proof.
constructor.
apply cgr_res_scope_step.
Qed.
Lemma cgr_res_scope_rev : forall n p q, (ν p) ‖ q ≡*[n] ν (p ‖ (NewVarC 0 q)).
Proof.
constructor.
apply cgr_res_scope_rev_step.
Qed.
Lemma cgr_choice_nil : forall n p, p + 𝟘 ≡*[n] p.
Proof.
constructor.
apply cgr_choice_nil_step.
Qed.
Lemma cgr_choice_nil_rev : forall n p, (g p) ≡*[n] p + 𝟘.
Proof.
constructor.
apply cgr_choice_nil_rev_step.
Qed.
Lemma cgr_choice_com : forall n p q, p + q ≡*[n] q + p.
Proof.
constructor.
apply cgr_choice_com_step.
Qed.
Lemma cgr_choice_assoc : forall n p q r, (p + q) + r ≡*[n] p + (q + r).
Proof.
constructor.
apply cgr_choice_assoc_step.
Qed.
Lemma cgr_choice_assoc_rev : forall n p q r, p + (q + r) ≡*[n] (p + q) + r.
Proof.
constructor.
apply cgr_choice_assoc_rev_step.
Qed.
Lemma cgr_recursion : forall n x p q, p ≡*[n] q -> (rec x • p) ≡*[n] (rec x • q).
Proof.
intros n x p q H. dependent induction H.
constructor.
apply cgr_recursion_step. exact H.
transitivity (rec x • y); assumption.
Qed.
Lemma cgr_tau : forall n p q, p ≡*[n] q -> (𝛕 • p) ≡*[n] (𝛕 • q).
Proof.
intros n p q H. dependent induction H.
constructor.
apply cgr_tau_step. exact H.
transitivity (𝛕 • y); assumption.
Qed.
Lemma cgr_input : forall n c p q, p ≡*[S n] q -> (c ? p) ≡*[n] (c ? q).
Proof.
intros n c p q H.
dependent induction H.
* constructor. apply cgr_input_step. auto.
* transitivity (c ? y). apply (IHclos_trans1 n c eq_refl). apply (IHclos_trans2 n c eq_refl).
Qed.
Lemma cgr_output : forall n c v p q, p ≡*[n] q -> (c ! v • p) ≡*[n] (c ! v • q).
Proof.
intros n c v p q H. dependent induction H.
constructor.
apply cgr_output_step. exact H.
transitivity (c ! v • y); assumption.
Qed.
Lemma cgr_par : forall n p q r, p ≡*[n] q-> p ‖ r ≡*[n] q ‖ r.
Proof.
intros n p q r H. dependent induction H.
constructor.
apply cgr_par_step. exact H.
transitivity (y ‖ r); assumption.
Qed.
Lemma cgr_res : forall n p q, p ≡*[n] q-> ν p ≡*[n] ν q.
Proof.
intros n p q H. dependent induction H.
constructor.
apply cgr_res_step. exact H.
transitivity (ν y); assumption.
Qed.
Lemma cgr_if_left : forall n C p q q', q ≡*[n] q' -> (If C Then p Else q) ≡*[n] (If C Then p Else q').
Proof.
intros n C p q q' H. dependent induction H.
constructor.
apply cgr_if_left_step. exact H.
transitivity (If C Then p Else y); assumption.
Qed.
Lemma cgr_if_right : forall n C p p' q, p ≡*[n] p' -> (If C Then p Else q) ≡*[n] (If C Then p' Else q).
Proof.
intros n C p p' q H. dependent induction H.
constructor.
apply cgr_if_right_step. exact H.
transitivity (If C Then y Else q); assumption.
Qed.

Section AlternativeCongruence.

(* Alternative definition of congruence step, better suited to prove that it's
  a congruence *)
Reserved Notation "p ≡ₐ[ n ] q" (at level 70).
Reserved Notation "p ≡g[ n ] q" (at level 70).
Inductive altcgr : nat -> proc -> proc -> Prop :=
| altcgr_refl_step : forall n p, p ≡ₐ[n] p
| altcgr_if_true_step : forall n p q E, Eval_Eq n E = Some true -> (If E Then p Else q) ≡ₐ[n] p
| altcgr_if_true_rev_step  : forall n p q E, Eval_Eq n E = Some true -> p ≡ₐ[n] If E Then p Else q
| altcgr_if_false_step  : forall n p q E, Eval_Eq n E = Some false -> (If E Then p Else q) ≡ₐ[n] q
| altcgr_if_false_rev_step  : forall n p q E, Eval_Eq n E = Some false -> q ≡ₐ[n] If E Then p Else q
| altcgr_par_nil_step : forall n p,
    p ‖ 𝟘 ≡ₐ[n] p
| altcgr_par_nil_rev_step : forall n p,
    p ≡ₐ[n] p ‖ 𝟘
| altcgr_par_com_step : forall n p q,
    p ‖ q ≡ₐ[n] q ‖ p
| altcgr_par_assoc_step : forall n p q r,
    (p ‖ q) ‖ r ≡ₐ[n] p ‖ (q ‖ r)
| altcgr_par_assoc_rev_step : forall n p q r,
    p ‖ (q  ‖ r) ≡ₐ[n] (p ‖ q) ‖ r
| altcgr_res_nil_step : forall n,
   ν (g 𝟘) ≡ₐ[n] (g 𝟘)
| altcgr_res_nil_rev_step : forall n,
   (g 𝟘) ≡ₐ[n] ν (g 𝟘)
| altcgr_res_swap_step : forall n p,
    ν (ν p) ≡ₐ[n] ν (ν (VarSwap_in_proc 0 p))
| altcgr_res_swap_rev_step : forall n p,
    ν (ν (VarSwap_in_proc 0 p)) ≡ₐ[n] ν (ν p)
| altcgr_res_scope_step : forall n p q,
    ν (p ‖ (NewVarC 0 q)) ≡ₐ[n] (ν p) ‖ q
| altcgr_res_scope_rev_step : forall n p q,
    (ν p) ‖ q ≡ₐ[n] ν (p ‖ (NewVarC 0 q))
| altcgr_recursion_step : forall n x p q,
    p ≡ₐ[n] q -> (rec x • p) ≡ₐ[n] (rec x • q)
| altcgr_par_step : forall n p q r,
    p ≡ₐ[n] q -> p ‖ r ≡ₐ[n] q ‖ r
| altcgr_res_step : forall n p q,
    p ≡ₐ[n] q -> ν p ≡ₐ[n] ν q
| altcgr_if_left_step : forall n C p q q',
    q ≡ₐ[n] q' -> (If C Then p Else q) ≡ₐ[n] (If C Then p Else q')
| altcgr_if_right_step : forall n C p p' q,
    p ≡ₐ[n] p' -> (If C Then p Else q) ≡ₐ[n] (If C Then p' Else q)
| altcgr_guard : forall n (g1 g2 : gproc), g1 ≡g[n] g2 -> g g1 ≡ₐ[n] g g2
| altcgr_trans : forall n (p q r : proc) , p ≡ₐ[n] q -> q ≡ₐ[n] r -> p ≡ₐ[n] r

with altcgr_gstep : nat -> gproc -> gproc -> Prop :=
| altcgr_tau_step : forall n p q,
    p ≡ₐ[n] q -> (𝛕 • p) ≡g[n] (𝛕 • q)
| altcgr_input_step : forall n c p q,
    p ≡ₐ[S n] q -> (c ? p) ≡g[n] (c ? q)
| altcgr_output_step : forall n c v p q,
    p ≡ₐ[n] q -> (c ! v • p) ≡g[n] (c ! v • q)
| altcgr_choice_nil_step : forall n p,
    (p + 𝟘) ≡g[n] p
| altcgr_choice_nil_rev_step : forall n p,
    p ≡g[n] (p + 𝟘)
| altcgr_choice_com_step : forall n p q,
    (p + q) ≡g[n] (q + p)
| altcgr_choice_assoc_step : forall n p q r,
    ((p + q) + r) ≡g[n] (p + (q + r))
| altcgr_choice_assoc_rev_step : forall n p q r,
    (p + (q + r)) ≡g[n] ((p + q) + r)
| altcgr_choice_step : forall n p1 q1 p2,
    p1 ≡g[n] q1 -> (p1 + p2) ≡g[n] (q1 + p2)
| galtcgr_trans : forall n (p q r : gproc), p ≡g[n] q -> q ≡g[n] r -> p ≡g[n] r
| galtcgr_refl_step : forall n p, p ≡g[n] p
| galtcgr_sym_step : forall n p q, q ≡g[n] p -> p ≡g[n] q
where "p ≡ₐ[ n ] q" := (altcgr n p q)
and "p ≡g[ n ] q" := (altcgr_gstep n p q).

#[local] Hint Constructors altcgr:alt_step_structure.

(* Transitive closure of congruence on guards only *)
Definition guardcgr (n : nat) :=
  clos_trans proc (fun p1 p2 => exists g1 g2, p1 = g g1 /\ p2 = g g2 /\ p1 ≡[n] p2).

(* Stronger statement : congruences under tau preserve guards *)
Lemma guardcgr_tau : forall n p q, p ≡*[n] q -> guardcgr n (𝛕 • p) (𝛕 • q).
Proof.
intros n p q H. induction H.
constructor.
- eexists; eexists; repeat split. apply cgr_tau_step. exact H.
- econstructor 2; eauto with cgr_eq.
Qed.

Lemma guardcgr_input : forall n c p q, p ≡*[S n] q -> guardcgr n (c ? p) (c ? q).
Proof.
intros n c p q H. induction H.
- constructor. eexists; eexists; repeat split. now apply cgr_input_step.
- econstructor 2; eauto with cgr_eq.
Qed.

Lemma guardcgr_output : forall n c v p q, p ≡*[n] q -> guardcgr n (c ! v • p) (c ! v • q).
Proof.
intros n c v p q H. induction H.
- constructor. eexists; eexists; repeat split. now apply cgr_output_step.
- econstructor 2; eauto with cgr_eq.
Qed.

#[local] Instance guard_cgr_refl n : Symmetric (guardcgr n).
Proof.
  intros x y H. induction H.
  - constructor. decompose record H. eauto with *.
  - econstructor 2; eauto with *.
Qed.

#[global] Instance altcgr_refl_step_is_refl n : Reflexive (altcgr n).
Proof. intro. apply altcgr_refl_step. Qed.

#[global] Instance altcgr_grefl_step_is_refl n : Reflexive (altcgr_gstep n).
Proof. intro. constructor. Qed.

#[local] Instance altcgr_symm_step n : Symmetric (altcgr n).
Proof. intros p q hcgr. induction hcgr; try solve [constructor; try exact IHhcgr];
try solve[now (do 3 (try constructor))].
- constructor. now constructor.
- econstructor; eauto.
Qed.

(* Equivalence between the two definitions of congruence *)

Scheme proc_ind2 := Induction for proc Sort Prop
  with gproc_ind2 := Induction for gproc Sort Prop.

Lemma cgr_step_altcgr n p q: cgr_step n p q -> altcgr n p q.
Proof.
revert n q.
induction p using proc_ind2 with (P0 :=
  (fun gp => forall d gq, cgr_step d (g gp) (g gq) -> altcgr_gstep d gp gq));
intros d q Hq;
try (solve[inversion Hq; subst; eauto with *; do 2 try constructor; eauto]).
inversion Hq; subst; eauto with *;
try (solve[inversion Hq; subst; eauto with *; do 2 try constructor; eauto]).
constructor. now apply IHp.
Qed.

Lemma cgr_altcgr n p q: cgr n p q -> altcgr n p q.
Proof. intro H. induction H; eauto using cgr_step_altcgr with *. Qed.

Scheme altcgr_ind2 := Induction for altcgr Sort Prop
  with galtcgr_ind2 := Induction for altcgr_gstep Sort Prop.

Combined Scheme altcgr_mutind from altcgr_ind2,galtcgr_ind2.

Lemma guardcgr_choice_step n p1 q1 p2: guardcgr n (g p1) (g q1) ->
  guardcgr n (g (p1 + p2)) (g (q1 + p2)).
Proof.
  intros H%clos_trans_tn1. apply clos_tn1_trans. dependent induction H.
  - constructor. decompose record H; subst.
    eexists; eexists; repeat split. now constructor.
  - decompose record H; subst; clear H. inversion H2; subst.
    econstructor 2; eauto.
    eexists; eexists; repeat split. now constructor.
Qed.

Lemma guardcgr_cgr n p q : guardcgr n p q -> cgr n p q.
Proof.
intro H. induction H.
decompose record H; subst; now constructor.
transitivity y; assumption.
Qed.

(* The following goes through because we strengthen the conclusion on guards *)
Lemma altcgr_cgr :
  (forall n p q, altcgr n p q -> p ≡*[n] q) /\
  (forall n gp gq, altcgr_gstep n gp gq -> guardcgr n gp gq).
Proof.
apply altcgr_mutind; try solve [repeat constructor; eauto with *]; intros.
- now apply cgr_recursion.
- now apply cgr_par.
- now apply cgr_res.
- now apply cgr_if_left.
- now apply cgr_if_right.
- now apply guardcgr_cgr.
- transitivity q; assumption.
- now apply guardcgr_tau.
- now apply guardcgr_input.
- now apply guardcgr_output.
- now apply guardcgr_choice_step.
- intros. now apply t_trans with (g q).
- now symmetry.
Qed.

Lemma NewVar_in_ChannelData_and_VarSwap_in_ChannelData j k0 c :
(NewVar_in_ChannelData (S (S (j + k0))) (VarSwap_in_ChannelData k0 c)
        = VarSwap_in_ChannelData k0 (NewVar_in_ChannelData (S (S (j + k0))) c)).
Proof.
  destruct c.
  + simpl. reflexivity.
  + simpl. destruct (decide (n = k0)).
    - subst. simpl. destruct (decide (j + k0 < k0)).
      * rewrite decide_True; try lia.
      * rewrite decide_False; try lia.
        rewrite decide_False; try lia. simpl.
        rewrite decide_True; try lia. eauto.
    - simpl. destruct (decide ((n = S k0)%nat)); subst. 
      * simpl. destruct (decide ((S (S (j + k0)) < S k0)%nat)); subst.
        ++ rewrite decide_False; try lia.
        ++ rewrite decide_False; try lia. simpl.
           rewrite decide_False; try lia.
           rewrite decide_True; try lia. eauto.
      * destruct (decide (S (S (j + k0)) < S n)).
        ++ simpl. rewrite decide_True; try lia.
           destruct (decide ((S n = k0))).
           ** subst. lia.
           ** rewrite decide_False; try lia. eauto.
        ++ simpl. rewrite decide_False; try lia.
           rewrite decide_False; eauto.
           rewrite decide_False; try lia. eauto.
Qed.

Lemma NewVarC_and_VarSwap j k0 p : (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p)).
Proof.
  revert j k0.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + reflexivity.
  + assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + assert (S (S (S (j + k0))) = S (S (j + (S k0)))) as eq' by lia. rewrite eq'.
    assert (NewVarC (S (S (j + (S k0)))) (VarSwap_in_proc (S k0) p)
        = VarSwap_in_proc (S k0) (NewVarC (S (S (j + (S k0)))) p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + destruct g; simpl in *.
    * reflexivity.
    * reflexivity.
    * assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p)) as eq1.
      { eapply Hp. simpl. lia. } rewrite eq1.
      rewrite NewVar_in_ChannelData_and_VarSwap_in_ChannelData. eauto.
   * assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p)) as eq1.
      { eapply Hp. simpl. lia. } rewrite eq1.
     rewrite NewVar_in_ChannelData_and_VarSwap_in_ChannelData. eauto.
   * assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p)) as eq.
     { eapply Hp. simpl. lia. }
     rewrite eq. eauto.
   * assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 (g g1)) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) (g g1))) as eq1.
     { eapply Hp. simpl. lia. }
     assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 (g g2)) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) (g g2))) as eq2.
     { eapply Hp. simpl. lia. } simpl in *. inversion eq1. inversion eq2.
     rewrite H0 , H1. eauto.
Qed.

Lemma NewVar_in_ChannelData_and_NewVar_in_ChannelData i j c :
    NewVar_in_ChannelData (i + (S j)) (NewVar_in_ChannelData i c) 
      = NewVar_in_ChannelData i (NewVar_in_ChannelData ( i + j ) c).
Proof.
  destruct c. simpl.
  + eauto.
  + simpl. destruct (decide ((i < S n))).
    - simpl. destruct (decide (i + j < S n)).
      * rewrite decide_True; try lia. simpl.
        rewrite decide_True; try lia. eauto.
      * rewrite decide_False; try lia. simpl.
        rewrite decide_True; try lia. eauto.
    - simpl. rewrite decide_False; try lia.
      rewrite decide_False; try lia. simpl.
      rewrite decide_False; try lia. eauto.
Qed.

Lemma NewVarC_and_NewVarC i j p : NewVarC (i + (S j)) (NewVarC i p) = NewVarC i (NewVarC ( i + j ) p).
Proof.
  revert i j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert ((NewVarC (i + S j) (NewVarC i p1)) = (NewVarC i (NewVarC (i + j) p1))) as eq1.
    { eapply Hp. simpl. lia. } rewrite eq1.
    assert ((NewVarC (i + S j) (NewVarC i p2)) = (NewVarC i (NewVarC (i + j) p2))) as eq2.
    { eapply Hp. simpl. lia. } rewrite eq2. eauto.
  + eauto.
  + assert ((NewVarC (i + S j) (NewVarC i p)) = (NewVarC i (NewVarC (i + j) p))) as eq.
      { eapply Hp. simpl. eauto. } rewrite eq. eauto.
  + assert ((NewVarC (i + S j) (NewVarC i p1)) = (NewVarC i (NewVarC (i + j) p1))) as eq1.
    { eapply Hp. simpl. lia. } rewrite eq1.
    assert ((NewVarC (i + S j) (NewVarC i p2)) = (NewVarC i (NewVarC (i + j) p2))) as eq2.
    { eapply Hp. simpl. lia. } rewrite eq2. eauto.
  + assert (NewVarC (S (i + S j)) (NewVarC (S i) p) = NewVarC (S i) (NewVarC (S (i + j)) p)) as eq.
    { replace ((S (i + S j))) with ((S i) + S j)%nat; try lia.
      replace (S (i + j)) with ((S i) + j)%nat; try lia. eapply Hp.
      simpl. lia. } rewrite eq. eauto.
  + destruct g; simpl.
    * eauto.
    * eauto.
    * rewrite NewVar_in_ChannelData_and_NewVar_in_ChannelData.
      assert ((NewVarC (i + S j) (NewVarC i p)) = (NewVarC i (NewVarC (i + j) p))) as eq.
      { eapply Hp. simpl. eauto. } rewrite eq. eauto.
    * rewrite NewVar_in_ChannelData_and_NewVar_in_ChannelData.
      assert ((NewVarC (i + S j) (NewVarC i p)) = (NewVarC i (NewVarC (i + j) p))) as eq.
      { eapply Hp. simpl. eauto. } rewrite eq. eauto.
    * assert ((NewVarC (i + S j) (NewVarC i p)) = (NewVarC i (NewVarC (i + j) p))) as eq.
      { eapply Hp. simpl. eauto. } rewrite eq. eauto.
    * assert ((NewVarC (i + S j) (NewVarC i (g g1))) = (NewVarC i (NewVarC (i + j) (g g1)))) as eq1.
      { eapply Hp. simpl. lia. } inversion eq1.
      assert ((NewVarC (i + S j) (NewVarC i (g g2))) = (NewVarC i (NewVarC (i + j) (g g2)))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq2. eauto.
Qed.

Notation "⇑ g" := (gNewVarC 0 g) (at level 40).

(* Being syntactically equivalent to a guard, hidden under parallels and unnecessary restrictions *)
Fixpoint sguard (n : nat) (g0 : gproc) (p : proc) := match p with
| (p ‖ q) => (sguard n 𝟘 p /\ sguard n g0 q) \/ (sguard n 𝟘 q /\ sguard n g0 p)
| (ν p) => sguard n (⇑ g0) p
| g p => p ≡g[n] g0
| If E Then p Else q => (Eval_Eq n E = Some true /\ sguard n g0 p) \/
                        (Eval_Eq n E = Some false /\ sguard n g0 q)
| _ => False
end.

(* congruence is preserved by renamings (mutual induction with the proc-level statement) *)
Lemma NewVarC_altcgr_mut :
  (forall n p q, p ≡ₐ[n] q -> forall j, (NewVarC j p) ≡ₐ[n] (NewVarC j q)) /\
  (forall n g1 g2, g1 ≡g[n] g2 -> forall j, (gNewVarC j g1) ≡g[n] (gNewVarC j g2)).
Proof.
apply altcgr_mutind; intros; simpl; try solve [constructor; eauto with *].
- replace (NewVarC (S (S j)) (VarSwap_in_proc 0 p)) with (VarSwap_in_proc 0 (NewVarC (S (S j)) p)).
  + constructor.
  + symmetry. replace (S (S j)) with (S (S (j + 0))) by lia.
    apply NewVarC_and_VarSwap.
- replace (NewVarC (S (S j)) (VarSwap_in_proc 0 p)) with (VarSwap_in_proc 0 (NewVarC (S (S j)) p)).
  + constructor.
  + symmetry. replace (S (S j)) with (S (S (j + 0))) by lia.
    apply NewVarC_and_VarSwap.
- replace (NewVarC (S j) (NewVarC 0 q)) with (NewVarC 0 (NewVarC j q)).
  + constructor.
  + symmetry. exact (NewVarC_and_NewVarC 0 j q).
- replace (NewVarC (S j) (NewVarC 0 q)) with (NewVarC 0 (NewVarC j q)).
  + constructor.
  + symmetry. exact (NewVarC_and_NewVarC 0 j q).
- eapply altcgr_trans; eauto.
- eapply galtcgr_trans; eauto.
Qed.

Lemma gNewVarC_altcgr n g1 g2 : g1 ≡g[n] g2 -> (gNewVarC 0 g1) ≡g[n] (gNewVarC 0 g2).
Proof. intro H. exact (proj2 NewVarC_altcgr_mut n g1 g2 H 0). Qed.

(* 
Pi-calculus version:
Lemma ren2_altcgr:
  (forall p1 p2, p1 ≡ₐ p2 -> forall s1 s2, ren2 s1 s2 p1 ≡ₐ ren2 s1 s2 p2) /\
  (forall g1 g2, g1 ≡g g2 -> forall s1 s2, ren2 s1 s2 g1 ≡g ren2 s1 s2 g2).
Proof.
apply altcgr_mutind; intros; asimpl; simpl; try solve [constructor; eauto with *].
- (* unification issue *)
  generalize (altcgr_nu_nu_step (ren2 s1 (0 .: (1 .: (fun x : nat => S (S (s2 x))))) p)).
  now asimpl.
- generalize (altcgr_scope_step (ren2 s1 (0 .: s2 >> S) P) (ren2 s1 s2 Q)).
  now asimpl.
- generalize (altcgr_scope_rev_step (ren2 s1 (0 .: s2 >> S) P) (ren2 s1 s2 Q)).
  now asimpl.
- eapply altcgr_trans; eauto.
- eapply galtcgr_trans; eauto.
Qed. *)


Lemma sguard_cgr_proper n p g1 g2: sguard n g1 p -> g1 ≡g[n] g2 -> sguard n g2 p.
Proof.
revert g1 g2. induction p; simpl; intuition.
- left. intuition. eauto with *.
- right. intuition. eauto with *.
- left. eauto with *.
- right. eauto with *.
- eapply IHp; [eassumption|]. now apply gNewVarC_altcgr.
- eapply galtcgr_trans; eauto.
Qed.

Lemma gNewVarC_swap_0_S k g0 : gNewVarC (S k) (gNewVarC 0 g0) = gNewVarC 0 (gNewVarC k g0).
Proof.
  pose proof (NewVarC_and_NewVarC 0 k (g g0)) as Heq.
  simpl in Heq.
  injection Heq as Heq.
  exact Heq.
Qed.

Lemma NewVar_in_ChannelData_inj k c1 c2 :
  NewVar_in_ChannelData k c1 = NewVar_in_ChannelData k c2 -> c1 = c2.
Proof.
  destruct c1, c2; simpl; intros H.
  - exact H.
  - destruct (decide (k < S n)); discriminate.
  - destruct (decide (k < S n)); discriminate.
  - destruct (decide (k < S n)); destruct (decide (k < S n0)); injection H as H; f_equal; lia.
Qed.

Lemma NewVarC_inj p1 : forall k p2, NewVarC k p1 = NewVarC k p2 -> p1 = p2.
Proof.
  induction p1 as (p1 & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p1; intros k p2 Heq; destruct p2; simpl in *; try discriminate.
  + injection Heq as Heq1 Heq2.
    f_equal.
    * eapply Hp; [simpl; lia | exact Heq1].
    * eapply Hp; [simpl; lia | exact Heq2].
  + injection Heq as Heq.
    subst.
    reflexivity.
  + injection Heq as Heq.
    f_equal.
    exact Heq.
    eapply Hp; [simpl; lia | exact H].
  + injection Heq as Heq1 Heq2.
    subst.
    f_equal.
    * eapply Hp; [simpl; lia | exact Heq2].
    * eapply Hp; [simpl; lia | exact H].
  + injection Heq as Heq.
    f_equal.
    eapply Hp; [simpl; lia | exact Heq].
  + destruct g, g0; simpl in *; try discriminate.
    * reflexivity.
    * reflexivity.
    * injection Heq as Heq1 Heq2.
      f_equal.
      -- assert (c = c0) as Hc by (eapply NewVar_in_ChannelData_inj; exact Heq1).
         assert (p = p0) as Hpp by (eapply Hp; [simpl; lia | exact Heq2]).
         subst.
         reflexivity.
    * injection Heq as Heq1 Heq2 Heq3.
      assert (c = c0) as Hc by (eapply NewVar_in_ChannelData_inj; exact Heq1).
      assert (p = p0) as Hpp by (eapply Hp; [simpl; lia | exact Heq3]).
      subst.
      reflexivity.
    * injection Heq as Heq.
      f_equal.
      assert (p = p0) as Hpp by (eapply Hp; [simpl; lia | exact Heq]).
      subst.
      reflexivity.
    * injection Heq as Heq1 Heq2.
      assert (g g1 = g g0_1) as E1 by (eapply Hp; [simpl; lia | simpl; f_equal; exact Heq1]).
      assert (g g2 = g g0_2) as E2 by (eapply Hp; [simpl; lia | simpl; f_equal; exact Heq2]).
      injection E1 as E1.
      injection E2 as E2.
      subst.
      reflexivity.
Qed.

Corollary gNewVarC_inj k g1 g2 : gNewVarC k g1 = gNewVarC k g2 -> g1 = g2.
Proof.
  intro H.
  assert (g g1 = g g2) as E by (apply (NewVarC_inj (g g1) k (g g2)); simpl; f_equal; exact H).
  injection E as E.
  exact E.
Qed.

Definition NewVar_in_ChannelData_down (k : nat) (Y : ChannelData) : ChannelData :=
match Y with
| cst v => cst v
| bvar i => if (decide (k < i)) then Nat.pred i else i
end.

Fixpoint NewVarCdown (k : nat) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (NewVarCdown k P) ‖ (NewVarCdown k Q)
| pr_var i => pr_var i
| rec x • P =>  rec x • (NewVarCdown k P)
| If C Then P Else Q => If C Then (NewVarCdown k P) Else (NewVarCdown k Q)
| ν P => ν (NewVarCdown (S k) P)
| g M => gNewVarCdown k M
end

with gNewVarCdown k M {struct M} : gproc :=
match M with
| ① => ①
| 𝟘 => 𝟘
| c ? p => (NewVar_in_ChannelData_down k c) ? (NewVarCdown k p)
| c ! v • p => (NewVar_in_ChannelData_down k c) ! v • (NewVarCdown k p)
| 𝛕 • p => 𝛕 • (NewVarCdown k p)
| p1 + p2 => (gNewVarCdown k p1) + (gNewVarCdown k p2)
end.

Lemma NewVar_in_ChannelData_retract k c : NewVar_in_ChannelData_down k (NewVar_in_ChannelData k c) = c.
Proof.
  destruct c; simpl; auto.
  destruct (decide (k < S n)).
  - simpl.
    destruct (decide (k < S n)); [f_equal; lia | lia].
  - simpl.
    destruct (decide (k < n)); [lia | reflexivity].
Qed.

Lemma NewVarC_retract p : forall k, NewVarCdown k (NewVarC k p) = p.
Proof.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros k; simpl.
  + assert (NewVarCdown k (NewVarC k p1) = p1) as H1 by (apply Hp; simpl; lia).
    assert (NewVarCdown k (NewVarC k p2) = p2) as H2 by (apply Hp; simpl; lia).
    rewrite H1, H2.
    reflexivity.
  + reflexivity.
  + assert (NewVarCdown k (NewVarC k p) = p) as H1 by (apply Hp; simpl; lia).
    rewrite H1.
    reflexivity.
  + assert (NewVarCdown k (NewVarC k p1) = p1) as H1 by (apply Hp; simpl; lia).
    assert (NewVarCdown k (NewVarC k p2) = p2) as H2 by (apply Hp; simpl; lia).
    rewrite H1, H2.
    reflexivity.
  + assert (NewVarCdown (S k) (NewVarC (S k) p) = p) as H1 by (apply Hp; simpl; lia).
    rewrite H1.
    reflexivity.
  + destruct g; simpl; try reflexivity.
    * assert (NewVar_in_ChannelData_down k (NewVar_in_ChannelData k c) = c) as Hc by (apply NewVar_in_ChannelData_retract).
      assert (NewVarCdown k (NewVarC k p) = p) as Hpp by (apply Hp; simpl; lia).
      rewrite Hc, Hpp.
      reflexivity.
    * assert (NewVar_in_ChannelData_down k (NewVar_in_ChannelData k c) = c) as Hc by (apply NewVar_in_ChannelData_retract).
      assert (NewVarCdown k (NewVarC k p) = p) as Hpp by (apply Hp; simpl; lia).
      rewrite Hc, Hpp.
      reflexivity.
    * assert (NewVarCdown k (NewVarC k p) = p) as Hpp by (apply Hp; simpl; lia).
      rewrite Hpp.
      reflexivity.
    * assert (NewVarCdown k (NewVarC k (g g1)) = g g1) as H1 by (apply Hp; simpl; lia).
      assert (NewVarCdown k (NewVarC k (g g2)) = g g2) as H2 by (apply Hp; simpl; lia).
      simpl in H1, H2.
      injection H1 as H1.
      injection H2 as H2.
      rewrite H1, H2.
      reflexivity.
Qed.

Corollary gNewVarC_retract k g0 : gNewVarCdown k (gNewVarC k g0) = g0.
Proof.
  assert (NewVarCdown k (NewVarC k (g g0)) = g g0) as H by (apply NewVarC_retract).
  simpl in H.
  injection H as H.
  exact H.
Qed.

Lemma NewVar_in_ChannelData_down_and_VarSwap_in_ChannelData j k0 c :
NewVar_in_ChannelData_down (S (S (j + k0))) (VarSwap_in_ChannelData k0 c)
        = VarSwap_in_ChannelData k0 (NewVar_in_ChannelData_down (S (S (j + k0))) c).
Proof.
  destruct c.
  + simpl.
    reflexivity.
  + simpl.
    destruct (decide (n = k0)).
    - subst.
      simpl.
      destruct (decide (S (S (j+k0)) < k0)); try lia.
      rewrite decide_False; try lia.
      simpl.
      destruct (decide (k0 = k0)); try lia.
      reflexivity.
    - simpl.
      destruct (decide (n = S k0)); subst.
      * simpl.
        destruct (decide (S (S (j+k0)) < S k0)); try lia.
        rewrite decide_False; try lia.
        simpl.
        destruct (decide (S k0 = k0)); try lia.
        destruct (decide (S k0 = S k0)); try lia.
        reflexivity.
      * destruct (decide (S (S (j+k0)) < n)).
        ++ simpl.
           rewrite decide_True; try lia.
           destruct (decide (Nat.pred n = k0)); try lia.
           destruct (decide (Nat.pred n = S k0)); try lia.
           reflexivity.
        ++ simpl.
           destruct (decide (n = k0)); try lia.
           destruct (decide (n = S k0)); try lia.
           rewrite decide_False; try lia.
           reflexivity.
Qed.

Lemma NewVarCdown_and_VarSwap j k0 p : (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p)).
Proof.
  revert j k0.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + reflexivity.
  + assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + assert (S (S (S (j + k0))) = S (S (j + (S k0)))) as eq' by lia. rewrite eq'.
    assert (NewVarCdown (S (S (j + (S k0)))) (VarSwap_in_proc (S k0) p)
        = VarSwap_in_proc (S k0) (NewVarCdown (S (S (j + (S k0)))) p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + destruct g; simpl in *.
    * reflexivity.
    * reflexivity.
    * assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p)) as eq1.
      { eapply Hp. simpl. lia. } rewrite eq1.
      rewrite NewVar_in_ChannelData_down_and_VarSwap_in_ChannelData. eauto.
    * assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p)) as eq1.
      { eapply Hp. simpl. lia. } rewrite eq1.
      rewrite NewVar_in_ChannelData_down_and_VarSwap_in_ChannelData. eauto.
    * assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 (g g1)) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) (g g1))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 (g g2)) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) (g g2))) as eq2.
      { eapply Hp. simpl. lia. } simpl in *. inversion eq1. inversion eq2.
      rewrite H0, H1. eauto.
Qed.

Lemma NewVar_in_ChannelData_up_down i j c :
  NewVar_in_ChannelData_down (i + S j) (NewVar_in_ChannelData i c) = NewVar_in_ChannelData i (NewVar_in_ChannelData_down (i+j) c).
Proof.
  destruct c.
  simpl.
  + eauto.
  + simpl.
    destruct (decide (i < S n)).
    - simpl.
      destruct (decide (i + j < n)).
      * rewrite decide_True; try lia.
        simpl.
        rewrite decide_True; try lia.
        f_equal; lia.
      * rewrite decide_False; try lia.
        simpl.
        rewrite decide_True; try lia.
        eauto.
    - simpl.
      rewrite decide_False; try lia.
      destruct (decide (i + j < n)); try lia.
      simpl.
      destruct (decide (i < S n)); [lia | reflexivity].
Qed.

Lemma NewVarC_up_down i j p : NewVarCdown (i + S j) (NewVarC i p) = NewVarC i (NewVarCdown (i+j) p).
Proof.
  revert i j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (NewVarCdown (i + S j) (NewVarC i p1) = NewVarC i (NewVarCdown (i+j) p1)) as eq1.
    { eapply Hp. simpl. lia. } rewrite eq1.
    assert (NewVarCdown (i + S j) (NewVarC i p2) = NewVarC i (NewVarCdown (i+j) p2)) as eq2.
    { eapply Hp. simpl. lia. } rewrite eq2. eauto.
  + eauto.
  + assert (NewVarCdown (i + S j) (NewVarC i p) = NewVarC i (NewVarCdown (i+j) p)) as eq.
    { eapply Hp. simpl. eauto. } rewrite eq. eauto.
  + assert (NewVarCdown (i + S j) (NewVarC i p1) = NewVarC i (NewVarCdown (i+j) p1)) as eq1.
    { eapply Hp. simpl. lia. } rewrite eq1.
    assert (NewVarCdown (i + S j) (NewVarC i p2) = NewVarC i (NewVarCdown (i+j) p2)) as eq2.
    { eapply Hp. simpl. lia. } rewrite eq2. eauto.
  + assert (NewVarCdown (S (i + S j)) (NewVarC (S i) p) = NewVarC (S i) (NewVarCdown (S (i+j)) p)) as eq.
    { replace ((S (i + S j))) with ((S i) + S j)%nat; try lia.
      replace (S (i + j)) with ((S i) + j)%nat; try lia. eapply Hp.
      simpl. lia. } rewrite eq. eauto.
  + destruct g; simpl.
    * eauto.
    * eauto.
    * rewrite NewVar_in_ChannelData_up_down.
      assert (NewVarCdown (i + S j) (NewVarC i p) = NewVarC i (NewVarCdown (i+j) p)) as eq.
      { eapply Hp. simpl. eauto. } rewrite eq. eauto.
    * rewrite NewVar_in_ChannelData_up_down.
      assert (NewVarCdown (i + S j) (NewVarC i p) = NewVarC i (NewVarCdown (i+j) p)) as eq.
      { eapply Hp. simpl. eauto. } rewrite eq. eauto.
    * assert (NewVarCdown (i + S j) (NewVarC i p) = NewVarC i (NewVarCdown (i+j) p)) as eq.
      { eapply Hp. simpl. eauto. } rewrite eq. eauto.
    * assert (NewVarCdown (i + S j) (NewVarC i (g g1)) = NewVarC i (NewVarCdown (i+j) (g g1))) as eq1.
      { eapply Hp. simpl. lia. } inversion eq1.
      assert (NewVarCdown (i + S j) (NewVarC i (g g2)) = NewVarC i (NewVarCdown (i+j) (g g2))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq2. eauto.
Qed.

Lemma NewVarCdown_altcgr_mut :
  (forall n p q, p ≡ₐ[n] q -> forall j, (NewVarCdown j p) ≡ₐ[n] (NewVarCdown j q)) /\
  (forall n g1 g2, g1 ≡g[n] g2 -> forall j, (gNewVarCdown j g1) ≡g[n] (gNewVarCdown j g2)).
Proof.
apply altcgr_mutind; intros; simpl.
all: try solve [constructor; auto].
- replace (NewVarCdown (S (S j)) (VarSwap_in_proc 0 p)) with (VarSwap_in_proc 0 (NewVarCdown (S (S j)) p)).
  + constructor.
  + symmetry. replace (S (S j)) with (S (S (j + 0))) by lia.
    apply NewVarCdown_and_VarSwap.
- replace (NewVarCdown (S (S j)) (VarSwap_in_proc 0 p)) with (VarSwap_in_proc 0 (NewVarCdown (S (S j)) p)).
  + constructor.
  + symmetry. replace (S (S j)) with (S (S (j + 0))) by lia.
    apply NewVarCdown_and_VarSwap.
- replace (NewVarCdown (S j) (NewVarC 0 q)) with (NewVarC 0 (NewVarCdown j q)).
  + constructor.
  + symmetry. exact (NewVarC_up_down 0 j q).
- replace (NewVarCdown (S j) (NewVarC 0 q)) with (NewVarC 0 (NewVarCdown j q)).
  + constructor.
  + symmetry. exact (NewVarC_up_down 0 j q).
- eapply altcgr_trans; eauto.
- eapply galtcgr_trans; eauto.
Qed.

Corollary gNewVarC_altcgr_reflect n k p g0 : gNewVarC k p ≡g[n] gNewVarC k g0 -> p ≡g[n] g0.
Proof.
  intro H.
  apply (proj2 NewVarCdown_altcgr_mut) with (j:=k) in H.
  rewrite (gNewVarC_retract k p) in H.
  rewrite (gNewVarC_retract k g0) in H.
  exact H.
Qed.

Lemma sguardNewVar n g0 q:  sguard n g0 q <-> sguard n (⇑ g0) (NewVarC 0 q).
Proof.
split.
- enough (forall q k g0, sguard n g0 q -> sguard n (gNewVarC k g0) (NewVarC k q)) as Hgen.
  { intro H. apply Hgen. exact H. }
  clear g0 q. induction q; intros k g0 H; simpl in *; auto.
  + destruct H as [[H1 H2]|[H1 H2]].
    * left. split.
      -- replace (𝟘) with (gNewVarC k 𝟘) by reflexivity. now apply IHq1.
      -- now apply IHq2.
    * right. split.
      -- replace (𝟘) with (gNewVarC k 𝟘) by reflexivity. now apply IHq2.
      -- now apply IHq1.
  + destruct H as [[H1 H2]|[H1 H2]].
    * left. split; auto.
    * right. split; auto.
  + rewrite <- gNewVarC_swap_0_S. apply IHq. exact H.
  + apply (proj2 NewVarC_altcgr_mut). exact H.
- enough (forall q k g0, sguard n (gNewVarC k g0) (NewVarC k q) -> sguard n g0 q) as Hgen.
  { intro H. apply (Hgen q 0 g0). exact H. }
  clear g0 q. induction q; intros k g0 H; simpl in *; auto.
  + destruct H as [[H1 H2]|[H1 H2]].
    * left. split.
      -- replace (𝟘) with (gNewVarC k 𝟘) in H1 by reflexivity. eapply IHq1; exact H1.
      -- eapply IHq2; exact H2.
    * right. split.
      -- replace (𝟘) with (gNewVarC k 𝟘) in H1 by reflexivity. eapply IHq2; exact H1.
      -- eapply IHq1; exact H2.
  + destruct H as [[H1 H2]|[H1 H2]].
    * left. split; auto. eapply IHq1; exact H2.
    * right. split; auto. eapply IHq2; exact H2.
  + rewrite <- gNewVarC_swap_0_S in H. eapply IHq; exact H.
  + eapply gNewVarC_altcgr_reflect; exact H.
Qed.



Lemma VarSwap_in_ChannelData_invol k0 c : VarSwap_in_ChannelData k0 (VarSwap_in_ChannelData k0 c) = c.
Proof.
destruct c; simpl; auto.
destruct (decide (n = k0)).
- subst. simpl. destruct (decide (S k0 = k0)); try lia.
  destruct (decide (S k0 = S k0)); try lia. reflexivity.
- destruct (decide (n = S k0)).
  + subst. simpl. destruct (decide (k0 = k0)); try lia. reflexivity.
  + simpl. destruct (decide (n = k0)); try lia. destruct (decide (n = S k0)); try lia. reflexivity.
Qed.

Lemma VarSwap_in_proc_invol p : forall k0, VarSwap_in_proc k0 (VarSwap_in_proc k0 p) = p.
Proof.
induction p as (p & Hp) using
  (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros k0; simpl.
+ assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p1) = p1) as H1 by (apply Hp; simpl; lia).
  assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p2) = p2) as H2 by (apply Hp; simpl; lia).
  rewrite H1, H2. reflexivity.
+ reflexivity.
+ assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p) = p) as H1 by (apply Hp; simpl; lia).
  rewrite H1. reflexivity.
+ assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p1) = p1) as H1 by (apply Hp; simpl; lia).
  assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p2) = p2) as H2 by (apply Hp; simpl; lia).
  rewrite H1, H2. reflexivity.
+ assert (VarSwap_in_proc (S k0) (VarSwap_in_proc (S k0) p) = p) as H1 by (apply Hp; simpl; lia).
  rewrite H1. reflexivity.
+ destruct g; simpl; try reflexivity.
  * rewrite VarSwap_in_ChannelData_invol.
    assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p) = p) as Hpp by (apply Hp; simpl; lia).
    rewrite Hpp. reflexivity.
  * rewrite VarSwap_in_ChannelData_invol.
    assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p) = p) as Hpp by (apply Hp; simpl; lia).
    rewrite Hpp. reflexivity.
  * assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p) = p) as Hpp by (apply Hp; simpl; lia).
    rewrite Hpp. reflexivity.
  * assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 (g g1)) = g g1) as H1 by (apply Hp; simpl; lia).
    assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 (g g2)) = g g2) as H2 by (apply Hp; simpl; lia).
    simpl in H1, H2. injection H1 as H1. injection H2 as H2.
    rewrite H1, H2. reflexivity.
Qed.

Corollary gVarSwap_in_proc_invol k0 g1 : gVarSwap_in_proc k0 (gVarSwap_in_proc k0 g1) = g1.
Proof.
assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 (g g1)) = g g1) as H by (apply VarSwap_in_proc_invol).
simpl in H. injection H as H. exact H.
Qed.

Lemma NewVar_in_ChannelData_and_VarSwap_in_ChannelData_le i k0 c : i <= k0 ->
  VarSwap_in_ChannelData (S k0) (NewVar_in_ChannelData i c) = NewVar_in_ChannelData i (VarSwap_in_ChannelData k0 c).
Proof.
intro Hle.
destruct c; simpl; auto.
destruct (decide (i < S n)).
- simpl.
  destruct (decide (n = k0)).
  + subst.
    destruct (decide (S k0 = S k0)); try lia.
    simpl.
    destruct (decide (i < S (S k0))); [f_equal; lia | lia].
  + destruct (decide (n = S k0)).
    * subst.
      destruct (decide (S (S k0) = S k0)); try lia.
      destruct (decide (S (S k0) = S (S k0))); try lia.
      simpl.
      destruct (decide (i < S k0)); [f_equal; lia | lia].
    * destruct (decide (S n = S k0)); try lia.
      destruct (decide (S n = S (S k0))); try lia.
      simpl.
      destruct (decide (i < S n)); [f_equal; lia | lia].
- simpl.
  destruct (decide (n = S k0)); try lia.
  destruct (decide (n = S (S k0))); try lia.
  destruct (decide (n = k0)); try lia.
  simpl.
  destruct (decide (i < S n)); [lia | reflexivity].
Qed.

Lemma NewVarC_and_VarSwap_le p : forall i k0, i <= k0 ->
  VarSwap_in_proc (S k0) (NewVarC i p) = NewVarC i (VarSwap_in_proc k0 p).
Proof.
induction p as (p & Hp) using
  (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros i k0 Hle; simpl.
+ assert (VarSwap_in_proc (S k0) (NewVarC i p1) = NewVarC i (VarSwap_in_proc k0 p1)) as eq1.
  { apply Hp; [simpl; lia | lia]. }
  assert (VarSwap_in_proc (S k0) (NewVarC i p2) = NewVarC i (VarSwap_in_proc k0 p2)) as eq2.
  { apply Hp; [simpl; lia | lia]. }
  rewrite eq1, eq2. reflexivity.
+ reflexivity.
+ assert (VarSwap_in_proc (S k0) (NewVarC i p) = NewVarC i (VarSwap_in_proc k0 p)) as eq.
  { apply Hp; [simpl; lia | lia]. }
  rewrite eq. reflexivity.
+ assert (VarSwap_in_proc (S k0) (NewVarC i p1) = NewVarC i (VarSwap_in_proc k0 p1)) as eq1.
  { apply Hp; [simpl; lia | lia]. }
  assert (VarSwap_in_proc (S k0) (NewVarC i p2) = NewVarC i (VarSwap_in_proc k0 p2)) as eq2.
  { apply Hp; [simpl; lia | lia]. }
  rewrite eq1, eq2. reflexivity.
+ assert (VarSwap_in_proc (S (S k0)) (NewVarC (S i) p) = NewVarC (S i) (VarSwap_in_proc (S k0) p)) as eq.
  { apply Hp; [simpl; lia | lia]. }
  rewrite eq. reflexivity.
+ destruct g; simpl.
  * reflexivity.
  * reflexivity.
  * rewrite NewVar_in_ChannelData_and_VarSwap_in_ChannelData_le; auto.
    assert (VarSwap_in_proc (S k0) (NewVarC i p) = NewVarC i (VarSwap_in_proc k0 p)) as eq.
    { apply Hp; [simpl; lia | lia]. }
    rewrite eq. reflexivity.
  * rewrite NewVar_in_ChannelData_and_VarSwap_in_ChannelData_le; auto.
    assert (VarSwap_in_proc (S k0) (NewVarC i p) = NewVarC i (VarSwap_in_proc k0 p)) as eq.
    { apply Hp; [simpl; lia | lia]. }
    rewrite eq. reflexivity.
  * assert (VarSwap_in_proc (S k0) (NewVarC i p) = NewVarC i (VarSwap_in_proc k0 p)) as eq.
    { apply Hp; [simpl; lia | lia]. }
    rewrite eq. reflexivity.
  * assert (VarSwap_in_proc (S k0) (NewVarC i (g g1)) = NewVarC i (VarSwap_in_proc k0 (g g1))) as eq1.
    { apply Hp; [simpl; lia | lia]. } inversion eq1.
    assert (VarSwap_in_proc (S k0) (NewVarC i (g g2)) = NewVarC i (VarSwap_in_proc k0 (g g2))) as eq2.
    { apply Hp; [simpl; lia | lia]. } inversion eq2.
    rewrite H0, H1. reflexivity.
Qed.

Corollary gVarSwap_and_gNewVarC0 k0 g1 :
  gVarSwap_in_proc (S k0) (gNewVarC 0 g1) = gNewVarC 0 (gVarSwap_in_proc k0 g1).
Proof.
assert (VarSwap_in_proc (S k0) (NewVarC 0 (g g1)) = NewVarC 0 (VarSwap_in_proc k0 (g g1))) as H.
{ apply NewVarC_and_VarSwap_le. lia. }
simpl in H. injection H as H. exact H.
Qed.

Lemma VarSwap_in_ChannelData_disjoint j k0 c :
  VarSwap_in_ChannelData j (VarSwap_in_ChannelData (S (S (j+k0))) c) = VarSwap_in_ChannelData (S (S (j+k0))) (VarSwap_in_ChannelData j c).
Proof.
destruct c; simpl; auto.
repeat match goal with
| |- context[decide (?a = ?b)] => destruct (decide (a = b))
end; try lia; try reflexivity.
all: simpl; repeat match goal with
| |- context[decide (?a = ?b)] => destruct (decide (a = b))
end; try lia; try reflexivity.
Qed.

Lemma VarSwap_and_VarSwap_disjoint p : forall j k0,
  VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p).
Proof.
induction p as (p & Hp) using
  (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros j k0; simpl.
+ assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p1) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p1)) as eq1.
  { apply Hp. simpl. lia. }
  assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p2) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p2)) as eq2.
  { apply Hp. simpl. lia. }
  rewrite eq1, eq2. reflexivity.
+ reflexivity.
+ assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p)) as eq.
  { apply Hp. simpl. lia. }
  rewrite eq. reflexivity.
+ assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p1) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p1)) as eq1.
  { apply Hp. simpl. lia. }
  assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p2) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p2)) as eq2.
  { apply Hp. simpl. lia. }
  rewrite eq1, eq2. reflexivity.
+ assert (S (S (S (j + k0))) = S (S (S j + k0))) as eq' by lia. rewrite eq'.
  assert (VarSwap_in_proc (S j) (VarSwap_in_proc (S (S (S j+k0))) p) = VarSwap_in_proc (S (S (S j+k0))) (VarSwap_in_proc (S j) p)) as eq.
  { apply Hp. simpl. lia. }
  rewrite eq. reflexivity.
+ destruct g; simpl.
  * reflexivity.
  * reflexivity.
  * rewrite VarSwap_in_ChannelData_disjoint.
    assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p)) as eq.
    { apply Hp. simpl. lia. }
    rewrite eq. reflexivity.
  * rewrite VarSwap_in_ChannelData_disjoint.
    assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p)) as eq.
    { apply Hp. simpl. lia. }
    rewrite eq. reflexivity.
  * assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p)) as eq.
    { apply Hp. simpl. lia. }
    rewrite eq. reflexivity.
  * assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) (g g1)) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j (g g1))) as eq1.
    { apply Hp. simpl. lia. } inversion eq1.
    assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) (g g2)) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j (g g2))) as eq2.
    { apply Hp. simpl. lia. } inversion eq2.
    rewrite H0, H1. reflexivity.
Qed.

Lemma VarSwap_altcgr_mut :
  (forall n p q, p ≡ₐ[n] q -> forall k0, (VarSwap_in_proc k0 p) ≡ₐ[n] (VarSwap_in_proc k0 q)) /\
  (forall n g1 g2, g1 ≡g[n] g2 -> forall k0, (gVarSwap_in_proc k0 g1) ≡g[n] (gVarSwap_in_proc k0 g2)).
Proof.
apply altcgr_mutind; intros; simpl.
all: try solve [constructor; auto].
- replace (VarSwap_in_proc (S (S k0)) (VarSwap_in_proc 0 p)) with (VarSwap_in_proc 0 (VarSwap_in_proc (S (S k0)) p)).
  + constructor.
  + exact (VarSwap_and_VarSwap_disjoint p 0 k0).
- replace (VarSwap_in_proc (S (S k0)) (VarSwap_in_proc 0 p)) with (VarSwap_in_proc 0 (VarSwap_in_proc (S (S k0)) p)).
  + constructor.
  + exact (VarSwap_and_VarSwap_disjoint p 0 k0).
- replace (VarSwap_in_proc (S k0) (NewVarC 0 q)) with (NewVarC 0 (VarSwap_in_proc k0 q)).
  + constructor.
  + symmetry. apply NewVarC_and_VarSwap_le. lia.
- replace (VarSwap_in_proc (S k0) (NewVarC 0 q)) with (NewVarC 0 (VarSwap_in_proc k0 q)).
  + constructor.
  + symmetry. apply NewVarC_and_VarSwap_le. lia.
- eapply altcgr_trans; eauto.
- eapply galtcgr_trans; eauto.
Qed.

Lemma sguard_VarSwap_gen : forall n p k0 g1, sguard n g1 p -> sguard n (gVarSwap_in_proc k0 g1) (VarSwap_in_proc k0 p).
Proof.
intros n p. induction p; intros k0 g1 H; simpl in *; auto.
- destruct H as [[H1 H2]|[H1 H2]].
  + left. split.
    * replace (𝟘) with (gVarSwap_in_proc k0 𝟘) by reflexivity. now apply IHp1.
    * now apply IHp2.
  + right. split.
    * replace (𝟘) with (gVarSwap_in_proc k0 𝟘) by reflexivity. now apply IHp2.
    * now apply IHp1.
- destruct H as [[H1 H2]|[H1 H2]].
  + left. split; auto.
  + right. split; auto.
- rewrite <- gVarSwap_and_gNewVarC0. apply IHp. exact H.
- apply (proj2 VarSwap_altcgr_mut). exact H.
Qed.

Lemma sguard_VarSwap_in_proc n g1 p:
  sguard n g1 p <-> sguard n (gVarSwap_in_proc 0 g1) (VarSwap_in_proc 0 p).
Proof.
split.
- apply sguard_VarSwap_gen.
- intro H.
  apply (sguard_VarSwap_gen n (VarSwap_in_proc 0 p) 0 (gVarSwap_in_proc 0 g1)) in H.
  rewrite VarSwap_in_proc_invol in H.
  rewrite gVarSwap_in_proc_invol in H.
  exact H.
Qed.


Lemma NewVar_in_ChannelData_double_fixed k c :
  VarSwap_in_ChannelData k (NewVar_in_ChannelData k (NewVar_in_ChannelData k c)) = NewVar_in_ChannelData k (NewVar_in_ChannelData k c).
Proof.
destruct c; simpl; auto.
destruct (decide (k < S n)).
- simpl. destruct (decide (k < S (S n))).
  + simpl. destruct (decide (S (S n) = k)); try lia.
    destruct (decide (S (S n) = S k)); try lia. reflexivity.
  + lia.
- simpl. destruct (decide (k < S n)); try lia.
  destruct (decide (n = k)); try lia.
  destruct (decide (n = S k)); try lia.
  simpl. destruct (decide (n = k)); try lia.
  destruct (decide (n = S k)); try lia. reflexivity.
Qed.

Lemma VarSwap_fixes_NewVarC_double p : forall k,
  VarSwap_in_proc k (NewVarC k (NewVarC k p)) = NewVarC k (NewVarC k p).
Proof.
induction p as (p & Hp) using
  (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros k; simpl.
+ assert (VarSwap_in_proc k (NewVarC k (NewVarC k p1)) = NewVarC k (NewVarC k p1)) as H1 by (apply Hp; simpl; lia).
  assert (VarSwap_in_proc k (NewVarC k (NewVarC k p2)) = NewVarC k (NewVarC k p2)) as H2 by (apply Hp; simpl; lia).
  rewrite H1, H2. reflexivity.
+ reflexivity.
+ assert (VarSwap_in_proc k (NewVarC k (NewVarC k p)) = NewVarC k (NewVarC k p)) as H1 by (apply Hp; simpl; lia).
  rewrite H1. reflexivity.
+ assert (VarSwap_in_proc k (NewVarC k (NewVarC k p1)) = NewVarC k (NewVarC k p1)) as H1 by (apply Hp; simpl; lia).
  assert (VarSwap_in_proc k (NewVarC k (NewVarC k p2)) = NewVarC k (NewVarC k p2)) as H2 by (apply Hp; simpl; lia).
  rewrite H1, H2. reflexivity.
+ assert (VarSwap_in_proc (S k) (NewVarC (S k) (NewVarC (S k) p)) = NewVarC (S k) (NewVarC (S k) p)) as H1 by (apply Hp; simpl; lia).
  rewrite H1. reflexivity.
+ destruct g; simpl; try reflexivity.
  * rewrite NewVar_in_ChannelData_double_fixed.
    assert (VarSwap_in_proc k (NewVarC k (NewVarC k p)) = NewVarC k (NewVarC k p)) as Hpp by (apply Hp; simpl; lia).
    rewrite Hpp. reflexivity.
  * rewrite NewVar_in_ChannelData_double_fixed.
    assert (VarSwap_in_proc k (NewVarC k (NewVarC k p)) = NewVarC k (NewVarC k p)) as Hpp by (apply Hp; simpl; lia).
    rewrite Hpp. reflexivity.
  * assert (VarSwap_in_proc k (NewVarC k (NewVarC k p)) = NewVarC k (NewVarC k p)) as Hpp by (apply Hp; simpl; lia).
    rewrite Hpp. reflexivity.
  * assert (VarSwap_in_proc k (NewVarC k (NewVarC k (g g1))) = NewVarC k (NewVarC k (g g1))) as H1 by (apply Hp; simpl; lia).
    assert (VarSwap_in_proc k (NewVarC k (NewVarC k (g g2))) = NewVarC k (NewVarC k (g g2))) as H2 by (apply Hp; simpl; lia).
    simpl in H1, H2. injection H1 as H1. injection H2 as H2.
    rewrite H1, H2. reflexivity.
Qed.

Lemma gVarSwap_NewVar_NewVar g0 :
  gVarSwap_in_proc 0 (⇑ (⇑ g0)) = ⇑ (⇑ g0).
Proof.
assert (VarSwap_in_proc 0 (NewVarC 0 (NewVarC 0 (g g0))) = NewVarC 0 (NewVarC 0 (g g0))) as H by (apply VarSwap_fixes_NewVarC_double).
simpl in H. injection H as H. exact H.
Qed.

Lemma NewVar_altcgr_gstep n g1 g2: g1 ≡g[n] g2 <-> (⇑ g1) ≡g[n] (⇑ g2).
Proof.
split.
- intro H. apply (proj2 NewVarC_altcgr_mut). exact H.
- apply gNewVarC_altcgr_reflect.
Qed.




Lemma altcgr_guard_proper n (p0 p1 : proc) (g0 : gproc) : (p0 ≡ₐ[n] p1) -> sguard n g0 p0
  -> sguard n g0 p1.
Proof.
intro H. dependent induction H generalizing g0; simpl; try solve[constructor]; auto with *;
intuition; simpl; eauto with *.
- eapply sguard_cgr_proper; eauto.
- change 𝟘 with (⇑ 𝟘) in H. now apply NewVar_altcgr_gstep.
- change 𝟘 with (⇑ 𝟘). now rewrite <- NewVar_altcgr_gstep.
- rewrite <- gVarSwap_NewVar_NewVar. now rewrite <- sguard_VarSwap_in_proc.
- rewrite <- gVarSwap_NewVar_NewVar in H. now rewrite sguard_VarSwap_in_proc.
- left. split; trivial. now rewrite sguardNewVar.
- right. split; trivial. change 𝟘 with (⇑ 𝟘) in H. now rewrite sguardNewVar.
- left. split; trivial. now rewrite <- sguardNewVar.
- right. split; trivial. change 𝟘 with (⇑ 𝟘). now rewrite <- sguardNewVar.
- apply galtcgr_trans with g1; trivial. now apply galtcgr_sym_step.
Qed.

(* The congruence between guards, is no stronger than the congruence over guards *)
Lemma altcgr_guard_rev n g1 g2: g g1 ≡ₐ[n] g g2 -> g1 ≡g[n] g2.
Proof.
intro Ha. inversion Ha; subst; [constructor|auto|].
apply (altcgr_guard_proper n q (g g1) g2); [now symmetry|].
apply (altcgr_guard_proper n (g g2) q g2); [now symmetry|].
constructor.
Qed.

Lemma cgr_choice : forall n p q r, g p ≡*[n] g q -> p + r ≡*[n] q + r.
Proof.
intros n p q r H%cgr_altcgr%altcgr_guard_rev.
apply altcgr_cgr. now do 2 constructor.
Qed.

End AlternativeCongruence.

(* If Then Else of processes respects ≡*[n] *)
Lemma cgr_full_if n C p p' q q' : p ≡*[n] p' -> q ≡*[n] q' -> (If C Then p Else q) ≡*[n] (If C Then p' Else q').
Proof.
intros.
apply transitivity with (If C Then p Else q'). apply cgr_if_left. exact H0.
apply cgr_if_right. exact H.
Qed.

(* The sum of guards respects ≡*[n] *)
Lemma cgr_fullchoice n M1 M2 M3 M4 : g M1 ≡*[n] g M2 -> g M3 ≡*[n] g M4 -> M1 + M3 ≡*[n] M2 + M4.
Proof.
intros.
apply transitivity with (g (M2 + M3)). apply cgr_choice. exact H. apply transitivity with (g (M3 + M2)).
apply cgr_choice_com. apply transitivity with (g (M4 + M2)). apply cgr_choice. exact H0. apply cgr_choice_com.
Qed.
(* The parallele of process respects ≡*[n] *)
Lemma cgr_fullpar n M1 M2 M3 M4 : M1 ≡*[n] M2 -> M3 ≡*[n] M4 -> M1 ‖ M3 ≡*[n] M2 ‖ M4.
Proof.
intros.
apply transitivity with (M2 ‖ M3). apply cgr_par. exact H. apply transitivity with (M3 ‖ M2).
apply cgr_par_com. apply transitivity with (M4 ‖ M2). apply cgr_par. exact H0. apply cgr_par_com.
Qed.


Hint Resolve cgr_if_true cgr_if_true_rev cgr_if_false cgr_if_false_rev
cgr_par_nil cgr_par_nil_rev cgr_par_com cgr_par_assoc cgr_par_assoc_rev 
cgr_choice_nil cgr_choice_nil_rev cgr_choice_com cgr_choice_assoc cgr_choice_assoc_rev
cgr_recursion cgr_tau cgr_input cgr_output cgr_if_left cgr_if_right cgr_par cgr_choice
cgr_full_if cgr_fullchoice cgr_fullpar cgr_res_nil cgr_res_nil_rev cgr_res_swap cgr_res_swap_rev cgr_res
cgr_res_scope cgr_res_scope_rev cgr_refl cgr_symm cgr_trans:cgr.

Lemma subst_equation d E v x : Eval_Eq (S d) E = Some x -> Eval_Eq d (subst_in_Equation d v E) = Some x.
Proof.
  intros H. destruct E as [v0 v1]. destruct v0 as [t|n]; destruct v1 as [t'|n0];
    simpl in *; eauto; try discriminate.
  - destruct (decide (S d <= n0)) as [Hn|Hn]; [| discriminate].
    injection H as Hx. subst x.
    rewrite decide_False by lia.
    rewrite decide_False by lia.
    simpl.
    rewrite decide_True by lia.
    reflexivity.
  - destruct (decide (S d <= n)) as [Hn|Hn]; [| discriminate].
    injection H as Hx. subst x.
    rewrite decide_False by lia.
    rewrite decide_False by lia.
    simpl.
    rewrite decide_True by lia.
    reflexivity.
  - destruct (decide (n = n0)) as [->|Hneq].
    + injection H as Hx. subst x.
      destruct (decide (n0 = d)) as [->|Hnd].
      * destruct v as [c|i]; simpl; rewrite decide_True; reflexivity.
      * destruct (decide (n0 < d)) as [Hlt|Hlt]; simpl; rewrite decide_True; reflexivity.
    + destruct (decide (S d <= n)) as [Hn|Hn]; [| discriminate].
      destruct (decide (S d <= n0)) as [Hn0|Hn0]; [| discriminate].
      injection H as Hx. subst x.
      rewrite decide_False by lia.
      rewrite decide_False by lia.
      simpl.
      rewrite decide_False by lia.
      rewrite decide_False by lia.
      simpl.
      destruct (decide (Nat.pred n = Nat.pred n0)); [lia|].
      rewrite decide_True by lia.
      rewrite decide_True by lia.
      reflexivity.
Qed.

Lemma NewVar_equation n E k x : k <= n -> Eval_Eq n E = Some x -> Eval_Eq (S n) (NewVar_in_Equation k E) = Some x.
Proof.
  intros Hkn H. destruct E as [v0 v1]. destruct v0 as [t|i]; destruct v1 as [t'|i'];
    simpl in *; eauto; try discriminate.
  - destruct (decide (n <= i')) as [Hi|Hi]; [| discriminate].
    injection H as Hx. subst x.
    rewrite decide_True by lia.
    simpl.
    rewrite decide_True by lia.
    reflexivity.
  - destruct (decide (n <= i)) as [Hi|Hi]; [| discriminate].
    injection H as Hx. subst x.
    rewrite decide_True by lia.
    simpl.
    rewrite decide_True by lia.
    reflexivity.
  - destruct (decide (i = i')) as [->|Hneq].
    + injection H as Hx. subst x.
      destruct (decide (k < S i')) as [Hlt|Hlt]; simpl; rewrite decide_True by reflexivity; reflexivity.
    + destruct (decide (n <= i)) as [Hi|Hi]; [| discriminate].
      destruct (decide (n <= i')) as [Hi'|Hi']; [| discriminate].
      injection H as Hx. subst x.
      rewrite decide_True by lia.
      rewrite decide_True by lia.
      simpl.
      destruct (decide (S i = S i')); [lia|].
      rewrite decide_True by lia.
      rewrite decide_True by lia.
      reflexivity.
Qed.


Lemma subst_and_VarSwap k k0 v p : subst_in_proc k v (VarSwap_in_proc k0 p) = (VarSwap_in_proc k0 (subst_in_proc k v p)).
Proof. 
  revert k k0 v.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (subst_in_proc k v (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (subst_in_proc k v p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (subst_in_proc k v (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (subst_in_proc k v p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + reflexivity.
  + assert (subst_in_proc k v (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (subst_in_proc k v p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + assert (subst_in_proc k v (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (subst_in_proc k v p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (subst_in_proc k v (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (subst_in_proc k v p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + assert (subst_in_proc k v (VarSwap_in_proc (S k0) p) = VarSwap_in_proc (S k0) (subst_in_proc k v p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + destruct g; simpl in *.
    * reflexivity.
    * reflexivity.
    * assert ((subst_in_proc (S k) (Succ_bvar v) (VarSwap_in_proc k0 p)) 
          = (VarSwap_in_proc k0 (subst_in_proc (S k) (Succ_bvar v) p))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
   * assert (subst_in_proc k v (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (subst_in_proc k v p)) as eq.
     { eapply Hp. simpl. lia. }
     rewrite eq. eauto.
   * assert (subst_in_proc k v (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (subst_in_proc k v p)) as eq.
     { eapply Hp. simpl. lia. }
     rewrite eq. eauto.
   * assert (subst_in_proc k v (VarSwap_in_proc k0 (g g1)) = VarSwap_in_proc k0 (subst_in_proc k v (g g1))) as eq1.
     { eapply Hp. simpl. lia. }
     assert (subst_in_proc k v (VarSwap_in_proc k0 (g g2)) = VarSwap_in_proc k0 (subst_in_proc k v (g g2))) as eq2.
     { eapply Hp. simpl. lia. } simpl in *. inversion eq1. inversion eq2.
     rewrite H0 , H1. eauto.
Qed.

Lemma subst_and_NewVarC k j v q : subst_in_proc k v (NewVarC j q) = NewVarC j (subst_in_proc k v q).
Proof.
  revert k j v.
  induction q as (q & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct q; intros; simpl in *.
  + assert (subst_in_proc k v (NewVarC j q1) = NewVarC j (subst_in_proc k v q1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (subst_in_proc k v (NewVarC j q2) = NewVarC j (subst_in_proc k v q2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1 , eq2. eauto.
  + eauto.
  + assert (subst_in_proc k v (NewVarC j q) = NewVarC j (subst_in_proc k v q)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + assert (subst_in_proc k v (NewVarC j q1) = NewVarC j (subst_in_proc k v q1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (subst_in_proc k v (NewVarC j q2) = NewVarC j (subst_in_proc k v q2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1 , eq2. eauto.
  + assert (subst_in_proc k v (NewVarC (S j) q) = NewVarC (S j) (subst_in_proc k v q)) as eq1.
    { eapply Hp. simpl. eauto. }
    rewrite eq1. eauto.
  + destruct g; simpl in *.
    * eauto.
    * eauto.
    * assert ((subst_in_proc (S k) (Succ_bvar v) (NewVarC j p))
        = (NewVarC j (subst_in_proc (S k) (Succ_bvar v) p))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (subst_in_proc k v (NewVarC j p) = NewVarC j (subst_in_proc k v p)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (subst_in_proc k v (NewVarC j p) = NewVarC j (subst_in_proc k v p)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (subst_in_proc k v (NewVarC j (g g1)) = NewVarC j (subst_in_proc k v (g g1))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (subst_in_proc k v (NewVarC j (g g2)) = NewVarC j (subst_in_proc k v (g g2))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.


Lemma cgr_step_subst : forall d p q, cgr_step d p q -> forall n, d = S n -> forall v,
    cgr_step n (subst_in_proc n v p) (subst_in_proc n v q).
Proof.
intros d p q H. induction H; intros n0 Heqn w; subst n; simpl; eauto with cgr_step_structure.
- apply cgr_if_true_step. eapply subst_equation. eauto.
- apply cgr_if_true_rev_step. eapply subst_equation. eauto.
- apply cgr_if_false_step. eapply subst_equation. eauto.
- apply cgr_if_false_rev_step. eapply subst_equation. eauto.
- rewrite subst_and_VarSwap. apply cgr_res_swap_step.
- rewrite subst_and_VarSwap. apply cgr_res_swap_rev_step.
- rewrite subst_and_NewVarC. apply cgr_res_scope_step.
- rewrite subst_and_NewVarC. apply cgr_res_scope_rev_step.
Qed.

Lemma Congruence_Respects_Substitution : forall n p q v, p ≡*[S n] q -> (subst_in_proc n v p) ≡*[n] (subst_in_proc n v q).
Proof.
intros n p q v H. dependent induction H.
* constructor. eapply cgr_step_subst; eauto.
* transitivity (subst_in_proc n v y). apply (IHclos_trans1 n v eq_refl). apply (IHclos_trans2 n v eq_refl).
Qed.

Lemma NewVar_and_VarSwap j k0 p : (NewVar j (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVar j p)).
Proof.
  revert j k0.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (NewVar j (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (NewVar j p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVar j (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (NewVar j p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + reflexivity.
  + assert (NewVar j (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVar j p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + assert (NewVar j (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (NewVar j p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVar j (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (NewVar j p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + assert (NewVar j (VarSwap_in_proc (S k0) p) = VarSwap_in_proc (S k0) (NewVar j p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + destruct g; simpl in *.
    * reflexivity.
    * reflexivity.
    * assert (NewVar (S j) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVar (S j) p)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
   * assert (NewVar j (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVar j p)) as eq.
     { eapply Hp. simpl. lia. }
     rewrite eq. eauto.
   * assert (NewVar j (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVar j p)) as eq.
     { eapply Hp. simpl. lia. }
     rewrite eq. eauto.
   * assert (NewVar j (VarSwap_in_proc k0 (g g1)) = VarSwap_in_proc k0 (NewVar j (g g1))) as eq1.
     { eapply Hp. simpl. lia. }
     assert (NewVar j (VarSwap_in_proc k0 (g g2)) = VarSwap_in_proc k0 (NewVar j (g g2))) as eq2.
     { eapply Hp. simpl. lia. } simpl in *. inversion eq1. inversion eq2.
     rewrite H0 , H1. eauto.
Qed.

Lemma NewVar_and_NewVarC j k p : (NewVar k (NewVarC j p) = (NewVarC j (NewVar k p))).
Proof.
  revert j k.
  (* Induction on the size of p*)
  induction p as (p & Hp) using
      (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros; destruct p ; simpl in *.
  + assert (NewVar k (NewVarC j p1) = NewVarC j (NewVar k p1)) as eq1.
    { eapply Hp; simpl ; lia. }
    assert (NewVar k (NewVarC j p2) = NewVarC j (NewVar k p2)) as eq2.
    { eapply Hp; simpl ; lia. }
    rewrite eq1, eq2. eauto.
  + eauto.
  + assert (NewVar k (NewVarC j p) = NewVarC j (NewVar k p)) as eq.
    { eapply Hp; simpl ; lia. }
    rewrite eq. eauto.
  + assert (NewVar k (NewVarC j p1) = NewVarC j (NewVar k p1)) as eq1.
    { eapply Hp; simpl ; lia. }
    assert (NewVar k (NewVarC j p2) = NewVarC j (NewVar k p2)) as eq2.
    { eapply Hp; simpl ; lia. }
    rewrite eq1, eq2. eauto.
  + assert (NewVar k (NewVarC (S j) p) = NewVarC (S j) (NewVar k p)) as eq.
    { eapply Hp; simpl ; lia. }
    rewrite eq. eauto.
  + destruct g; simpl in *.
    * eauto.
    * eauto.
    * assert (NewVar (S k) (NewVarC j p) = NewVarC j (NewVar (S k) p)) as eq.
      { eapply Hp; simpl ; lia. }
      rewrite eq. eauto.
    * assert (NewVar k (NewVarC j p) = NewVarC j (NewVar k p)) as eq.
      { eapply Hp; simpl ; lia. }
      rewrite eq. eauto.
    * assert (NewVar k (NewVarC j p) = NewVarC j (NewVar k p)) as eq.
      { eapply Hp; simpl ; lia. }
      rewrite eq. eauto.
    * assert (NewVar k (NewVarC j (g g1)) = NewVarC j (NewVar k (g g1))) as eq1.
      { eapply Hp; simpl ; lia. }
      assert (NewVar k (NewVarC j (g g2)) = NewVarC j (NewVar k (g g2))) as eq2.
      { eapply Hp; simpl ; lia. } inversion eq1. inversion eq2.
      rewrite H0, H1. eauto.
Qed.


Lemma cgr_step_NewVar : forall n p q, cgr_step n p q -> forall j, j <= n -> cgr_step (S n) (NewVar j p) (NewVar j q).
Proof.
intros n p q H. induction H; intros j Hjn; simpl; eauto with cgr_step_structure.
- apply cgr_if_true_step. eapply NewVar_equation; eauto.
- apply cgr_if_true_rev_step. eapply NewVar_equation; eauto.
- apply cgr_if_false_step. eapply NewVar_equation; eauto.
- apply cgr_if_false_rev_step. eapply NewVar_equation; eauto.
- rewrite NewVar_and_VarSwap. apply cgr_res_swap_step.
- rewrite NewVar_and_VarSwap. apply cgr_res_swap_rev_step.
- rewrite NewVar_and_NewVarC. apply cgr_res_scope_step.
- rewrite NewVar_and_NewVarC. apply cgr_res_scope_rev_step.
- apply cgr_input_step. apply IHcgr_step. lia.
Qed.

Lemma NewVar_Respects_Congruence : forall n p p' j, j <= n -> p ≡*[n] p' -> NewVar j p ≡*[S n] NewVar j p'.
Proof.
intros n p p' j Hjn H. dependent induction H.
- constructor. eapply cgr_step_NewVar; eauto.
- transitivity (NewVar j y); assumption.
Qed.

(* [NewVarC] only ever shifts channel indices, an index space entirely
   disjoint from the ValueData depth [n] that [Eval_Eq]/[cgr_step] track, so
   it never needs to change [n]. *)
Lemma cgr_step_NewVarC : forall n p q, cgr_step n p q -> forall j, cgr_step n (NewVarC j p) (NewVarC j q).
Proof.
intros n p q H. induction H; intros j; simpl; eauto with cgr_step_structure.
- replace (NewVarC (S (S j)) (VarSwap_in_proc 0 p)) with (VarSwap_in_proc 0 (NewVarC (S (S j)) p)).
  + apply cgr_res_swap_step.
  + symmetry. replace (S (S j)) with (S (S (j + 0))) by lia. apply NewVarC_and_VarSwap.
- replace (NewVarC (S (S j)) (VarSwap_in_proc 0 p)) with (VarSwap_in_proc 0 (NewVarC (S (S j)) p)).
  + apply cgr_res_swap_rev_step.
  + symmetry. replace (S (S j)) with (S (S (j + 0))) by lia. apply NewVarC_and_VarSwap.
- replace (NewVarC (S j) (NewVarC 0 q)) with (NewVarC 0 (NewVarC j q)).
  + apply cgr_res_scope_step.
  + symmetry. exact (NewVarC_and_NewVarC 0 j q).
- replace (NewVarC (S j) (NewVarC 0 q)) with (NewVarC 0 (NewVarC j q)).
  + apply cgr_res_scope_rev_step.
  + symmetry. exact (NewVarC_and_NewVarC 0 j q).
Qed.

Lemma NewVarC_Respects_Congruence : forall n p p' j, p ≡*[n] p' -> NewVarC j p ≡*[n] NewVarC j p'.
Proof.
intros n p p' j H. dependent induction H.
- constructor. apply cgr_step_NewVarC; eauto.
- transitivity (NewVarC j y); assumption.
Qed.

(* Substition lemma, needed to contextualise the equivalence *)
Lemma cgr_subst1 : forall p n q q' x, q ≡*[n] q' → pr_subst x p q ≡*[n] pr_subst x p q'.
Proof.
(* Induction on the size of p*)
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
intros n q q' x H.
destruct p; simpl.
  - apply cgr_fullpar.
    apply Hp. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ. exact H.
    apply Hp. simpl. rewrite <-Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply Nat.lt_0_succ. exact H.
  - destruct (decide (x = n0)). exact H. reflexivity.
  - destruct (decide (x = n0)). reflexivity. apply cgr_recursion. apply Hp. simpl. auto. exact H.
  - apply cgr_full_if.
    apply Hp. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ. exact H.
    apply Hp. simpl. rewrite <-Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply Nat.lt_0_succ. exact H.
  - eapply cgr_res. apply Hp. simpl. auto with arith. eapply NewVarC_Respects_Congruence. assumption.
  - destruct g; intros; simpl.
    * reflexivity.
    * reflexivity.
    * apply cgr_input. apply Hp. simpl. auto with arith. apply NewVar_Respects_Congruence. lia. assumption.
    * apply cgr_output. apply Hp. simpl. auto. auto.
    * apply cgr_tau. apply Hp. simpl. auto. auto.
    * apply cgr_fullchoice.
      assert (pr_subst x (g g1) q ≡*[n] pr_subst x (g g1) q'). apply Hp. simpl. auto with arith. auto.
      auto. assert (pr_subst x (g g2) q ≡*[n] pr_subst x (g g2) q'). apply Hp. simpl. auto with arith. auto.
      auto.
Qed.

Lemma VarSwap_NewVarC_in_ChannelData k c : NewVar_in_ChannelData k (NewVar_in_ChannelData k c) 
  = VarSwap_in_ChannelData k (NewVar_in_ChannelData k (NewVar_in_ChannelData k c)).
Proof.
  destruct c; simpl.
  + eauto.
  + destruct (decide (k < S n)).
    * simpl. rewrite decide_True; try lia.
      simpl. rewrite decide_False; try lia.
      rewrite decide_False; try lia. eauto.
    * simpl. rewrite decide_False; try lia.
      simpl. rewrite decide_False; try lia.
      rewrite decide_False; try lia. eauto.
Qed.

Lemma VarSwap_NewVarC k q : NewVarC k (NewVarC k q) = VarSwap_in_proc k (NewVarC k (NewVarC k q)).
Proof.
  revert k.
  induction q as (q & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct q ; intros; simpl in *.
  + assert (NewVarC k (NewVarC k q1) = VarSwap_in_proc k (NewVarC k (NewVarC k q1))) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarC k (NewVarC k q2) = VarSwap_in_proc k (NewVarC k (NewVarC k q2))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1 at 1. rewrite eq2 at 1. eauto.
  + eauto.
  + assert (NewVarC k (NewVarC k q) = VarSwap_in_proc k (NewVarC k (NewVarC k q))) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq at 1. eauto.
  + assert (NewVarC k (NewVarC k q1) = VarSwap_in_proc k (NewVarC k (NewVarC k q1))) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarC k (NewVarC k q2) = VarSwap_in_proc k (NewVarC k (NewVarC k q2))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1 at 1. rewrite eq2 at 1. eauto.
  + assert (NewVarC (S k) (NewVarC (S k) q) = VarSwap_in_proc (S k) (NewVarC (S k) (NewVarC (S k) q))) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq at 1. eauto.
  + destruct g; simpl in *.
    * eauto.
    * eauto.
    * assert (NewVarC k (NewVarC k p) = VarSwap_in_proc k (NewVarC k (NewVarC k p))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq at 1. eauto. rewrite VarSwap_NewVarC_in_ChannelData at 1.
      eauto.
    * assert (NewVarC k (NewVarC k p) = VarSwap_in_proc k (NewVarC k (NewVarC k p))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq at 1. rewrite VarSwap_NewVarC_in_ChannelData at 1.
      eauto.
    * assert (NewVarC k (NewVarC k p) = VarSwap_in_proc k (NewVarC k (NewVarC k p))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq at 1. eauto.
    * assert (NewVarC k (NewVarC k (g g1)) = VarSwap_in_proc k (NewVarC k (NewVarC k (g g1)))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (NewVarC k (NewVarC k (g g2)) = VarSwap_in_proc k (NewVarC k (NewVarC k (g g2)))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

Lemma pr_subst_and_VarSwap n p0 k q : pr_subst n (VarSwap_in_proc k p0) (NewVarC k (NewVarC k q)) 
      = VarSwap_in_proc k (pr_subst n p0 (NewVarC k (NewVarC k q))).
Proof.
  revert n k q.
  induction p0 as (p0 & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros; destruct p0; simpl in *.
  + assert (pr_subst n (VarSwap_in_proc k p0_1) (NewVarC k (NewVarC k q))
       = VarSwap_in_proc k (pr_subst n p0_1 (NewVarC k (NewVarC k q)))) as eq1.
    { eapply Hp. simpl. lia. }
    assert (pr_subst n (VarSwap_in_proc k p0_2) (NewVarC k (NewVarC k q))
       = VarSwap_in_proc k (pr_subst n p0_2 (NewVarC k (NewVarC k q)))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + destruct (decide (n = n0)); subst.
    ++ simpl. rewrite VarSwap_NewVarC at 1. eauto.
    ++ simpl. eauto.
  + destruct (decide (n = n0)); subst.
    ++ eauto.
    ++ simpl. assert (pr_subst n (VarSwap_in_proc k p0) (NewVarC k (NewVarC k q)) 
          = VarSwap_in_proc k (pr_subst n p0 (NewVarC k (NewVarC k q)))) as eq.
       { eapply Hp. simpl. lia. }
       rewrite eq. eauto.
  + assert (pr_subst n (VarSwap_in_proc k p0_1) (NewVarC k (NewVarC k q))
      = VarSwap_in_proc k (pr_subst n p0_1 (NewVarC k (NewVarC k q)))) as eq1.
    { eapply Hp. simpl. lia. }
    assert (pr_subst n (VarSwap_in_proc k p0_2) (NewVarC k (NewVarC k q))
      = VarSwap_in_proc k (pr_subst n p0_2 (NewVarC k (NewVarC k q)))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + assert (NewVarC (0 + (S k)) (NewVarC 0 q) = NewVarC 0 (NewVarC ( 0 + k ) q)) as eq.
    { rewrite NewVarC_and_NewVarC. eauto. }
    assert (NewVarC (0 + (S k)) (NewVarC 0 (NewVarC k q)) = NewVarC 0 (NewVarC ( 0 + k ) (NewVarC k q))) as eq2.
    { rewrite NewVarC_and_NewVarC. eauto. } simpl in *. rewrite<- eq2. rewrite<- eq.
    assert (pr_subst n (VarSwap_in_proc (S k) p0) (NewVarC (S k) (NewVarC (S k) (NewVarC 0 q)))
      = VarSwap_in_proc (S k) (pr_subst n p0 (NewVarC (S k) (NewVarC (S k) (NewVarC 0 q))))) as eq1.
    { eapply Hp. simpl. lia. } rewrite eq1. eauto.
  + destruct g; simpl.
    * eauto.
    * eauto.
    * rewrite NewVar_and_NewVarC. rewrite NewVar_and_NewVarC.
      assert ((pr_subst n (VarSwap_in_proc k p) (NewVarC k (NewVarC k (NewVar 0 q))))
        = (VarSwap_in_proc k (pr_subst n p (NewVarC k (NewVarC k (NewVar 0 q)))))) as eq1.
      { eapply Hp. simpl. lia. } rewrite eq1. eauto.
    * assert (pr_subst n (VarSwap_in_proc k p) (NewVarC k (NewVarC k q))
        = VarSwap_in_proc k (pr_subst n p (NewVarC k (NewVarC k q)))) as eq1.
      { eapply Hp. simpl. lia. } rewrite eq1. eauto.
    * assert (pr_subst n (VarSwap_in_proc k p) (NewVarC k (NewVarC k q))
        = VarSwap_in_proc k (pr_subst n p (NewVarC k (NewVarC k q)))) as eq1.
      { eapply Hp. simpl. lia. } rewrite eq1. eauto.
    * assert (pr_subst n (VarSwap_in_proc k (g g1)) (NewVarC k (NewVarC k q))
        = VarSwap_in_proc k (pr_subst n (g g1) (NewVarC k (NewVarC k q)))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (pr_subst n (VarSwap_in_proc k (g g2)) (NewVarC k (NewVarC k q))
        = VarSwap_in_proc k (pr_subst n (g g2) (NewVarC k (NewVarC k q)))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

Lemma pr_subst_and_NewVarC q0 q n k : (pr_subst n (NewVarC k q0) (NewVarC k q) = NewVarC k (pr_subst n q0 q)).
Proof.
  revert n k q.
  induction q0 as (q0 & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct q0; intros; simpl in *.
  + assert (pr_subst n (NewVarC k q0_1) (NewVarC k q) = NewVarC k (pr_subst n q0_1 q)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (pr_subst n (NewVarC k q0_2) (NewVarC k q) = NewVarC k (pr_subst n q0_2 q)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1 , eq2. eauto.
  + destruct (decide(n0 = n)).
    - eauto.
    - simpl. eauto.
  + destruct (decide(n0 = n)).
    - eauto.
    - simpl. assert (pr_subst n0 (NewVarC k q0) (NewVarC k q) = NewVarC k (pr_subst n0 q0 q)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + assert (pr_subst n (NewVarC k q0_1) (NewVarC k q) = NewVarC k (pr_subst n q0_1 q)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (pr_subst n (NewVarC k q0_2) (NewVarC k q) = NewVarC k (pr_subst n q0_2 q)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1 , eq2. eauto.
  + assert (NewVarC (0 + (S k)) (NewVarC 0 q) = NewVarC 0 (NewVarC ( 0 + k ) q)) as eq1.
    { rewrite NewVarC_and_NewVarC. eauto. }
    simpl in *. rewrite<- eq1.
    assert (pr_subst n (NewVarC (S k) q0) (NewVarC (S k) (NewVarC 0 q))
      = NewVarC (S k) (pr_subst n q0 (NewVarC 0 q))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq2. eauto.
  + destruct g; simpl in *.
    * eauto.
    * eauto.
    * simpl. rewrite NewVar_and_NewVarC.
      assert ((pr_subst n (NewVarC k p) (NewVarC k (NewVar 0 q))) = (NewVarC k (pr_subst n p (NewVar 0 q)))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (pr_subst n (NewVarC k p) (NewVarC k q) = NewVarC k (pr_subst n p q)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (pr_subst n (NewVarC k p) (NewVarC k q) = NewVarC k (pr_subst n p q)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (pr_subst n (NewVarC k (g g1)) (NewVarC k q) = NewVarC k (pr_subst n (g g1) q)) as eq1.
      { eapply Hp. simpl. lia. }
      assert (pr_subst n (NewVarC k (g g2)) (NewVarC k q) = NewVarC k (pr_subst n (g g2) q)) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

(* ≡ respects the substitution of his variable*)
Lemma cgr_step_subst2 : forall p d p' q x, cgr_step d p p' → pr_subst x p q ≡[d] pr_subst x p' q.
Proof.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros d p' q n hcgr. inversion hcgr; subst; try auto; try (exact H); try (now constructor).
  - simpl. rewrite pr_subst_and_VarSwap. eapply cgr_res_swap_step.
  - simpl. rewrite pr_subst_and_VarSwap. eapply cgr_res_swap_rev_step.
  - simpl. rewrite pr_subst_and_NewVarC. eapply cgr_res_scope_step.
  - simpl. rewrite pr_subst_and_NewVarC. eapply cgr_res_scope_rev_step.
  - simpl. destruct (decide (n = x)). auto. constructor. apply Hp. subst. simpl. auto.  exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H.
  - simpl. constructor. apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H.
  - simpl. constructor. apply Hp. subst. simpl. simpl. lia. eauto.
  - simpl. constructor. apply Hp. subst. simpl. lia. eauto.
  - simpl. constructor. apply Hp. subst. simpl. lia. eauto.
  - simpl. apply cgr_choice_step.
    assert (pr_subst n (g p1) q ≡[d] pr_subst n (g q1) q). apply Hp. subst. simpl. rewrite <-Nat.add_succ_r.
    apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H. eauto.
Qed.

(* ≡* respects the substitution of his variable *)
Lemma cgr_subst2 : forall n q p p' x, p ≡*[n] p' → pr_subst x p q ≡*[n] pr_subst x p' q.
Proof.
intros n q p p' x hcgr. induction hcgr. constructor. now eapply cgr_step_subst2. apply transitivity with (pr_subst x y q).
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

Hint Resolve cgr_is_eq_rel: ccs.
Hint Constructors clos_trans:ccs.
Hint Unfold cgr:ccs.

End VCCS_congruence.

Global Notation "p ≡ q" := (cgr_step 0 p q) (at level 70).
Global Notation "p ≡[ n ] q" := (cgr_step n p q) (at level 70).
Global Notation "p ≡* q" := (cgr 0 p q) (at level 70).
Global Notation "p ≡*[ n ] q" := (cgr n p q) (at level 70).

Global Hint Resolve cgr_is_eq_rel: ccs.
Global Hint Constructors clos_trans:ccs.
Global Hint Unfold cgr:ccs.
Global Hint Constructors cgr_step:cgr_step_structure.

Global Hint Resolve cgr_refl cgr_symm cgr_trans:cgr_eq.

#[export] Hint Resolve cgr_if_true cgr_if_true_rev cgr_if_false cgr_if_false_rev
cgr_par_nil cgr_par_nil_rev cgr_par_com cgr_par_assoc cgr_par_assoc_rev 
cgr_choice_nil cgr_choice_nil_rev cgr_choice_com cgr_choice_assoc cgr_choice_assoc_rev
cgr_recursion cgr_tau cgr_input cgr_if_left cgr_if_right cgr_par cgr_choice
cgr_full_if cgr_fullchoice cgr_fullpar cgr_res_nil cgr_res_nil_rev cgr_res_swap cgr_res_swap_rev cgr_res
cgr_res_scope cgr_res_scope_rev cgr_refl @cgr_symm cgr_trans:cgr.

