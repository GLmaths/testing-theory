(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>

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
From Must Require Import TransitionSystems Must Completeness.

Require Import Coq.Wellfounded.Inverse_Image.

Definition name := string.

(* Definition of processes*)
Inductive proc : Type :=
(* To parallele two processes*)
| pr_par : proc -> proc -> proc
(* Variable in a process, for recursion and substitution*)
| pr_var : nat -> proc
(* recursion for process*)
| pr_rec : nat -> proc -> proc
(*The Guards*)
| g : gproc -> proc

with gproc : Type :=
(* The success operation*)
| gpr_success : gproc
(* The Process that does nothing*)
| gpr_nil : gproc
(*An input is a name of a channel followed by a process*)
| gpr_input : name -> proc -> gproc
(*An output is a name of a channel followed by a process*)
| gpr_output : name -> proc -> gproc
(*A tau action : does nothing *)
| gpr_tau : proc -> gproc
(* To choose between two processes*)
| gpr_choice : gproc -> gproc -> gproc
.

(* decision procedure to equal processes*)
Fixpoint proc_dec (x y : proc) : { x = y } + { x <> y }
with gproc_dec (x y : gproc) : { x = y } + { x <> y }.
Proof.
  decide equality; destruct (decide (n = n0)); eauto.
  decide equality; destruct (decide (n = n0)); eauto.
Qed.

#[global] Instance proc_eq_decision_instance : EqDecision proc.
Proof. by exact proc_dec. Defined.


Notation pr_success := (g gpr_success).
Notation θ := (g gpr_nil).
Notation pr_input a p := (g (gpr_input a p)).
Notation pr_output a p := (g (gpr_output a p)).
Notation pr_tau p := (g (gpr_tau p)).
Notation pr_choice p q := (g (gpr_choice p q)).

(*Some notation to simplify the view of the code*)
Infix "∥" := pr_par (at level 50).
Infix "˖" := pr_choice (at level 50).
Infix "?" := gpr_input (at level 50).
Infix "!" := gpr_output (at level 50).


(*Definition for the size of a term : proc, to do induction on it in the future*)
Fixpoint size (p : proc) :=
  match p with
  | pr_par p q  => S (size p + size q)
  | pr_var _ => 1
  | pr_rec x p => S (size p)
  | g p => gsize p
  end

with gsize p :=
  match p with
  | gpr_success => 1
  | gpr_nil => 0
  | gpr_input a p => S (size p)
  | gpr_output a p => S (size p)
  | gpr_tau p => S (size p)
  | gpr_choice p q => S (gsize p + gsize q)
  end.


(* Substitution, usefull for Recursion def and Context definition (for congruence) *)
Fixpoint pr_subst id p q :=
  match p with
  | pr_par p1 p2 => pr_par (pr_subst id p1 q) (pr_subst id p2 q)
  | pr_var id' => if decide (id = id') then q else p
  | pr_rec id' p' =>
    if decide (id = id') then p else pr_rec id' (pr_subst id p' q)
  | g gp => g (gpr_subst id gp q)
end

with gpr_subst id p q {struct p} := match p with
| gpr_success => p
| gpr_nil => p
| gpr_input a p =>
    gpr_input a (pr_subst id p q)

| gpr_output a p =>
    gpr_output a (pr_subst id p q)

| gpr_tau p =>
    gpr_tau (pr_subst id p q)
| gpr_choice p1 p2 =>
    gpr_choice (gpr_subst id p1 q) (gpr_subst id p2 q)
end.


(* The Labelled Transition System (LTS-transition) *)
Inductive lts : proc -> Act name -> proc -> Prop :=
(*The Input and the Output*)
| lts_input : forall {a t},
    lts (pr_input a t) (ActExt (ActIn a)) t
| lts_output : forall {a t},
    lts (pr_output a t) (ActExt (ActOut a)) t

(*The actions Tau*)
| lts_tau : forall {t},
    lts (pr_tau t) τ t
| lts_rec : forall {x p},
    lts (pr_rec x p) τ (pr_subst x p (pr_rec x p))

(* Communication of a channel output and input that have the same name*)
| lts_comL : forall {a p1 p2 q1 q2},
    lts p1 (ActExt (ActOut a)) p2 ->
    lts q1 (ActExt (ActIn a)) q2 ->
    lts (pr_par p1 q1) τ (pr_par p2 q2)
| lts_comR : forall {a p1 p2 q1 q2},
    lts p1 (ActExt (ActOut a)) p2 ->
    lts q1 (ActExt (ActIn a)) q2 ->
    lts (pr_par q1 p1) τ (pr_par q2 p2)

(*The decoration for the transition system...*)
(*...for the parallele*)
| lts_parL : forall {α p1 p2 q},
    lts p1 α p2 ->
    lts (pr_par p1 q) α (pr_par p2 q)
| lts_parR : forall {α p q1 q2},
    lts q1 α q2 ->
    lts (pr_par p q1) α (pr_par p q2)
(*...for the sum*)
| lts_choiceL : forall {p1 p2 q α},
    lts (g p1) α q ->
    lts (pr_choice p1 p2) α q
| lts_choiceR : forall {p1 p2 q α},
    lts (g p2) α q ->
    lts (pr_choice p1 p2) α q
.


#[global] Hint Constructors lts:ccs.

Reserved Notation "p ≡ q" (at level 70).
(*Naïve definition of a relation ≡ that will become a congruence ≡* by transitivity*)
Inductive cgr_step : proc -> proc -> Prop :=
(*  Reflexivity of the Relation ≡  *)
| cgr_refl_step : forall p, p ≡ p

(* Rules for the Parallèle *)
| cgr_par_nil_step : forall p,
    p ∥ θ ≡ p
| cgr_par_nil_rev_step : forall p,
    p ≡ p ∥ θ
| cgr_par_com_step : forall p q,
    p ∥ q ≡ q ∥ p
| cgr_par_assoc_step : forall p q r,
    (p ∥ q) ∥ r ≡ p ∥(q ∥r)
| cgr_par_assoc_rev_step : forall p q r,
    p ∥(q ∥ r) ≡ (p ∥ q) ∥ r

(* Rules for the Summation *)
| cgr_choice_nil_step : forall p,
    p ˖ gpr_nil ≡ (g p)
| cgr_choice_nil_rev_step : forall p,
    (g p) ≡ p ˖ gpr_nil
| cgr_choice_com_step : forall p q,
    p ˖ q ≡ q ˖ p
| cgr_choice_assoc_step : forall p q r,
    (gpr_choice p  q) ˖ r ≡ p ˖ (gpr_choice q r)
| cgr_choice_assoc_rev_step : forall p q r,
    p ˖ (gpr_choice q r) ≡ (gpr_choice p q) ˖ r

(*The reduction is given to certain terms...*)
| cgr_recursion_step : forall x p q,
    cgr_step p q -> (pr_rec x p) ≡ (pr_rec x q)
| cgr_tau_step : forall p q,
    cgr_step p q ->
    (pr_tau p) ≡ (pr_tau q)
| cgr_input_step : forall a p q,
    cgr_step p q ->
    (pr_input a p) ≡ (pr_input a q)
| cgr_output_step : forall a p q,
    cgr_step p q ->
    (pr_output a p) ≡ (pr_output a q)
| cgr_par_step : forall p q r,
    cgr_step p q->
    p ∥ r ≡ q ∥ r

(*...and sums (only for gards (by sanity))*)
| cgr_choice_step : forall p1 q1 p2,
    cgr_step (g p1) (g q1) -> 
    p1 ˖ p2 ≡ q1 ˖ p2
.


#[global] Hint Constructors cgr_step:cgr_step_structure.

Infix "≡" := cgr_step (at level 70).

(* The relation ≡ is an reflexive*)
#[global] Instance cgr_refl_step_is_refl : Reflexive cgr_step.
Proof. intro. apply cgr_refl_step. Qed.
(* The relation ≡ is symmetric*)
#[global] Instance cgr_symm_step : Symmetric cgr_step.
Proof. intros p q hcgr. induction hcgr; constructor ; auto. Qed.

(* Defining the transitive closure of ≡*)
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
Lemma cgr_par_nil : forall p, p ∥ θ ≡* p.
Proof.
constructor.
apply cgr_par_nil_step.
Qed.
Lemma cgr_par_nil_rev : forall p, p ≡* p ∥ θ.
Proof.
constructor.
apply cgr_par_nil_rev_step.
Qed.
Lemma cgr_par_com : forall p q, p ∥ q ≡* q ∥ p.
Proof.
constructor.
apply cgr_par_com_step.
Qed.
Lemma cgr_par_assoc : forall p q r, (p ∥ q) ∥ r ≡* p ∥(q ∥r).
Proof.
constructor.
apply cgr_par_assoc_step.
Qed.
Lemma cgr_par_assoc_rev : forall p q r, p ∥(q ∥ r) ≡* (p ∥ q) ∥ r.
Proof.
constructor.
apply cgr_par_assoc_rev_step.
Qed.
Lemma cgr_choice_nil : forall p, p ˖ gpr_nil ≡* (g p).
Proof.
constructor.
apply cgr_choice_nil_step.
Qed.
Lemma cgr_choice_nil_rev : forall p, (g p) ≡* p ˖ gpr_nil.
Proof.
constructor.
apply cgr_choice_nil_rev_step.
Qed.
Lemma cgr_choice_com : forall p q, p ˖ q ≡* q ˖ p.
Proof.
constructor.
apply cgr_choice_com_step.
Qed.
Lemma cgr_choice_assoc : forall p q r, (gpr_choice p  q) ˖ r ≡* p ˖ (gpr_choice q r).
Proof.
constructor.
apply cgr_choice_assoc_step.
Qed.
Lemma cgr_choice_assoc_rev : forall p q r, p ˖ (gpr_choice q r) ≡* (gpr_choice p q) ˖ r.
Proof.
constructor.
apply cgr_choice_assoc_rev_step.
Qed.
Lemma cgr_recursion : forall x p q, p ≡* q -> (pr_rec x p) ≡* (pr_rec x q).
Proof.
intros. dependent induction H. 
constructor. 
apply cgr_recursion_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_tau : forall p q, p ≡* q -> (pr_tau p) ≡* (pr_tau q).
Proof.
intros. dependent induction H. 
constructor. 
apply cgr_tau_step. exact H. eauto with cgr_eq.
Qed. 
Lemma cgr_input : forall a p q, p ≡* q -> (pr_input a p) ≡* (pr_input a q).
Proof.
intros. dependent induction H. 
constructor.
apply cgr_input_step. exact H. eauto with cgr_eq.
Qed. 
Lemma cgr_output : forall a p q, p ≡* q -> (pr_output a p) ≡* (pr_output a q).
Proof.
intros. dependent induction H. 
constructor.
apply cgr_output_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_par : forall p q r, p ≡* q-> p ∥ r ≡* q ∥ r.
Proof.
intros. dependent induction H. 
constructor.
apply cgr_par_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_choice : forall p1 q1 p2, (g p1) ≡* (g q1) ->  p1 ˖ p2 ≡* q1 ˖ p2.
Proof.
intros. dependent induction H. 
  - constructor. apply cgr_choice_step. exact H.
  -
Admitted.


(* The sum of guards respects ≡* *)
Lemma cgr_fullchoice : forall M1 M2 M3 M4, g M1 ≡* g M2 -> g M3 ≡* g M4 -> M1 ˖ M3 ≡* M2 ˖ M4.
Proof.
intros.
apply transitivity with (M2 ˖ M3). apply cgr_choice. exact H. apply transitivity with (M3 ˖ M2).
apply cgr_choice_com. apply transitivity with (M4 ˖ M2). apply cgr_choice. exact H0. apply cgr_choice_com.
Qed.
(* The parallele of process respects ≡* *)
Lemma cgr_fullpar : forall M1 M2 M3 M4, M1 ≡* M2 -> M3 ≡* M4 -> M1 ∥ M3 ≡* M2 ∥ M4.
Proof.
intros.
apply transitivity with (M2 ∥ M3). apply cgr_par. exact H. apply transitivity with (M3 ∥ M2).
apply cgr_par_com. apply transitivity with (M4 ∥ M2). apply cgr_par. exact H0. apply cgr_par_com.
Qed.

(* Decision procedure for the name of channel *)
Definition name_eq_dec : forall (x y : name), { x = y } + { x <> y } := string_dec.

#[global] Instance name_eqdecision : EqDecision name. by exact name_eq_dec. Defined.


#[global] Hint Resolve cgr_par_nil cgr_par_nil_rev cgr_par_nil_rev cgr_par_com cgr_par_assoc 
cgr_par_assoc_rev cgr_choice_nil cgr_choice_nil_rev cgr_choice_com cgr_choice_assoc 
cgr_choice_assoc_rev cgr_recursion cgr_tau cgr_input cgr_output cgr_par cgr_choice 
cgr_refl cgr_symm cgr_trans:cgr.


(* State Transition System (STS-reduction) *)
Inductive sts : proc -> proc -> Prop :=
(*The axiomes*)
(* Communication of channels output and input that have the same name *)
| sts_com : forall {μ p1 m1 p2 m2},
    sts (pr_par(pr_choice (gpr_output μ p1) (m1)) (pr_choice (gpr_input μ p2) (m2))) (pr_par p1 p2)
(* Nothing more , something less *)
| sts_tau : forall {t m},
    sts (pr_choice (gpr_tau t) m) t
(* Resursion *)
| sts_rec : forall {x p},
    sts (pr_rec x p) (pr_subst x p (pr_rec x p))

(* The left parallele respect the Reduction *)
| sts_par : forall {p1 p2 q},
    sts p1 p2 ->
    sts (pr_par p1 q) (pr_par p2 q)

(*The Congruence respects the Reduction *)
| sts_cong : forall {p1 p2 q2 q1},
    p1 ≡* p2 -> sts p2 q2 -> q2 ≡* q1 -> sts p1 q1
.
Infix "➙" := sts (at level 50).

#[global] Hint Constructors sts:ccs.

(* For the (STS-reduction), the reductible terms and reducted terms are pretty all the same, up to ≡* *)
Lemma ReductionShape : forall P Q, P ➙ Q ->
((exists x P1 P2 M1 M2 S, ((P ≡* (((x ! P1) ˖ M1) ∥ ((x ? P2) ˖ M2)) ∥ S)) /\ (Q ≡*((P1 ∥ P2) ∥ S)))
\/ (exists P1 M1 S, (P ≡* (((gpr_tau P1) ˖ M1) ∥ S)) /\ (Q ≡* (P1 ∥ S)))
\/ (exists n P1 S, (P ≡* ((pr_rec n P1) ∥ S)) /\ (Q ≡* (pr_subst n P1 (pr_rec n P1) ∥ S)))).
Proof.
intros P Q Transition.
induction Transition.
  - left. exists μ. exists p1. exists p2. exists m1. exists m2. exists (g gpr_nil). split; apply cgr_par_nil_rev.
  - right. left. exists t. exists m. exists θ. split; apply cgr_par_nil_rev.
  - right. right. exists x. exists p. exists θ. split; apply cgr_par_nil_rev.
  - destruct IHTransition as [IH|[IH|IH]]; [ left | right; left | right; right]; decompose record IH.
    * exists x. exists x0. exists x1. exists x2. exists x3. exists (x4 ∥ q). split.
        ** apply transitivity with (((((x ! x0) ˖ x2) ∥ ((x ? x1) ˖ x3)) ∥ x4) ∥ q). apply cgr_par. exact H. apply cgr_par_assoc.
        ** apply transitivity with (((x0 ∥ x1) ∥ x4) ∥ q). apply cgr_par. exact H1.  apply cgr_par_assoc.
    * exists x. exists x0. exists (x1 ∥ q). split.
        ** apply transitivity with (((gpr_tau x ˖ x0) ∥ x1) ∥ q). apply cgr_par. exact H0.
        apply cgr_par_assoc.
        ** apply transitivity with (x ∥(x1) ∥ q). apply cgr_par. exact H1. apply cgr_par_assoc.
    * exists x. exists x0. exists (x1 ∥ q). split. 
        ** apply transitivity with ((pr_rec x x0 ∥ x1) ∥ q). apply cgr_par. exact H0. apply cgr_par_assoc.
        ** apply transitivity with ((pr_subst x x0 (pr_rec x x0) ∥ x1) ∥ q). apply cgr_par. exact H1. apply cgr_par_assoc.
  - destruct IHTransition as [IH|[IH|IH]]; [ left | right; left | right; right];  decompose record IH.
    * exists x. exists x0. exists x1. exists x2. exists x3. exists x4. split. apply cgr_trans with p2. exact H. exact H1.
      apply cgr_trans with q2. apply cgr_symm. exact H0. exact H3.
    * exists x. exists x0. exists x1. split. apply cgr_trans with p2. exact H. exact H2. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
    * exists x. exists x0. exists x1. split. apply cgr_trans with p2. exact H. exact H2. apply cgr_trans with q2.
      apply cgr_symm. apply H0. apply H3.
Qed.


(* For the (LTS-transition), the transitable terms and transitted terms, that performs a INPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForInput : forall P V x, (lts P (ActExt (ActIn x)) V -> 
(exists Q M R, ((P ≡* ((x ? Q) ˖ M) ∥ R)) /\ (V ≡* (Q ∥ R)) /\ ((exists L,P = (g L)) -> R = θ))).
Proof.
intros P V x Transition.
 dependent induction Transition.
- exists t. exists gpr_nil. exists θ. split ; try split.
  * apply cgr_trans with ((x ? t) ˖ gpr_nil). apply cgr_trans with (g (x ? t)). apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
  * reflexivity.
- destruct (IHTransition x). reflexivity. decompose record H. exists x0. exists x1. exists (x2 ∥ q). split; try split.
  * apply cgr_trans with ((((x ? x0) ˖ x1) ∥ x2) ∥ q). apply cgr_par. exact H0. apply cgr_par_assoc.
  * apply cgr_trans with ((x0 ∥ x2) ∥ q). apply cgr_par. exact H1. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition x). reflexivity. decompose record H. exists x0. exists x1. exists (x2 ∥ p). split; try split.
  * apply cgr_trans with ((((x ? x0) ˖ x1) ∥ x2) ∥ p). apply cgr_trans with (q1 ∥ p). apply cgr_par_com. apply cgr_par. exact H0. apply cgr_par_assoc.
  * apply cgr_trans with ((x0 ∥ x2) ∥ p). apply cgr_trans with (q2 ∥ p). apply cgr_par_com. apply cgr_par. exact H1. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition x). reflexivity. decompose record H. exists x0. exists (gpr_choice x1 p2). exists θ. split ; try split.
  * apply cgr_trans with ((x ? x0) ˖ gpr_choice x1 p2). apply cgr_trans with ((gpr_choice (x ? x0) x1) ˖ p2).
    apply cgr_choice. assert (x2 = θ). apply H3. exists p1. reflexivity. rewrite H2 in H0. apply transitivity with (((x ? x0) ˖ x1) ∥ θ).
    exact H0. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x2 = θ). apply H3. exists p1. reflexivity. rewrite H2 in H1. exact H1.
  * reflexivity.
- destruct (IHTransition x). reflexivity. decompose record H. exists x0. exists (gpr_choice x1 p1). exists θ. split; try split.
  * apply cgr_trans with ((x ? x0) ˖ gpr_choice x1 p1). apply cgr_trans with ((gpr_choice (x ? x0) x1) ˖ p1).
    apply cgr_trans with (p2 ˖ p1). apply cgr_choice_com. apply cgr_choice. assert (x2 = θ). apply H3. exists p2. reflexivity.
    apply cgr_trans with (((x ? x0) ˖ x1) ∥ x2). exact H0. rewrite H2. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x2 = θ). apply H3. exists p2. reflexivity. rewrite <-H2. exact H1.
  * reflexivity.
Qed.

(* For the (LTS-transition), the transitable terms and transitted terms, that performs a OUPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForOutput : forall P V x, (lts P (ActExt (ActOut x)) V -> 
(exists Q M R, ((P ≡* ((x! Q) ˖ M) ∥ R)) /\ (V ≡* (Q ∥ R)) /\ ((exists L,P = (g L)) -> R = θ))).
Proof.
intros P V x Transition.
 dependent induction Transition.
- exists t. exists gpr_nil. exists θ. split ; try split.
  * apply cgr_trans with ((x ! t) ˖ gpr_nil). apply cgr_trans with (g (x ! t)). apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
  * reflexivity.
- destruct (IHTransition x). reflexivity. decompose record H. exists x0. exists x1. exists (x2 ∥ q). split; try split.
  * apply cgr_trans with ((((x ! x0) ˖ x1) ∥ x2) ∥ q). apply cgr_par. exact H0. apply cgr_par_assoc.
  * apply cgr_trans with ((x0 ∥ x2) ∥ q). apply cgr_par. exact H1. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition x). reflexivity. decompose record H. exists x0. exists x1. exists (x2 ∥ p). split; try split.
  * apply cgr_trans with ((((x ! x0) ˖ x1) ∥ x2) ∥ p). apply cgr_trans with (q1 ∥ p). apply cgr_par_com. apply cgr_par. exact H0. apply cgr_par_assoc.
  * apply cgr_trans with ((x0 ∥ x2) ∥ p). apply cgr_trans with (q2 ∥ p). apply cgr_par_com. apply cgr_par. exact H1. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition x). reflexivity. decompose record H. exists x0. exists (gpr_choice x1 p2). exists θ. split ; try split.
  * apply cgr_trans with ((x ! x0) ˖ gpr_choice x1 p2). apply cgr_trans with ((gpr_choice (x ! x0) x1) ˖ p2).
    apply cgr_choice. assert (x2 = θ). apply H3. exists p1. reflexivity. rewrite H2 in H0. apply transitivity with (((x ! x0) ˖ x1) ∥ θ).
    exact H0. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x2 = θ). apply H3. exists p1. reflexivity. rewrite H2 in H1. exact H1.
  * reflexivity.
- destruct (IHTransition x). reflexivity. decompose record H. exists x0. exists (gpr_choice x1 p1). exists θ. split; try split.
  * apply cgr_trans with ((x ! x0) ˖ gpr_choice x1 p1). apply cgr_trans with ((gpr_choice (x ! x0) x1) ˖ p1).
    apply cgr_trans with (p2 ˖ p1). apply cgr_choice_com. apply cgr_choice. assert (x2 = θ). apply H3. exists p2. reflexivity.
    apply cgr_trans with (((x ! x0) ˖ x1) ∥ x2). exact H0. rewrite H2. apply cgr_par_nil. apply cgr_choice_assoc. apply cgr_par_nil_rev.
  * assert (x2 = θ). apply H3. exists p2. reflexivity. rewrite <-H2. exact H1.
  * reflexivity.
Qed.

(* For the (LTS-transition), the transitable Guards and transitted terms, that performs a Tau ,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForTauAndGuard : forall P V, ((lts P τ V) /\ (exists L, P = (g L))) -> 
(exists Q M, ((P ≡* ((gpr_tau Q) ˖ M))) /\ (V ≡* (Q))).
Proof.
intros P V Hyp. 
destruct Hyp. rename H into Transition. dependent induction Transition.
- exists t. exists gpr_nil. split. 
  * apply cgr_choice_nil_rev.
  * apply cgr_refl.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- destruct (IHTransition (reflexivity τ)). exists p1. reflexivity. destruct H. destruct H.  exists x. 
  exists (gpr_choice x0 p2). split. apply cgr_trans with ((gpr_choice (gpr_tau x) x0) ˖ p2). apply cgr_choice. exact H.
  apply cgr_choice_assoc. exact H1.
- destruct (IHTransition (reflexivity τ)). exists p2. reflexivity. destruct H. destruct H.  exists x. 
  exists (gpr_choice x0 p1). split. apply cgr_trans with ((gpr_choice (gpr_tau x) x0) ˖ p1). apply cgr_trans with (p2 ˖ p1). 
  apply cgr_choice_com. apply cgr_choice. exact H. apply cgr_choice_assoc. exact H1.
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
  - destruct g0.
    * reflexivity.
    * reflexivity.
    * intro. apply cgr_input. apply Hp. simpl. auto. exact H.
    * intro. apply cgr_output. apply Hp. simpl. auto. exact H.
    * intro. apply cgr_tau. apply Hp. simpl. auto. exact H.
    * intro. simpl. apply cgr_fullchoice. 
      assert (pr_subst x (g g0_1) q ≡* pr_subst x (g g0_1) q'). apply Hp. simpl. 
      rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ. exact H.
      exact H0.
      assert (pr_subst x (g g0_2) q ≡* pr_subst x (g g0_2) q'). apply Hp. simpl. 
      rewrite <-Nat.add_succ_l. apply PeanoNat.Nat.lt_add_pos_l. apply Nat.lt_0_succ. exact H.
      exact H0.
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
  - simpl. destruct (decide (n = x)). constructor. exact H. constructor. apply Hp. subst. simpl. auto.  exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H. 
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H. 
  - simpl. constructor. apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H.
  - simpl. apply cgr_choice_step. 
    assert (pr_subst n (g p1) q ≡ pr_subst n (g q1) q). apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H. exact H2.
Qed.

(* ≡* respects the substitution of his variable *)
Lemma cgr_subst2 q p p' x : p ≡* p' → pr_subst x p q ≡* pr_subst x p' q.
Proof. 
intros hcgr. induction hcgr. constructor. now eapply cgr_step_subst2. apply transitivity with (pr_subst x y q).
exact IHhcgr1. exact IHhcgr2.
Qed.

(* ≡ respects the substitution / recursion *)
Lemma cgr_subst p q x : p ≡ q -> pr_subst x p (pr_rec x p) ≡* pr_subst x q (pr_rec x q).
Proof.
  intro heq.
  etrans.
  eapply cgr_subst2. constructor. eassumption.
  eapply cgr_subst1. constructor. apply cgr_recursion_step. exact heq.
Qed.

(* p 'is equivalent some r 'and r performs α to q *)
Definition lts_sc1 p α q := exists r, p ≡* r /\ (lts r α q).

(* p performs α to some r and this is equivalent to q*)
Definition lts_sc p α q := exists r, ((lts p α r) /\ r ≡* q).

(* the structural congruence respects transition *)
Lemma Congruence_Respects_Transition : forall p q α, lts_sc1 p α q -> lts_sc p α q.
Proof.
(* by induction on the congruence and the step then...*)
  intros p q α (p' & hcgr & l).
  revert q α l.
  dependent induction hcgr.
  - dependent induction H. 
(* reasonning about all possible cases due to the structure of terms *)
    + intros. exists q.  split.  exact l. reflexivity. 
    + intros. exists (q ∥ θ). split. apply lts_parL. exact l. auto with cgr (*par contexte parallele*). 
    + intros. dependent destruction l. inversion l2. inversion l1. exists p2. split. exact l. auto with cgr. 
      inversion l.
    + intros. dependent destruction l.
      -- exists (q2 ∥ p2). split. eapply lts_comR. instantiate (1:= a). exact l1. exact l2. auto with cgr.
      -- exists (p2 ∥ q2). split. eapply lts_comL. instantiate (1:= a). exact l1. exact l2. auto with cgr.
      -- exists (p ∥ p2). split. apply lts_parR. exact l. auto with cgr.
      -- exists (q2 ∥ q). split. apply lts_parL. exact l. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l2. 
         * exists ((p2 ∥ p0) ∥ r). split.
           apply lts_parL. eapply lts_comL. instantiate (1:= a). exact l1. exact l2. auto with cgr.
         * exists ((p2 ∥ q) ∥ q2). split. eapply lts_comL. instantiate (1:= a). apply lts_parL. exact l1.
           exact l2. apply cgr_par_assoc.
      -- dependent destruction l1. 
         * exists ((q2 ∥ p2) ∥ r). split. apply lts_parL. eapply lts_comR. instantiate (1:= a). exact l1.
           exact l2. auto with cgr.
         * exists ((q2 ∥ q) ∥ q0). split. eapply lts_comR. instantiate (1:= a). exact l1. apply lts_parL.
           exact l2. auto with cgr.
      -- exists ((p2 ∥ q) ∥ r). split. apply lts_parL. apply lts_parL. exact l. auto with cgr.
      -- dependent destruction l.
         * exists ((p ∥ p2) ∥ q2). split. eapply lts_comL. instantiate (1:= a). apply lts_parR. exact l1.
           exact l2. auto with cgr.
         * exists ((p ∥ q2) ∥ p2). split. eapply lts_comR. instantiate (1:= a). exact l1. apply lts_parR.
           exact l2. auto with cgr.
         * exists ((p ∥ p2) ∥ r). split. apply lts_parL. apply lts_parR. exact l. auto with cgr.
         * exists ((p ∥ q) ∥ q2). split. apply lts_parR. exact l. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l1. 
         * exists (p2 ∥ (q ∥ q2)). split.
           eapply lts_comL. instantiate (1:= a). exact l1. apply lts_parR. exact l2. auto with cgr.
         * exists (p ∥ (q0 ∥ q2)). split. apply lts_parR. eapply lts_comL. instantiate (1:= a). exact l1.
           exact l2. auto with cgr.
      -- dependent destruction l2. 
         * exists (p0 ∥ (q ∥ p2)). split. eapply lts_comR. instantiate (1:= a). apply lts_parR.  exact l1.
           exact l2. auto with cgr.
         * exists (p ∥ (q2 ∥ p2)). split. apply lts_parR. eapply lts_comR. instantiate (1:= a). exact l1. 
           exact l2. auto with cgr.
      -- dependent destruction l.
         * exists (p2 ∥ (q2 ∥ r)). split. eapply lts_comL. instantiate (1:= a).  exact l1. apply lts_parL.
           exact l2. auto with cgr.
         * exists (q2 ∥ (p2 ∥ r)). split. eapply lts_comR. instantiate (1:= a). apply lts_parL. exact l1. 
           exact l2. auto with cgr.
         * exists (p2 ∥( q ∥ r)). split. apply lts_parL. exact l. auto with cgr.
         * exists (p ∥ (q2 ∥ r)). split. apply lts_parR. apply lts_parL. exact l. auto with cgr.
      -- exists (p ∥ (q ∥ q2)). split. apply lts_parR. apply lts_parR. exact l. auto with cgr.
    + intros. exists q.  split. apply lts_choiceL.  exact l. auto with cgr.
    + intros. dependent destruction l.
      -- exists q. split. exact l. auto with cgr.
      -- inversion l.
    + intros. dependent destruction l.
      -- exists q0. split. apply lts_choiceR. exact l. auto with cgr.
      -- exists q0. split. apply lts_choiceL. exact l. auto with cgr.
    + intros. dependent destruction l.
      -- exists q0. split. apply lts_choiceL. apply lts_choiceL. exact l. auto with cgr.
      -- dependent destruction l.
         * exists q0. split. apply lts_choiceL. apply lts_choiceR. exact l. auto with cgr.
         * exists q0. split. apply lts_choiceR. exact l. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l.
         * exists q0. split. apply lts_choiceL. exact l. auto with cgr.
         * exists q0. split. apply lts_choiceR. apply lts_choiceL. exact l. auto with cgr.
      -- exists q0. split. apply lts_choiceR. apply lts_choiceR. exact l. auto with cgr.
    + intros. dependent destruction l. exists (pr_subst x p (pr_rec x p)). split. apply lts_rec.
      apply cgr_subst. exact H.
    + intros. dependent destruction l. exists p.  split. apply lts_tau. constructor. exact H.
    + intros. dependent destruction l. exists p. split. apply lts_input. constructor. apply H.
    + intros. dependent destruction l. exists p. split. apply lts_output. constructor. apply H.
    + intros. dependent destruction l. 
      -- destruct (IHcgr_step p2 (ActExt (ActOut a))). exact l1. exists (x ∥ q2). split. eapply lts_comL. destruct H0. exact l.
         exact l2. destruct H0. auto with cgr.
      -- destruct (IHcgr_step q2 (ActExt (ActIn a))). exact l2. exists (x ∥ p2). split. eapply lts_comR. destruct H0. exact l1.
         destruct H0.  exact H0. destruct H0. auto with cgr.
      -- destruct (IHcgr_step p2 α). exact l. destruct H0. exists (x ∥ r). split. apply lts_parL. exact H0. auto with cgr.
      -- exists (p ∥ q2). split. apply lts_parR. exact l. apply cgr_par. constructor. exact H.
    + intros. dependent destruction l.
      -- destruct (IHcgr_step q α). exact l. destruct H0. exists x. split. apply lts_choiceL. exact H0. exact H1.
      -- exists q. split. apply lts_choiceR. exact l. auto with cgr.
  - intros. destruct (IHhcgr2 q α). exact l. destruct (IHhcgr1 x0 α). destruct H. exact H. exists x1. split. destruct H0. exact H0.
    destruct H. destruct H0. eauto with cgr.
Qed.

(* One side of the Harmony Lemma *)
Lemma Reduction_Implies_TausAndCong : forall P Q, (sts P Q) -> (lts_sc P τ Q).
Proof.
intros P Q Reduction. 
assert (((exists x P1 P2 M1 M2 S, ((P ≡* (((x!P1) ˖ M1) ∥ ((x ? P2) ˖ M2)) ∥ S)) /\ (Q ≡* ((P1 ∥ P2) ∥ S)))
\/ (exists P1 M1 S, (P ≡* (((gpr_tau P1) ˖ M1) ∥ S)) /\ (Q ≡* (P1 ∥ S)))
\/ (exists n P1 S, (P ≡* ((pr_rec n P1) ∥ S)) /\ (Q ≡* (pr_subst n P1 (pr_rec n P1) ∥ S))))). apply ReductionShape. exact Reduction. destruct H.

(*First case τ by communication *)

- decompose record H. assert (lts ((((x ! x0) ˖ x2) ∥ ((x ? x1) ˖ x3)) ∥ x4) τ ((x0 ∥ x1) ∥ x4)).
  * apply lts_parL. eapply lts_comL. apply lts_choiceL. instantiate (1:= x). apply lts_output. apply lts_choiceL. apply lts_input.
  * assert (lts_sc1 P τ ((x0 ∥ x1) ∥ x4)). exists ((((x ! x0) ˖ x2) ∥ ((x ? x1) ˖ x3)) ∥ x4). split. exact H0. exact H1.
    assert (lts_sc P τ ((x0 ∥ x1) ∥ x4)). apply Congruence_Respects_Transition. exact H3. destruct H4. destruct H4. 
    exists x5. split. exact H4. apply transitivity with ((x0 ∥ x1) ∥ x4). exact H5. symmetry. exact H2.

- destruct H. 

(*Second case τ by Tau Action *)

  * decompose record H. assert (lts ((gpr_tau x ˖ x0) ∥ x1) τ (x ∥ x1)). constructor. apply lts_choiceL. apply lts_tau.  
    assert (lts_sc1 P τ (x ∥ x1)). exists ((gpr_tau x ˖ x0) ∥ x1). split. exact H1. exact H0.
    assert (lts_sc P τ (x ∥ x1)). apply Congruence_Respects_Transition. exact H3. destruct H4. destruct H4. 
    exists x2. split. exact H4. apply transitivity with (x ∥ x1). exact H5. symmetry. exact H2.

(*Third case τ by rec *)
  * decompose record H. assert (lts (pr_rec x x0 ∥ x1) τ (pr_subst x x0 (pr_rec x x0) ∥ x1)). constructor. apply lts_rec.  
    assert (lts_sc1 P τ ((pr_subst x x0 (pr_rec x x0) ∥ x1))). exists (pr_rec x x0 ∥ x1). split. exact H1. exact H0.
    assert (lts_sc P τ (pr_subst x x0 (pr_rec x x0) ∥ x1)). apply Congruence_Respects_Transition. exact H3. destruct H4. destruct H4. 
    exists x2. split. exact H4. apply transitivity with (pr_subst x x0 (pr_rec x x0) ∥ x1). exact H5. symmetry. exact H2.
Qed.


(* The More Stronger Harmony Lemma (in one side) is more stronger *)
Lemma Congruence_Simplicity : (forall α , ((forall P Q, (((lts P α Q) -> (sts P Q)))) -> (forall P Q, ((lts_sc P α Q) -> (sts P Q))))).
Proof.
intros. destruct H0. destruct H0. eapply sts_cong. instantiate (1:=P). apply cgr_refl. instantiate (1:=x). apply H. exact H0. 
exact H1.
Qed.

(* Some lemmas for multiple parallele processes to simplify the statements of proof*)
Lemma InversionParallele : forall P Q R S, (P ∥ Q) ∥ (R ∥ S) ≡* (P ∥ R) ∥ (Q ∥ S) .
Proof.
intros.
apply transitivity with (((P ∥ Q) ∥ R) ∥ S). apply cgr_par_assoc_rev.
apply transitivity with ((P ∥ (Q ∥ R)) ∥ S). apply cgr_par. apply cgr_par_assoc.
apply transitivity with (((Q ∥ R) ∥ P) ∥ S). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ∥ R) ∥ (P ∥ S)). apply cgr_par_assoc.
apply transitivity with ((R ∥ Q) ∥ (P ∥ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with (((R ∥ Q) ∥ P) ∥ S). apply cgr_par_assoc_rev.
apply transitivity with ((P ∥ (R ∥ Q)) ∥ S). apply cgr_par. apply cgr_par_com.
apply transitivity with (((P ∥ R) ∥ Q) ∥ S). apply cgr_par. apply cgr_par_assoc_rev.
apply transitivity with ((P ∥ R) ∥ (Q ∥ S)). apply cgr_par_assoc.
reflexivity.
Qed.
Lemma InversionParallele2 : forall P Q R S, (P ∥ Q) ∥ (R ∥ S) ≡* (R ∥ P) ∥ (S ∥ Q).
Proof.
intros. 
apply transitivity with ((P ∥ R) ∥ (Q ∥ S)). apply InversionParallele.
apply transitivity with ((R ∥ P) ∥ (Q ∥ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ∥ S) ∥ (R ∥ P)). apply cgr_par_com.
apply transitivity with ((S ∥ Q) ∥ (R ∥ P)). apply cgr_par. apply cgr_par_com.
apply cgr_par_com.
Qed.
Lemma InversionParallele3 : forall P Q R S, (P ∥ Q) ∥ (R ∥ S) ≡* (R ∥ Q) ∥ (P ∥ S).
Proof.
intros.
apply transitivity with ((Q ∥ P) ∥ (R ∥ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ∥ R) ∥ (P ∥ S)). apply InversionParallele. apply cgr_par. apply cgr_par_com.
Qed.


Lemma Taus_Implies_Reduction : forall P Q, (lts P τ Q) -> (sts P Q).
Proof.
intros.
dependent induction H.
  - eapply sts_cong.  instantiate (1:=  ((gpr_tau t) ˖ gpr_nil)). apply cgr_choice_nil_rev. instantiate (1:=t).
    apply sts_tau. apply cgr_refl.
  - apply sts_rec.
  - destruct (TransitionShapeForOutput p1 p2 a). exact H. destruct H1. destruct H1. destruct H1. destruct H2.
    destruct (TransitionShapeForInput q1 q2 a). exact H0. destruct H4. destruct H4. destruct H4. destruct H5.
    eapply sts_cong. instantiate (1:=(((a ! x) ˖ x0) ∥ ((a ? x2) ˖ x3)) ∥ (x1 ∥ x4)).
    apply cgr_trans with ((((a ! x) ˖ x0) ∥ x1) ∥ (((a ? x2) ˖ x3) ∥ x4)). apply cgr_fullpar. exact H1. exact H4.
    apply InversionParallele. 
    instantiate (1 := (x ∥ x2) ∥ (x1 ∥ x4)). apply sts_par. apply sts_com.
    apply transitivity with ((x ∥ x1) ∥ (x2 ∥ x4)). apply InversionParallele. apply cgr_fullpar. 
    symmetry. exact H2. symmetry. exact H5.
  - destruct (TransitionShapeForOutput p1 p2 a). exact H. destruct H1. destruct H1. destruct H1. destruct H2.
    destruct (TransitionShapeForInput q1 q2 a). exact H0. destruct H4. destruct H4. destruct H4. destruct H5.
    eapply sts_cong. instantiate (1:=(((a ! x) ˖ x0) ∥ ((a ? x2) ˖ x3)) ∥ (x1 ∥ x4)).
    apply transitivity with (p1 ∥ q1). apply cgr_par_com.
    apply transitivity with ((((a ! x) ˖ x0) ∥ x1) ∥ (((a ? x2) ˖ x3) ∥ x4)).
    apply cgr_fullpar. exact H1. exact H4. apply InversionParallele. 
    instantiate (1 := (x ∥ x2) ∥ (x1 ∥ x4)). apply sts_par. apply sts_com.
    apply transitivity with ((x ∥ x1) ∥ (x2 ∥ x4)). apply InversionParallele. apply transitivity with (p2 ∥ q2). apply cgr_fullpar. 
    symmetry. exact H2. symmetry. exact H5. apply cgr_par_com.
- apply sts_par. apply IHlts. reflexivity.
- eapply sts_cong. instantiate (1:= q1 ∥ p). apply cgr_par_com. instantiate (1:= q2 ∥ p).
  apply sts_par. apply IHlts. reflexivity. apply cgr_par_com.
- destruct (TransitionShapeForTauAndGuard (g p1) q). split. exact H. exists p1. reflexivity.
  destruct H0. destruct H0. eapply sts_cong. instantiate (1:= (((gpr_tau x) ˖ (gpr_choice x0  p2)))).
  apply transitivity with ((gpr_choice (gpr_tau x) x0 ) ˖ p2). apply cgr_choice. exact H0. apply cgr_choice_assoc.
  instantiate (1:= x). apply sts_tau. symmetry. exact H1.
- destruct (TransitionShapeForTauAndGuard (g p2) q). split. exact H. exists p2. reflexivity.
  destruct H0. destruct H0. eapply sts_cong. instantiate (1:= (((gpr_tau x) ˖ (gpr_choice x0  p1)))).
  apply transitivity with ((gpr_choice (gpr_tau x) x0 ) ˖ p1). apply transitivity with (p2 ˖ p1). apply cgr_choice_com.
  apply cgr_choice. exact H0. apply cgr_choice_assoc. instantiate (1:= x). apply sts_tau. symmetry. exact H1.
Qed.

(* One side of the Harmony Lemma*)
Lemma TausAndCong_Implies_Reduction: forall P Q, (lts_sc P τ Q) -> (sts P Q).
Proof.
intros P Q H.
apply Congruence_Simplicity with τ. exact Taus_Implies_Reduction. exact H.
Qed.

Theorem HarmonyLemmaForCCS : forall P Q, (lts_sc P τ Q) <-> (sts P Q).
Proof.
intros. split.
* apply TausAndCong_Implies_Reduction.
* apply Reduction_Implies_TausAndCong.
Qed.





