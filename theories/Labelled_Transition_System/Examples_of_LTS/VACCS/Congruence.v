From stdpp Require Import base countable.
From TestingTheory Require Import VACCS.
From Stdlib Require Import Relations Program.Equality Wellfounded.Inverse_Image.

Module Type VACCS_congruence.

Include VACCS_proc.

Reserved Notation "p ≡ q" (at level 70).
(*Naïve definition of a relation ≡ that will become a congruence ≡* by transitivity*)
Inductive cgr_step : proc -> proc -> Prop :=
(*  Reflexivity of the Relation ≡  *)
| cgr_refl_step : forall p, p ≡ p

(* Rules for pattern matching *)
| cgr_if_true_step : forall p q E, Eval_Eq E = Some true -> (If E Then p Else q) ≡ p
| cgr_if_true_rev_step  : forall p q E, Eval_Eq E = Some true -> p ≡ If E Then p Else q
| cgr_if_false_step  : forall p q E, Eval_Eq E = Some false -> (If E Then p Else q) ≡ q
| cgr_if_false_rev_step  : forall p q E, Eval_Eq E = Some false -> q ≡ If E Then p Else q

(* Rules for the Parallel *)
| cgr_par_nil_step : forall p, 
    p ‖ 𝟘 ≡ p
| cgr_par_nil_rev_step : forall p,
    p ≡ p ‖ 𝟘
| cgr_par_com_step : forall p q,
    p ‖ q ≡ q ‖ p
| cgr_par_assoc_step : forall p q r,
    (p ‖ q) ‖ r ≡ p ‖ (q ‖ r)
| cgr_par_assoc_rev_step : forall p q r,
    p ‖ (q  ‖ r) ≡ (p ‖ q) ‖ r

(* Rules for the Restriction *)
| cgr_res_nil_step :
   ν (g 𝟘) ≡ (g 𝟘)
| cgr_res_nil_rev_step :
   (g 𝟘) ≡ ν (g 𝟘)
| cgr_res_swap_step : forall p,
    ν (ν p) ≡ ν (ν (VarSwap_in_proc 0 p))
| cgr_res_swap_rev_step : forall p,
    ν (ν (VarSwap_in_proc 0 p)) ≡ ν (ν p)
| cgr_res_scope_step : forall p q,
    ν (p ‖ (NewVarC 0 q)) ≡ (ν p) ‖ q
| cgr_res_scope_rev_step : forall p q,
    (ν p) ‖ q ≡ ν (p ‖ (NewVarC 0 q)) 

(* Rules for the Summation *)
| cgr_choice_nil_step : forall p,
    cgr_step (p + 𝟘) p
| cgr_choice_nil_rev_step : forall p,
    cgr_step (g p) (p + 𝟘)
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
    cgr_step (𝛕 • p) (𝛕 • q)
| cgr_input_step : forall c p q,
    cgr_step p q ->
    cgr_step (c ? p) (c ? q)
| cgr_par_step : forall p q r,
    cgr_step p q ->
    p ‖ r ≡ q ‖ r
| cgr_res_step : forall p q,
    cgr_step p q ->
    ν p ≡ ν q
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
where "p ≡ q" := (cgr_step p q).

Hint Constructors cgr_step:cgr_step_structure.

Infix "≡" := cgr_step (at level 70).

(* The relation ≡ is an reflexive *)
#[global] Instance cgr_refl_step_is_refl : Reflexive cgr_step.
Proof. intro. apply cgr_refl_step. Qed.
(* The relation ≡ is symmetric *)
#[global] Instance cgr_symm_step : Symmetric cgr_step.
Proof. intros p q hcgr. induction hcgr; econstructor ; eauto.
Qed.

(* Defining the transitive closure of ≡ *)
Infix "≡" := cgr_step (at level 70).
(* Defining the transitive closure of ≡ *)
Definition cgr := (clos_trans proc cgr_step).

Infix "≡*" := cgr (at level 70).


(* The relation ≡* is reflexive *)
#[global] Instance cgr_refl : Reflexive cgr.
Proof. intros. constructor. apply cgr_refl_step. Qed.
(* The relation ≡* is symmetric *)
#[global] Instance cgr_symm : Symmetric cgr.
Proof. intros p q hcgr. induction hcgr. constructor. apply cgr_symm_step. exact H. eapply t_trans; eauto. Qed.
(* The relation ≡* is transitive *)
#[global] Instance cgr_trans : Transitive cgr.
Proof. intros p q r hcgr1 hcgr2. eapply t_trans; eauto. Qed.

Hint Resolve cgr_refl cgr_symm cgr_trans:cgr_eq.

(* The relation ≡* is an equivence relation *)
#[global] Instance cgr_is_eq_rel  : Equivalence cgr.
Proof. repeat split.
       + apply cgr_refl.
       + apply cgr_symm.
       + apply cgr_trans.
Qed.

(* the relation ≡* respects all the rules that ≡ respected *)
Lemma cgr_if_true : forall p q E, Eval_Eq E = Some true -> (If E Then p Else q) ≡* p.
Proof. constructor. apply cgr_if_true_step; eauto. Qed.

Lemma cgr_if_true_rev : forall p q E, Eval_Eq E = Some true -> p ≡* (If E Then p Else q).
Proof. constructor. apply cgr_if_true_rev_step; eauto. Qed.

Lemma cgr_if_false : forall p q E, Eval_Eq E = Some false -> (If E Then p Else q) ≡* q.
Proof. constructor. apply cgr_if_false_step; eauto. Qed.

Lemma cgr_if_false_rev : forall p q E, Eval_Eq E = Some false -> q ≡* (If E Then p Else q).
Proof. constructor. apply cgr_if_false_rev_step; eauto. Qed.

Lemma cgr_par_nil : forall p, p ‖ 𝟘 ≡* p.
Proof. constructor. apply cgr_par_nil_step. Qed.

Lemma cgr_par_nil_rev : forall p, p ≡* p ‖ 𝟘.
Proof. constructor. apply cgr_par_nil_rev_step. Qed.

Lemma cgr_par_com : forall p q, p ‖ q ≡* q ‖ p.
Proof. constructor. apply cgr_par_com_step. Qed.

Lemma cgr_par_assoc : forall p q r, (p ‖ q) ‖ r ≡* p ‖ (q ‖r).
Proof. constructor. apply cgr_par_assoc_step. Qed.

Lemma cgr_par_assoc_rev : forall p q r, p ‖(q ‖ r) ≡* (p ‖ q) ‖ r.
Proof. constructor. apply cgr_par_assoc_rev_step. Qed.

Lemma cgr_res_nil : ν (g 𝟘) ≡* (g 𝟘).
Proof. constructor. apply cgr_res_nil_step. Qed.

Lemma cgr_res_nil_rev : (g 𝟘) ≡* ν (g 𝟘).
Proof. constructor. apply cgr_res_nil_rev_step. Qed.

Lemma cgr_res_swap : forall p, ν (ν p) ≡* ν (ν (VarSwap_in_proc 0 p)).
Proof. constructor. apply cgr_res_swap_step. Qed.

Lemma cgr_res_swap_rev : forall p, ν (ν (VarSwap_in_proc 0 p)) ≡* ν (ν p).
Proof. constructor. apply cgr_res_swap_rev_step. Qed.

Lemma cgr_res_scope : forall p q, ν (p ‖ (NewVarC 0 q)) ≡* (ν p) ‖ q.
Proof. constructor. apply cgr_res_scope_step. Qed.

Lemma cgr_res_scope_rev : forall p q, (ν p) ‖ q ≡* ν (p ‖ (NewVarC 0 q)).
Proof. constructor. apply cgr_res_scope_rev_step. Qed.

Lemma cgr_choice_nil : forall p, p + 𝟘 ≡* p.
Proof. constructor. apply cgr_choice_nil_step. Qed.

Lemma cgr_choice_nil_rev : forall p, (g p) ≡* p + 𝟘.
Proof. constructor. apply cgr_choice_nil_rev_step. Qed.

Lemma cgr_choice_com : forall p q, p + q ≡* q + p.
Proof. constructor. apply cgr_choice_com_step. Qed.

Lemma cgr_choice_assoc : forall p q r, (p + q) + r ≡* p + (q + r).
Proof. constructor. apply cgr_choice_assoc_step. Qed.

Lemma cgr_choice_assoc_rev : forall p q r, p + (q + r) ≡* (p + q) + r.
Proof. constructor. apply cgr_choice_assoc_rev_step. Qed.

Lemma cgr_recursion : forall x p q, p ≡* q -> (rec x • p) ≡* (rec x • q).
Proof.
intros ? ? ? H. dependent induction H. constructor.
apply cgr_recursion_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_tau : forall p q, p ≡* q -> (𝛕 • p) ≡* (𝛕 • q).
Proof.
intros ? ? H. dependent induction H. constructor.
apply cgr_tau_step. exact H. eauto with cgr_eq.
Qed. 
Lemma cgr_input : forall c p q, p ≡* q -> (c ? p) ≡* (c ? q).
Proof.
intros ? ? ? H. dependent induction H. 
- constructor. apply cgr_input_step. auto.
- eauto with cgr_eq.
Qed.
Lemma cgr_par : forall p q r, p ≡* q-> p ‖ r ≡* q ‖ r.
Proof.
intros ? ? ? H. dependent induction H. 
constructor. apply cgr_par_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_res : forall p q, p ≡* q-> ν p ≡* ν q.
Proof.
intros. dependent induction H. 
constructor.
apply cgr_res_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_if_left : forall C p q q', q ≡* q' ->
  (If C Then p Else q) ≡* (If C Then p Else q').
Proof.
intros ? ? ? ? H. dependent induction H. 
constructor. apply cgr_if_left_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_if_right : forall C p p' q, p ≡* p' ->
  (If C Then p Else q) ≡* (If C Then p' Else q).
Proof.
intros ? ? ? ? H. dependent induction H. 
constructor. apply cgr_if_right_step. exact H. eauto with cgr_eq.
Qed.

Global Instance cgr_refl_step_is_refl' : Reflexive cgr_step.
Proof. apply cgr_refl_step_is_refl. Qed.

Section AlternativeCongruence.

(* Alternative definition of congruence step, better suited to prove that it's
  a congruence *)
Reserved Notation "p ≡ₐ q" (at level 70).
Reserved Notation "p ≡g q" (at level 70).
Inductive altcgr : proc -> proc -> Prop :=
| altcgr_refl_step : forall p, p ≡ₐ p
| altcgr_if_true_step : forall p q E, Eval_Eq E = Some true -> (If E Then p Else q) ≡ₐ p
| altcgr_if_true_rev_step  : forall p q E, Eval_Eq E = Some true -> p ≡ₐ If E Then p Else q
| altcgr_if_false_step  : forall p q E, Eval_Eq E = Some false -> (If E Then p Else q) ≡ₐ q
| altcgr_if_false_rev_step  : forall p q E, Eval_Eq E = Some false -> q ≡ₐ If E Then p Else q
| altcgr_par_nil_step : forall p, 
    p ‖ 𝟘 ≡ₐ p
| altcgr_par_nil_rev_step : forall p,
    p ≡ₐ p ‖ 𝟘
| altcgr_par_com_step : forall p q,
    p ‖ q ≡ₐ q ‖ p
| altcgr_par_assoc_step : forall p q r,
    (p ‖ q) ‖ r ≡ₐ p ‖ (q ‖ r)
| altcgr_par_assoc_rev_step : forall p q r,
    p ‖ (q  ‖ r) ≡ₐ (p ‖ q) ‖ r
| altcgr_res_nil_step :
   ν (g 𝟘) ≡ₐ (g 𝟘)
| altcgr_res_nil_rev_step :
   (g 𝟘) ≡ₐ ν (g 𝟘)
| altcgr_res_swap_step : forall p,
    ν (ν p) ≡ₐ ν (ν (VarSwap_in_proc 0 p))
| altcgr_res_swap_rev_step : forall p,
    ν (ν (VarSwap_in_proc 0 p)) ≡ₐ ν (ν p)
| altcgr_res_scope_step : forall p q,
    ν (p ‖ (NewVarC 0 q)) ≡ₐ (ν p) ‖ q
| altcgr_res_scope_rev_step : forall p q,
    (ν p) ‖ q ≡ₐ ν (p ‖ (NewVarC 0 q))
| altcgr_recursion_step : forall x p q,
    p ≡ₐ q -> (rec x • p) ≡ₐ (rec x • q)
| altcgr_par_step : forall p q r,
    p ≡ₐ q -> p ‖ r ≡ₐ q ‖ r
| altcgr_res_step : forall p q,
    p ≡ₐ q -> ν p ≡ₐ ν q
| altcgr_if_left_step : forall C p q q',
    q ≡ₐ q' -> (If C Then p Else q) ≡ₐ (If C Then p Else q')
| altcgr_if_right_step : forall C p p' q,
    p ≡ₐ p' -> (If C Then p Else q) ≡ₐ (If C Then p' Else q)
| altcgr_guard : forall (g1 g2 : gproc), g1 ≡g g2 -> g g1 ≡ₐ g g2
| altcgr_trans : forall (p q r : proc) , p ≡ₐ q -> q ≡ₐ r -> p ≡ₐ r

with altcgr_gstep : gproc -> gproc -> Prop :=
| altcgr_tau_step : forall p q,
    p ≡ₐ q -> (𝛕 • p) ≡g (𝛕 • q)
| altcgr_input_step : forall c p q,
    p ≡ₐ q -> (c ? p) ≡g (c ? q)
| altcgr_choice_nil_step : forall p,
    (p + 𝟘) ≡g p
| altcgr_choice_nil_rev_step : forall p,
    p ≡g (p + 𝟘)
| altcgr_choice_com_step : forall p q,
    (p + q) ≡g (q + p)
| altcgr_choice_assoc_step : forall p q r,
    ((p + q) + r) ≡g (p + (q + r))
| altcgr_choice_assoc_rev_step : forall p q r,
    (p + (q + r)) ≡g ((p + q) + r)
| altcgr_choice_step : forall p1 q1 p2,
    p1 ≡g q1 -> (p1 + p2) ≡g (q1 + p2)
| galtcgr_trans : forall (p q r : gproc), p ≡g q -> q ≡g r -> p ≡g r
| galtcgr_refl_step : forall p, p ≡g p
| galtcgr_sym_step : forall p q, q ≡g p -> p ≡g q
where "p ≡ₐ q" := (altcgr p q)
and "p ≡g q" := (altcgr_gstep p q).

#[local] Hint Constructors altcgr:alt_step_structure.

(* Transitive closure of congruence on guards only *)
Definition guardcgr  :=
  clos_trans proc (fun p1 p2 => exists g1 g2, p1 = g g1 /\ p2 = g g2 /\ p1 ≡ p2).

(* Stronger statement : congruences under tau preserve guards *)
Lemma guardcgr_tau : forall p q, p ≡* q -> guardcgr (𝛕 • p) (𝛕 • q).
Proof.
intros. induction H.
constructor.
- eexists; eexists; repeat split. apply cgr_tau_step. exact H.
- econstructor 2; eauto with cgr_eq.
Qed.

Lemma guardcgr_input : forall c p q, p ≡* q -> guardcgr (c ? p) (c ? q).
Proof.
intros. induction H.
- constructor. eexists; eexists; repeat split. now apply cgr_input_step.
- econstructor 2; eauto with cgr_eq.
Qed.

#[local] Instance guard_cgr_refl : Symmetric guardcgr.
Proof.
  intros x y H. induction H.
  - constructor. decompose record H. eauto with *.
  - econstructor 2; eauto with *.
Qed.

#[global] Instance altcgr_refl_step_is_refl : Reflexive altcgr.
Proof. intro. apply altcgr_refl_step. Qed.

#[global] Instance altcgr_grefl_step_is_refl : Reflexive altcgr_gstep.
Proof. intro. constructor. Qed.

#[local] Instance altcgr_symm_step : Symmetric altcgr.
Proof. intros p q hcgr. induction hcgr; try solve [constructor; try exact IHhcgr];
try solve[now (do 3 (try constructor))].
- constructor. now constructor.
- econstructor; eauto.
Qed.

(* Equivalence between the two definitions of congruence *)

Scheme proc_ind2 := Induction for proc Sort Prop
  with gproc_ind2 := Induction for gproc Sort Prop.

Lemma cgr_step_altcgr p q: cgr_step p q -> altcgr p q.
Proof.
revert q.
induction p using proc_ind2 with (P0 :=
  (fun gp => forall gq, cgr_step (g gp) (g gq) -> altcgr_gstep gp gq));
intros q Hq;
try (solve[inversion Hq; subst; eauto with *; do 2 try constructor; eauto]).
inversion Hq; subst; eauto with *;
try (solve[inversion Hq; subst; eauto with *; do 2 try constructor; eauto]).
constructor. now apply IHp.
Qed.

Lemma cgr_altcgr p q: cgr p q -> altcgr p q.
Proof. intro H. induction H; eauto using cgr_step_altcgr with *. Qed.

Scheme altcgr_ind2 := Induction for altcgr Sort Prop
  with galtcgr_ind2 := Induction for altcgr_gstep Sort Prop.

Combined Scheme altcgr_mutind from altcgr_ind2,galtcgr_ind2.

Lemma guardcgr_choice_step p1 q1 p2: guardcgr (g p1) (g q1) ->
  guardcgr (g (p1 + p2)) (g (q1 + p2)).
Proof.
  intros H%clos_trans_tn1. apply clos_tn1_trans. dependent induction H.
  - constructor. decompose record H; subst.
    eexists; eexists; repeat split. now constructor.
  - decompose record H; subst; clear H. inversion H2; subst.
    econstructor 2; eauto.
    eexists; eexists; repeat split. now constructor.
Qed.

Lemma guardcgr_cgr p q : guardcgr p q -> cgr p q.
Proof. intro H. induction H; eauto with *; decompose record H; now constructor. Qed.

(* The following goes through because we strengthen the conclusion on guards *)
Lemma altcgr_cgr :
  (forall p q, altcgr p q -> p ≡* q) /\
  (forall gp gq, altcgr_gstep gp gq -> guardcgr gp gq).
Proof.
apply altcgr_mutind; try solve [repeat constructor; eauto with *]; intros.
- now apply cgr_recursion.
- now apply cgr_par.
- now apply cgr_res.
- now apply cgr_if_left.
- now apply cgr_if_right.
- now apply guardcgr_cgr.
- eauto with *.
- now apply guardcgr_tau.
- now apply guardcgr_input.
- now apply guardcgr_choice_step.
- intros. now apply t_trans with (g q).
- now symmetry.
Qed.
Notation "⇑ g" := (gNewVarC 0 g) (at level 40).

(* Being syntactically equivalent to a guard, hidden under parallels and unnecessary restrictions *)
Fixpoint sguard (g0 : gproc) (p : proc) := match p with
| (p ‖ q) => (sguard 𝟘 p /\ sguard g0 q) \/ (sguard 𝟘 q /\ sguard g0 p)
| (ν p) => sguard (⇑ g0) p
| g p => p ≡g g0
| If E Then p Else q => (Eval_Eq E = Some true /\ sguard g0 p) \/
                        (Eval_Eq E = Some false /\ sguard g0 q)
| _ => False
end.

(* congruence is preserved by renamings *)
Lemma gNewVarC_altcgr g g' : g ≡g g' -> gNewVarC 0 g ≡g gNewVarC 0 g'.
Proof.

Admitted.

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


Lemma sguard_cgr_proper p g g': sguard g p -> g ≡g g' -> sguard g' p.
Proof.
revert g g'. induction p; simpl; intuition.
- left. intuition. eauto with *.
- right. intuition. eauto with *.
- left. eauto with *.
- right. eauto with *.
- eapply IHp; [eassumption|]. now apply gNewVarC_altcgr.
- apply galtcgr_trans with g1; trivial.
Qed.

Lemma sguardNewVar g0 q:  sguard g0 q <-> sguard (⇑ g0) (NewVarC 0 q).
Proof.
Admitted.

Lemma NewVar_altcgr_gstep g g': g ≡g g' <-> (⇑ g) ≡g (⇑ g').
Proof.
Admitted.
(* similar to NewVar_Respects_Congruence *)

Lemma sguard_VarSwap_in_proc g p:
  sguard g p <-> sguard (gVarSwap_in_proc 0 g) (VarSwap_in_proc 0 p).
Proof.
Admitted.

Lemma gVarSwap_NewVar_NewVar g0 :
  gVarSwap_in_proc 0 (⇑ (⇑ g0)) = ⇑ (⇑ g0).
Proof.
Admitted.

Lemma altcgr_guard_proper (p0 p1 : proc) (g0 : gproc) : (p0 ≡ₐ p1) -> sguard g0 p0
  -> sguard g0 p1.
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
Lemma altcgr_guard_rev g1 g2: g g1 ≡ₐ g g2 -> g1 ≡g g2.
Proof.
intro Ha. inversion Ha; subst; [constructor|auto|].
apply (altcgr_guard_proper q (g g1) g2); [now symmetry|].
apply (altcgr_guard_proper (g g2) q g2); [now symmetry|].
constructor.
Qed.

End AlternativeCongruence.

Lemma cgr_choice : forall p q r, g p ≡* g q -> p + r ≡* q + r.
Proof.
intros p q r H%cgr_altcgr%altcgr_guard_rev.
apply altcgr_cgr. now do 2 constructor.
Qed.

(* The if of processes respects ≡* *)
Lemma cgr_full_if : forall C p p' q q', p ≡* p' -> q ≡* q' -> (If C Then p Else q) ≡* (If C Then p' Else q').
Proof.
intros.
 transitivity (If C Then p Else q'). apply cgr_if_left. exact H0. 
apply cgr_if_right. exact H. 
Qed.

(* The sum of guards respects ≡* *)
Lemma cgr_fullchoice M1 M2 M3 M4 : g M1 ≡* g M2 -> g M3 ≡* g M4 -> M1 + M3 ≡* M2 + M4.
Proof.
intros.
 transitivity (g (M2 + M3)). apply cgr_choice. exact H.  transitivity (g (M3 + M2)).
apply cgr_choice_com.  transitivity (g (M4 + M2)). apply cgr_choice. exact H0. apply cgr_choice_com.
Qed.

(* The parallele of process respects ≡* *)
Lemma cgr_fullpar M1 M2 M3 M4 : M1 ≡* M2 -> M3 ≡* M4 -> M1 ‖ M3 ≡* M2 ‖ M4.
Proof.
intros.
 transitivity (M2 ‖ M3). apply cgr_par. exact H.  transitivity (M3 ‖ M2).
apply cgr_par_com.  transitivity (M4 ‖ M2). apply cgr_par. exact H0. apply cgr_par_com.
Qed.


#[global] Hint Resolve cgr_if_true cgr_if_true_rev cgr_if_false cgr_if_false_rev
cgr_par_nil cgr_par_nil_rev cgr_par_com cgr_par_assoc cgr_par_assoc_rev 
cgr_choice_nil cgr_choice_nil_rev cgr_choice_com cgr_choice_assoc cgr_choice_assoc_rev
cgr_recursion cgr_tau cgr_input cgr_if_left cgr_if_right cgr_par cgr_choice
cgr_full_if cgr_fullchoice cgr_fullpar cgr_res_nil cgr_res_nil_rev cgr_res_swap cgr_res_swap_rev cgr_res
cgr_res_scope cgr_res_scope_rev cgr_refl cgr_symm cgr_trans:cgr.

(* TODO: as instances of Proper? *)

Lemma Congruence_Respects_Substitution : forall p q v k, p ≡* q -> (subst_in_proc k v p) ≡* (subst_in_proc k v q).
Proof.
intros. revert k. revert v. dependent induction H. 
* dependent induction H; simpl; eauto with cgr.
  - intros. eapply cgr_if_true; eapply subst_equation in H; eauto.
  - intros. eapply cgr_if_true_rev; eapply subst_equation in H; eauto.
  - intros. eapply cgr_if_false; eapply subst_equation in H; eauto.
  - intros. eapply cgr_if_false_rev; eapply subst_equation in H; eauto.
  - intros. rewrite subst_and_VarSwap. eapply cgr_res_swap.
  - intros. rewrite subst_and_VarSwap. eapply cgr_res_swap_rev.
  - intros. rewrite subst_and_NewVarC. eapply cgr_res_scope.
  - intros. rewrite subst_and_NewVarC. eapply cgr_res_scope_rev.
* eauto with cgr.
Qed.

Lemma NewVar_Respects_Congruence : forall p p' j, p ≡* p' -> NewVar j p ≡* NewVar j p'.
Proof.
intros.  revert j.  dependent induction H.
- dependent induction H ; simpl ; auto with cgr.
* intros. eapply cgr_if_true; eapply NewVar_equation in H; eauto.
* intros. eapply cgr_if_true_rev; eapply NewVar_equation in H; eauto.
* intros. eapply cgr_if_false; eapply NewVar_equation in H; eauto.
* intros. eapply cgr_if_false_rev; eapply NewVar_equation in H; eauto.
* intros. rewrite NewVar_and_VarSwap. eapply cgr_res_swap.
* intros. rewrite NewVar_and_VarSwap. eapply cgr_res_swap_rev.
* intros. rewrite NewVar_and_NewVarC. eapply cgr_res_scope.
* intros. rewrite NewVar_and_NewVarC. eapply cgr_res_scope_rev.
* intros. apply cgr_choice. apply IHcgr_step.
- eauto with cgr.
Qed.

Lemma NewVarC_Respects_Congruence : forall p p' j, p ≡* p' -> NewVarC j p ≡* NewVarC j p'.
Proof.
intros.  revert j.  dependent induction H.
  - dependent induction H ; simpl ; auto with cgr.
    * intros. replace j with (j + 0)%nat; eauto.
      rewrite NewVarC_and_VarSwap. eapply cgr_res_swap.
    * intros. replace j with (j + 0)%nat; eauto.
      rewrite NewVarC_and_VarSwap. eapply cgr_res_swap_rev.
    * intros. assert (NewVarC (0 + (S j)) (NewVarC 0 q) = NewVarC 0 (NewVarC ( 0 + j ) q)) as eq.
      { rewrite NewVarC_and_NewVarC. eauto. }
      simpl in *. rewrite eq. eapply cgr_res_scope.
    * intros. assert (NewVarC (0 + (S j)) (NewVarC 0 q) = NewVarC 0 (NewVarC ( 0 + j ) q)) as eq.
      { rewrite NewVarC_and_NewVarC. eauto. }
      simpl in *. rewrite eq. eapply cgr_res_scope_rev.
    * intros. eapply cgr_fullchoice; eauto. reflexivity.
  - eauto with cgr.
Qed.


(* Substition lemma, needed to contextualise the equivalence *)
Lemma cgr_subst1 p q q' x : q ≡* q' → pr_subst x p q ≡* pr_subst x p q'.
Proof.
revert q q' x.
(* Induction on the size of p*)
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros; simpl.
(* all induction cases for proc (not guards) *)
  - apply cgr_fullpar.
    apply Hp. simpl. auto with arith. assumption. 
    apply Hp. simpl. auto with arith. assumption. 
  - destruct (decide (x = n)). assumption. reflexivity.
  - destruct (decide (x = n)). reflexivity. apply cgr_recursion. apply Hp. simpl. auto. assumption.
  - apply cgr_full_if.
    apply Hp. simpl. auto with arith. assumption. 
    apply Hp. simpl. auto with arith. assumption.  
  - eauto with cgr.
  - eapply cgr_res. apply Hp. simpl. auto with arith. eapply NewVarC_Respects_Congruence. assumption.
  (* all induction cases for guards *)
  - destruct g0; simpl.
    * reflexivity.
    * reflexivity.
    * apply cgr_input. apply Hp. simpl. auto with arith. apply NewVar_Respects_Congruence. assumption.
    * apply cgr_tau. apply Hp. simpl. auto with arith. assumption.
    * apply cgr_fullchoice. 
      assert (pr_subst x (g g0_1) q ≡* pr_subst x (g g0_1) q'). apply Hp. simpl. auto with arith. assumption.
      auto. assert (pr_subst x (g g0_2) q ≡* pr_subst x (g g0_2) q'). apply Hp. simpl. auto with arith. assumption.
      auto. 
Qed.

(* ≡ respects the substitution (in recursion) of his variable *)
Lemma cgr_step_subst2 : forall p p' q x, p ≡ p' → pr_subst x p q ≡ pr_subst x p' q.
Proof.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros p' q n hcgr ; inversion hcgr; try auto; try (exact H); try (now constructor).
  - simpl. rewrite pr_subst_and_VarSwap. eapply cgr_res_swap_step.
  - simpl. rewrite pr_subst_and_VarSwap. eapply cgr_res_swap_rev_step.
  - simpl. rewrite pr_subst_and_NewVarC. eapply cgr_res_scope_step.
  - simpl. rewrite pr_subst_and_NewVarC. eapply cgr_res_scope_rev_step.
  - simpl. destruct (decide (n = x)). auto. constructor. apply Hp. subst. simpl. auto.  exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H.
  - simpl. constructor. apply Hp. subst. simpl. auto. exact H. 
  - simpl. constructor. apply Hp. subst. simpl. auto with arith. assumption. 
  - simpl. constructor. apply Hp. subst. simpl. auto with arith. assumption. 
  - simpl. constructor. apply Hp. subst. simpl. auto with arith. assumption.
  - simpl. constructor. apply Hp. subst. simpl. auto with arith. assumption. 
  - simpl. apply cgr_choice_step. 
    assert (pr_subst n (g p1) q ≡ pr_subst n (g q1) q). apply Hp. subst. simpl. rewrite <-Nat.add_succ_r. 
    apply PeanoNat.Nat.lt_add_pos_r. apply Nat.lt_0_succ.
    exact H. exact H2.
Qed.

(* ≡* respects the substitution of his variable *)
Lemma cgr_subst2 q p p' x : p ≡* p' → pr_subst x p q ≡* pr_subst x p' q.
Proof. 
intros hcgr. induction hcgr. constructor. now eapply cgr_step_subst2.  transitivity (pr_subst x y q).
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

End VACCS_congruence.