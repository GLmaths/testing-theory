Require Import Coq.Program.Equality Lia Arith.
Require Import Relations Morphisms.
From Must Require Import Clos_n.
From Must.pi Require Import Renamings.

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

| cgr_choice_nil_step : forall p,
    (p + 𝟘) ≡ p
| cgr_choice_nil_rev_step : forall p,
    (g p) ≡ (p + 𝟘)
| cgr_choice_com_step : forall p q,
    (p + q) ≡ (q + p)
| cgr_choice_assoc_step : forall p q r,
    ((p + q) + r) ≡ (p + (q + r))
| cgr_choice_assoc_rev_step : forall p q r,
    (p + (q + r)) ≡ ((p + q) + r)

| cgr_recursion_step : forall p q,
    p ≡ q -> (rec p) ≡ (rec q)
| cgr_tau_step : forall p q,
    p ≡ q ->
    (t • p) ≡ (t • q)
| cgr_input_step : forall c p q,
    p ≡ q ->
    (c ? p) ≡ (c ? q)
| cgr_output_step : forall c v p q,
    p ≡ q ->
    (c ! v • p) ≡ (c ! v • q)
| cgr_par_step : forall p q r,
    p ≡ q ->
    (p ‖ r) ≡ (q ‖ r)
| cgr_if_left_step : forall C p q q',
    q ≡ q' ->
    (If C Then p Else q) ≡ (If C Then p Else q')
| cgr_if_right_step : forall C p p' q,
    p ≡ p' ->
    (If C Then p Else q) ≡ (If C Then p' Else q)

(* this rule is in the corrected book of Sangiorgi, see his typos *)
| cgr_choice_step : forall p1 q1 p2,
    (g p1) ≡ (g q1) -> 
    (p1 + p2) ≡ (q1 + p2)

| cgr_nu_nu_step : forall p,
    (ν ν p) ≡ (ν ν (p ⟨swap⟩))
| cgr_res_nil_step :
    (ν 𝟘) ≡ 𝟘
| cgr_res_nil_rev_step :
    𝟘 ≡ (ν 𝟘)
| cgr_res_step : forall p q,
    p ≡ q ->
    (ν p) ≡ (ν q)
| cgr_scope_step: forall (P Q:proc),
    (ν (P ‖ (⇑ Q) )) ≡ ((ν P) ‖ Q)
| cgr_scope_rev_step: forall (P Q:proc),
    ((ν P) ‖ Q) ≡ (ν (P ‖ (⇑ Q)))
where "p ≡ q" := (cgr_step p q).

#[global] Hint Constructors cgr_step:cgr_step_structure.

(* Alternative definition of congruence step, better suited to prove that it's
  a congruence *)
Reserved Notation "p ≡ₐ q" (at level 70).
Reserved Notation "p ≡g q" (at level 70).
Inductive altcgr : proc -> proc -> Prop :=
| altcgr_refl_step : forall p, p ≡ₐ p
| altcgr_par_nil_step : forall p, 
    (p ‖ 𝟘) ≡ₐ p
| altcgr_par_nil_rev_step : forall p,
    p ≡ₐ (p ‖ 𝟘)
| altcgr_par_com_step : forall p q,
    (p ‖ q) ≡ₐ (q ‖ p)
| altcgr_par_assoc_step : forall p q r,
    ((p ‖ q) ‖ r) ≡ₐ (p ‖ (q ‖ r))
| altcgr_par_assoc_rev_step : forall p q r,
    (p ‖ (q  ‖ r)) ≡ₐ ((p ‖ q) ‖ r)
| altcgr_recursion_step : forall p q,
    p ≡ₐ q -> (rec p) ≡ₐ (rec q)
| altcgr_par_step : forall p q r,
    p ≡ₐ q ->
    (p ‖ r) ≡ₐ (q ‖ r)
| altcgr_if_left_step : forall C p q q',
    q ≡ₐ q' ->
    (If C Then p Else q) ≡ₐ (If C Then p Else q')
| altcgr_if_right_step : forall C p p' q,
    p ≡ₐ p' ->
    (If C Then p Else q) ≡ₐ (If C Then p' Else q)
| altcgr_nu_nu_step : forall p,
    (ν ν p) ≡ₐ (ν ν (p ⟨swap⟩))
| altcgr_res_nil_step :
    (ν 𝟘) ≡ₐ 𝟘
| altcgr_res_nil_rev_step :
    g 𝟘 ≡ₐ (ν 𝟘)
| altcgr_res_step : forall p q,
    p ≡ₐ q ->
    (ν p) ≡ₐ (ν q)
| altcgr_scope_step: forall (P Q:proc),
    (ν (P ‖ (⇑ Q) )) ≡ₐ ((ν P) ‖ Q)
| altcgr_scope_rev_step: forall (P Q:proc),
    ((ν P) ‖ Q) ≡ₐ (ν (P ‖ (⇑ Q)))
(* This rules is custom ; it's easily in the transitive closure of the standard
 congruence. It actually implies altcgr_res_nil_step *)
 (*
| altcgr_scope_free: forall (p q : proc), p ≡ₐ ⇑ q -> ν p ≡ₐ q
| altcgr_scope_free_rev: forall (p q : proc), p ≡ₐ ⇑ q -> q ≡ₐ ν p
*)
| altcgr_guard : forall (g1 g2 : gproc), g1 ≡g g2 -> g g1 ≡ₐ g g2
| altcgr_trans : forall (p q r : proc) , p ≡ₐ q -> q ≡ₐ r -> p ≡ₐ r

with altcgr_gstep : gproc -> gproc -> Prop :=
| galtcgr_tau_step : forall p q,
    p ≡ₐ q ->
    (t • p) ≡g (t • q)
| galtcgr_input_step : forall c p q,
    p ≡ₐ q ->
    (c ? p) ≡g (c ? q)
| galtcgr_output_step : forall c v p q,
    p ≡ₐ q ->
    (c ! v • p) ≡g (c ! v • q)
| galtcgr_choice_step : forall p1 q1 p2,
    p1 ≡g q1 ->
    (p1 + p2) ≡g (q1 + p2)
| galtcgr_trans : forall (p q r : gproc), p ≡g q -> q ≡g r -> p ≡g r
| galtcgr_choice_nil_step : forall p,
    (p + 𝟘) ≡g p
| galtcgr_choice_nil_rev_step : forall p,
    p ≡g (p + 𝟘)
| galtcgr_choice_com_step : forall p q,
    (p + q) ≡g (q + p)
| galtcgr_choice_assoc_step : forall p q r,
    ((p + q) + r) ≡g (p + (q + r))
| galtcgr_choice_assoc_rev_step : forall p q r,
    (p + (q + r)) ≡g ((p + q) + r)
| galtcgr_refl_step : forall p, p ≡g p
| galtcgr_sym_step : forall p q, q ≡g p -> p ≡g q
where "p ≡ₐ q" := (altcgr p q)
and "p ≡g q" := (altcgr_gstep p q).
#[local] Hint Constructors altcgr:alt_step_structure.

#[global] Instance cgr_refl_step_is_refl : Reflexive cgr_step.
Proof. intro. apply cgr_refl_step. Qed.
#[global] Instance cgr_symm_step : Symmetric cgr_step.
Proof. intros p q hcgr. induction hcgr; try solve [constructor; try exact IHhcgr].
rewrite <- (Swap_Proc_Involutive p) at 2. apply cgr_nu_nu_step.
Qed.

Infix "≡" := cgr_step (at level 70).

Definition cgr := (clos_trans proc cgr_step).
Infix "≡*" := cgr (at level 70).

#[global] Instance cgr_refl : Reflexive cgr.
Proof. intros. constructor. apply cgr_refl_step. Qed.
#[global] Instance cgr_symm : Symmetric cgr.
Proof. intros p q hcgr. induction hcgr. constructor. apply cgr_symm_step.
exact H. eapply t_trans; eauto. Qed.
#[global] Instance cgr_trans : Transitive cgr.
Proof. intros p q r hcgr1 hcgr2. eapply t_trans; eauto. Qed.

#[global] Hint Resolve cgr_refl cgr_symm cgr_trans:cgr_eq.

#[global] Instance cgr_is_eq_rel  : Equivalence cgr.
Proof. repeat split.
       + apply cgr_refl.
       + apply cgr_symm.
       + apply cgr_trans.
Qed.

(* Transitive closure of congruence on guards only *)
Definition guardcgr  :=
  clos_trans proc (fun p1 p2 => exists g1 g2, p1 = g g1 /\ p2 = g g2 /\ p1 ≡ p2).

#[local] Instance guard_cgr_refl : Symmetric guardcgr.
Proof.
  intros x y H. induction H.
  - constructor. decompose record H. eauto with *.
  - econstructor 2; eauto with *.
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
Lemma cgr_choice_nil_rev : forall p, (g p) ≡* p + 𝟘.
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
intros. induction H.
constructor.
apply cgr_recursion_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_tau : forall p q, p ≡* q -> (t • p) ≡* (t • q).
Proof.
intros. induction H.
constructor.
- apply cgr_tau_step. exact H.
- eauto with cgr_eq.
Qed.

(* Stronger statement : congruences under tau preserve guards *)
Lemma guardcgr_tau : forall p q, p ≡* q -> guardcgr (t • p) (t • q).
Proof.
intros. induction H.
constructor.
- eexists; eexists; repeat split. apply cgr_tau_step. exact H.
- econstructor 2; eauto with cgr_eq.
Qed.

Lemma cgr_input : forall c p q, p ≡* q -> (c ? p) ≡* (c ? q).
Proof.
intros. induction H.
- constructor. now apply cgr_input_step.
- eauto with cgr_eq.
Qed.

Lemma guardcgr_input : forall c p q, p ≡* q -> guardcgr (c ? p) (c ? q).
Proof.
intros. induction H.
- constructor. eexists; eexists; repeat split. now apply cgr_input_step.
- econstructor 2; eauto with cgr_eq.
Qed.

Lemma cgr_output : forall c v p q, p ≡* q -> (c ! v • p) ≡* (c ! v • q).
Proof.
intros. induction H.
- constructor. now apply cgr_output_step.
- eauto with cgr_eq.
Qed.

Lemma guardcgr_output : forall c v p q, p ≡* q -> guardcgr (c ! v • p) (c ! v • q).
Proof.
intros. induction H.
- constructor. eexists; eexists; repeat split. now constructor.
- econstructor 2; eauto with cgr_eq.
Qed.

Lemma cgr_res : forall p q, p ≡* q -> (ν p) ≡* (ν q).
Proof.
intros. induction H.
- constructor. apply cgr_res_step. exact H.
- eauto with cgr_eq.
Qed.
Lemma cgr_nu_nu : forall p, (ν ν p) ≡* (ν ν (p ⟨swap⟩)).
Proof.
intros p. constructor. apply cgr_nu_nu_step.
Qed.
Lemma cgr_res_nil : 𝟘 ≡* (ν 𝟘).
Proof.
constructor. exact cgr_res_nil_rev_step.
Qed.
Lemma cgr_scope : forall P Q, 
  ν (P ‖ (⇑ Q)) ≡* (ν P) ‖ Q.
Proof.
intros P Q. constructor. apply cgr_scope_step.
Qed.
Lemma cgr_scope_rev : forall P Q, 
  (ν P ‖ Q) ≡* ν (P ‖ (⇑Q)).
Proof.
intros P Q. constructor. apply cgr_scope_rev_step.
Qed.
Lemma cgr_par : forall p q r, p ≡* q-> p ‖ r ≡* q ‖ r.
Proof.
intros. induction H.
- constructor. now apply cgr_par_step.
- eauto with cgr_eq.
Qed.
Lemma cgr_if_left : forall C p q q', q ≡* q' -> (If C Then p Else q) ≡* (If C Then p Else q').
Proof.
intros. induction H.
constructor.
apply cgr_if_left_step. exact H. eauto with cgr_eq.
Qed.
Lemma cgr_if_right : forall C p p' q, p ≡* p' -> (If C Then p Else q) ≡* (If C Then p' Else q).
Proof.
intros. induction H.
- constructor.  apply cgr_if_right_step. exact H.
- eauto with cgr_eq.
Qed.

Lemma cgr_n_par_l p p' q n: clos_n altcgr n p p' ->
  clos_n altcgr n (p ‖ q) (p' ‖ q).
Proof.
induction 1 as [|n p p' p'' Hp' Hind].
- constructor.
- apply clos_n_step with (p' ‖ q).
  + now constructor.
  + apply IHHind.
Qed.

#[global] Instance altcgr_refl_step_is_refl : Reflexive altcgr.
Proof. intro. apply altcgr_refl_step. Qed.

#[global] Instance altcgr_grefl_step_is_refl : Reflexive altcgr_gstep.
Proof. intro. constructor. Qed.

#[local] Instance altcgr_symm_step : Symmetric altcgr.
Proof. intros p q hcgr. induction hcgr; try solve [constructor; try exact IHhcgr];
try solve[now (do 3 (try constructor))].
- rewrite <- (Swap_Proc_Involutive p) at 2. apply altcgr_nu_nu_step.
- constructor. now constructor.
- econstructor; eauto.
Qed.

(* The lemmas on renaming suffice for all of the treatment, except recursive variables. *)
Instance RenProperStep : Proper (eq ==> (pointwise_relation _ eq) ==> cgr_step ==> cgr_step) ren2.
Proof.
intros sp' sp Hp s' s Hs q1 q2 Hq. rewrite Hs. clear Hs s'. subst.
  revert sp s.
  induction Hq; intros; try solve [asimpl; auto with cgr_step_structure].
  - asimpl. apply cgr_choice_step. apply IHHq.
  - asimpl. simpl. change (idsRen >> sp) with sp.
    replace (ren_proc sp (1 .: (0 .: (fun x => S (S (s x))))) p) 
      with  ((ren_proc sp (0 .: (1 .: (fun x => S (S (s x))))) p) ⟨swap⟩)
      by now asimpl.
    apply cgr_nu_nu_step.
  - unfold ren2. simpl. rewrite permute_ren. exact (cgr_scope_step _ _).
  - unfold ren2. simpl. rewrite permute_ren. exact (cgr_scope_rev_step _ _).
Qed.

Instance RenProper : Proper (eq ==> (pointwise_relation _ eq) ==> cgr ==> cgr) ren2.
Proof.
intros sp' sp Hp s' s Hs q1 q2 Hq. rewrite Hs.
induction Hq as [p q base_case | p r q transitivity_case].
- subst. apply t_step. apply RenProperStep; trivial. intro n; trivial.
- subst. now rewrite IHtransitivity_case.
Qed.


(*
(* It takes two more steps to apply congruences on the right hand side of
  a parallel *)
Lemma cgr_n_par_r p p' q n: clos_n altcgr n p p' ->
  clos_n altcgr (S (S n)) (q ‖ p) (q ‖ p').
Proof.
intro Hp. apply clos_n_step with (p ‖ q); [constructor|].
replace (S n) with (n + 1)%nat by apply PeanoNat.Nat.add_1_r.
apply clos_n_trans with (p' ‖ q).
- apply cgr_n_par_l, Hp.
- apply clos_n_step with (q ‖ p'); constructor.
Qed.


Lemma altcgr_n_nu p p' n: clos_n altcgr n p p' ->
  clos_n altcgr n (ν p) (ν p').
Proof.
induction 1 as [|n p p' Hp' Hind].
- constructor.
- apply clos_n_step with (ν p').
  + now constructor.
  + apply IHclos_n.
Qed.

Lemma shift_nil (q : proc) : ⇑ q = 𝟘 -> q = 𝟘.
Proof.
destruct q; unfold shift_op, Shift_proc; asimpl; trivial; try solve[intro H; inversion H].
destruct g0; unfold shift_op, Shift_gproc; asimpl; trivial; intro H; inversion H.
Qed.

Lemma Shift_Proc_Injective : forall (p1 p2: proc), ⇑ p1 = ⇑ p2 -> p1 = p2.
Proof.
unfold shift_op, Shift_proc. intros.
eapply Injective_Ren_Proc. apply Shift_Injective.
exact H.
Qed.
*)

(* Equivalence between the two definitions *)

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
- now apply cgr_if_left.
- now apply cgr_if_right.
- now apply cgr_res.
- now apply guardcgr_cgr.
- eauto with *.
- now apply guardcgr_tau.
- now apply guardcgr_input.
- now apply guardcgr_output.
- now apply guardcgr_choice_step.
- intros. now apply t_trans with (g q).
- now symmetry.
Qed.

(* Being syntactically equivalent to a guard, hidden under parallels and unnecessary restrictions *)
Fixpoint sguard (g0 : gproc) (p : proc) := match p with
| (p ‖ q) => (sguard 𝟘 p /\ sguard g0 q) \/ (sguard 𝟘 q /\ sguard g0 p)
| (ν p) => sguard (⇑ g0) p
| g p => p ≡g g0
| _ => False
end.

(* congruence is preserved by renamings *)
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
Qed.

Lemma sguard_cgr_proper p g g': sguard g p -> g ≡g g' -> sguard g' p.
Proof.
revert g g'. induction p; simpl; intuition.
- left. intuition. eauto with *.
- right. intuition. eauto with *.
- eapply IHp; [eassumption|]. now apply ren2_altcgr.
- apply galtcgr_trans with g1; trivial.
Qed.

Lemma ren2_sguard p g s1 s2 : sguard g p -> sguard (ren2 s1 s2 g) (ren2 s1 s2 p).
Proof.
revert g s1 s2. induction p; intros g s1 s2; simpl; intuition.
- left. split; [now apply (IHp1 𝟘)| now apply IHp2].
- right. split; [now apply (IHp2 𝟘) | now apply IHp1].
- revert H. rewrite <- permute_ren_guard. apply IHp; trivial.
- now apply ren2_altcgr.
Qed.

Definition shift_down_proc := ren2 ids pred.
Axiom shift_down_up_proc : forall p : proc, shift_down_proc (⇑ p) = p.
Definition shift_down_gproc := ren2 ids pred : gproc -> gproc.
Axiom shift_down_up_gproc : forall p : gproc, shift_down_gproc (⇑ p) = p.

Instance RenProperAltcgr : Proper (eq ==> (eq) ==> altcgr ==> altcgr) ren2.
Proof. intros ?????????. subst. now apply ren2_altcgr. Qed.

Lemma altcgr_guard_proper (p0 p1 : proc) (g0 : gproc) : (p0 ≡ₐ p1) -> sguard g0 p0
  -> sguard g0 p1.
Proof.
intro H. dependent induction H generalizing g0; simpl; try solve[constructor]; auto with *;
intuition; simpl; eauto with *.
- eapply sguard_cgr_proper; eauto.
- replace (⇑ (⇑ g0)) with ((⇑ (⇑ g0)) ⟨ swap ⟩) by (now asimpl).
  now apply ren2_sguard.
- rewrite <- (shift_down_up_gproc g0), <- (shift_down_up_gproc 𝟘).
  change (⇑ 𝟘) with 𝟘. now apply ren2_altcgr.
- change 𝟘 with (⇑ 𝟘). now apply ren2_altcgr.
- left. split; trivial.
  rewrite <- (shift_down_up_gproc g0), <- (shift_down_up_proc Q).
  now apply ren2_sguard.
- right. split; trivial. change 𝟘 with (⇑ 𝟘) in H.
  rewrite <- (shift_down_up_proc Q), <- (shift_down_up_gproc 𝟘).
  now apply ren2_sguard.
- left. split; trivial. now apply ren2_sguard.
- right. split; trivial. change 𝟘 with (⇑ 𝟘). now apply ren2_sguard.
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

(* Choice respects ≡* *)
Lemma cgr_choice : forall p q r, g p ≡* g q -> p + r ≡* q + r.
Proof.
intros p q r H%cgr_altcgr%altcgr_guard_rev.
apply altcgr_cgr. now do 2 constructor.
Qed.

(* The if of processes respects ≡* *)
Lemma cgr_full_if : forall C p p' q q', p ≡* p' -> q ≡* q' -> (If C Then p Else q) ≡* (If C Then p' Else q').
Proof.
intros.
apply transitivity with (If C Then p Else q'). apply cgr_if_left. exact H0. 
apply cgr_if_right. exact H. 
Qed.
(* The sum of guards respects ≡* *)
Lemma cgr_fullchoice : forall M1 M2 M3 M4, (g M1) ≡* (g M2) -> (g M3) ≡* (g M4) -> M1 + M3 ≡* M2 + M4.
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
cgr_choice_assoc_rev cgr_recursion cgr_tau cgr_input cgr_if_left cgr_if_right cgr_par cgr_choice 
cgr_refl cgr_symm cgr_res cgr_scope cgr_scope_rev cgr_res_nil cgr_trans : cgr.

#[global] Instance pr_par_proper : Proper (cgr ==> cgr ==> cgr) pr_par.
Proof.
intros p p' Hp q q' Hq.
apply (cgr_fullpar _ _ _ _ Hp Hq).
Qed.

Definition gpr_cgr p q := g p ≡* g q.
#[global] Instance gpr_choice_proper : Proper (gpr_cgr ==> gpr_cgr ==> cgr) gpr_choice.
Proof. intros p p' Hp q q' Hq. apply cgr_fullchoice; assumption. Qed.

#[global] Instance pr_res_proper : Proper (cgr ==> cgr) pr_res.
Proof. intros p p' Hp. apply cgr_res; assumption. Qed.

#[global] Instance pr_rec_proper : Proper (cgr ==> cgr) pr_rec.
Proof. intros p p' Hp. apply cgr_recursion; assumption. Qed.

#[global] Instance pr_tau_proper : Proper (cgr ==> cgr) gpr_tau.
Proof. intros p p' Hp. apply cgr_tau; assumption. Qed.

(* Allow rewriting of cgr_step inside cgr *)
#[global] Instance cgr_step_subrelation : subrelation cgr_step cgr.
Proof.
  intros x y H. constructor. exact H.
Qed.

(* The old Congruence lemmas can now be restated using Autosubst's help.
   This still requires some technical work and lemmas on substitutions. *)

(* In order to treat recursive variables, we need more subtle instances on substitutions *)
Definition eq_up_to_cgr f g := forall x :nat, f x ≡* g x.

Instance SubstProperStep : Proper (eq ==> (pointwise_relation _ eq) ==> cgr_step ==> cgr_step) subst2.
Proof.
intros sp' sp Hp s' s Hs q1 q2 Hq. subst. rewrite Hs. clear Hs s'. revert sp s.
induction Hq;  intros; try solve [asimpl; auto with cgr_step_structure].
- asimpl. apply cgr_choice_step. apply IHHq.
- cbn. rewrite Up_Up_Subst_Swap. now apply cgr_nu_nu_step.
- unfold subst2. simpl. rewrite Shift_Permute_Subst. exact (cgr_scope_step _ _).
- unfold subst2. simpl. rewrite Shift_Permute_Subst. exact (cgr_scope_rev_step _ _).
Qed.

Instance SubstProper : Proper (eq ==> (pointwise_relation _ eq) ==> cgr ==> cgr) subst2.
Proof.
intros sp' sp Hp s' s Hs q1 q2 Hq. rewrite Hs, Hp.
induction Hq as [p q base_case | p r q transitivity_case].
- apply t_step. apply SubstProperStep; trivial. reflexivity.
- subst. now rewrite IHtransitivity_case.
Qed.

Lemma SubstProper_proc
  (p : proc)
  (sp sp' : nat -> proc) (Hp : eq_up_to_cgr sp sp')
  (s : nat -> Data) : 
  p[sp; s] ≡* p[sp'; s]
with SubstProper_gproc
  (q : gproc)
  (sp sp' : nat -> proc) (Hp : eq_up_to_cgr sp sp')
  (s : nat -> Data) :
  gpr_cgr (q[sp; s]) (q[sp'; s]).
Proof.
induction p; cbn.
- apply Hp.
- apply cgr_recursion. fold subst_proc. apply SubstProper_proc.
  (* if two substitutions are eq_up_to_cgr, they are also when moved below a binder *)
  intros [|n].
  + reflexivity.
  + simpl. apply RenProper; try reflexivity. apply Hp.
- rewrite (SubstProper_proc p1), (SubstProper_proc p2). reflexivity. assumption. assumption.
- rewrite SubstProper_proc. reflexivity.
  intros [|n].
  + apply RenProper; try reflexivity. apply Hp.
  + apply RenProper; try reflexivity. apply Hp.
- apply cgr_full_if.
  + rewrite SubstProper_proc; try reflexivity. assumption.
  + rewrite SubstProper_proc; try reflexivity. assumption.
- fold subst_gproc. apply SubstProper_gproc. assumption.
- unfold gpr_cgr in *. induction q; cbn.
  + reflexivity.
  + reflexivity.
  (* This is, very surprisingly, the only place where we need cgr_output. *)
  + fold subst_proc. apply cgr_output. apply SubstProper_proc. assumption.
  + fold subst_proc. apply cgr_input. apply SubstProper_proc.
    intros [|n].
    * apply RenProper; try reflexivity. apply Hp.
    * apply RenProper; try reflexivity. apply Hp.
  + fold subst_proc. apply cgr_tau. apply SubstProper_proc. assumption.
  + apply cgr_fullchoice.
    * rewrite SubstProper_gproc; try reflexivity. assumption.
    * rewrite SubstProper_gproc; try reflexivity. assumption.
Qed.

Instance SubstProperMutual : Proper (eq_up_to_cgr ==> (pointwise_relation _ eq) ==> eq ==> cgr) subst2.
Proof.
intros sp' sp Hp s' s Hs q1 q2 Hq. subst. rewrite Hs.
apply SubstProper_proc. assumption.
Qed.

Instance SubstProperTotal : Proper (eq_up_to_cgr ==> eq ==> cgr ==> cgr) subst2.
Proof.
intros sp' sp Hp s' s Hs q1 q2 Hq.
subst. now rewrite Hq, Hp.
Qed.

Instance SconsProper : Proper (cgr ==> eq ==> eq_up_to_cgr) scons.
intros p p' Hp s s' Hs. subst.
intros [|n]; simpl.
- trivial.
- reflexivity.
Qed.

Instance NewsProper : Proper (eq ==> cgr ==> cgr) νs.
Proof.
intros n ? <- p1 p2 Heq. induction n.
- now simpl.
- simpl. now apply cgr_res.
Qed.
Instance nvarsProper : Proper (eq ==> cgr ==> cgr) (@nvars proc _).
Proof.
intros n ? <- p1 p2 Heq. induction n.
- now simpl.
- simpl. unfold shift_op. unfold Shift_proc. now rewrite IHn.
Qed.

Lemma n_extrusion : forall n p q, (νs n p) ‖ q ≡* νs n (p ‖ nvars n q).
Proof.
induction n.
- now simpl.
- intros p q. simpl. rewrite <- cgr_scope. rewrite IHn. now rewrite shift_in_nvars.
Qed.

#[global] Hint Resolve cgr_is_eq_rel: ccs.
#[global] Hint Constructors clos_trans:ccs.
#[global] Hint Unfold cgr:ccs.
