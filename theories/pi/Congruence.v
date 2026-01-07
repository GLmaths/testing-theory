Require Import Coq.Program.Equality.
Require Import Relations Morphisms.

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

#[global] Instance cgr_refl_step_is_refl : Reflexive cgr_step.
Proof. intro. apply cgr_refl_step. Qed.
#[global] Instance cgr_symm_step : Symmetric cgr_step.
Proof. intros p q hcgr. induction hcgr; try solve [constructor; try exact IHhcgr].
- rewrite <- (Swap_Proc_Involutive p) at 2. apply cgr_nu_nu_step.
Qed.

Infix "≡" := cgr_step (at level 70).

Definition cgr := (clos_trans proc cgr_step).
Infix "≡*" := cgr (at level 70).

#[global] Instance cgr_refl : Reflexive cgr.
Proof. intros. constructor. apply cgr_refl_step. Qed.
#[global] Instance cgr_symm : Symmetric cgr.
Proof. intros p q hcgr. induction hcgr. constructor. apply cgr_symm_step. exact H. eapply t_trans; eauto. Qed.
#[global] Instance cgr_trans : Transitive cgr.
Proof. intros p q r hcgr1 hcgr2. eapply t_trans; eauto. Qed.

#[global] Hint Resolve cgr_refl cgr_symm cgr_trans:cgr_eq.

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
Lemma cgr_input : forall c p q, p ≡* q -> (c ? p) ≡* (c ? q).
Proof.
intros. induction H. 
- constructor. now apply cgr_input_step.
- eauto with cgr_eq.
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
Lemma cgr_choice : forall p q r, (g p) ≡* (g q) -> p + r ≡* q + r.
Proof.
intros. dependent induction H.
- constructor. apply cgr_choice_step. exact H.
- etransitivity. apply (IHclos_trans1 p q). reflexivity. admit.
Admitted.

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

Definition eq_up_to_cgr f g := forall x :nat, f x ≡* g x.

Instance SubstProperStep : Proper (eq ==> (pointwise_relation _ eq) ==> cgr_step ==> cgr_step) subst2.
Proof.
intros sp' sp Hp s' s Hs q1 q2 Hq. subst. rewrite Hs. clear Hs s'. revert sp s.
induction Hq;  intros; try solve [asimpl; auto with cgr_step_structure].
- asimpl. apply cgr_choice_step. apply IHHq.
- admit.
(* - change ((ν (ν p)) [sp; s]) with ((ν (ν p)) [sp; s]).
  asimpl. simpl.
  unfold shift.
  assert (subst_proc sp ((var_Data 1) .: ((var_Data 0) .: (fun x => ren_Data S (ren_Data S (s x))))) p = 
          ren_proc ids swap
            (subst_proc sp ((var_Data 0) .: (var_Data 1 .: (fun x => ren_Data S (ren_Data S (s x))))) p)).
          unfold swap. asimpl. simpl. cbn.
  rewrite H.
  apply cgr_nu_nu_step. *)
- unfold subst2. simpl. rewrite permute_subst. exact (cgr_scope_step _ _).
- unfold subst2. simpl. rewrite permute_subst. exact (cgr_scope_rev_step _ _).
Admitted.

Instance SubstProper : Proper (eq ==> (pointwise_relation _ eq) ==> cgr ==> cgr) subst2.
Proof.
intros sp' sp Hp s' s Hs q1 q2 Hq. rewrite Hs, Hp.
induction Hq as [p q base_case | p r q transitivity_case].
- apply t_step. apply SubstProperStep; trivial. intro n; trivial.
- subst. now rewrite IHtransitivity_case.
Qed.

Instance SubstProper' : Proper (eq_up_to_cgr ==> (pointwise_relation _ eq) ==> eq ==> cgr) subst2.
Proof.
intros sp' sp Hp s' s Hs q1 q2 Hq. subst. rewrite Hs. clear Hs.
revert sp' sp s Hp. induction q2; intros; try solve [asimpl; auto with cgr].
- asimpl. simpl. apply cgr_recursion. apply IHq2.
intro n.
destruct n.
+ reflexivity.
+ simpl.
 (* apply Hp.

revert sp sp' Hp.
 induction n.
+ reflexivity.
+ intros. simpl. *)
Admitted.

Instance SubstProperTotal : Proper (eq_up_to_cgr ==> eq ==> cgr ==> cgr) subst2.
intros sp' sp Hp s' s Hs q1 q2 Hq. subst.
now rewrite Hq, Hp.
Qed.

Instance SubstProper'' : Proper (cgr ==> eq ==> eq_up_to_cgr) scons.
intros p p' Hp s s' Hs. subst.
intros [|n]; simpl.
- trivial.
- reflexivity.
Qed.

Instance RenProperStep : Proper (eq ==> (pointwise_relation _ eq) ==> cgr_step ==> cgr_step) ren2.
Proof.
intros sp' sp Hp s' s Hs q1 q2 Hq. rewrite Hs. clear Hs s'. subst.
  revert sp s.
  induction Hq; intros; try solve [asimpl; auto with cgr_step_structure].
  - asimpl. apply cgr_choice_step. apply IHHq.
  - asimpl. simpl. change (idsRen >> sp) with sp.
    assert (ren_proc sp (1 .: (0 .: (fun x => S (S (s x))))) p = 
            ren_proc ids swap (ren_proc sp (0 .: (1 .: (fun x => S (S (s x))))) p)).
            unfold swap. asimpl. now cbn.
    rewrite H.
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

Instance NewsProper : Proper (eq ==> cgr ==> cgr) νs.
Proof.
intros n ? <- p1 p2 Heq. induction n.
- now simpl.
- simpl. now apply cgr_res.
Qed.
Instance nvars_proper : Proper (eq ==> cgr ==> cgr) (@nvars proc _).
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
