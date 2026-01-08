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
Lemma cgr_output : forall c v p q, p ≡* q -> (c ! v • p) ≡* (c ! v • q).
Proof.
intros. induction H.
- constructor. now apply cgr_output_step.
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

Lemma cgr_n_par_l p p' q n: clos_n cgr_step n p p' ->
  clos_n cgr_step n (p ‖ q) (p' ‖ q).
Proof.
induction 1 as [|n p p' p'' Hp' Hind].
- constructor.
- apply clos_n_step with (p' ‖ q).
  + now constructor.
  + apply IHHind.
Qed.

(* It takes two more steps to apply congruences on the right hand side of
  a parallel *)
Lemma cgr_n_par_r p p' q n: clos_n cgr_step n p p' ->
  clos_n cgr_step (S (S n)) (q ‖ p) (q ‖ p').
Proof.
intro Hp. apply clos_n_step with (p ‖ q); [constructor|].
replace (S n) with (n + 1)%nat by apply PeanoNat.Nat.add_1_r.
apply clos_n_trans with (p' ‖ q).
- apply cgr_n_par_l, Hp.
- apply clos_n_step with (q ‖ p'); constructor.
Qed.


Lemma cgr_n_nu p p' n: clos_n cgr_step n p p' ->
  clos_n cgr_step n (ν p) (ν p').
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

Lemma clos_n_cgr_step_shift q p n: clos_n cgr_step n (⇑ q) (⇑ p) ->
  clos_n cgr_step n q p.
Proof.
intro H; dependent induction H.
- replace q with p; [constructor|].
(*   apply Shift_Op_Injective. *)
Admitted.

Lemma cgr_n_extrusion p q g0 n: clos_n cgr_step n ((ν p) ‖ q) (g g0) ->
  clos_n cgr_step n (ν (p ‖ ⇑ q)) g0.
Proof.
intro H. dependent induction H. inversion H; subst.
Admitted.

(*
Lemma cgr_n_par_guard p q g0 n : (clos_n cgr_step n (p ‖ q) (g g0) ->
  exists np nq,
   (n >= (np + nq + 2)%nat /\ (clos_n cgr_step np p (g 𝟘) /\ clos_n cgr_step nq q (g g0)) \/
   (n >= (np + nq + 2)%nat /\ clos_n cgr_step np p (g g0) /\ clos_n cgr_step nq q (g 𝟘)) \/
   (n >= (np + 1)%nat /\ clos_n cgr_step np p (g g0) /\ q = g 𝟘))).
Proof.
(* by strong induction *)
revert p q g0. induction n as [n IH] using lt_wf_ind; intros p q g0.
destruct n as [|n]; [intro H; inversion H|].
intro H; apply clos_n_S_inv in H.
- destruct H as [Heq | [p' [Hpp' Hp'q]]]; [inversion Heq|].
  dependent destruction Hpp'.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * exists (S np), nq. left. repeat split; [lia| |]; trivial.
      apply clos_n_S, Hp.
    * exists (S np), nq. right. left. repeat split; [lia| |]; trivial.
      apply clos_n_S, Hp.
    * inversion Hq; subst. exists (S np), 0. right; right.
      repeat split; trivial.
      -- lia.
      -- apply clos_n_S, Hp.
    * constructor.
  + exists n, 0. right. right. repeat split; [lia|]; trivial.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists (S (S np')), (nq' + nq)%nat. left.
         repeat split; [lia| |].
         ++ apply clos_n_S, clos_n_S, Hp'.
         ++ now apply clos_n_trans with (g 𝟘).
      -- exists (np' + nq)%nat, (S (S nq')). right. left.
         repeat split; [lia| |].
         ++	now apply clos_n_trans with (g 𝟘).
         ++ apply clos_n_S, clos_n_S, Hq'.
      -- subst. exists (np' + nq)%nat, 0. right. right.
         repeat split; [lia|]; trivial.
         apply clos_n_trans with (g 𝟘); trivial.
      -- lia.
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', nq'. left.
         repeat split; [lia| |]; trivial.
      -- exists np', nq'. right. left. repeat split; [lia| |]; trivial.
      -- inversion Hq'; subst. exists np', 0. right; right.
         repeat split; trivial. lia.
      -- lia.
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', nq'. left. repeat split; [lia| |]; trivial.
      -- exists np', nq'. right. left. repeat split; trivial. lia.
      -- inversion Hq'; subst. exists np', 0. right; right.
         repeat split; trivial. lia.
      -- lia.
    * lia.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * exists nq, np. right. left. repeat split; trivial. lia.
    * exists nq, np. left. repeat split; trivial. lia.
    * inversion Hq; subst. exists 0, np. left. repeat split; trivial. lia. constructor.
    * lia.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * apply IH in Hq as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists (np + (2 + np'))%nat, nq'. left. repeat split; trivial. lia.
         apply clos_n_trans with (g 𝟘 ‖ q0).
         ++ apply cgr_n_par_l, Hp.
         ++ apply clos_n_step with (q0 ‖ g 𝟘); [constructor|].
            apply clos_n_step with q0; [constructor|]; trivial.
      -- exists (np + S (S np'))%nat, nq'. right. left.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g 𝟘 ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_step with (q0 ‖ g 𝟘); [constructor|].
            apply clos_n_step with q0; [constructor|]. trivial.
      -- eexists (np + (2 + np'))%nat, 0; right; right.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g 𝟘 ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_step with (q0 ‖ g 𝟘); [constructor|].
            apply clos_n_step with q0; [constructor|]. trivial.
      -- lia.
    * apply IH in Hq as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists (np + ((2 + np') + 1))%nat, nq'. right. left.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g g0 ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_trans with (g g0 ‖ g 𝟘).
          ** now apply cgr_n_par_r.
          ** eapply clos_n_step; [|constructor]. constructor.
      -- exists (np + ((2 + np') + 1))%nat, nq'. right. left.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g g0 ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_trans with (g g0 ‖ g 𝟘).
          ** now apply cgr_n_par_r.
          ** eapply clos_n_step; [|constructor]. constructor.
      -- exists (np + ((2 + np') + 1))%nat, 0. right. right. repeat split; trivial; [lia|].
         apply clos_n_trans with (g g0 ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_trans with (g g0 ‖ g 𝟘).
          ** now apply cgr_n_par_r.
          ** eapply clos_n_step; [|constructor]. constructor.
      -- lia.
    * inversion Hq.
    * lia.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', (nq' + S (S nq))%nat. left. repeat split; trivial; [lia|].
         apply clos_n_trans with (g 𝟘 ‖ r).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_step with (r ‖ g 𝟘); [constructor|].
            apply clos_n_step with r; [constructor|]. trivial.
      -- exists np', (nq' + S (S nq))%nat. left. repeat split; trivial; [lia|].
         apply clos_n_trans with (g 𝟘 ‖ r).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_step with (r ‖ g 𝟘); [constructor|].
            apply clos_n_step with r; [constructor|]. trivial.
      -- exists np', (S (S nq)). left. repeat split; trivial; [lia|].
         inversion Hq'. apply clos_n_step with (r  ‖ g 𝟘);[constructor|].
         apply clos_n_step with r;[constructor|]. trivial.
      -- lia.
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', (nq' + (S (S nq) + 1))%nat. left. repeat split; trivial; [lia|].
         apply clos_n_trans with (g g0 ‖ r); [now apply cgr_n_par_l|].
         apply clos_n_trans with (g g0 ‖ g 𝟘); [now apply cgr_n_par_r|].
         apply clos_n_step with (g g0); constructor.
      -- exists np', (nq' + (2 + nq))%nat. right. left.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g 𝟘 ‖ r); [now apply cgr_n_par_l|].
         apply clos_n_step with (r ‖ g 𝟘); [constructor|].
         apply clos_n_step with r; [constructor|]. trivial.
      -- exists np', (2 + nq)%nat. right. left.
         repeat split; trivial; [lia|]. inversion Hq'; subst.
         apply clos_n_step with (r ‖ g 𝟘); [constructor|].
         apply clos_n_step with r; [constructor|]. trivial.
      -- lia.
    * inversion Hq; subst.
      apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', (S nq'). left. repeat split; trivial; [lia|].
         apply clos_n_step with q0; [constructor|]. trivial.
      -- exists np', (S nq')%nat. right. left. repeat split; trivial; [lia|].
         apply clos_n_step with q0; [constructor|]. trivial.
      -- exists np', 1. right. left. repeat split; trivial; [lia|].
         inversion Hq'. apply clos_n_step with (g 𝟘); constructor.
      -- lia.
    * lia.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * exists (S np), nq. left. repeat split; [lia| |]; trivial.
      apply clos_n_step with q0; trivial.
    * exists (S np), nq. right. left. repeat split; [lia| |]; trivial.
      apply clos_n_step with q0; trivial.
    * exists (S np), nq. right. right. repeat split; [lia| |]; trivial.
      apply clos_n_step with q0; trivial.
    * constructor.
  + apply IH in Hp'q as (np0 & nq0 & Hge & Hnp & Hg0); [|lia|exact q].
    apply IH in Hnp as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * exists (np + 1 + nq0)%nat, nq. right. left. repeat split.
      -- lia.
      -- apply clos_n_trans with (g 𝟘); trivial.
         eapply clos_n_trans with (ν (g 𝟘)).
         ++ apply cgr_n_nu, Hp.
         ++ econstructor; constructor.
      -- now apply clos_n_cgr_step_shift.
    * exists (np + 1)%nat, (nq + nq0)%nat. left. repeat split.
      -- lia.
      -- apply clos_n_trans with (ν 𝟘); [|econstructor; constructor].
         now apply cgr_n_nu.
      -- apply clos_n_trans with (g 𝟘); trivial.
         now apply clos_n_cgr_step_shift.
    * exists (np + 1 + nq0)%nat, nq. right. right. repeat split.
      -- lia.
      -- apply clos_n_trans with (g 𝟘); trivial.
         apply clos_n_trans with (ν 𝟘); trivial.
         ++ now apply cgr_n_nu.
         ++ econstructor; constructor.
      -- now apply shift_nil.
    * lia.
- destruct H as [Heq|[p' [Hpp' Hp'q]]]; [inversion Heq|].
  dependent destruction Hpp'.
  + apply IH in Hp'q as (np & nq & Hge & Hnp & Hnq); [|lia| exact q].
    exists np, nq. repeat split; trivial. lia.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * apply IH in Hp as (np' & nq' & Hge & Hnp' & Hnq') ; [|lia|exact q].
      exists np', nq. repeat split; trivial; lia.
    * apply IH in Hp as (np' & nq' & Hge & Hnp' & Hnq') ; [|lia|exact q].
      exists np', nq'. repeat split; trivial; lia.
    * apply IH in Hp as (np' & nq' & Hge & Hnp' & Hnq') ; [|lia|exact q].
      exists np', nq'. repeat split; trivial; lia.
    * lia.
  + apply IH in Hp'q as (np & nq & Hge & Hnp & Hnq); [|lia| exact q].
    exists np, nq. repeat split.
    * lia.
    * admit.
    * trivial.
  + exists 0, n. repeat split.
    * lia.
    * constructor.
    * trivial.
  + apply IH in Hp'q as (np & nq & Hge & Hnp & Hnq); [|lia| exact q].
    exists (S np)%nat, nq. repeat split.
    * lia.
    * econstructor; eassumption.
    * trivial.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * apply IH in Hp as (np' & nq' & Hge' & Hnp' & Hnq'); [|lia| exact q].
    *
    *
    * lia.
Qed.
*)

Lemma cgr_n_par_guard p q g0 n : (clos_n cgr_step n (p ‖ q) (g g0) ->
  exists np nq,
   (n >= (np + nq + 2)%nat /\ (clos_n cgr_step np p (g 𝟘) /\ clos_n cgr_step nq q (g g0)) \/
   (n >= (np + nq + 2)%nat /\ clos_n cgr_step np p (g g0) /\ clos_n cgr_step nq q (g 𝟘)) \/
   (n >= (np + 1)%nat /\ clos_n cgr_step np p (g g0) /\ q = g 𝟘))) /\
  (clos_n cgr_step n (ν p) (g g0) ->
    (exists np nq, n >= (np + nq + 1)%nat /\ clos_n cgr_step np p (g 𝟘) /\ clos_n cgr_step nq 𝟘 g0) \/
    (exists np, n >= (np + 2)%nat /\ clos_n cgr_step np p (⇑ g0))).
Proof.
(* by strong induction *)
revert p q g0. induction n as [n IH] using lt_wf_ind; intros p q g0.
destruct n as [|n]; [split; intro H; inversion H|].
split; intro H; apply clos_n_S_inv in H.
- destruct H as [Heq | [p' [Hpp' Hp'q]]]; [inversion Heq|].
  dependent destruction Hpp'.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * exists (S np), nq. left. repeat split; [lia| |]; trivial.
      apply clos_n_S, Hp.
    * exists (S np), nq. right. left. repeat split; [lia| |]; trivial.
      apply clos_n_S, Hp.
    * inversion Hq; subst. exists (S np), 0. right; right.
      repeat split; trivial.
      -- lia.
      -- apply clos_n_S, Hp.
    * constructor.
  + exists n, 0. right. right. repeat split; [lia|]; trivial.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists (S (S np')), (nq' + nq)%nat. left.
         repeat split; [lia| |].
         ++ apply clos_n_S, clos_n_S, Hp'.
         ++ now apply clos_n_trans with (g 𝟘).
      -- exists (np' + nq)%nat, (S (S nq')). right. left.
         repeat split; [lia| |].
         ++	now apply clos_n_trans with (g 𝟘).
         ++ apply clos_n_S, clos_n_S, Hq'.
      -- subst. exists (np' + nq)%nat, 0. right. right.
         repeat split; [lia|]; trivial.
         apply clos_n_trans with (g 𝟘); trivial.
      -- lia.
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', nq'. left.
         repeat split; [lia| |]; trivial.
      -- exists np', nq'. right. left. repeat split; [lia| |]; trivial.
      -- inversion Hq'; subst. exists np', 0. right; right.
         repeat split; trivial. lia.
      -- lia.
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', nq'. left. repeat split; [lia| |]; trivial.
      -- exists np', nq'. right. left. repeat split; trivial. lia.
      -- inversion Hq'; subst. exists np', 0. right; right.
         repeat split; trivial. lia.
      -- lia.
    * lia.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * exists nq, np. right. left. repeat split; trivial. lia.
    * exists nq, np. left. repeat split; trivial. lia.
    * inversion Hq; subst. exists 0, np. left. repeat split; trivial. lia. constructor.
    * lia.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * apply IH in Hq as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists (np + (2 + np'))%nat, nq'. left. repeat split; trivial. lia.
         apply clos_n_trans with (g 𝟘 ‖ q0).
         ++ apply cgr_n_par_l, Hp.
         ++ apply clos_n_step with (q0 ‖ g 𝟘); [constructor|].
            apply clos_n_step with q0; [constructor|]; trivial.
      -- exists (np + S (S np'))%nat, nq'. right. left.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g 𝟘 ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_step with (q0 ‖ g 𝟘); [constructor|].
            apply clos_n_step with q0; [constructor|]. trivial.
      -- eexists (np + (2 + np'))%nat, 0; right; right.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g 𝟘 ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_step with (q0 ‖ g 𝟘); [constructor|].
            apply clos_n_step with q0; [constructor|]. trivial.
      -- lia.
    * apply IH in Hq as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists (np + ((2 + np') + 1))%nat, nq'. right. left.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g g0 ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_trans with (g g0 ‖ g 𝟘).
          ** now apply cgr_n_par_r.
          ** eapply clos_n_step; [|constructor]. constructor.
      -- exists (np + ((2 + np') + 1))%nat, nq'. right. left.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g g0 ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_trans with (g g0 ‖ g 𝟘).
          ** now apply cgr_n_par_r.
          ** eapply clos_n_step; [|constructor]. constructor.
      -- exists (np + ((2 + np') + 1))%nat, 0. right. right. repeat split; trivial; [lia|].
         apply clos_n_trans with (g g0 ‖ q0).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_trans with (g g0 ‖ g 𝟘).
          ** now apply cgr_n_par_r.
          ** eapply clos_n_step; [|constructor]. constructor.
      -- lia.
    * inversion Hq.
    * lia.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', (nq' + S (S nq))%nat. left. repeat split; trivial; [lia|].
         apply clos_n_trans with (g 𝟘 ‖ r).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_step with (r ‖ g 𝟘); [constructor|].
            apply clos_n_step with r; [constructor|]. trivial.
      -- exists np', (nq' + S (S nq))%nat. left. repeat split; trivial; [lia|].
         apply clos_n_trans with (g 𝟘 ‖ r).
         ++ now apply cgr_n_par_l.
         ++ apply clos_n_step with (r ‖ g 𝟘); [constructor|].
            apply clos_n_step with r; [constructor|]. trivial.
      -- exists np', (S (S nq)). left. repeat split; trivial; [lia|].
         inversion Hq'. apply clos_n_step with (r  ‖ g 𝟘);[constructor|].
         apply clos_n_step with r;[constructor|]. trivial.
      -- lia.
    * apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', (nq' + (S (S nq) + 1))%nat. left. repeat split; trivial; [lia|].
         apply clos_n_trans with (g g0 ‖ r); [now apply cgr_n_par_l|].
         apply clos_n_trans with (g g0 ‖ g 𝟘); [now apply cgr_n_par_r|].
         apply clos_n_step with (g g0); constructor.
      -- exists np', (nq' + (2 + nq))%nat. right. left.
         repeat split; trivial; [lia|].
         apply clos_n_trans with (g 𝟘 ‖ r); [now apply cgr_n_par_l|].
         apply clos_n_step with (r ‖ g 𝟘); [constructor|].
         apply clos_n_step with r; [constructor|]. trivial.
      -- exists np', (2 + nq)%nat. right. left.
         repeat split; trivial; [lia|]. inversion Hq'; subst.
         apply clos_n_step with (r ‖ g 𝟘); [constructor|].
         apply clos_n_step with r; [constructor|]. trivial.
      -- lia.
    * inversion Hq; subst.
      apply IH in Hp as (np' & nq' & [[Hnpq' [Hp' Hq']] | [[Hnpq' [Hp' Hq']] | [Hnpq' [Hp' Hq']]]]).
      -- exists np', (S nq'). left. repeat split; trivial; [lia|].
         apply clos_n_step with q0; [constructor|]. trivial.
      -- exists np', (S nq')%nat. right. left. repeat split; trivial; [lia|].
         apply clos_n_step with q0; [constructor|]. trivial.
      -- exists np', 1. right. left. repeat split; trivial; [lia|].
         inversion Hq'. apply clos_n_step with (g 𝟘); constructor.
      -- lia.
    * lia.
  + apply IH in Hp'q as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * exists (S np), nq. left. repeat split; [lia| |]; trivial.
      apply clos_n_step with q0; trivial.
    * exists (S np), nq. right. left. repeat split; [lia| |]; trivial.
      apply clos_n_step with q0; trivial.
    * exists (S np), nq. right. right. repeat split; [lia| |]; trivial.
      apply clos_n_step with q0; trivial.
    * constructor.
  + apply IH in Hp'q as [(np0 & nq0 & Hge & Hnp & Hg0)|(np0 & Hge & Hnp0)]; [| |lia|exact q].
    * apply IH in Hnp as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
      -- exists (np + 1 + nq0)%nat, nq. right. left. repeat split.
        ++ lia.
        ++ apply clos_n_trans with (g 𝟘); trivial.
           eapply clos_n_trans with (ν (g 𝟘)).
           ** apply cgr_n_nu, Hp.
           ** econstructor; constructor.
        ++ now apply clos_n_cgr_step_shift.
      -- exists (np + 1)%nat, (nq + nq0)%nat. left. repeat split.
        ++ lia.
        ++ apply clos_n_trans with (ν 𝟘); [|econstructor; constructor].
           now apply cgr_n_nu.
        ++ apply clos_n_trans with (g 𝟘); trivial.
           now apply clos_n_cgr_step_shift.
      -- exists (np + 1 + nq0)%nat, nq. right. right. repeat split.
        ++ lia.
        ++ apply clos_n_trans with (g 𝟘); trivial.
           apply clos_n_trans with (ν 𝟘); trivial.
           ** now apply cgr_n_nu.
           ** econstructor; constructor.
        ++ now apply shift_nil.
      -- lia.
  * apply IH in Hnp0 as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
      -- exists (np + 1)%nat, nq. left. repeat split.
        ++ lia.
        ++ apply clos_n_trans with (ν 𝟘); trivial.
           ** apply cgr_n_nu, Hp.
           ** econstructor; constructor.
        ++ now apply clos_n_cgr_step_shift.
      -- exists (np + 3)%nat, (nq)%nat. right; left. repeat split.
        ++ lia.
        ++ admit.
        ++ now apply clos_n_cgr_step_shift.
      -- exists (np + 3)%nat, nq. right. right. repeat split.
        ++ lia.
        ++ admit.
        ++ now apply shift_nil.
      -- lia.
- destruct H as [Heq|[p' [Hpp' Hp'q]]]; [inversion Heq|].
  dependent destruction Hpp'.
  + apply IH in Hp'q as [(np & nq & Hge & Hnp & Hnq)|(np & Hge & Hnp)]; [| |lia| exact q].
    * left. exists np, nq. repeat split; trivial. lia.
    * right. exists np. split; trivial. lia.
  + apply IH in Hp'q as (np' & nq' & [[Hnpq' [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * apply IH in Hp as [(np & nq & Hge & Hnp & Hnq)|(np & Hge & Hnp)]; [| |lia| exact q].
      -- right. exists (np + nq')%nat.
         split. lia. eapply clos_n_trans; try eassumption.
         admit. (* lemma about all substitutions *)
      -- right. exists (np + nq')%nat.
         split. lia. eapply clos_n_trans; try eassumption.
         admit.
    * apply IH in Hp as [(np & nq & Hge & Hnp & Hnq)|(np & Hge & Hnp)]; [| |lia| exact q].
      -- right. exists (np + nq)%nat.
         split. lia. eapply clos_n_trans; try eassumption.
         admit. (* lemma about all substitutions *)
      -- right. exists (np)%nat.
         split. lia. eassumption.
    * apply IH in Hp as [(np & nq & Hge & Hnp & Hnq)|(np & Hge & Hnp)]; [| |lia| exact q].
      -- right. exists (np + nq)%nat.
         split. lia. eapply clos_n_trans; try eassumption.
         admit. (* lemma about all substitutions *)
      -- right. exists (np)%nat.
         split. lia. eassumption.
    * lia.
  + apply IH in Hp'q as [(np & nq & Hge & Hnp & Hnq)|(np & Hge & Hnp)]; [| |lia| exact q].
    * left. exists np, nq. repeat split.
      -- lia.
      -- admit. (* not so trivial. one more IH? *)
      -- trivial.
    * right. exists np. split. lia. admit. (* same *)
  + left. exists 0, n. repeat split.
    * lia.
    * constructor.
    * trivial.
  + apply IH in Hp'q as [(np & nq & Hge & Hnp & Hnq)|(np & Hge & Hnp)]; [| |lia| exact q].
    * left. exists (S np), nq. repeat split.
      -- lia.
      -- econstructor; eassumption.
      -- eassumption.
    * right. exists (S np). repeat split.
      -- lia.
      -- econstructor; eassumption.
  + apply IH in Hp'q as (np' & nq' & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
    * apply IH in Hp as [(np & nq & Hge & Hnp & Hnq)|(np & Hge & Hnp)]; [| |lia| exact q].
      -- right. exists (np + S (S nq'))%nat. repeat split.
        ++ lia.
        ++ apply clos_n_trans with (𝟘 ‖ ⇑ Q).
          ** now apply cgr_n_par_l.
          ** apply clos_n_step with (⇑ Q ‖ 𝟘 ); [constructor|].
             apply clos_n_step with (⇑ Q); [constructor|].
             admit. (* subst lemma *)
      -- right. exists (np + S (S nq'))%nat. split. lia.
         apply clos_n_trans with (𝟘 ‖ ⇑ Q); [now apply cgr_n_par_l|].
         apply clos_n_step with (⇑ Q ‖ 𝟘); [constructor|].
         apply clos_n_step with (⇑ Q); [constructor|].
         admit. (*subst lemma *)
    * apply IH in Hp as [(np & nq & Hge & Hnp & Hnq)|(np & Hge & Hnp)]; [| |lia| exact q].
      -- left. exists (S (S nq') + S np)%nat, nq. repeat split.
        ++ lia.
        ++ apply clos_n_trans with (P ‖ g 𝟘).
           ** apply cgr_n_par_r. admit.  (*subst lemma *)
           ** eapply clos_n_step; [|eassumption]. constructor.
        ++ assumption.
      -- right. exists (S (S nq') + S np)%nat. split. lia.
         apply clos_n_trans with (P ‖ 𝟘).
         ++ apply cgr_n_par_r. admit. (*subst lemma *)
         ++ eapply clos_n_step; [|eassumption]. constructor.
    * subst.
      apply IH in Hp as [(np & nq & Hge & Hnp & Hnq)|(np & Hge & Hnp)]; [| |lia| exact q].
      -- left. exists (S np), nq. repeat split.
        ++ lia.
        ++ apply clos_n_step with P; [constructor|trivial].
        ++ trivial.
      -- right. exists (S np). split. lia. apply clos_n_step with P; [constructor|trivial].
    * lia.
Admitted.

Lemma cgr_n_par_nil_l p q n: clos_n cgr_step n (g p ‖ g 𝟘) (g q) ->
  clos_n cgr_step n (g p) (g q).
Proof.
intro Hp. apply cgr_n_par_guard in Hp
  as (np & nq & [[Hnpq [Hp Hq]] | [[Hnpq [Hp Hq]] | [Hnpq [Hp Hq]]]]).
- assert (Hle : (np + nq)%nat <= n) by lia.
  unshelve eapply (clos_n_le _ Hle).
  eapply clos_n_trans; eassumption.
- apply (clos_n_le Hp). lia.
- apply (clos_n_le Hp). lia.
Qed.

Lemma cgr_n_nu_nil_l p q n: clos_n cgr_step n (ν p) (g q) ->
  clos_n cgr_step n (p) (g q).
Proof.
intro Hp. apply cgr_n_par_guard in Hp
  as (np & nq & [Hnpq [Hp Hq]]); [|exact p].
assert (Hle : (np + nq)%nat <= n) by lia.
unshelve eapply (clos_n_le _ Hle).
eapply clos_n_trans; eassumption.
Qed.

Lemma cgr_choice : forall p q r, g p ≡* g q -> p + r ≡* q + r.
Proof.
(* By induction on the __length__ of the cgr-derivation *)
intros p q r H. apply clos_trans_clos_n in H as [n Hn].
revert n p q r Hn. induction n as [|n]; intros p q r Hn;
[inversion Hn; subst; reflexivity|].
apply clos_n_S_inv in Hn as [Heq|[p' [Hpp' Hp'q]]]; [now inversion Heq|].
dependent destruction Hpp';
try solve[etransitivity; [|eapply IHn; eauto]; repeat constructor].
- apply IHn, cgr_n_par_nil_l, Hp'q.
- transitivity (g (t • q0 + r)); [repeat constructor| apply IHn]; trivial.
- transitivity (g (c ? q0 + r)); [repeat constructor| apply IHn]; trivial.
- transitivity (g (c ! v • q0 + r)); [repeat constructor| apply IHn]; trivial.
- transitivity (g (q1 + p2 + r)); [repeat constructor| apply IHn]; trivial.
- apply IHn. apply cgr_n_nu_nil_l, Hp'q.
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
