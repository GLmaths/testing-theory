




(* 

(* Induction schemes *)


Scheme proc_gproc_ind := Induction for proc Sort Prop
  with gproc_proc_ind := Induction for gproc Sort Prop.

(* Combined Scheme proc_gproc_mutind from proc_gproc_ind,gproc_proc_ind. (*not usefull with our situation *) *)

(*Require Import FunInd.

Function size2 (p : proc) := 
  match p with
  | p ‖ q  => S (size2 p + size2 q)
  | pr_var _ => 1
  | If C Then p Else q => S (size2 p + size2 q)
  | rec x • p => S (size2 p)
  | c ! v • 𝟘 => 1
  | g ① => 1
  | g 𝟘 => 0
  | g (c ? x • p) => 0 (*S (size2 p)*)
  | g (t • p) => 0 (*S (size2 p)*)
  | g (p + q) => 0 (*S (size2 (g p) + size2 (g q))*)
  end.

Check size2_ind.

Functional Scheme size_ind := Induction for size2 Sort Prop.

Check size_ind.

Function size3 (p : proc) := 
  match p with
  | p ‖ q  => S (size3 p + size3 q)
  | pr_var _ => 1
  | If C Then p Else q => S (size3 p + size3 q)
  | rec x • p => S (size3 p)
  | c ! v • 𝟘 => 1
  | g p => gsize3 p
  end

with gsize3 p :=
  match p with
  | ① => 1
  | 𝟘 => 0
  | c ? x • p => S (size3 p)
  | t • p => S (size3 p)
  | p + q => S (gsize3 p + gsize3 q)
end.

Check size3_ind.

(* error if size3 is Fixpoint *) 
Functional Scheme size33_ind := Induction for size3 Sort Prop.
Functional Scheme gsize33_ind := Induction for gsize3 Sort Prop.
Check size33_ind.


Functional Scheme proc_size_ind3 := Induction for size3 Sort Prop
with gproc_size_ind2 := Induction for gsize3 Sort Prop.

Check proc_size_ind3. *)

Definition PPS (P : proc -> Prop) (p : gproc) := P (g p).

Lemma proc_gproc_myinduction : ∀ (P : proc → Prop),
         (∀ p : proc, P p → ∀ p0 : proc, P p0 → P (p ‖ p0))
         → (∀ n : nat, P n)
           → (∀ (n : nat) (p : proc), P p → P (rec n • p))
             → (∀ (e : Equation Data) (p : proc), P p → ∀ p0 : proc, P p0 → P (If e
                                                                                Then p 
                                                                                Else p0))
               → (∀ (c : Channel) (d : Data), P (c ! d • 𝟘))
                 → (∀ g0 : gproc, P (g g0) → P g0)
                   → P (g ①)
                     → P (g 𝟘)
                       → (∀ (c : Channel) (p : proc), P p → P (g (gpr_input c p)))
                         → (∀ p : proc, P p → P (g (t • p)))
                           → (∀ g1 : gproc, P (g g1) → ∀ g0 : gproc, P (g g0) → P (g (g1 + g0))) → ∀ p : proc, P p.
Proof.

intros. revert p. eapply proc_gproc_ind.
- eauto.
- eauto.
- eauto.
- eauto.
- eauto.
- intros. instantiate (1 := PPS P) in H10. unfold PPS in H10. eauto.
- intros. unfold PPS. eauto.
- intros. unfold PPS. eauto.
- intros. unfold PPS. eauto.
- intros. unfold PPS. eauto.
- intros. unfold PPS. eauto.
Qed.


(*
(* Version with the induction principle with the same P for proc and gproc *)
induction p,(size3) using proc_gproc_myinduction; intros; simpl.
(* have to specify P0 with functional induction (size3 p) *)

- apply cgr_fullpar.
    apply IHn. assumption. 
    apply IHn0. assumption. 
- destruct (decide (x = _x)). assumption. reflexivity.
- apply cgr_full_if.
    apply IHn. assumption.
    apply IHn0. assumption.
- destruct (decide (x0 = x)).
    * reflexivity.
    * apply cgr_recursion. eapply IHn. assumption.
- eauto with cgr.
- eauto.
- reflexivity.
- reflexivity.
- apply cgr_input. eapply IHn. apply NewVar_Respects_Congruence. assumption.
- apply cgr_tau. eapply IHn. assumption.
- apply cgr_fullchoice. 
  * eapply IHn. assumption.
  * eapply IHn0. assumption. *)


(* Version with the induction principle (not with dependent *)
(*
functional induction (size3 p) using size3_ind; intros; simpl; auto.

- apply cgr_fullpar.
    apply IHn. assumption. 
    apply IHn0. assumption. 
- destruct (decide (x = _x)). assumption. reflexivity.
- apply cgr_full_if.
    apply IHn. assumption.
    apply IHn0. assumption.
- destruct (decide (x0 = x)).
    * reflexivity.
    * apply cgr_recursion. eapply IHn. assumption.
- eauto with cgr.
- (* cant move forward due to dependent inductive types *) 
*)


(* Version with the mutual induction principle *)
(*
einduction p using proc_gproc_ind; simpl;  intros.

- apply cgr_fullpar.
    apply IHp0_1. assumption. 
    apply IHp0_2. assumption. 
- destruct (decide (x = n)). assumption. reflexivity.
- destruct (decide (x = n)). reflexivity. apply cgr_recursion. apply IHp0. assumption.
- apply cgr_full_if.
    apply IHp0_1. assumption.
    apply IHp0_2. assumption.
- eauto with cgr.
- instantiate (1 := cgr_subst2) in IHp0.
  unfold cgr_subst2 in IHp0. apply IHp0. assumption.
- unfold cgr_subst2. simpl; intros. auto with cgr.
- unfold cgr_subst2. simpl; intros. auto with cgr.
- unfold cgr_subst2. simpl; intros. apply cgr_input. apply IHp0. apply NewVar_Respects_Congruence. assumption.
- unfold cgr_subst2. simpl; intros. apply cgr_tau. apply IHp0. assumption.
- unfold cgr_subst2. simpl; intros. apply cgr_fullchoice.
  * unfold cgr_subst2 in IHp0. apply IHp0. assumption.
  * unfold cgr_subst2 in IHp1. apply IHp1. assumption. *)
 
einduction p using proc_gproc_myinduction; simpl;  intros.

- apply cgr_fullpar.
    apply IHp0_1. assumption. 
    apply IHp0_2. assumption. 
- destruct (decide (x = n)). assumption. reflexivity.
- destruct (decide (x = n)). reflexivity. apply cgr_recursion. apply IHp0. assumption.
- apply cgr_full_if.
    apply IHp0_1. assumption.
    apply IHp0_2. assumption.
- eauto with cgr.
- apply IHp0. assumption.
- reflexivity.
- reflexivity.
- apply cgr_input. apply IHp0. apply NewVar_Respects_Congruence. assumption.
- apply cgr_tau. apply IHp0. assumption.
- apply cgr_fullchoice.
  * apply IHp0. assumption.
  * apply IHp1. assumption.

(*  (* Old version *)
(* Induction on the size of p*)
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros; simpl.
  - apply cgr_fullpar.
    apply Hp. simpl. auto with arith. assumption. 
    apply Hp. simpl. auto with arith. assumption. 
  - destruct (decide (x = n)). assumption. reflexivity.
  - destruct (decide (x = n)). reflexivity. apply cgr_recursion. apply Hp. simpl. auto. assumption.
  - apply cgr_full_if.
    apply Hp. simpl. auto with arith. assumption. 
    apply Hp. simpl. auto with arith. assumption.  
  - eauto with cgr.
  - destruct g0; simpl.
    * reflexivity.
    * reflexivity.
    * apply cgr_input. apply Hp. simpl. auto with arith. apply NewVar_Respects_Congruence. assumption.
    * apply cgr_tau. apply Hp. simpl. auto with arith. assumption.
    * apply cgr_fullchoice. 
      assert (pr_subst x (g g0_1) q ≡* pr_subst x (g g0_1) q'). apply Hp. simpl. auto with arith. assumption.
      auto. assert (pr_subst x (g g0_2) q ≡* pr_subst x (g g0_2) q'). apply Hp. simpl. auto with arith. assumption. 
      auto. *)
Qed.


Scheme proc_ind0 := Induction for proc Sort Prop
with gproc_ind0 := Induction for gproc Sort Prop.

Combined Scheme proc_ind' from proc_ind0, gproc_ind0.

Local Definition proc_Prop (P : proc -> Prop) := 
  (forall p, P p) /\ (forall q, P (g q)).

Ltac my_proc_ind p :=
match goal with |- ?Q ?p => idtac Q;
  enough (X : proc_Prop Q); [apply X | apply proc_ind'] end.

(* Demonstrate how to use the my_proc_ind tactic *)
Goal (forall p : proc, p = p).
intro p.
my_proc_ind p.
Abort. *)

