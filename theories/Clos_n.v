(** Reflexive transitive closure with embedded length parameter *)

From Coq Require Import Relations Program.Equality.
From stdpp Require Import base.

Set Implicit Arguments.

Inductive clos_n {A : Type} (R : relation A) : nat -> relation A :=
| clos_n_refl : forall x, clos_n R 0 x x
| clos_n_step : forall n x y z, R x y -> clos_n R n y z -> clos_n R (S n) x z.

Lemma clos_trans_clos_n {A : Type} (R : relation A) : 
 forall x y, clos_trans A R x y -> exists n, clos_n R n x y.
Proof.
intros x y H. apply clos_trans_t1n in H.
induction H.
- exists 1. econstructor; eauto. constructor.
- destruct IHclos_trans_1n as (n1 & Hn1).
  exists (S n1). econstructor; eauto.
Qed.

Lemma clos_n_clos_trans `{_ : Reflexive A R} :
 forall x y n, clos_n R n x y -> clos_trans A R x y.
Proof.
induction 1 as [|n].
- now constructor.
- eapply t_trans; eauto. now constructor.
Qed.

Lemma clos_n_S_inv {A : Type} (R : relation A) x y n:
  clos_n R (S n) x y -> x = y \/ (exists z, R x z /\ clos_n R n z y).
Proof. intro H. dependent destruction H; eauto. Qed.

(* At most n transitions implies at most S n transitions *)
Lemma clos_n_S `{_ : Reflexive A R} x y n:
  clos_n R n x y -> clos_n R (S n) x y.
Proof. induction 1; econstructor; eauto. constructor. Qed.

Lemma clos_n_le `{_ : Reflexive A R} {x y n m}:
  clos_n R n x y -> n <= m -> clos_n R m x y.
Proof.
  intros Hxy Hle. revert Hxy. induction Hle; trivial. intro.
  now apply clos_n_S, IHHle.
Qed.

Lemma clos_n_trans `{_ : Reflexive A R} x y z n p:
  clos_n R n x y -> clos_n R p y z -> clos_n R (n + p) x z.
Proof.
revert x y z p. induction n; intros x y z p Hxy Hyz.
- inversion Hxy; subst. apply Hyz.
- apply clos_n_S_inv in Hxy as [Heq | [z' [Hxz' Hz'y]]].
  + subst. apply (clos_n_le Hyz). apply PeanoNat.Nat.le_add_l.
  + simpl. apply clos_n_step with z'; trivial. eapply IHn; eauto.
Qed.
