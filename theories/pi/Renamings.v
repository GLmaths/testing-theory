
Require Export signatures.pi.
Require Export signatures.unscoped.
Require Import Relations Morphisms.
Arguments core.funcomp _ _ _/.

(** Notation for π calculus terms *)
Notation "x ∨ y" := (Or x y) (at level 50).
Notation "x ⩽ y" := (Inequality x y) (at level 50).

Notation "c ⋉ v" := (act c v) (at level 50).
Definition τ := tau_action.

Notation "①" := (gpr_success).
Notation "𝟘" := (gpr_nil).
Notation "P + Q" := (gpr_choice P Q).
Notation "c ! v • P" := (gpr_output c v P) (at level 50).
Notation "c ? P" := (gpr_input c P) (at level 50).
Notation "'t' • P" := (gpr_tau P) (at level 50).
Notation "'rec' p" := (pr_rec p) (at level 50).
Notation "P ‖ Q" := (pr_par P Q) (at level 60).
Notation "'ν' P" := (pr_res P) (at level 50).
Notation "'If' C 'Then' P 'Else' Q" := (pr_if_then_else C P Q)
(at level 200, right associativity, format
"'[v   ' 'If'  C '/' '[' 'Then'  P  ']' '/' '[' 'Else'  Q ']' ']'").

Coercion g : gproc >-> proc.

Definition νs n := Nat.iter n (fun p => ν p).

(** Notations for renamings and substitutions *)
Notation "tm [ s1 ; s2 ]" :=
  (subst2 s1 s2 tm) (at level 10, right associativity) : subst_scope.
Notation "tm [ s ]" :=
  (subst1 s tm) (at level 10, right associativity) : subst_scope.
Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.
Notation "f >> g" := (fun x => g (f x)) (at level 50) : subst_scope.
Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at next level, right associativity) : subst_scope.
Open Scope subst_scope.
Notation "⋅" := ids.
Notation "tm ⟨ r ⟩" := (ren2 ids r tm) (at level 20).

Coercion cst : Value >-> Data.
Coercion var_Data : nat >-> Data.
Coercion var_proc : nat >-> proc.

(** Autosubst doesn't generate these for Action, since it doesn't contain bound variables *)

Definition ren_Act (xi : nat -> nat) (a : Act) : Act :=
  match a with
  | ActIn (act d1 d2) => ActIn (act (ren_Data xi d1) (ren_Data xi d2))
  | FreeOut (act d1 d2) => FreeOut (act (ren_Data xi d1) (ren_Data xi d2))
  | BoundOut d1 => BoundOut (ren_Data xi d1)
  | tau_action => tau_action
 end.

Lemma compRenRen_Act (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat)
  (Eq_Act : forall x, core.funcomp zeta xi x = rho x) (s : Act) :
  ren_Act zeta (ren_Act xi s) = ren_Act rho s.
  Proof.
  destruct s; try destruct e.
  - simpl. f_equal. f_equal; now apply compRenRen_Data.
  - simpl. f_equal. f_equal; now apply compRenRen_Data.
  - simpl. f_equal. now apply compRenRen_Data.
  - reflexivity.
Qed.

Lemma renRen_Act (xi : nat -> nat) (zeta : nat -> nat) (a : Act)
  :
  ren_Act zeta (ren_Act xi a) =
  ren_Act (core.funcomp zeta xi) a.
Proof.
exact (compRenRen_Act xi zeta _ (fun n => eq_refl) a).
Qed.

#[global] Instance Ren_Act : (Ren1 _ _ _) := @ren_Act.

(** Definition and properties of swap and shift renaming *)

Definition swap : nat -> nat := 1 .: (0 .: (shift >> shift >> ids)).

Lemma swap_involutive : (pointwise_relation _ eq) (swap >> swap) ids.
Proof.
  intros [|[|x]]; reflexivity.
Qed.

Lemma shift_shift_swap : forall x, (shift >> shift >> swap) x = (shift >> shift) x.
Proof.
  intros [|[|x]]; reflexivity.
Qed.

Definition injective (σ : nat -> nat) :=
  forall x y, σ x = σ y -> x = y.

Lemma Shift_Injective : injective shift.
Proof.
  intros x y H. now inversion H.
Qed.

Lemma Swap_Injective : injective swap.
Proof.
  assert (Aux: forall y, 1 <> ((0 .: (fun x : nat => ⋅ (shift (shift x)))) y) )
  by (destruct y; [ now simpl | intro H; inversion H ]).
  assert (Aux2: injective (0 .: (fun x0 : nat => ⋅ (shift (shift x0)))))
  by (intros x y H; destruct x,y; inversion H; trivial).
  intros x y H. 
  induction x, y.
  - trivial.
  - simpl in H. apply Aux in H. contradiction.
  - simpl in H. apply eq_sym, Aux in H. contradiction.
  - simpl in H. apply Aux2 in H. now rewrite H.
Qed.

(* uses morphisms instances to avoid functional extensionality *)
Lemma Swap_Proc_Involutive : forall p, p ⟨swap⟩ ⟨swap⟩ = p.
Proof.
asimpl. intro p. rewrite swap_involutive. now asimpl.
Qed.

Class Shiftable (A : Type) := shift_op : A -> A.
Instance Shift_proc : Shiftable proc := ren2 ids shift.
Instance Shift_Data : Shiftable Data := ren1 shift.
Instance Shift_Act  : Shiftable Act := ren1 shift.
Notation "⇑" := shift_op.

Lemma Shift_Op_Injective : forall (d1 d2: Data),
  ⇑ d1 = ⇑ d2 -> d1 = d2.
Proof.
unfold shift_op, Shift_Data, ren1, Ren_Data, ren_Data.
intros. destruct d1, d2; inversion H; trivial.
Qed.

Definition nvars {A: Type} `{_ : Shiftable A} (n : nat) : A -> A :=
  Nat.iter n (⇑).

Lemma shift_in_nvars {A : Type} `{Shiftable A}:
  forall n (q:A), ⇑ (nvars n q) = nvars n (⇑ q).
Proof.
induction n.
- now simpl.
- intros. simpl. now rewrite IHn.
Qed.

Lemma permute_subst : forall sp s Q,
  (⇑ Q) [(up_Data_proc sp); (up_Data_Data s)]
  =
  ⇑ (Q [sp; s]).
Proof. now asimpl. Qed.

Lemma permute_ren : forall sp s Q,
  ren2 (upRen_Data_proc sp) (upRen_Data_Data s) (⇑ Q)
  =
  ⇑ (ren2 sp s Q).
Proof. now asimpl. Qed.

Lemma permute_ren1 : forall s (d:Data),
  ren1 (up_ren s) (⇑ d) = ⇑ (ren1 s d).
Proof. now asimpl. Qed.

Lemma Shift_Shift_Swap_pr : forall p, (⇑ (⇑ p)) ⟨swap⟩ = ⇑ (⇑ p).
Proof. now asimpl. Qed.

Lemma Shift_Shift_Swap_Data : forall (d: Data), ren1 swap (⇑ (⇑ d)) = ⇑ (⇑ d).
Proof. now asimpl. Qed.

Lemma Shift_Shift_Swap_Act : forall x, ren1 swap (⇑ (⇑ x)) = ⇑ (⇑ x).
intro x. asimpl. unfold Ren_Act, ren_Act, shift_op, Shift_Act.
destruct x; try destruct e; asimpl; simpl.
- f_equal; f_equal; asimpl; reflexivity.
- f_equal; f_equal; asimpl; reflexivity.
- f_equal; asimpl; reflexivity.
- f_equal; f_equal; asimpl; reflexivity.
Qed.

Lemma Shift_Swap : forall (p:proc), (⇑ p) ⟨swap⟩ = p ⟨up_ren shift⟩.
Proof. asimpl. unfold core.funcomp. simpl. now asimpl. Qed.
