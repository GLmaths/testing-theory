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

Definition injective (σ : nat -> nat) :=
  forall x y, σ x = σ y -> x = y.

Lemma Injective_UpRen : forall (σ : nat -> nat),
  injective σ -> injective (up_ren σ).
Proof.
intros σ Hinj.
intros [|n0] [|n1] H; trivial; inversion H.
apply Hinj in H1. now rewrite H1.
Qed.

Lemma Injective_Ren_Data : forall (σ : nat -> nat),
  injective σ -> forall d1 d2 : Data, ren1 σ d1 = ren1 σ d2 -> d1 = d2.
Proof.
intros σ Hinj d1 d2 Heq.
destruct d1, d2; inversion Heq; try reflexivity; now rewrite (Hinj n0 n).
Qed.

Lemma Injective_Ren_Equation : forall (σ : nat -> nat),
  injective σ -> forall e1 e2 : Equation, ren_Equation σ e1 = ren_Equation σ e2 -> e1 = e2.
Proof.
intros σ Hinj e1 e2 Heq. revert σ Hinj Heq. revert e2.
induction e1; intros; destruct e2; inversion Heq; try reflexivity.
- apply Injective_Ren_Data in H0, H1. now subst. exact Hinj. exact Hinj.
- erewrite IHe1_1, IHe1_2. reflexivity.
  exact Hinj. exact H1. exact Hinj. exact H0.
- erewrite IHe1. reflexivity.
  exact Hinj. exact H0.
Qed.

Lemma Injective_Ren_Proc : forall p1 p2 : proc, 
  forall (σ : nat -> nat), injective σ -> p1 ⟨σ⟩ = p2 ⟨σ⟩ -> p1 = p2
with Injective_Ren_GProc : forall g1 g2 : gproc, 
  forall (σ : nat -> nat), injective σ -> g1 ⟨σ⟩ = g2 ⟨σ⟩ -> g1 = g2.
Proof.
intros p1. induction p1; intros; destruct p2; inversion H0.
- exact H0.
- f_equal.  unfold upRen_proc_proc, upRen_proc_Data in H2.
  assert (Hrew: pointwise_relation _ eq (up_ren ⋅) ids) by now intros [|n].
  rewrite Hrew in H2.
  eapply IHp1. apply H. exact H2.
- f_equal. eapply IHp1_1. apply H. exact H2.
  eapply IHp1_2. apply H. exact H3.
- f_equal. unfold upRen_Data_proc, upRen_Data_Data in H2.
  eapply IHp1. apply Injective_UpRen. exact H. exact H2.
- f_equal.
  + now apply Injective_Ren_Equation in H2.
  + eapply IHp1_1. exact H. exact H3.
  + eapply IHp1_2. exact H. exact H4.
- f_equal. eapply Injective_Ren_GProc. exact H. exact H2.
- intro g1. induction g1; intros; destruct g2; inversion H0.
+ reflexivity.
+ reflexivity.
+ apply Injective_Ren_Data in H2, H3. apply Injective_Ren_Proc in H4. now subst.
  exact H. exact H. exact H.
+ apply Injective_Ren_Data in H2. unfold upRen_Data_Data in H3.
  apply Injective_Ren_Proc in H3. now subst.
  apply Injective_UpRen. exact H. exact H.
+ apply Injective_Ren_Proc in H2. now subst. exact H.
+ erewrite IHg1_1, IHg1_2. reflexivity.
  exact H. exact H3. exact H. exact H2.
Qed.

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
Instance Shift_gproc : Shiftable gproc := ren2 ids shift.
Instance Shift_Data : Shiftable Data := ren1 shift.
Instance Shift_Act  : Shiftable Act := ren1 shift.
Notation "⇑" := shift_op.

Definition nvars {A: Type} `{_ : Shiftable A} (n : nat) : A -> A :=
  Nat.iter n (⇑).

Lemma Shift_to_Ren : forall (p:proc) n, nvars n p = p ⟨Nat.iter n shift⟩.
Proof.
intros p n. induction n.
- now asimpl.
- simpl. rewrite IHn. now asimpl.
Qed.

Lemma Shift_to_Ren_Data : forall (d:Data) n, nvars n d = ren1 (Nat.iter n shift) d.
Proof.
intros p n. induction n.
- now asimpl.
- simpl. rewrite IHn. now asimpl.
Qed.

Lemma nvars_sum : forall n m {A: Type} `{_ : Shiftable A} (q:A),
  nvars n (nvars m q) = nvars (n + m) q.
Proof.
intros n m A Hq. induction n.
- now simpl.
- intros. simpl. now rewrite IHn.
Qed.

Lemma Push_nvars_output: forall n c v P,
  nvars n (c ! v • P) = (nvars n c) ! (nvars n v) • (nvars n P).
Proof.
intros. induction n; simpl; auto.
rewrite IHn. reflexivity.
Qed.

Lemma Push_nvars_par: forall n P Q,
  nvars n (P ‖ Q) = (nvars n P) ‖ (nvars n Q).
Proof.
intros. induction n. trivial. simpl. now rewrite IHn.
Qed.

Lemma Push_nvars_choice: forall n P Q,
  nvars n (g (P + Q)) = (nvars n  P) + (nvars n Q).
Proof.
intros. induction n. trivial. simpl. now rewrite IHn.
Qed.

Lemma Push_nvars_FreeOut : forall n c v, nvars n (FreeOut (c ⋉ v)) = FreeOut (nvars n c ⋉ nvars n v).
Proof.
intros n c v.
induction n; simpl; try reflexivity.
rewrite IHn. reflexivity.
Qed.

Lemma Push_nvars_ActIn : forall n c v, nvars n (ActIn (c ⋉ v)) = ActIn (nvars n c ⋉ nvars n v).
Proof.
intros n c v.
induction n; simpl; try reflexivity.
rewrite IHn. reflexivity.
Qed.

Lemma Push_nvars_BoundOut : forall n v, nvars n (BoundOut  v) = BoundOut (nvars n v).
Proof.
intros n v.
induction n; simpl; try reflexivity.
rewrite IHn. reflexivity.
Qed.

Lemma shift_in_nvars {A : Type} `{Shiftable A}:
  forall n (q:A), ⇑ (nvars n q) = nvars n (⇑ q).
Proof.
induction n.
- now simpl.
- intros. simpl. now rewrite IHn.
Qed.

Lemma Shift_Permute_Subst : forall sp s Q,
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

Lemma shift_permute : forall p σ,
  p ⟨σ⟩ ⟨shift⟩ = p ⟨shift⟩ ⟨up_ren σ⟩.
Proof. now asimpl. Qed.

Lemma shift_permute_Data : forall (v:Data) σ,
  ren1 shift (ren1 σ v) = ren1 (up_ren σ) (ren1 shift v).
Proof. now asimpl. Qed.

(** Autosubst should solve this? *)
Lemma shift_permute_Action : forall (a:Act) σ,
  ren1 shift (ren1 σ a) = ren1 (up_ren σ) (ren1 shift a).
Proof.
intros.
unfold ren1, Ren_Act.
now repeat rewrite renRen_Act.
Qed.

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

Lemma Invert_Shift : forall (c: Data) c' σ,
  ⇑ c = ren1 (up_ren σ) c' -> exists c'', c' = ⇑ c''.
Proof.
intros c c' σ Heq.
assert (H1 : ⇑ c <> 0) by  (destruct c; intro H; now inversion H).
rewrite Heq in H1.
assert (H2 : c' <> 0) by
(intro Hdiff; rewrite Hdiff in H1; asimpl in H1; contradiction).
destruct c'.
- destruct n; [contradiction|]. now exists n.
- now exists v.
Qed.

Lemma Invert_Bound_Out : forall (α:Act) c,
   BoundOut c = ⇑ α -> exists d, c = ⇑ d /\ α = BoundOut d.
Proof.
intros. destruct α; try destruct e; inversion H.
now exists d.
Qed.

Lemma Up_Up_Swap : forall (p: proc) σ,
  p ⟨swap⟩ ⟨up_ren (up_ren σ)⟩ = p ⟨up_ren (up_ren σ)⟩ ⟨swap⟩.
Proof. intros. asimpl. now simpl. Qed.

Lemma Up_Up_Subst_Swap : forall (p: proc) σ1 σ2,
  ((p ⟨swap⟩) [(up_Data_proc (up_Data_proc σ1)); (up_Data_Data (up_Data_Data σ2))])
  =
  (p [(up_Data_proc (up_Data_proc σ1)); (up_Data_Data (up_Data_Data σ2))] ⟨swap⟩).
Proof.
intros. asimpl. simpl. apply subst_proc_morphism.
- intros [|[|n]]; now asimpl.
- intros [|[|n]]; now asimpl.
- trivial.
Qed.

Definition upn n sigma :=
Nat.iter n (fun sigma => up_ren sigma) sigma.

Lemma shift_upn_permute: forall (d:Data) n,
 ren1 (up_ren (upn n swap)) (⇑ d) = ⇑ (ren1 (upn n swap) d).
Proof. destruct n; now rewrite permute_ren1. Qed.

Lemma shiftn_permute: forall (d:Data) n sigma, 
  ren1 (upn n sigma) (nvars n d) = nvars n (ren1 sigma d).
Proof.
  intros.
  induction n.
  - now simpl.
  - simpl nvars. rewrite <- IHn.
    unfold shift_op, Shift_Data.
    now rewrite shift_permute_Data.
Qed.

Lemma upnswap_neut: forall n (d:Data), 
  (ren1 (upn n swap) (⇑ (⇑ (nvars n d)))) = (⇑ (⇑ (nvars n d))).
Proof.
  induction n; intros.
  - simpl. now rewrite Shift_Shift_Swap_Data.
  - simpl nvars. simpl upn. rewrite shift_upn_permute.
    simpl nvars in IHn. now rewrite IHn.
Qed.

Lemma var0_shiftupn: forall n,
  ⇑ (ren1 (upn n swap) (nvars n (var_Data 0))) = 
  ren1 (upn (S n) swap) (ren1 (upn n swap) (nvars n (var_Data 0))).
Proof.
  intro.
  induction n.
  - reflexivity.
  - simpl nvars. simpl upn.
    rewrite shift_upn_permute.
    rewrite IHn at 1.
    unfold shift_op, Shift_Data.
    now rewrite shift_permute_Data.
Qed.

Lemma var0_shiftupn2: forall n,
  ⇑ (nvars n (var_Data 0)) = ren1 (upn n swap) (nvars n (var_Data 0)).
Proof.
  intros. 
  induction n.
  - reflexivity.
  - simpl nvars in *. rewrite IHn. now erewrite var0_shiftupn.
Qed.

Lemma upn_up: forall n sigma, 
  upn n (up_ren sigma) = up_ren (upn n sigma).
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl upn. now rewrite IHn.
Qed.

Lemma upn_νs: forall n P sigma, 
  (νs n P)⟨sigma⟩ = νs n (P⟨upn n sigma⟩).
Proof.
  intros.
  generalize dependent sigma.
  induction n; intros.
  - reflexivity.
  - cbn in *. rewrite IHn. rewrite upn_up. auto.
Qed.

Lemma nvars_νs: forall n m P, nvars m (νs n P) = νs n (P⟨ upn n (Nat.iter m shift) ⟩).
Proof.
intros n m P.
rewrite Shift_to_Ren.
apply upn_νs.
Qed.

Lemma shift_νs: forall n P, 
  ⇑ (νs n P) = νs n (P⟨upn n shift⟩).
Proof.
 unfold shift_op, Shift_proc.
 intros. eapply upn_νs.
Qed.

Lemma Shift_of_nat: forall n m, Nat.iter n shift m = Nat.add n m.
Proof.
induction n.
- reflexivity.
- intros. simpl. now rewrite IHn.
Qed.

Lemma Up_Shift_Sum: forall n m x,
(upn m (Nat.iter n shift) (m + x)) = Nat.add n (m + x).
Proof.
intros.
induction m.
- simpl. now rewrite Shift_of_nat.
- simpl. rewrite IHm. now rewrite PeanoNat.Nat.add_succ_r. 
Qed.

Lemma Pointwise_Up_Shift_Sum: forall n m,
(pointwise_relation _ eq)
 (core.funcomp (upn m (Nat.iter n shift)) (Nat.iter m shift))
  (Nat.iter (n + m) shift).
Proof.
intros.
induction m.
- simpl. rewrite PeanoNat.Nat.add_0_r. reflexivity.
- simpl. unfold core.funcomp in IHm.
  intro x.
  repeat rewrite Shift_of_nat. rewrite Up_Shift_Sum.
  rewrite PeanoNat.Nat.add_succ_r.
  now rewrite PeanoNat.Nat.add_assoc.
Qed.
