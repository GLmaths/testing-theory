(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Lia.
From stdpp Require Import base countable list sets.
From TestingTheory Require Import ActTau InputOutputActions VCCS.Language.LTS.

Section VCCS_Value_Swap.

Context `{VP : VCCS_Parameters}.

Definition lift_atom (d : nat) (a : ValueData) : ValueData :=
  match a with
  | cst v => cst v
  | bvar j => bvar (d + j)
  end.

Definition swap_data (d : nat) (a b D : ValueData) : ValueData :=
  if decide (D = lift_atom d a) then lift_atom d b
  else if decide (D = lift_atom d b) then lift_atom d a else D.

Definition swap_eq (d : nat) (a b : ValueData) (E : Equation ValueData) : Equation ValueData :=
  match E with
  | D1 == D2 => swap_data d a b D1 == swap_data d a b D2
  end.

Fixpoint swap_at (d : nat) (a b : ValueData) (p : proc) : proc :=
  match p with
  | P ‖ Q => swap_at d a b P ‖ swap_at d a b Q
  | pr_var i => pr_var i
  | rec x • P => rec x • swap_at d a b P
  | If C Then P Else Q => If (swap_eq d a b C) Then (swap_at d a b P) Else (swap_at d a b Q)
  | ν P => ν (swap_at d a b P)
  | g M => swap_at_g d a b M
  end

with swap_at_g (d : nat) (a b : ValueData) (M : gproc) : gproc :=
  match M with
  | ① => ①
  | 𝟘 => 𝟘
  | c ? • p => c ? • swap_at (S d) a b p
  | c ! v • p => c ! (swap_data d a b v) • swap_at d a b p
  | 𝛕 • p => 𝛕 • swap_at d a b p
  | p1 + p2 => swap_at_g d a b p1 + swap_at_g d a b p2
  end.

Definition swap_proc (a b : ValueData) (p : proc) : proc := swap_at 0 a b p.

Definition swap_ext (a b : ValueData) (μ : ExtAct TypeOfActions) : ExtAct TypeOfActions :=
  match μ with
  | ActIn (c, v) => ActIn (c, swap_data 0 a b v)
  | ActOut (c, v) => ActOut (c, swap_data 0 a b v)
  end.

Definition swap_act (a b : ValueData) (α : ActIO TypeOfActions) : ActIO TypeOfActions :=
  match α with
  | ActExt μ => ActExt (swap_ext a b μ)
  | τ => τ
  end.

Lemma swap_data_invol d a b D : swap_data d a b (swap_data d a b D) = D.
Proof. unfold swap_data. repeat case_decide; congruence. Qed.

Lemma swap_data_inj d a b D D' : swap_data d a b D = swap_data d a b D' → D = D'.
Proof. intros h. rewrite <- (swap_data_invol d a b D), <- (swap_data_invol d a b D'), h. reflexivity. Qed.

Lemma swap_eq_invol d a b E : swap_eq d a b (swap_eq d a b E) = E.
Proof. destruct E. simpl. by rewrite !swap_data_invol. Qed.

Lemma swap_ext_invol a b μ : swap_ext a b (swap_ext a b μ) = μ.
Proof. destruct μ as [[c v] | [c v]]; simpl; by rewrite swap_data_invol. Qed.

Lemma swap_act_invol a b α : swap_act a b (swap_act a b α) = α.
Proof. destruct α; simpl; [by rewrite swap_ext_invol | reflexivity]. Qed.

Lemma swap_at_invol a b :
  (∀ p d, swap_at d a b (swap_at d a b p) = p) ∧ (∀ M d, swap_at_g d a b (swap_at_g d a b M) = M).
Proof.
  apply proc_ind'; intros; simpl;
    rewrite ?H, ?H0, ?swap_eq_invol, ?swap_data_invol; reflexivity.
Qed.

Lemma swap_proc_invol a b p : swap_proc a b (swap_proc a b p) = p.
Proof. exact (proj1 (swap_at_invol a b) p 0). Qed.

Lemma swap_subst_Data a b k X Y :
  swap_data k a b (subst_Data k X Y) = subst_Data k (swap_data k a b X) (swap_data (S k) a b Y).
Proof.
  unfold swap_data, subst_Data.
  destruct a as [va | ja], b as [vb | jb], Y as [vy | iy]; simpl;
    repeat case_decide; simplify_eq; try reflexivity; try lia;
    try (exfalso; match goal with h : _ ≠ _ |- _ => apply h; f_equal; lia end);
    try (f_equal; lia).
Qed.

Lemma swap_subst_Equation a b k X E :
  swap_eq k a b (subst_in_Equation k X E) = subst_in_Equation k (swap_data k a b X) (swap_eq (S k) a b E).
Proof. destruct E. simpl. by rewrite !swap_subst_Data. Qed.

Lemma swap_Succ_bvar a b k X : swap_data (S k) a b (Succ_bvar X) = Succ_bvar (swap_data k a b X).
Proof.
  unfold swap_data, Succ_bvar.
  destruct a as [va | ja], b as [vb | jb], X as [vx | ix]; simpl;
    repeat case_decide; simplify_eq; try reflexivity; try lia;
    try (exfalso; match goal with h : _ ≠ _ |- _ => apply h; f_equal; lia end);
    try (f_equal; lia).
Qed.

Lemma swap_subst a b :
  (∀ p k X, swap_at k a b (subst_in_proc k X p) = subst_in_proc k (swap_data k a b X) (swap_at (S k) a b p)) ∧
  (∀ M k X, swap_at_g k a b (subst_in_gproc k X M) = subst_in_gproc k (swap_data k a b X) (swap_at_g (S k) a b M)).
Proof.
  apply proc_ind'; intros; simpl;
    rewrite ?H, ?H0, ?swap_subst_Equation, ?swap_subst_Data, ?swap_Succ_bvar; reflexivity.
Qed.

Lemma swap_NewVar_in_Data a b k d D :
  k ≤ d → swap_data (S d) a b (NewVar_in_Data k D) = NewVar_in_Data k (swap_data d a b D).
Proof.
  intros hk. unfold swap_data, NewVar_in_Data.
  destruct a as [va | ja], b as [vb | jb], D as [vy | iy]; simpl;
    repeat case_decide; simplify_eq; try reflexivity; try lia;
    try (exfalso; match goal with h : _ ≠ _ |- _ => apply h; f_equal; lia end);
    try (f_equal; lia).
Qed.

Lemma swap_NewVar_in_Equation a b k d E :
  k ≤ d → swap_eq (S d) a b (NewVar_in_Equation k E) = NewVar_in_Equation k (swap_eq d a b E).
Proof. intros hk. destruct E. simpl. by rewrite !swap_NewVar_in_Data. Qed.

Lemma swap_NewVar a b :
  (∀ p k d, k ≤ d → swap_at (S d) a b (NewVar k p) = NewVar k (swap_at d a b p)) ∧
  (∀ M k d, k ≤ d → swap_at_g (S d) a b (gNewVar k M) = gNewVar k (swap_at_g d a b M)).
Proof.
  apply proc_ind'; intros; simpl;
    rewrite ?H, ?H0, ?swap_NewVar_in_Equation, ?swap_NewVar_in_Data by lia; reflexivity.
Qed.

Lemma swap_NewVarC a b :
  (∀ p k d, swap_at d a b (NewVarC k p) = NewVarC k (swap_at d a b p)) ∧
  (∀ M k d, swap_at_g d a b (gNewVarC k M) = gNewVarC k (swap_at_g d a b M)).
Proof. apply proc_ind'; intros; simpl; rewrite ?H, ?H0; reflexivity. Qed.

Lemma swap_pr_subst a b x :
  (∀ p q d, swap_at d a b (pr_subst x p q) = pr_subst x (swap_at d a b p) (swap_at d a b q)) ∧
  (∀ M q d, swap_at_g d a b (gpr_subst x M q) = gpr_subst x (swap_at_g d a b M) (swap_at d a b q)).
Proof.
  apply proc_ind'; intros; simpl.
  all: try (case_decide; reflexivity).
  all: rewrite ?H, ?H0, ?(proj1 (swap_NewVarC a b)), ?(proj1 (swap_NewVar a b)) by lia; try reflexivity.
  case_decide; simpl; [reflexivity | by rewrite H].
Qed.

Lemma Eval_Eq_zero D1 D2 : Eval_Eq 0 (D1 == D2) = Some (bool_decide (D1 = D2)).
Proof.
  destruct D1 as [t | i], D2 as [t' | i']; simpl; repeat case_decide; simplify_eq;
    try reflexivity; try lia; congruence.
Qed.

Lemma Eval_Eq_swap a b E : Eval_Eq 0 (swap_eq 0 a b E) = Eval_Eq 0 E.
Proof.
  destruct E as [D1 D2]. unfold swap_eq. rewrite !Eval_Eq_zero. f_equal.
  apply bool_decide_ext. split; [apply swap_data_inj | intros ->; reflexivity].
Qed.

Lemma swap_VarC_action_add a b k μ : swap_ext a b (VarC_action_add k μ) = VarC_action_add k (swap_ext a b μ).
Proof. destruct μ as [[c v] | [c v]]; reflexivity. Qed.

Lemma lts_swap a b p α q : lts p α q → lts (swap_proc a b p) (swap_act a b α) (swap_proc a b q).
Proof.
  unfold swap_proc. induction 1; simpl.
  - rewrite (proj1 (swap_subst a b)). apply lts_input.
  - apply lts_output.
  - apply lts_tau.
  - rewrite (proj1 (swap_pr_subst a b x)). apply lts_recursion.
  - apply lts_ifOne; [rewrite Eval_Eq_swap; exact H | exact IHlts].
  - apply lts_ifZero; [rewrite Eval_Eq_swap; exact H | exact IHlts].
  - apply lts_res_ext. rewrite <- swap_VarC_action_add. exact IHlts.
  - apply lts_res_tau. exact IHlts.
  - eapply lts_comL; [exact IHlts1 | exact IHlts2].
  - eapply lts_comR; [exact IHlts1 | exact IHlts2].
  - apply lts_parL. exact IHlts.
  - apply lts_parR. exact IHlts.
  - apply lts_choiceL. exact IHlts.
  - apply lts_choiceR. exact IHlts.
Qed.

Definition atoms_of_data (d : nat) (D : ValueData) : list ValueData :=
  match D with
  | cst v => [cst v]
  | bvar i => if decide (d ≤ i) then [bvar (i - d)] else []
  end.

Definition atoms_of_eq (d : nat) (E : Equation ValueData) : list ValueData :=
  match E with
  | D1 == D2 => atoms_of_data d D1 ++ atoms_of_data d D2
  end.

Fixpoint atoms_at (d : nat) (p : proc) : list ValueData :=
  match p with
  | P ‖ Q => atoms_at d P ++ atoms_at d Q
  | pr_var _ => []
  | rec _ • P => atoms_at d P
  | If C Then P Else Q => atoms_of_eq d C ++ atoms_at d P ++ atoms_at d Q
  | ν P => atoms_at d P
  | g M => atoms_at_g d M
  end

with atoms_at_g (d : nat) (M : gproc) : list ValueData :=
  match M with
  | c ? • p => atoms_at (S d) p
  | c ! v • p => atoms_of_data d v ++ atoms_at d p
  | 𝛕 • p => atoms_at d p
  | p1 + p2 => atoms_at_g d p1 ++ atoms_at_g d p2
  | _ => []
  end.

Definition atoms_of (p : proc) : list ValueData := atoms_at 0 p.

Lemma swap_data_fix d a b D : a ∉ atoms_of_data d D → b ∉ atoms_of_data d D → swap_data d a b D = D.
Proof.
  unfold swap_data, atoms_of_data.
  destruct a as [va | ja], b as [vb | jb], D as [vy | iy]; simpl; intros ha hb;
    repeat case_decide; simplify_eq; try reflexivity; try lia;
    exfalso; rewrite ?Nat.add_sub' in *; set_solver.
Qed.

Lemma swap_eq_fix d a b E : a ∉ atoms_of_eq d E → b ∉ atoms_of_eq d E → swap_eq d a b E = E.
Proof.
  destruct E as [d1 d2]; simpl; intros ha hb.
  rewrite !swap_data_fix; [reflexivity | set_solver ..].
Qed.

Lemma swap_at_fix a b :
  (∀ p d, a ∉ atoms_at d p → b ∉ atoms_at d p → swap_at d a b p = p) ∧
  (∀ M d, a ∉ atoms_at_g d M → b ∉ atoms_at_g d M → swap_at_g d a b M = M).
Proof.
  apply proc_ind'; simpl; intros; try reflexivity;
    rewrite ?swap_eq_fix, ?swap_data_fix, ?H, ?H0 by set_solver; reflexivity.
Qed.

Lemma swap_proc_fix a b p : a ∉ atoms_of p → b ∉ atoms_of p → swap_proc a b p = p.
Proof. exact (proj1 (swap_at_fix a b) p 0). Qed.

End VCCS_Value_Swap.
(* end hide *)
