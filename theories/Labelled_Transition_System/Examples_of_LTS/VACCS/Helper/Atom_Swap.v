(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Lia.
From stdpp Require Import base countable list sets.
From TestingTheory Require Import ActTau InputOutputActions VACCS.Language.LTS.

Scheme vaccs_proc_ind0 := Induction for proc Sort Prop
with vaccs_gproc_ind0 := Induction for gproc Sort Prop.

Combined Scheme vaccs_proc_ind' from vaccs_proc_ind0, vaccs_gproc_ind0.

Section VACCS_Atom_Swap.

Context `{VP : VACCS_Parameters}.

Definition lift_D {T} (d : nat) (a : Data T) : Data T :=
  match a with
  | cst v => cst v
  | bvar j => bvar (d + j)
  end.

Definition swap_D {T} `{Countable T} (d : nat) (a b D : Data T) : Data T :=
  if decide (D = lift_D d a) then lift_D d b
  else if decide (D = lift_D d b) then lift_D d a else D.

Lemma swap_D_invol {T} `{Countable T} d (a b D : Data T) : swap_D d a b (swap_D d a b D) = D.
Proof. unfold swap_D. repeat case_decide; congruence. Qed.

Lemma swap_D_inj {T} `{Countable T} d (a b D D' : Data T) : swap_D d a b D = swap_D d a b D' → D = D'.
Proof. intros h. rewrite <- (swap_D_invol d a b D), <- (swap_D_invol d a b D'), h. reflexivity. Qed.

Lemma swap_D_subst a b k (X Y : ValueData) :
  swap_D k a b (subst_Data k X Y) = subst_Data k (swap_D k a b X) (swap_D (S k) a b Y).
Proof.
  unfold swap_D, subst_Data.
  destruct a as [va | ja], b as [vb | jb], Y as [vy | iy]; simpl;
    repeat case_decide; simplify_eq; try reflexivity; try lia;
    try (exfalso; match goal with h : _ ≠ _ |- _ => apply h; f_equal; lia end);
    try (f_equal; lia).
Qed.

Lemma swap_D_Succ a b k (X : ValueData) : swap_D (S k) a b (Succ_bvar X) = Succ_bvar (swap_D k a b X).
Proof.
  unfold swap_D, Succ_bvar.
  destruct a as [va | ja], b as [vb | jb], X as [vx | ix]; simpl;
    repeat case_decide; simplify_eq; try reflexivity; try lia;
    try (exfalso; match goal with h : _ ≠ _ |- _ => apply h; f_equal; lia end);
    try (f_equal; lia).
Qed.

Lemma swap_D_NewVar a b k d (D : ValueData) :
  k ≤ d → swap_D (S d) a b (NewVar_in_Data k D) = NewVar_in_Data k (swap_D d a b D).
Proof.
  intros hk. unfold swap_D, NewVar_in_Data.
  destruct a as [va | ja], b as [vb | jb], D as [vy | iy]; simpl;
    repeat case_decide; simplify_eq; try reflexivity; try lia;
    try (exfalso; match goal with h : _ ≠ _ |- _ => apply h; f_equal; lia end);
    try (f_equal; lia).
Qed.

Lemma swap_D_NewVarC a b k d (D : ChannelData) :
  k ≤ d → swap_D (S d) a b (NewVar_in_ChannelData k D) = NewVar_in_ChannelData k (swap_D d a b D).
Proof.
  intros hk. unfold swap_D, NewVar_in_ChannelData.
  destruct a as [va | ja], b as [vb | jb], D as [vy | iy]; simpl;
    repeat case_decide; simplify_eq; try reflexivity; try lia;
    try (exfalso; match goal with h : _ ≠ _ |- _ => apply h; f_equal; lia end);
    try (f_equal; lia).
Qed.

Lemma swap_D_VarC a b d (D : ChannelData) : swap_D (S d) a b (VarC_add 1 D) = VarC_add 1 (swap_D d a b D).
Proof.
  unfold swap_D, VarC_add.
  destruct a as [va | ja], b as [vb | jb], D as [vy | iy]; simpl;
    repeat case_decide; simplify_eq; try reflexivity; try lia;
    try (exfalso; match goal with h : _ ≠ _ |- _ => apply h; f_equal; lia end);
    try (f_equal; lia).
Qed.

Definition Atom : Type := (ChannelData + ValueData)%type.

Definition swap_cd (d : nat) (a b : Atom) (c : ChannelData) : ChannelData :=
  match a, b with
  | inl a', inl b' => swap_D d a' b' c
  | _, _ => c
  end.

Definition swap_vd (d : nat) (a b : Atom) (v : ValueData) : ValueData :=
  match a, b with
  | inr a', inr b' => swap_D d a' b' v
  | _, _ => v
  end.

Lemma swap_cd_invol d a b c : swap_cd d a b (swap_cd d a b c) = c.
Proof. destruct a, b; simpl; try reflexivity. apply swap_D_invol. Qed.

Lemma swap_vd_invol d a b v : swap_vd d a b (swap_vd d a b v) = v.
Proof. destruct a, b; simpl; try reflexivity. apply swap_D_invol. Qed.

Lemma swap_vd_inj d a b v v' : swap_vd d a b v = swap_vd d a b v' → v = v'.
Proof. intros h. rewrite <- (swap_vd_invol d a b v), <- (swap_vd_invol d a b v'), h. reflexivity. Qed.

Lemma swap_vd_subst a b k X Y :
  swap_vd k a b (subst_Data k X Y) = subst_Data k (swap_vd k a b X) (swap_vd (S k) a b Y).
Proof. destruct a, b; simpl; try reflexivity. apply swap_D_subst. Qed.

Lemma swap_vd_Succ a b k X : swap_vd (S k) a b (Succ_bvar X) = Succ_bvar (swap_vd k a b X).
Proof. destruct a, b; simpl; try reflexivity. apply swap_D_Succ. Qed.

Lemma swap_vd_NewVar a b k d D : k ≤ d → swap_vd (S d) a b (NewVar_in_Data k D) = NewVar_in_Data k (swap_vd d a b D).
Proof. intros hk. destruct a, b; simpl; try reflexivity. by apply swap_D_NewVar. Qed.

Lemma swap_cd_NewVarC a b k d D :
  k ≤ d → swap_cd (S d) a b (NewVar_in_ChannelData k D) = NewVar_in_ChannelData k (swap_cd d a b D).
Proof. intros hk. destruct a, b; simpl; try reflexivity. by apply swap_D_NewVarC. Qed.

Lemma swap_cd_VarC a b d D : swap_cd (S d) a b (VarC_add 1 D) = VarC_add 1 (swap_cd d a b D).
Proof. destruct a, b; simpl; try reflexivity. apply swap_D_VarC. Qed.

Definition swap_eq (d : nat) (a b : Atom) (E : Equation ValueData) : Equation ValueData :=
  match E with
  | D1 == D2 => swap_vd d a b D1 == swap_vd d a b D2
  end.

Fixpoint swap_at (dc dv : nat) (a b : Atom) (p : proc) : proc :=
  match p with
  | P ‖ Q => swap_at dc dv a b P ‖ swap_at dc dv a b Q
  | pr_var i => pr_var i
  | rec x • P => rec x • swap_at dc dv a b P
  | If C Then P Else Q => If (swap_eq dv a b C) Then (swap_at dc dv a b P) Else (swap_at dc dv a b Q)
  | c ! v • 𝟘 => swap_cd dc a b c ! swap_vd dv a b v • 𝟘
  | ν P => ν (swap_at (S dc) dv a b P)
  | g M => swap_at_g dc dv a b M
  end

with swap_at_g (dc dv : nat) (a b : Atom) (M : gproc) : gproc :=
  match M with
  | ① => ①
  | 𝟘 => 𝟘
  | c ? • p => swap_cd dc a b c ? • swap_at dc (S dv) a b p
  | 𝛕 • p => 𝛕 • swap_at dc dv a b p
  | p1 + p2 => swap_at_g dc dv a b p1 + swap_at_g dc dv a b p2
  end.

Definition swap_proc (a b : Atom) (p : proc) : proc := swap_at 0 0 a b p.

Definition swap_ext_at (dc : nat) (a b : Atom) (μ : ExtAct TypeOfActions) : ExtAct TypeOfActions :=
  match μ with
  | ActIn (c, v) => ActIn (swap_cd dc a b c, swap_vd 0 a b v)
  | ActOut (c, v) => ActOut (swap_cd dc a b c, swap_vd 0 a b v)
  end.

Definition swap_lab_at (dc : nat) (a b : Atom) (α : ActIO TypeOfActions) : ActIO TypeOfActions :=
  match α with
  | ActExt μ => ActExt (swap_ext_at dc a b μ)
  | τ => τ
  end.

Definition swap_ext (a b : Atom) (μ : ExtAct TypeOfActions) : ExtAct TypeOfActions := swap_ext_at 0 a b μ.

Lemma swap_eq_invol d a b E : swap_eq d a b (swap_eq d a b E) = E.
Proof. destruct E. simpl. by rewrite !swap_vd_invol. Qed.

Lemma swap_ext_invol a b μ : swap_ext a b (swap_ext a b μ) = μ.
Proof. destruct μ as [[c v] | [c v]]; unfold swap_ext; simpl; by rewrite swap_cd_invol, swap_vd_invol. Qed.

Lemma swap_at_invol a b :
  (∀ p dc dv, swap_at dc dv a b (swap_at dc dv a b p) = p) ∧
  (∀ M dc dv, swap_at_g dc dv a b (swap_at_g dc dv a b M) = M).
Proof.
  apply vaccs_proc_ind'; intros; simpl;
    rewrite ?H, ?H0, ?swap_eq_invol, ?swap_vd_invol, ?swap_cd_invol; reflexivity.
Qed.

Lemma swap_proc_invol a b p : swap_proc a b (swap_proc a b p) = p.
Proof. exact (proj1 (swap_at_invol a b) p 0 0). Qed.

Lemma swap_subst_Equation a b k X E :
  swap_eq k a b (subst_in_Equation k X E) = subst_in_Equation k (swap_vd k a b X) (swap_eq (S k) a b E).
Proof. destruct E. simpl. by rewrite !swap_vd_subst. Qed.

Lemma swap_subst a b :
  (∀ p dc k X, swap_at dc k a b (subst_in_proc k X p) = subst_in_proc k (swap_vd k a b X) (swap_at dc (S k) a b p)) ∧
  (∀ M dc k X, swap_at_g dc k a b (subst_in_gproc k X M) = subst_in_gproc k (swap_vd k a b X) (swap_at_g dc (S k) a b M)).
Proof.
  apply vaccs_proc_ind'; intros; simpl;
    rewrite ?H, ?H0, ?swap_subst_Equation, ?swap_vd_subst, ?swap_vd_Succ; reflexivity.
Qed.

Lemma swap_NewVar_in_Equation a b k d E :
  k ≤ d → swap_eq (S d) a b (NewVar_in_Equation k E) = NewVar_in_Equation k (swap_eq d a b E).
Proof. intros hk. destruct E. simpl. by rewrite !swap_vd_NewVar. Qed.

Lemma swap_NewVar a b :
  (∀ p dc k d, k ≤ d → swap_at dc (S d) a b (NewVar k p) = NewVar k (swap_at dc d a b p)) ∧
  (∀ M dc k d, k ≤ d → swap_at_g dc (S d) a b (gNewVar k M) = gNewVar k (swap_at_g dc d a b M)).
Proof.
  apply vaccs_proc_ind'; intros; simpl;
    rewrite ?H, ?H0, ?swap_NewVar_in_Equation, ?swap_vd_NewVar by lia; reflexivity.
Qed.

Lemma swap_NewVarC a b :
  (∀ p k dc dv, k ≤ dc → swap_at (S dc) dv a b (NewVarC k p) = NewVarC k (swap_at dc dv a b p)) ∧
  (∀ M k dc dv, k ≤ dc → swap_at_g (S dc) dv a b (gNewVarC k M) = gNewVarC k (swap_at_g dc dv a b M)).
Proof.
  apply vaccs_proc_ind'; intros; simpl;
    rewrite ?H, ?H0, ?swap_cd_NewVarC by lia; reflexivity.
Qed.

Lemma swap_pr_subst a b x :
  (∀ p q dc dv, swap_at dc dv a b (pr_subst x p q) = pr_subst x (swap_at dc dv a b p) (swap_at dc dv a b q)) ∧
  (∀ M q dc dv, swap_at_g dc dv a b (gpr_subst x M q) = gpr_subst x (swap_at_g dc dv a b M) (swap_at dc dv a b q)).
Proof.
  apply vaccs_proc_ind'; intros; simpl.
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
  apply bool_decide_ext. split; [apply swap_vd_inj | intros ->; reflexivity].
Qed.

Lemma swap_VarC_action_add a b dc μ :
  swap_ext_at (S dc) a b (VarC_action_add 1 μ) = VarC_action_add 1 (swap_ext_at dc a b μ).
Proof. destruct μ as [[c v] | [c v]]; simpl; by rewrite swap_cd_VarC. Qed.

Lemma lts_swap_at a b p α q :
  lts p α q → ∀ dc, lts (swap_at dc 0 a b p) (swap_lab_at dc a b α) (swap_at dc 0 a b q).
Proof.
  induction 1; intros dc; simpl.
  - rewrite (proj1 (swap_subst a b)). apply lts_input.
  - apply lts_output.
  - apply lts_tau.
  - rewrite (proj1 (swap_pr_subst a b x)). apply lts_recursion.
  - apply lts_ifOne; [rewrite Eval_Eq_swap; exact H | exact (IHlts dc)].
  - apply lts_ifZero; [rewrite Eval_Eq_swap; exact H | exact (IHlts dc)].
  - apply lts_res_ext. rewrite <- swap_VarC_action_add. exact (IHlts (S dc)).
  - apply lts_res_tau. exact (IHlts (S dc)).
  - eapply lts_comL; [exact (IHlts1 dc) | exact (IHlts2 dc)].
  - eapply lts_comR; [exact (IHlts1 dc) | exact (IHlts2 dc)].
  - apply lts_parL. exact (IHlts dc).
  - apply lts_parR. exact (IHlts dc).
  - apply lts_choiceL. exact (IHlts dc).
  - apply lts_choiceR. exact (IHlts dc).
Qed.

Definition atoms_of_D {T} `{Countable T} (inj : Data T → Atom) (d : nat) (D : Data T) : list Atom :=
  match D with
  | cst v => [inj (cst v)]
  | bvar i => if decide (d ≤ i) then [inj (bvar (i - d))] else []
  end.

Definition atoms_of_eq (d : nat) (E : Equation ValueData) : list Atom :=
  match E with
  | D1 == D2 => atoms_of_D inr d D1 ++ atoms_of_D inr d D2
  end.

Fixpoint atoms_at (dc dv : nat) (p : proc) : list Atom :=
  match p with
  | P ‖ Q => atoms_at dc dv P ++ atoms_at dc dv Q
  | pr_var _ => []
  | rec _ • P => atoms_at dc dv P
  | If C Then P Else Q => atoms_of_eq dv C ++ atoms_at dc dv P ++ atoms_at dc dv Q
  | c ! v • 𝟘 => atoms_of_D inl dc c ++ atoms_of_D inr dv v
  | ν P => atoms_at (S dc) dv P
  | g M => atoms_at_g dc dv M
  end

with atoms_at_g (dc dv : nat) (M : gproc) : list Atom :=
  match M with
  | c ? • p => atoms_of_D inl dc c ++ atoms_at dc (S dv) p
  | 𝛕 • p => atoms_at dc dv p
  | p1 + p2 => atoms_at_g dc dv p1 ++ atoms_at_g dc dv p2
  | _ => []
  end.

Definition atoms_of (p : proc) : list Atom := atoms_at 0 0 p.

Lemma swap_cd_fix d a b c : a ∉ atoms_of_D inl d c → b ∉ atoms_of_D inl d c → swap_cd d a b c = c.
Proof.
  destruct a as [a | a], b as [b | b]; simpl; intros ha hb; try reflexivity.
  unfold swap_D, atoms_of_D in *.
  destruct a as [va | ja], b as [vb | jb], c as [vy | iy]; simpl in *;
    repeat case_decide; simplify_eq; try reflexivity; try lia;
    exfalso; rewrite ?Nat.add_sub' in *; set_solver.
Qed.

Lemma swap_vd_fix d a b v : a ∉ atoms_of_D inr d v → b ∉ atoms_of_D inr d v → swap_vd d a b v = v.
Proof.
  destruct a as [a | a], b as [b | b]; simpl; intros ha hb; try reflexivity.
  unfold swap_D, atoms_of_D in *.
  destruct a as [va | ja], b as [vb | jb], v as [vy | iy]; simpl in *;
    repeat case_decide; simplify_eq; try reflexivity; try lia;
    exfalso; rewrite ?Nat.add_sub' in *; set_solver.
Qed.

Lemma swap_eq_fix d a b E : a ∉ atoms_of_eq d E → b ∉ atoms_of_eq d E → swap_eq d a b E = E.
Proof. destruct E as [d1 d2]; simpl; intros ha hb. rewrite !swap_vd_fix; [reflexivity | set_solver ..]. Qed.

Lemma swap_at_fix a b :
  (∀ p dc dv, a ∉ atoms_at dc dv p → b ∉ atoms_at dc dv p → swap_at dc dv a b p = p) ∧
  (∀ M dc dv, a ∉ atoms_at_g dc dv M → b ∉ atoms_at_g dc dv M → swap_at_g dc dv a b M = M).
Proof.
  apply vaccs_proc_ind'; simpl; intros; try reflexivity;
    rewrite ?swap_eq_fix, ?swap_cd_fix, ?swap_vd_fix, ?H, ?H0 by set_solver; reflexivity.
Qed.

Lemma swap_proc_fix a b p : a ∉ atoms_of p → b ∉ atoms_of p → swap_proc a b p = p.
Proof. exact (proj1 (swap_at_fix a b) p 0 0). Qed.

End VACCS_Atom_Swap.
(* end hide *)
