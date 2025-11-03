Require Import core unscoped.
Require Import Setoid Morphisms Relation_Definitions.

Parameter Value : Type.
(* Parameter Channel : Type. *)
Module Core.

Inductive Data : Type :=
  | var_Data : nat -> Data
  | cst : Value -> Data.

Lemma congr_cst {s0 : Value} {t0 : Value} (H0 : s0 = t0) : cst s0 = cst t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => cst x) H0)).
Qed.

Lemma upRen_Data_Data (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Definition ren_Data (xi_Data : nat -> nat) (s : Data) : Data :=
  match s with
  | var_Data s0 => var_Data (xi_Data s0)
  | cst s0 => cst s0
  end.

Lemma up_Data_Data (sigma : nat -> Data) : nat -> Data.
Proof.
exact (scons (var_Data var_zero) (funcomp (ren_Data shift) sigma)).
Defined.

Definition subst_Data (sigma_Data : nat -> Data) (s : Data) : Data :=
  match s with
  | var_Data s0 => sigma_Data s0
  | cst s0 => cst s0
  end.

Lemma upId_Data_Data (sigma : nat -> Data)
  (Eq : forall x, sigma x = var_Data x) :
  forall x, up_Data_Data sigma x = var_Data x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Data shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Definition idSubst_Data (sigma_Data : nat -> Data)
  (Eq_Data : forall x, sigma_Data x = var_Data x) (s : Data) :
  subst_Data sigma_Data s = s :=
  match s with
  | var_Data s0 => Eq_Data s0
  | cst s0 => congr_cst (eq_refl s0)
  end.

Lemma upExtRen_Data_Data (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_Data_Data xi x = upRen_Data_Data zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Definition extRen_Data (xi_Data : nat -> nat) (zeta_Data : nat -> nat)
  (Eq_Data : forall x, xi_Data x = zeta_Data x) (s : Data) :
  ren_Data xi_Data s = ren_Data zeta_Data s :=
  match s with
  | var_Data s0 => ap (var_Data) (Eq_Data s0)
  | cst s0 => congr_cst (eq_refl s0)
  end.

Lemma upExt_Data_Data (sigma : nat -> Data) (tau : nat -> Data)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_Data_Data sigma x = up_Data_Data tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Data shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Definition ext_Data (sigma_Data : nat -> Data) (tau_Data : nat -> Data)
  (Eq_Data : forall x, sigma_Data x = tau_Data x) (s : Data) :
  subst_Data sigma_Data s = subst_Data tau_Data s :=
  match s with
  | var_Data s0 => Eq_Data s0
  | cst s0 => congr_cst (eq_refl s0)
  end.

Lemma up_ren_ren_Data_Data (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_Data_Data zeta) (upRen_Data_Data xi) x =
  upRen_Data_Data rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Definition compRenRen_Data (xi_Data : nat -> nat) (zeta_Data : nat -> nat)
  (rho_Data : nat -> nat)
  (Eq_Data : forall x, funcomp zeta_Data xi_Data x = rho_Data x) (s : Data) :
  ren_Data zeta_Data (ren_Data xi_Data s) = ren_Data rho_Data s :=
  match s with
  | var_Data s0 => ap (var_Data) (Eq_Data s0)
  | cst s0 => congr_cst (eq_refl s0)
  end.

Lemma up_ren_subst_Data_Data (xi : nat -> nat) (tau : nat -> Data)
  (theta : nat -> Data) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_Data_Data tau) (upRen_Data_Data xi) x = up_Data_Data theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Data shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Definition compRenSubst_Data (xi_Data : nat -> nat) (tau_Data : nat -> Data)
  (theta_Data : nat -> Data)
  (Eq_Data : forall x, funcomp tau_Data xi_Data x = theta_Data x) (s : Data)
  : subst_Data tau_Data (ren_Data xi_Data s) = subst_Data theta_Data s :=
  match s with
  | var_Data s0 => Eq_Data s0
  | cst s0 => congr_cst (eq_refl s0)
  end.

Lemma up_subst_ren_Data_Data (sigma : nat -> Data) (zeta_Data : nat -> nat)
  (theta : nat -> Data)
  (Eq : forall x, funcomp (ren_Data zeta_Data) sigma x = theta x) :
  forall x,
  funcomp (ren_Data (upRen_Data_Data zeta_Data)) (up_Data_Data sigma) x =
  up_Data_Data theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_Data shift (upRen_Data_Data zeta_Data)
                (funcomp shift zeta_Data) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_Data zeta_Data shift (funcomp shift zeta_Data)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_Data shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Definition compSubstRen_Data (sigma_Data : nat -> Data)
  (zeta_Data : nat -> nat) (theta_Data : nat -> Data)
  (Eq_Data : forall x,
             funcomp (ren_Data zeta_Data) sigma_Data x = theta_Data x)
  (s : Data) :
  ren_Data zeta_Data (subst_Data sigma_Data s) = subst_Data theta_Data s :=
  match s with
  | var_Data s0 => Eq_Data s0
  | cst s0 => congr_cst (eq_refl s0)
  end.

Lemma up_subst_subst_Data_Data (sigma : nat -> Data) (tau_Data : nat -> Data)
  (theta : nat -> Data)
  (Eq : forall x, funcomp (subst_Data tau_Data) sigma x = theta x) :
  forall x,
  funcomp (subst_Data (up_Data_Data tau_Data)) (up_Data_Data sigma) x =
  up_Data_Data theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_Data shift (up_Data_Data tau_Data)
                (funcomp (up_Data_Data tau_Data) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_Data tau_Data shift
                      (funcomp (ren_Data shift) tau_Data) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_Data shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Definition compSubstSubst_Data (sigma_Data : nat -> Data)
  (tau_Data : nat -> Data) (theta_Data : nat -> Data)
  (Eq_Data : forall x,
             funcomp (subst_Data tau_Data) sigma_Data x = theta_Data x)
  (s : Data) :
  subst_Data tau_Data (subst_Data sigma_Data s) = subst_Data theta_Data s :=
  match s with
  | var_Data s0 => Eq_Data s0
  | cst s0 => congr_cst (eq_refl s0)
  end.

Lemma renRen_Data (xi_Data : nat -> nat) (zeta_Data : nat -> nat) (s : Data)
  :
  ren_Data zeta_Data (ren_Data xi_Data s) =
  ren_Data (funcomp zeta_Data xi_Data) s.
Proof.
exact (compRenRen_Data xi_Data zeta_Data _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Data_pointwise (xi_Data : nat -> nat) (zeta_Data : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_Data zeta_Data) (ren_Data xi_Data))
    (ren_Data (funcomp zeta_Data xi_Data)).
Proof.
exact (fun s => compRenRen_Data xi_Data zeta_Data _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Data (xi_Data : nat -> nat) (tau_Data : nat -> Data)
  (s : Data) :
  subst_Data tau_Data (ren_Data xi_Data s) =
  subst_Data (funcomp tau_Data xi_Data) s.
Proof.
exact (compRenSubst_Data xi_Data tau_Data _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Data_pointwise (xi_Data : nat -> nat) (tau_Data : nat -> Data)
  :
  pointwise_relation _ eq (funcomp (subst_Data tau_Data) (ren_Data xi_Data))
    (subst_Data (funcomp tau_Data xi_Data)).
Proof.
exact (fun s => compRenSubst_Data xi_Data tau_Data _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Data (sigma_Data : nat -> Data) (zeta_Data : nat -> nat)
  (s : Data) :
  ren_Data zeta_Data (subst_Data sigma_Data s) =
  subst_Data (funcomp (ren_Data zeta_Data) sigma_Data) s.
Proof.
exact (compSubstRen_Data sigma_Data zeta_Data _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Data_pointwise (sigma_Data : nat -> Data)
  (zeta_Data : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_Data zeta_Data) (subst_Data sigma_Data))
    (subst_Data (funcomp (ren_Data zeta_Data) sigma_Data)).
Proof.
exact (fun s => compSubstRen_Data sigma_Data zeta_Data _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Data (sigma_Data : nat -> Data) (tau_Data : nat -> Data)
  (s : Data) :
  subst_Data tau_Data (subst_Data sigma_Data s) =
  subst_Data (funcomp (subst_Data tau_Data) sigma_Data) s.
Proof.
exact (compSubstSubst_Data sigma_Data tau_Data _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Data_pointwise (sigma_Data : nat -> Data)
  (tau_Data : nat -> Data) :
  pointwise_relation _ eq
    (funcomp (subst_Data tau_Data) (subst_Data sigma_Data))
    (subst_Data (funcomp (subst_Data tau_Data) sigma_Data)).
Proof.
exact (fun s =>
       compSubstSubst_Data sigma_Data tau_Data _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_Data_Data (xi : nat -> nat) (sigma : nat -> Data)
  (Eq : forall x, funcomp (var_Data) xi x = sigma x) :
  forall x, funcomp (var_Data) (upRen_Data_Data xi) x = up_Data_Data sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Data shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Definition rinst_inst_Data (xi_Data : nat -> nat) (sigma_Data : nat -> Data)
  (Eq_Data : forall x, funcomp (var_Data) xi_Data x = sigma_Data x)
  (s : Data) : ren_Data xi_Data s = subst_Data sigma_Data s :=
  match s with
  | var_Data s0 => Eq_Data s0
  | cst s0 => congr_cst (eq_refl s0)
  end.

Lemma rinstInst'_Data (xi_Data : nat -> nat) (s : Data) :
  ren_Data xi_Data s = subst_Data (funcomp (var_Data) xi_Data) s.
Proof.
exact (rinst_inst_Data xi_Data _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Data_pointwise (xi_Data : nat -> nat) :
  pointwise_relation _ eq (ren_Data xi_Data)
    (subst_Data (funcomp (var_Data) xi_Data)).
Proof.
exact (fun s => rinst_inst_Data xi_Data _ (fun n => eq_refl) s).
Qed.

Lemma instId'_Data (s : Data) : subst_Data (var_Data) s = s.
Proof.
exact (idSubst_Data (var_Data) (fun n => eq_refl) s).
Qed.

Lemma instId'_Data_pointwise :
  pointwise_relation _ eq (subst_Data (var_Data)) id.
Proof.
exact (fun s => idSubst_Data (var_Data) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_Data (s : Data) : ren_Data id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Data s) (rinstInst'_Data id s)).
Qed.

Lemma rinstId'_Data_pointwise : pointwise_relation _ eq (@ren_Data id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_Data s) (rinstInst'_Data id s)).
Qed.

Lemma varL'_Data (sigma_Data : nat -> Data) (x : nat) :
  subst_Data sigma_Data (var_Data x) = sigma_Data x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_Data_pointwise (sigma_Data : nat -> Data) :
  pointwise_relation _ eq (funcomp (subst_Data sigma_Data) (var_Data))
    sigma_Data.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_Data (xi_Data : nat -> nat) (x : nat) :
  ren_Data xi_Data (var_Data x) = var_Data (xi_Data x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_Data_pointwise (xi_Data : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Data xi_Data) (var_Data))
    (funcomp (var_Data) xi_Data).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive ExtAction : Type :=
    act : Data -> Data -> ExtAction.

Lemma congr_act {s0 : Data} {s1 : Data} {t0 : Data} {t1 : Data}
  (H0 : s0 = t0) (H1 : s1 = t1) : act s0 s1 = act t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => act x s1) H0))
         (ap (fun x => act t0 x) H1)).
Qed.

Definition subst_ExtAction (sigma_Data : nat -> Data) (s : ExtAction) :
  ExtAction :=
  match s with
  | act s0 s1 => act (subst_Data sigma_Data s0) (subst_Data sigma_Data s1)
  end.

Definition idSubst_ExtAction (sigma_Data : nat -> Data)
  (Eq_Data : forall x, sigma_Data x = var_Data x) (s : ExtAction) :
  subst_ExtAction sigma_Data s = s :=
  match s with
  | act s0 s1 =>
      congr_act (idSubst_Data sigma_Data Eq_Data s0)
        (idSubst_Data sigma_Data Eq_Data s1)
  end.

Definition ext_ExtAction (sigma_Data : nat -> Data) (tau_Data : nat -> Data)
  (Eq_Data : forall x, sigma_Data x = tau_Data x) (s : ExtAction) :
  subst_ExtAction sigma_Data s = subst_ExtAction tau_Data s :=
  match s with
  | act s0 s1 =>
      congr_act (ext_Data sigma_Data tau_Data Eq_Data s0)
        (ext_Data sigma_Data tau_Data Eq_Data s1)
  end.

Definition compSubstSubst_ExtAction (sigma_Data : nat -> Data)
  (tau_Data : nat -> Data) (theta_Data : nat -> Data)
  (Eq_Data : forall x,
             funcomp (subst_Data tau_Data) sigma_Data x = theta_Data x)
  (s : ExtAction) :
  subst_ExtAction tau_Data (subst_ExtAction sigma_Data s) =
  subst_ExtAction theta_Data s :=
  match s with
  | act s0 s1 =>
      congr_act
        (compSubstSubst_Data sigma_Data tau_Data theta_Data Eq_Data s0)
        (compSubstSubst_Data sigma_Data tau_Data theta_Data Eq_Data s1)
  end.

Lemma substSubst_ExtAction (sigma_Data : nat -> Data)
  (tau_Data : nat -> Data) (s : ExtAction) :
  subst_ExtAction tau_Data (subst_ExtAction sigma_Data s) =
  subst_ExtAction (funcomp (subst_Data tau_Data) sigma_Data) s.
Proof.
exact (compSubstSubst_ExtAction sigma_Data tau_Data _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_ExtAction_pointwise (sigma_Data : nat -> Data)
  (tau_Data : nat -> Data) :
  pointwise_relation _ eq
    (funcomp (subst_ExtAction tau_Data) (subst_ExtAction sigma_Data))
    (subst_ExtAction (funcomp (subst_Data tau_Data) sigma_Data)).
Proof.
exact (fun s =>
       compSubstSubst_ExtAction sigma_Data tau_Data _ (fun n => eq_refl) s).
Qed.

Lemma instId'_ExtAction (s : ExtAction) : subst_ExtAction (var_Data) s = s.
Proof.
exact (idSubst_ExtAction (var_Data) (fun n => eq_refl) s).
Qed.

Lemma instId'_ExtAction_pointwise :
  pointwise_relation _ eq (subst_ExtAction (var_Data)) id.
Proof.
exact (fun s => idSubst_ExtAction (var_Data) (fun n => eq_refl) s).
Qed.

Inductive Act : Type :=
  | ActIn : ExtAction -> Act
  | FreeOut : ExtAction -> Act
  | BoundOut : ExtAction -> Act
  | tau_action : Act.

Lemma congr_ActIn {s0 : ExtAction} {t0 : ExtAction} (H0 : s0 = t0) :
  ActIn s0 = ActIn t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => ActIn x) H0)).
Qed.

Lemma congr_FreeOut {s0 : ExtAction} {t0 : ExtAction} (H0 : s0 = t0) :
  FreeOut s0 = FreeOut t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => FreeOut x) H0)).
Qed.

Lemma congr_BoundOut {s0 : ExtAction} {t0 : ExtAction} (H0 : s0 = t0) :
  BoundOut s0 = BoundOut t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => BoundOut x) H0)).
Qed.

Lemma congr_tau_action : tau_action = tau_action.
Proof.
exact (eq_refl).
Qed.

Definition subst_Act (sigma_Data : nat -> Data) (s : Act) : Act :=
  match s with
  | ActIn s0 => ActIn (subst_ExtAction sigma_Data s0)
  | FreeOut s0 => FreeOut (subst_ExtAction sigma_Data s0)
  | BoundOut s0 => BoundOut (subst_ExtAction sigma_Data s0)
  | tau_action => tau_action
  end.

Definition idSubst_Act (sigma_Data : nat -> Data)
  (Eq_Data : forall x, sigma_Data x = var_Data x) (s : Act) :
  subst_Act sigma_Data s = s :=
  match s with
  | ActIn s0 => congr_ActIn (idSubst_ExtAction sigma_Data Eq_Data s0)
  | FreeOut s0 => congr_FreeOut (idSubst_ExtAction sigma_Data Eq_Data s0)
  | BoundOut s0 => congr_BoundOut (idSubst_ExtAction sigma_Data Eq_Data s0)
  | tau_action => congr_tau_action
  end.

Definition ext_Act (sigma_Data : nat -> Data) (tau_Data : nat -> Data)
  (Eq_Data : forall x, sigma_Data x = tau_Data x) (s : Act) :
  subst_Act sigma_Data s = subst_Act tau_Data s :=
  match s with
  | ActIn s0 => congr_ActIn (ext_ExtAction sigma_Data tau_Data Eq_Data s0)
  | FreeOut s0 =>
      congr_FreeOut (ext_ExtAction sigma_Data tau_Data Eq_Data s0)
  | BoundOut s0 =>
      congr_BoundOut (ext_ExtAction sigma_Data tau_Data Eq_Data s0)
  | tau_action => congr_tau_action
  end.

Definition compSubstSubst_Act (sigma_Data : nat -> Data)
  (tau_Data : nat -> Data) (theta_Data : nat -> Data)
  (Eq_Data : forall x,
             funcomp (subst_Data tau_Data) sigma_Data x = theta_Data x)
  (s : Act) :
  subst_Act tau_Data (subst_Act sigma_Data s) = subst_Act theta_Data s :=
  match s with
  | ActIn s0 =>
      congr_ActIn
        (compSubstSubst_ExtAction sigma_Data tau_Data theta_Data Eq_Data s0)
  | FreeOut s0 =>
      congr_FreeOut
        (compSubstSubst_ExtAction sigma_Data tau_Data theta_Data Eq_Data s0)
  | BoundOut s0 =>
      congr_BoundOut
        (compSubstSubst_ExtAction sigma_Data tau_Data theta_Data Eq_Data s0)
  | tau_action => congr_tau_action
  end.

Lemma substSubst_Act (sigma_Data : nat -> Data) (tau_Data : nat -> Data)
  (s : Act) :
  subst_Act tau_Data (subst_Act sigma_Data s) =
  subst_Act (funcomp (subst_Data tau_Data) sigma_Data) s.
Proof.
exact (compSubstSubst_Act sigma_Data tau_Data _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Act_pointwise (sigma_Data : nat -> Data)
  (tau_Data : nat -> Data) :
  pointwise_relation _ eq
    (funcomp (subst_Act tau_Data) (subst_Act sigma_Data))
    (subst_Act (funcomp (subst_Data tau_Data) sigma_Data)).
Proof.
exact (fun s => compSubstSubst_Act sigma_Data tau_Data _ (fun n => eq_refl) s).
Qed.

Lemma instId'_Act (s : Act) : subst_Act (var_Data) s = s.
Proof.
exact (idSubst_Act (var_Data) (fun n => eq_refl) s).
Qed.

Lemma instId'_Act_pointwise :
  pointwise_relation _ eq (subst_Act (var_Data)) id.
Proof.
exact (fun s => idSubst_Act (var_Data) (fun n => eq_refl) s).
Qed.

Inductive Equation : Type :=
  | tt : Equation
  | ff : Equation
  | Inequality : Data -> Data -> Equation
  | Or : Equation -> Equation -> Equation
  | Not : Equation -> Equation.

Lemma congr_tt : tt = tt.
Proof.
exact (eq_refl).
Qed.

Lemma congr_ff : ff = ff.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Inequality {s0 : Data} {s1 : Data} {t0 : Data} {t1 : Data}
  (H0 : s0 = t0) (H1 : s1 = t1) : Inequality s0 s1 = Inequality t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Inequality x s1) H0))
         (ap (fun x => Inequality t0 x) H1)).
Qed.

Lemma congr_Or {s0 : Equation} {s1 : Equation} {t0 : Equation}
  {t1 : Equation} (H0 : s0 = t0) (H1 : s1 = t1) : Or s0 s1 = Or t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Or x s1) H0))
         (ap (fun x => Or t0 x) H1)).
Qed.

Lemma congr_Not {s0 : Equation} {t0 : Equation} (H0 : s0 = t0) :
  Not s0 = Not t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => Not x) H0)).
Qed.

Fixpoint ren_Equation (xi_Data : nat -> nat) (s : Equation) {struct s} :
Equation :=
  match s with
  | tt => tt
  | ff => ff
  | Inequality s0 s1 =>
      Inequality (ren_Data xi_Data s0) (ren_Data xi_Data s1)
  | Or s0 s1 => Or (ren_Equation xi_Data s0) (ren_Equation xi_Data s1)
  | Not s0 => Not (ren_Equation xi_Data s0)
  end.

Fixpoint subst_Equation (sigma_Data : nat -> Data) (s : Equation) {struct s}
   : Equation :=
  match s with
  | tt => tt
  | ff => ff
  | Inequality s0 s1 =>
      Inequality (subst_Data sigma_Data s0) (subst_Data sigma_Data s1)
  | Or s0 s1 =>
      Or (subst_Equation sigma_Data s0) (subst_Equation sigma_Data s1)
  | Not s0 => Not (subst_Equation sigma_Data s0)
  end.

Fixpoint idSubst_Equation (sigma_Data : nat -> Data)
(Eq_Data : forall x, sigma_Data x = var_Data x) (s : Equation) {struct s} :
subst_Equation sigma_Data s = s :=
  match s with
  | tt => congr_tt
  | ff => congr_ff
  | Inequality s0 s1 =>
      congr_Inequality (idSubst_Data sigma_Data Eq_Data s0)
        (idSubst_Data sigma_Data Eq_Data s1)
  | Or s0 s1 =>
      congr_Or (idSubst_Equation sigma_Data Eq_Data s0)
        (idSubst_Equation sigma_Data Eq_Data s1)
  | Not s0 => congr_Not (idSubst_Equation sigma_Data Eq_Data s0)
  end.

Fixpoint extRen_Equation (xi_Data : nat -> nat) (zeta_Data : nat -> nat)
(Eq_Data : forall x, xi_Data x = zeta_Data x) (s : Equation) {struct s} :
ren_Equation xi_Data s = ren_Equation zeta_Data s :=
  match s with
  | tt => congr_tt
  | ff => congr_ff
  | Inequality s0 s1 =>
      congr_Inequality (extRen_Data xi_Data zeta_Data Eq_Data s0)
        (extRen_Data xi_Data zeta_Data Eq_Data s1)
  | Or s0 s1 =>
      congr_Or (extRen_Equation xi_Data zeta_Data Eq_Data s0)
        (extRen_Equation xi_Data zeta_Data Eq_Data s1)
  | Not s0 => congr_Not (extRen_Equation xi_Data zeta_Data Eq_Data s0)
  end.

Fixpoint ext_Equation (sigma_Data : nat -> Data) (tau_Data : nat -> Data)
(Eq_Data : forall x, sigma_Data x = tau_Data x) (s : Equation) {struct s} :
subst_Equation sigma_Data s = subst_Equation tau_Data s :=
  match s with
  | tt => congr_tt
  | ff => congr_ff
  | Inequality s0 s1 =>
      congr_Inequality (ext_Data sigma_Data tau_Data Eq_Data s0)
        (ext_Data sigma_Data tau_Data Eq_Data s1)
  | Or s0 s1 =>
      congr_Or (ext_Equation sigma_Data tau_Data Eq_Data s0)
        (ext_Equation sigma_Data tau_Data Eq_Data s1)
  | Not s0 => congr_Not (ext_Equation sigma_Data tau_Data Eq_Data s0)
  end.

Fixpoint compRenRen_Equation (xi_Data : nat -> nat) (zeta_Data : nat -> nat)
(rho_Data : nat -> nat)
(Eq_Data : forall x, funcomp zeta_Data xi_Data x = rho_Data x) (s : Equation)
{struct s} :
ren_Equation zeta_Data (ren_Equation xi_Data s) = ren_Equation rho_Data s :=
  match s with
  | tt => congr_tt
  | ff => congr_ff
  | Inequality s0 s1 =>
      congr_Inequality
        (compRenRen_Data xi_Data zeta_Data rho_Data Eq_Data s0)
        (compRenRen_Data xi_Data zeta_Data rho_Data Eq_Data s1)
  | Or s0 s1 =>
      congr_Or (compRenRen_Equation xi_Data zeta_Data rho_Data Eq_Data s0)
        (compRenRen_Equation xi_Data zeta_Data rho_Data Eq_Data s1)
  | Not s0 =>
      congr_Not (compRenRen_Equation xi_Data zeta_Data rho_Data Eq_Data s0)
  end.

Fixpoint compRenSubst_Equation (xi_Data : nat -> nat)
(tau_Data : nat -> Data) (theta_Data : nat -> Data)
(Eq_Data : forall x, funcomp tau_Data xi_Data x = theta_Data x)
(s : Equation) {struct s} :
subst_Equation tau_Data (ren_Equation xi_Data s) =
subst_Equation theta_Data s :=
  match s with
  | tt => congr_tt
  | ff => congr_ff
  | Inequality s0 s1 =>
      congr_Inequality
        (compRenSubst_Data xi_Data tau_Data theta_Data Eq_Data s0)
        (compRenSubst_Data xi_Data tau_Data theta_Data Eq_Data s1)
  | Or s0 s1 =>
      congr_Or (compRenSubst_Equation xi_Data tau_Data theta_Data Eq_Data s0)
        (compRenSubst_Equation xi_Data tau_Data theta_Data Eq_Data s1)
  | Not s0 =>
      congr_Not
        (compRenSubst_Equation xi_Data tau_Data theta_Data Eq_Data s0)
  end.

Fixpoint compSubstRen_Equation (sigma_Data : nat -> Data)
(zeta_Data : nat -> nat) (theta_Data : nat -> Data)
(Eq_Data : forall x, funcomp (ren_Data zeta_Data) sigma_Data x = theta_Data x)
(s : Equation) {struct s} :
ren_Equation zeta_Data (subst_Equation sigma_Data s) =
subst_Equation theta_Data s :=
  match s with
  | tt => congr_tt
  | ff => congr_ff
  | Inequality s0 s1 =>
      congr_Inequality
        (compSubstRen_Data sigma_Data zeta_Data theta_Data Eq_Data s0)
        (compSubstRen_Data sigma_Data zeta_Data theta_Data Eq_Data s1)
  | Or s0 s1 =>
      congr_Or
        (compSubstRen_Equation sigma_Data zeta_Data theta_Data Eq_Data s0)
        (compSubstRen_Equation sigma_Data zeta_Data theta_Data Eq_Data s1)
  | Not s0 =>
      congr_Not
        (compSubstRen_Equation sigma_Data zeta_Data theta_Data Eq_Data s0)
  end.

Fixpoint compSubstSubst_Equation (sigma_Data : nat -> Data)
(tau_Data : nat -> Data) (theta_Data : nat -> Data)
(Eq_Data : forall x,
           funcomp (subst_Data tau_Data) sigma_Data x = theta_Data x)
(s : Equation) {struct s} :
subst_Equation tau_Data (subst_Equation sigma_Data s) =
subst_Equation theta_Data s :=
  match s with
  | tt => congr_tt
  | ff => congr_ff
  | Inequality s0 s1 =>
      congr_Inequality
        (compSubstSubst_Data sigma_Data tau_Data theta_Data Eq_Data s0)
        (compSubstSubst_Data sigma_Data tau_Data theta_Data Eq_Data s1)
  | Or s0 s1 =>
      congr_Or
        (compSubstSubst_Equation sigma_Data tau_Data theta_Data Eq_Data s0)
        (compSubstSubst_Equation sigma_Data tau_Data theta_Data Eq_Data s1)
  | Not s0 =>
      congr_Not
        (compSubstSubst_Equation sigma_Data tau_Data theta_Data Eq_Data s0)
  end.

Lemma renRen_Equation (xi_Data : nat -> nat) (zeta_Data : nat -> nat)
  (s : Equation) :
  ren_Equation zeta_Data (ren_Equation xi_Data s) =
  ren_Equation (funcomp zeta_Data xi_Data) s.
Proof.
exact (compRenRen_Equation xi_Data zeta_Data _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Equation_pointwise (xi_Data : nat -> nat)
  (zeta_Data : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_Equation zeta_Data) (ren_Equation xi_Data))
    (ren_Equation (funcomp zeta_Data xi_Data)).
Proof.
exact (fun s => compRenRen_Equation xi_Data zeta_Data _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Equation (xi_Data : nat -> nat) (tau_Data : nat -> Data)
  (s : Equation) :
  subst_Equation tau_Data (ren_Equation xi_Data s) =
  subst_Equation (funcomp tau_Data xi_Data) s.
Proof.
exact (compRenSubst_Equation xi_Data tau_Data _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Equation_pointwise (xi_Data : nat -> nat)
  (tau_Data : nat -> Data) :
  pointwise_relation _ eq
    (funcomp (subst_Equation tau_Data) (ren_Equation xi_Data))
    (subst_Equation (funcomp tau_Data xi_Data)).
Proof.
exact (fun s => compRenSubst_Equation xi_Data tau_Data _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Equation (sigma_Data : nat -> Data) (zeta_Data : nat -> nat)
  (s : Equation) :
  ren_Equation zeta_Data (subst_Equation sigma_Data s) =
  subst_Equation (funcomp (ren_Data zeta_Data) sigma_Data) s.
Proof.
exact (compSubstRen_Equation sigma_Data zeta_Data _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Equation_pointwise (sigma_Data : nat -> Data)
  (zeta_Data : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_Equation zeta_Data) (subst_Equation sigma_Data))
    (subst_Equation (funcomp (ren_Data zeta_Data) sigma_Data)).
Proof.
exact (fun s =>
       compSubstRen_Equation sigma_Data zeta_Data _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Equation (sigma_Data : nat -> Data) (tau_Data : nat -> Data)
  (s : Equation) :
  subst_Equation tau_Data (subst_Equation sigma_Data s) =
  subst_Equation (funcomp (subst_Data tau_Data) sigma_Data) s.
Proof.
exact (compSubstSubst_Equation sigma_Data tau_Data _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Equation_pointwise (sigma_Data : nat -> Data)
  (tau_Data : nat -> Data) :
  pointwise_relation _ eq
    (funcomp (subst_Equation tau_Data) (subst_Equation sigma_Data))
    (subst_Equation (funcomp (subst_Data tau_Data) sigma_Data)).
Proof.
exact (fun s =>
       compSubstSubst_Equation sigma_Data tau_Data _ (fun n => eq_refl) s).
Qed.

Fixpoint rinst_inst_Equation (xi_Data : nat -> nat)
(sigma_Data : nat -> Data)
(Eq_Data : forall x, funcomp (var_Data) xi_Data x = sigma_Data x)
(s : Equation) {struct s} :
ren_Equation xi_Data s = subst_Equation sigma_Data s :=
  match s with
  | tt => congr_tt
  | ff => congr_ff
  | Inequality s0 s1 =>
      congr_Inequality (rinst_inst_Data xi_Data sigma_Data Eq_Data s0)
        (rinst_inst_Data xi_Data sigma_Data Eq_Data s1)
  | Or s0 s1 =>
      congr_Or (rinst_inst_Equation xi_Data sigma_Data Eq_Data s0)
        (rinst_inst_Equation xi_Data sigma_Data Eq_Data s1)
  | Not s0 => congr_Not (rinst_inst_Equation xi_Data sigma_Data Eq_Data s0)
  end.

Lemma rinstInst'_Equation (xi_Data : nat -> nat) (s : Equation) :
  ren_Equation xi_Data s = subst_Equation (funcomp (var_Data) xi_Data) s.
Proof.
exact (rinst_inst_Equation xi_Data _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Equation_pointwise (xi_Data : nat -> nat) :
  pointwise_relation _ eq (ren_Equation xi_Data)
    (subst_Equation (funcomp (var_Data) xi_Data)).
Proof.
exact (fun s => rinst_inst_Equation xi_Data _ (fun n => eq_refl) s).
Qed.

Lemma instId'_Equation (s : Equation) : subst_Equation (var_Data) s = s.
Proof.
exact (idSubst_Equation (var_Data) (fun n => eq_refl) s).
Qed.

Lemma instId'_Equation_pointwise :
  pointwise_relation _ eq (subst_Equation (var_Data)) id.
Proof.
exact (fun s => idSubst_Equation (var_Data) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_Equation (s : Equation) : ren_Equation id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Equation s)
         (rinstInst'_Equation id s)).
Qed.

Lemma rinstId'_Equation_pointwise :
  pointwise_relation _ eq (@ren_Equation id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_Equation s)
         (rinstInst'_Equation id s)).
Qed.

Inductive proc : Type :=
  | var_proc : nat -> proc
  | pr_rec : proc -> proc
  | pr_par : proc -> proc -> proc
  | pr_res : proc -> proc
  | pr_if_then_else : Equation -> proc -> proc -> proc
  | g : gproc -> proc
with gproc : Type :=
  | gpr_success : gproc
  | gpr_nil : gproc
  | gpr_output : Data -> Data -> proc -> gproc
  | gpr_input : Data -> proc -> gproc
  | gpr_tau : proc -> gproc
  | gpr_choice : gproc -> gproc -> gproc.

Lemma congr_pr_rec {s0 : proc} {t0 : proc} (H0 : s0 = t0) :
  pr_rec s0 = pr_rec t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => pr_rec x) H0)).
Qed.

Lemma congr_pr_par {s0 : proc} {s1 : proc} {t0 : proc} {t1 : proc}
  (H0 : s0 = t0) (H1 : s1 = t1) : pr_par s0 s1 = pr_par t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => pr_par x s1) H0))
         (ap (fun x => pr_par t0 x) H1)).
Qed.

Lemma congr_pr_res {s0 : proc} {t0 : proc} (H0 : s0 = t0) :
  pr_res s0 = pr_res t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => pr_res x) H0)).
Qed.

Lemma congr_pr_if_then_else {s0 : Equation} {s1 : proc} {s2 : proc}
  {t0 : Equation} {t1 : proc} {t2 : proc} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) : pr_if_then_else s0 s1 s2 = pr_if_then_else t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans eq_refl (ap (fun x => pr_if_then_else x s1 s2) H0))
            (ap (fun x => pr_if_then_else t0 x s2) H1))
         (ap (fun x => pr_if_then_else t0 t1 x) H2)).
Qed.

Lemma congr_g {s0 : gproc} {t0 : gproc} (H0 : s0 = t0) : g s0 = g t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => g x) H0)).
Qed.

Lemma congr_gpr_success : gpr_success = gpr_success.
Proof.
exact (eq_refl).
Qed.

Lemma congr_gpr_nil : gpr_nil = gpr_nil.
Proof.
exact (eq_refl).
Qed.

Lemma congr_gpr_output {s0 : Data} {s1 : Data} {s2 : proc} {t0 : Data}
  {t1 : Data} {t2 : proc} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  gpr_output s0 s1 s2 = gpr_output t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => gpr_output x s1 s2) H0))
            (ap (fun x => gpr_output t0 x s2) H1))
         (ap (fun x => gpr_output t0 t1 x) H2)).
Qed.

Lemma congr_gpr_input {s0 : Data} {s1 : proc} {t0 : Data} {t1 : proc}
  (H0 : s0 = t0) (H1 : s1 = t1) : gpr_input s0 s1 = gpr_input t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => gpr_input x s1) H0))
         (ap (fun x => gpr_input t0 x) H1)).
Qed.

Lemma congr_gpr_tau {s0 : proc} {t0 : proc} (H0 : s0 = t0) :
  gpr_tau s0 = gpr_tau t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => gpr_tau x) H0)).
Qed.

Lemma congr_gpr_choice {s0 : gproc} {s1 : gproc} {t0 : gproc} {t1 : gproc}
  (H0 : s0 = t0) (H1 : s1 = t1) : gpr_choice s0 s1 = gpr_choice t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => gpr_choice x s1) H0))
         (ap (fun x => gpr_choice t0 x) H1)).
Qed.

Lemma upRen_proc_proc (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_proc_Data (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_Data_proc (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Fixpoint ren_proc (xi_proc : nat -> nat) (xi_Data : nat -> nat) (s : proc)
{struct s} : proc :=
  match s with
  | var_proc s0 => var_proc (xi_proc s0)
  | pr_rec s0 =>
      pr_rec
        (ren_proc (upRen_proc_proc xi_proc) (upRen_proc_Data xi_Data) s0)
  | pr_par s0 s1 =>
      pr_par (ren_proc xi_proc xi_Data s0) (ren_proc xi_proc xi_Data s1)
  | pr_res s0 =>
      pr_res
        (ren_proc (upRen_Data_proc xi_proc) (upRen_Data_Data xi_Data) s0)
  | pr_if_then_else s0 s1 s2 =>
      pr_if_then_else (ren_Equation xi_Data s0) (ren_proc xi_proc xi_Data s1)
        (ren_proc xi_proc xi_Data s2)
  | g s0 => g (ren_gproc xi_proc xi_Data s0)
  end
with ren_gproc (xi_proc : nat -> nat) (xi_Data : nat -> nat) (s : gproc)
{struct s} : gproc :=
  match s with
  | gpr_success => gpr_success
  | gpr_nil => gpr_nil
  | gpr_output s0 s1 s2 =>
      gpr_output (ren_Data xi_Data s0) (ren_Data xi_Data s1)
        (ren_proc xi_proc xi_Data s2)
  | gpr_input s0 s1 =>
      gpr_input (ren_Data xi_Data s0)
        (ren_proc (upRen_Data_proc xi_proc) (upRen_Data_Data xi_Data) s1)
  | gpr_tau s0 => gpr_tau (ren_proc xi_proc xi_Data s0)
  | gpr_choice s0 s1 =>
      gpr_choice (ren_gproc xi_proc xi_Data s0)
        (ren_gproc xi_proc xi_Data s1)
  end.

Lemma up_proc_proc (sigma : nat -> proc) : nat -> proc.
Proof.
exact (scons (var_proc var_zero) (funcomp (ren_proc shift id) sigma)).
Defined.

Lemma up_proc_Data (sigma : nat -> Data) : nat -> Data.
Proof.
exact (funcomp (ren_Data id) sigma).
Defined.

Lemma up_Data_proc (sigma : nat -> proc) : nat -> proc.
Proof.
exact (funcomp (ren_proc id shift) sigma).
Defined.

Fixpoint subst_proc (sigma_proc : nat -> proc) (sigma_Data : nat -> Data)
(s : proc) {struct s} : proc :=
  match s with
  | var_proc s0 => sigma_proc s0
  | pr_rec s0 =>
      pr_rec
        (subst_proc (up_proc_proc sigma_proc) (up_proc_Data sigma_Data) s0)
  | pr_par s0 s1 =>
      pr_par (subst_proc sigma_proc sigma_Data s0)
        (subst_proc sigma_proc sigma_Data s1)
  | pr_res s0 =>
      pr_res
        (subst_proc (up_Data_proc sigma_proc) (up_Data_Data sigma_Data) s0)
  | pr_if_then_else s0 s1 s2 =>
      pr_if_then_else (subst_Equation sigma_Data s0)
        (subst_proc sigma_proc sigma_Data s1)
        (subst_proc sigma_proc sigma_Data s2)
  | g s0 => g (subst_gproc sigma_proc sigma_Data s0)
  end
with subst_gproc (sigma_proc : nat -> proc) (sigma_Data : nat -> Data)
(s : gproc) {struct s} : gproc :=
  match s with
  | gpr_success => gpr_success
  | gpr_nil => gpr_nil
  | gpr_output s0 s1 s2 =>
      gpr_output (subst_Data sigma_Data s0) (subst_Data sigma_Data s1)
        (subst_proc sigma_proc sigma_Data s2)
  | gpr_input s0 s1 =>
      gpr_input (subst_Data sigma_Data s0)
        (subst_proc (up_Data_proc sigma_proc) (up_Data_Data sigma_Data) s1)
  | gpr_tau s0 => gpr_tau (subst_proc sigma_proc sigma_Data s0)
  | gpr_choice s0 s1 =>
      gpr_choice (subst_gproc sigma_proc sigma_Data s0)
        (subst_gproc sigma_proc sigma_Data s1)
  end.

Lemma upId_proc_proc (sigma : nat -> proc)
  (Eq : forall x, sigma x = var_proc x) :
  forall x, up_proc_proc sigma x = var_proc x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_proc shift id) (Eq n')
       | O => eq_refl
       end).
Qed.

Lemma upId_proc_Data (sigma : nat -> Data)
  (Eq : forall x, sigma x = var_Data x) :
  forall x, up_proc_Data sigma x = var_Data x.
Proof.
exact (fun n => ap (ren_Data id) (Eq n)).
Qed.

Lemma upId_Data_proc (sigma : nat -> proc)
  (Eq : forall x, sigma x = var_proc x) :
  forall x, up_Data_proc sigma x = var_proc x.
Proof.
exact (fun n => ap (ren_proc id shift) (Eq n)).
Qed.

Fixpoint idSubst_proc (sigma_proc : nat -> proc) (sigma_Data : nat -> Data)
(Eq_proc : forall x, sigma_proc x = var_proc x)
(Eq_Data : forall x, sigma_Data x = var_Data x) (s : proc) {struct s} :
subst_proc sigma_proc sigma_Data s = s :=
  match s with
  | var_proc s0 => Eq_proc s0
  | pr_rec s0 =>
      congr_pr_rec
        (idSubst_proc (up_proc_proc sigma_proc) (up_proc_Data sigma_Data)
           (upId_proc_proc _ Eq_proc) (upId_proc_Data _ Eq_Data) s0)
  | pr_par s0 s1 =>
      congr_pr_par (idSubst_proc sigma_proc sigma_Data Eq_proc Eq_Data s0)
        (idSubst_proc sigma_proc sigma_Data Eq_proc Eq_Data s1)
  | pr_res s0 =>
      congr_pr_res
        (idSubst_proc (up_Data_proc sigma_proc) (up_Data_Data sigma_Data)
           (upId_Data_proc _ Eq_proc) (upId_Data_Data _ Eq_Data) s0)
  | pr_if_then_else s0 s1 s2 =>
      congr_pr_if_then_else (idSubst_Equation sigma_Data Eq_Data s0)
        (idSubst_proc sigma_proc sigma_Data Eq_proc Eq_Data s1)
        (idSubst_proc sigma_proc sigma_Data Eq_proc Eq_Data s2)
  | g s0 => congr_g (idSubst_gproc sigma_proc sigma_Data Eq_proc Eq_Data s0)
  end
with idSubst_gproc (sigma_proc : nat -> proc) (sigma_Data : nat -> Data)
(Eq_proc : forall x, sigma_proc x = var_proc x)
(Eq_Data : forall x, sigma_Data x = var_Data x) (s : gproc) {struct s} :
subst_gproc sigma_proc sigma_Data s = s :=
  match s with
  | gpr_success => congr_gpr_success
  | gpr_nil => congr_gpr_nil
  | gpr_output s0 s1 s2 =>
      congr_gpr_output (idSubst_Data sigma_Data Eq_Data s0)
        (idSubst_Data sigma_Data Eq_Data s1)
        (idSubst_proc sigma_proc sigma_Data Eq_proc Eq_Data s2)
  | gpr_input s0 s1 =>
      congr_gpr_input (idSubst_Data sigma_Data Eq_Data s0)
        (idSubst_proc (up_Data_proc sigma_proc) (up_Data_Data sigma_Data)
           (upId_Data_proc _ Eq_proc) (upId_Data_Data _ Eq_Data) s1)
  | gpr_tau s0 =>
      congr_gpr_tau (idSubst_proc sigma_proc sigma_Data Eq_proc Eq_Data s0)
  | gpr_choice s0 s1 =>
      congr_gpr_choice
        (idSubst_gproc sigma_proc sigma_Data Eq_proc Eq_Data s0)
        (idSubst_gproc sigma_proc sigma_Data Eq_proc Eq_Data s1)
  end.

Lemma upExtRen_proc_proc (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_proc_proc xi x = upRen_proc_proc zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Lemma upExtRen_proc_Data (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_proc_Data xi x = upRen_proc_Data zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_Data_proc (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_Data_proc xi x = upRen_Data_proc zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Fixpoint extRen_proc (xi_proc : nat -> nat) (xi_Data : nat -> nat)
(zeta_proc : nat -> nat) (zeta_Data : nat -> nat)
(Eq_proc : forall x, xi_proc x = zeta_proc x)
(Eq_Data : forall x, xi_Data x = zeta_Data x) (s : proc) {struct s} :
ren_proc xi_proc xi_Data s = ren_proc zeta_proc zeta_Data s :=
  match s with
  | var_proc s0 => ap (var_proc) (Eq_proc s0)
  | pr_rec s0 =>
      congr_pr_rec
        (extRen_proc (upRen_proc_proc xi_proc) (upRen_proc_Data xi_Data)
           (upRen_proc_proc zeta_proc) (upRen_proc_Data zeta_Data)
           (upExtRen_proc_proc _ _ Eq_proc) (upExtRen_proc_Data _ _ Eq_Data)
           s0)
  | pr_par s0 s1 =>
      congr_pr_par
        (extRen_proc xi_proc xi_Data zeta_proc zeta_Data Eq_proc Eq_Data s0)
        (extRen_proc xi_proc xi_Data zeta_proc zeta_Data Eq_proc Eq_Data s1)
  | pr_res s0 =>
      congr_pr_res
        (extRen_proc (upRen_Data_proc xi_proc) (upRen_Data_Data xi_Data)
           (upRen_Data_proc zeta_proc) (upRen_Data_Data zeta_Data)
           (upExtRen_Data_proc _ _ Eq_proc) (upExtRen_Data_Data _ _ Eq_Data)
           s0)
  | pr_if_then_else s0 s1 s2 =>
      congr_pr_if_then_else (extRen_Equation xi_Data zeta_Data Eq_Data s0)
        (extRen_proc xi_proc xi_Data zeta_proc zeta_Data Eq_proc Eq_Data s1)
        (extRen_proc xi_proc xi_Data zeta_proc zeta_Data Eq_proc Eq_Data s2)
  | g s0 =>
      congr_g
        (extRen_gproc xi_proc xi_Data zeta_proc zeta_Data Eq_proc Eq_Data s0)
  end
with extRen_gproc (xi_proc : nat -> nat) (xi_Data : nat -> nat)
(zeta_proc : nat -> nat) (zeta_Data : nat -> nat)
(Eq_proc : forall x, xi_proc x = zeta_proc x)
(Eq_Data : forall x, xi_Data x = zeta_Data x) (s : gproc) {struct s} :
ren_gproc xi_proc xi_Data s = ren_gproc zeta_proc zeta_Data s :=
  match s with
  | gpr_success => congr_gpr_success
  | gpr_nil => congr_gpr_nil
  | gpr_output s0 s1 s2 =>
      congr_gpr_output (extRen_Data xi_Data zeta_Data Eq_Data s0)
        (extRen_Data xi_Data zeta_Data Eq_Data s1)
        (extRen_proc xi_proc xi_Data zeta_proc zeta_Data Eq_proc Eq_Data s2)
  | gpr_input s0 s1 =>
      congr_gpr_input (extRen_Data xi_Data zeta_Data Eq_Data s0)
        (extRen_proc (upRen_Data_proc xi_proc) (upRen_Data_Data xi_Data)
           (upRen_Data_proc zeta_proc) (upRen_Data_Data zeta_Data)
           (upExtRen_Data_proc _ _ Eq_proc) (upExtRen_Data_Data _ _ Eq_Data)
           s1)
  | gpr_tau s0 =>
      congr_gpr_tau
        (extRen_proc xi_proc xi_Data zeta_proc zeta_Data Eq_proc Eq_Data s0)
  | gpr_choice s0 s1 =>
      congr_gpr_choice
        (extRen_gproc xi_proc xi_Data zeta_proc zeta_Data Eq_proc Eq_Data s0)
        (extRen_gproc xi_proc xi_Data zeta_proc zeta_Data Eq_proc Eq_Data s1)
  end.

Lemma upExt_proc_proc (sigma : nat -> proc) (tau : nat -> proc)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_proc_proc sigma x = up_proc_proc tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_proc shift id) (Eq n')
       | O => eq_refl
       end).
Qed.

Lemma upExt_proc_Data (sigma : nat -> Data) (tau : nat -> Data)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_proc_Data sigma x = up_proc_Data tau x.
Proof.
exact (fun n => ap (ren_Data id) (Eq n)).
Qed.

Lemma upExt_Data_proc (sigma : nat -> proc) (tau : nat -> proc)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_Data_proc sigma x = up_Data_proc tau x.
Proof.
exact (fun n => ap (ren_proc id shift) (Eq n)).
Qed.

Fixpoint ext_proc (sigma_proc : nat -> proc) (sigma_Data : nat -> Data)
(tau_proc : nat -> proc) (tau_Data : nat -> Data)
(Eq_proc : forall x, sigma_proc x = tau_proc x)
(Eq_Data : forall x, sigma_Data x = tau_Data x) (s : proc) {struct s} :
subst_proc sigma_proc sigma_Data s = subst_proc tau_proc tau_Data s :=
  match s with
  | var_proc s0 => Eq_proc s0
  | pr_rec s0 =>
      congr_pr_rec
        (ext_proc (up_proc_proc sigma_proc) (up_proc_Data sigma_Data)
           (up_proc_proc tau_proc) (up_proc_Data tau_Data)
           (upExt_proc_proc _ _ Eq_proc) (upExt_proc_Data _ _ Eq_Data) s0)
  | pr_par s0 s1 =>
      congr_pr_par
        (ext_proc sigma_proc sigma_Data tau_proc tau_Data Eq_proc Eq_Data s0)
        (ext_proc sigma_proc sigma_Data tau_proc tau_Data Eq_proc Eq_Data s1)
  | pr_res s0 =>
      congr_pr_res
        (ext_proc (up_Data_proc sigma_proc) (up_Data_Data sigma_Data)
           (up_Data_proc tau_proc) (up_Data_Data tau_Data)
           (upExt_Data_proc _ _ Eq_proc) (upExt_Data_Data _ _ Eq_Data) s0)
  | pr_if_then_else s0 s1 s2 =>
      congr_pr_if_then_else (ext_Equation sigma_Data tau_Data Eq_Data s0)
        (ext_proc sigma_proc sigma_Data tau_proc tau_Data Eq_proc Eq_Data s1)
        (ext_proc sigma_proc sigma_Data tau_proc tau_Data Eq_proc Eq_Data s2)
  | g s0 =>
      congr_g
        (ext_gproc sigma_proc sigma_Data tau_proc tau_Data Eq_proc Eq_Data s0)
  end
with ext_gproc (sigma_proc : nat -> proc) (sigma_Data : nat -> Data)
(tau_proc : nat -> proc) (tau_Data : nat -> Data)
(Eq_proc : forall x, sigma_proc x = tau_proc x)
(Eq_Data : forall x, sigma_Data x = tau_Data x) (s : gproc) {struct s} :
subst_gproc sigma_proc sigma_Data s = subst_gproc tau_proc tau_Data s :=
  match s with
  | gpr_success => congr_gpr_success
  | gpr_nil => congr_gpr_nil
  | gpr_output s0 s1 s2 =>
      congr_gpr_output (ext_Data sigma_Data tau_Data Eq_Data s0)
        (ext_Data sigma_Data tau_Data Eq_Data s1)
        (ext_proc sigma_proc sigma_Data tau_proc tau_Data Eq_proc Eq_Data s2)
  | gpr_input s0 s1 =>
      congr_gpr_input (ext_Data sigma_Data tau_Data Eq_Data s0)
        (ext_proc (up_Data_proc sigma_proc) (up_Data_Data sigma_Data)
           (up_Data_proc tau_proc) (up_Data_Data tau_Data)
           (upExt_Data_proc _ _ Eq_proc) (upExt_Data_Data _ _ Eq_Data) s1)
  | gpr_tau s0 =>
      congr_gpr_tau
        (ext_proc sigma_proc sigma_Data tau_proc tau_Data Eq_proc Eq_Data s0)
  | gpr_choice s0 s1 =>
      congr_gpr_choice
        (ext_gproc sigma_proc sigma_Data tau_proc tau_Data Eq_proc Eq_Data s0)
        (ext_gproc sigma_proc sigma_Data tau_proc tau_Data Eq_proc Eq_Data s1)
  end.

Lemma up_ren_ren_proc_proc (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_proc_proc zeta) (upRen_proc_proc xi) x =
  upRen_proc_proc rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_proc_Data (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_proc_Data zeta) (upRen_proc_Data xi) x =
  upRen_proc_Data rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_Data_proc (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_Data_proc zeta) (upRen_Data_proc xi) x =
  upRen_Data_proc rho x.
Proof.
exact (Eq).
Qed.

Fixpoint compRenRen_proc (xi_proc : nat -> nat) (xi_Data : nat -> nat)
(zeta_proc : nat -> nat) (zeta_Data : nat -> nat) (rho_proc : nat -> nat)
(rho_Data : nat -> nat)
(Eq_proc : forall x, funcomp zeta_proc xi_proc x = rho_proc x)
(Eq_Data : forall x, funcomp zeta_Data xi_Data x = rho_Data x) (s : proc)
{struct s} :
ren_proc zeta_proc zeta_Data (ren_proc xi_proc xi_Data s) =
ren_proc rho_proc rho_Data s :=
  match s with
  | var_proc s0 => ap (var_proc) (Eq_proc s0)
  | pr_rec s0 =>
      congr_pr_rec
        (compRenRen_proc (upRen_proc_proc xi_proc) (upRen_proc_Data xi_Data)
           (upRen_proc_proc zeta_proc) (upRen_proc_Data zeta_Data)
           (upRen_proc_proc rho_proc) (upRen_proc_Data rho_Data)
           (up_ren_ren _ _ _ Eq_proc) Eq_Data s0)
  | pr_par s0 s1 =>
      congr_pr_par
        (compRenRen_proc xi_proc xi_Data zeta_proc zeta_Data rho_proc
           rho_Data Eq_proc Eq_Data s0)
        (compRenRen_proc xi_proc xi_Data zeta_proc zeta_Data rho_proc
           rho_Data Eq_proc Eq_Data s1)
  | pr_res s0 =>
      congr_pr_res
        (compRenRen_proc (upRen_Data_proc xi_proc) (upRen_Data_Data xi_Data)
           (upRen_Data_proc zeta_proc) (upRen_Data_Data zeta_Data)
           (upRen_Data_proc rho_proc) (upRen_Data_Data rho_Data) Eq_proc
           (up_ren_ren _ _ _ Eq_Data) s0)
  | pr_if_then_else s0 s1 s2 =>
      congr_pr_if_then_else
        (compRenRen_Equation xi_Data zeta_Data rho_Data Eq_Data s0)
        (compRenRen_proc xi_proc xi_Data zeta_proc zeta_Data rho_proc
           rho_Data Eq_proc Eq_Data s1)
        (compRenRen_proc xi_proc xi_Data zeta_proc zeta_Data rho_proc
           rho_Data Eq_proc Eq_Data s2)
  | g s0 =>
      congr_g
        (compRenRen_gproc xi_proc xi_Data zeta_proc zeta_Data rho_proc
           rho_Data Eq_proc Eq_Data s0)
  end
with compRenRen_gproc (xi_proc : nat -> nat) (xi_Data : nat -> nat)
(zeta_proc : nat -> nat) (zeta_Data : nat -> nat) (rho_proc : nat -> nat)
(rho_Data : nat -> nat)
(Eq_proc : forall x, funcomp zeta_proc xi_proc x = rho_proc x)
(Eq_Data : forall x, funcomp zeta_Data xi_Data x = rho_Data x) (s : gproc)
{struct s} :
ren_gproc zeta_proc zeta_Data (ren_gproc xi_proc xi_Data s) =
ren_gproc rho_proc rho_Data s :=
  match s with
  | gpr_success => congr_gpr_success
  | gpr_nil => congr_gpr_nil
  | gpr_output s0 s1 s2 =>
      congr_gpr_output
        (compRenRen_Data xi_Data zeta_Data rho_Data Eq_Data s0)
        (compRenRen_Data xi_Data zeta_Data rho_Data Eq_Data s1)
        (compRenRen_proc xi_proc xi_Data zeta_proc zeta_Data rho_proc
           rho_Data Eq_proc Eq_Data s2)
  | gpr_input s0 s1 =>
      congr_gpr_input (compRenRen_Data xi_Data zeta_Data rho_Data Eq_Data s0)
        (compRenRen_proc (upRen_Data_proc xi_proc) (upRen_Data_Data xi_Data)
           (upRen_Data_proc zeta_proc) (upRen_Data_Data zeta_Data)
           (upRen_Data_proc rho_proc) (upRen_Data_Data rho_Data) Eq_proc
           (up_ren_ren _ _ _ Eq_Data) s1)
  | gpr_tau s0 =>
      congr_gpr_tau
        (compRenRen_proc xi_proc xi_Data zeta_proc zeta_Data rho_proc
           rho_Data Eq_proc Eq_Data s0)
  | gpr_choice s0 s1 =>
      congr_gpr_choice
        (compRenRen_gproc xi_proc xi_Data zeta_proc zeta_Data rho_proc
           rho_Data Eq_proc Eq_Data s0)
        (compRenRen_gproc xi_proc xi_Data zeta_proc zeta_Data rho_proc
           rho_Data Eq_proc Eq_Data s1)
  end.

Lemma up_ren_subst_proc_proc (xi : nat -> nat) (tau : nat -> proc)
  (theta : nat -> proc) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_proc_proc tau) (upRen_proc_proc xi) x = up_proc_proc theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_proc shift id) (Eq n')
       | O => eq_refl
       end).
Qed.

Lemma up_ren_subst_proc_Data (xi : nat -> nat) (tau : nat -> Data)
  (theta : nat -> Data) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_proc_Data tau) (upRen_proc_Data xi) x = up_proc_Data theta x.
Proof.
exact (fun n => ap (ren_Data id) (Eq n)).
Qed.

Lemma up_ren_subst_Data_proc (xi : nat -> nat) (tau : nat -> proc)
  (theta : nat -> proc) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_Data_proc tau) (upRen_Data_proc xi) x = up_Data_proc theta x.
Proof.
exact (fun n => ap (ren_proc id shift) (Eq n)).
Qed.

Fixpoint compRenSubst_proc (xi_proc : nat -> nat) (xi_Data : nat -> nat)
(tau_proc : nat -> proc) (tau_Data : nat -> Data) (theta_proc : nat -> proc)
(theta_Data : nat -> Data)
(Eq_proc : forall x, funcomp tau_proc xi_proc x = theta_proc x)
(Eq_Data : forall x, funcomp tau_Data xi_Data x = theta_Data x) (s : proc)
{struct s} :
subst_proc tau_proc tau_Data (ren_proc xi_proc xi_Data s) =
subst_proc theta_proc theta_Data s :=
  match s with
  | var_proc s0 => Eq_proc s0
  | pr_rec s0 =>
      congr_pr_rec
        (compRenSubst_proc (upRen_proc_proc xi_proc)
           (upRen_proc_Data xi_Data) (up_proc_proc tau_proc)
           (up_proc_Data tau_Data) (up_proc_proc theta_proc)
           (up_proc_Data theta_Data) (up_ren_subst_proc_proc _ _ _ Eq_proc)
           (up_ren_subst_proc_Data _ _ _ Eq_Data) s0)
  | pr_par s0 s1 =>
      congr_pr_par
        (compRenSubst_proc xi_proc xi_Data tau_proc tau_Data theta_proc
           theta_Data Eq_proc Eq_Data s0)
        (compRenSubst_proc xi_proc xi_Data tau_proc tau_Data theta_proc
           theta_Data Eq_proc Eq_Data s1)
  | pr_res s0 =>
      congr_pr_res
        (compRenSubst_proc (upRen_Data_proc xi_proc)
           (upRen_Data_Data xi_Data) (up_Data_proc tau_proc)
           (up_Data_Data tau_Data) (up_Data_proc theta_proc)
           (up_Data_Data theta_Data) (up_ren_subst_Data_proc _ _ _ Eq_proc)
           (up_ren_subst_Data_Data _ _ _ Eq_Data) s0)
  | pr_if_then_else s0 s1 s2 =>
      congr_pr_if_then_else
        (compRenSubst_Equation xi_Data tau_Data theta_Data Eq_Data s0)
        (compRenSubst_proc xi_proc xi_Data tau_proc tau_Data theta_proc
           theta_Data Eq_proc Eq_Data s1)
        (compRenSubst_proc xi_proc xi_Data tau_proc tau_Data theta_proc
           theta_Data Eq_proc Eq_Data s2)
  | g s0 =>
      congr_g
        (compRenSubst_gproc xi_proc xi_Data tau_proc tau_Data theta_proc
           theta_Data Eq_proc Eq_Data s0)
  end
with compRenSubst_gproc (xi_proc : nat -> nat) (xi_Data : nat -> nat)
(tau_proc : nat -> proc) (tau_Data : nat -> Data) (theta_proc : nat -> proc)
(theta_Data : nat -> Data)
(Eq_proc : forall x, funcomp tau_proc xi_proc x = theta_proc x)
(Eq_Data : forall x, funcomp tau_Data xi_Data x = theta_Data x) (s : gproc)
{struct s} :
subst_gproc tau_proc tau_Data (ren_gproc xi_proc xi_Data s) =
subst_gproc theta_proc theta_Data s :=
  match s with
  | gpr_success => congr_gpr_success
  | gpr_nil => congr_gpr_nil
  | gpr_output s0 s1 s2 =>
      congr_gpr_output
        (compRenSubst_Data xi_Data tau_Data theta_Data Eq_Data s0)
        (compRenSubst_Data xi_Data tau_Data theta_Data Eq_Data s1)
        (compRenSubst_proc xi_proc xi_Data tau_proc tau_Data theta_proc
           theta_Data Eq_proc Eq_Data s2)
  | gpr_input s0 s1 =>
      congr_gpr_input
        (compRenSubst_Data xi_Data tau_Data theta_Data Eq_Data s0)
        (compRenSubst_proc (upRen_Data_proc xi_proc)
           (upRen_Data_Data xi_Data) (up_Data_proc tau_proc)
           (up_Data_Data tau_Data) (up_Data_proc theta_proc)
           (up_Data_Data theta_Data) (up_ren_subst_Data_proc _ _ _ Eq_proc)
           (up_ren_subst_Data_Data _ _ _ Eq_Data) s1)
  | gpr_tau s0 =>
      congr_gpr_tau
        (compRenSubst_proc xi_proc xi_Data tau_proc tau_Data theta_proc
           theta_Data Eq_proc Eq_Data s0)
  | gpr_choice s0 s1 =>
      congr_gpr_choice
        (compRenSubst_gproc xi_proc xi_Data tau_proc tau_Data theta_proc
           theta_Data Eq_proc Eq_Data s0)
        (compRenSubst_gproc xi_proc xi_Data tau_proc tau_Data theta_proc
           theta_Data Eq_proc Eq_Data s1)
  end.

Lemma up_subst_ren_proc_proc (sigma : nat -> proc) (zeta_proc : nat -> nat)
  (zeta_Data : nat -> nat) (theta : nat -> proc)
  (Eq : forall x, funcomp (ren_proc zeta_proc zeta_Data) sigma x = theta x) :
  forall x,
  funcomp (ren_proc (upRen_proc_proc zeta_proc) (upRen_proc_Data zeta_Data))
    (up_proc_proc sigma) x = up_proc_proc theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_proc shift id (upRen_proc_proc zeta_proc)
                (upRen_proc_Data zeta_Data) (funcomp shift zeta_proc)
                (funcomp id zeta_Data) (fun x => eq_refl) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_proc zeta_proc zeta_Data shift id
                      (funcomp shift zeta_proc) (funcomp id zeta_Data)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma n')))
                (ap (ren_proc shift id) (Eq n')))
       | O => eq_refl
       end).
Qed.

Lemma up_subst_ren_proc_Data (sigma : nat -> Data) (zeta_Data : nat -> nat)
  (theta : nat -> Data)
  (Eq : forall x, funcomp (ren_Data zeta_Data) sigma x = theta x) :
  forall x,
  funcomp (ren_Data (upRen_proc_Data zeta_Data)) (up_proc_Data sigma) x =
  up_proc_Data theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_Data id (upRen_proc_Data zeta_Data)
            (funcomp id zeta_Data) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_Data zeta_Data id (funcomp id zeta_Data)
                  (fun x => eq_refl) (sigma n))) (ap (ren_Data id) (Eq n)))).
Qed.

Lemma up_subst_ren_Data_proc (sigma : nat -> proc) (zeta_proc : nat -> nat)
  (zeta_Data : nat -> nat) (theta : nat -> proc)
  (Eq : forall x, funcomp (ren_proc zeta_proc zeta_Data) sigma x = theta x) :
  forall x,
  funcomp (ren_proc (upRen_Data_proc zeta_proc) (upRen_Data_Data zeta_Data))
    (up_Data_proc sigma) x = up_Data_proc theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_proc id shift (upRen_Data_proc zeta_proc)
            (upRen_Data_Data zeta_Data) (funcomp id zeta_proc)
            (funcomp shift zeta_Data) (fun x => eq_refl) (fun x => eq_refl)
            (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_proc zeta_proc zeta_Data id shift
                  (funcomp id zeta_proc) (funcomp shift zeta_Data)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_proc id shift) (Eq n)))).
Qed.

Fixpoint compSubstRen_proc (sigma_proc : nat -> proc)
(sigma_Data : nat -> Data) (zeta_proc : nat -> nat) (zeta_Data : nat -> nat)
(theta_proc : nat -> proc) (theta_Data : nat -> Data)
(Eq_proc : forall x,
           funcomp (ren_proc zeta_proc zeta_Data) sigma_proc x = theta_proc x)
(Eq_Data : forall x, funcomp (ren_Data zeta_Data) sigma_Data x = theta_Data x)
(s : proc) {struct s} :
ren_proc zeta_proc zeta_Data (subst_proc sigma_proc sigma_Data s) =
subst_proc theta_proc theta_Data s :=
  match s with
  | var_proc s0 => Eq_proc s0
  | pr_rec s0 =>
      congr_pr_rec
        (compSubstRen_proc (up_proc_proc sigma_proc)
           (up_proc_Data sigma_Data) (upRen_proc_proc zeta_proc)
           (upRen_proc_Data zeta_Data) (up_proc_proc theta_proc)
           (up_proc_Data theta_Data) (up_subst_ren_proc_proc _ _ _ _ Eq_proc)
           (up_subst_ren_proc_Data _ _ _ Eq_Data) s0)
  | pr_par s0 s1 =>
      congr_pr_par
        (compSubstRen_proc sigma_proc sigma_Data zeta_proc zeta_Data
           theta_proc theta_Data Eq_proc Eq_Data s0)
        (compSubstRen_proc sigma_proc sigma_Data zeta_proc zeta_Data
           theta_proc theta_Data Eq_proc Eq_Data s1)
  | pr_res s0 =>
      congr_pr_res
        (compSubstRen_proc (up_Data_proc sigma_proc)
           (up_Data_Data sigma_Data) (upRen_Data_proc zeta_proc)
           (upRen_Data_Data zeta_Data) (up_Data_proc theta_proc)
           (up_Data_Data theta_Data) (up_subst_ren_Data_proc _ _ _ _ Eq_proc)
           (up_subst_ren_Data_Data _ _ _ Eq_Data) s0)
  | pr_if_then_else s0 s1 s2 =>
      congr_pr_if_then_else
        (compSubstRen_Equation sigma_Data zeta_Data theta_Data Eq_Data s0)
        (compSubstRen_proc sigma_proc sigma_Data zeta_proc zeta_Data
           theta_proc theta_Data Eq_proc Eq_Data s1)
        (compSubstRen_proc sigma_proc sigma_Data zeta_proc zeta_Data
           theta_proc theta_Data Eq_proc Eq_Data s2)
  | g s0 =>
      congr_g
        (compSubstRen_gproc sigma_proc sigma_Data zeta_proc zeta_Data
           theta_proc theta_Data Eq_proc Eq_Data s0)
  end
with compSubstRen_gproc (sigma_proc : nat -> proc) (sigma_Data : nat -> Data)
(zeta_proc : nat -> nat) (zeta_Data : nat -> nat) (theta_proc : nat -> proc)
(theta_Data : nat -> Data)
(Eq_proc : forall x,
           funcomp (ren_proc zeta_proc zeta_Data) sigma_proc x = theta_proc x)
(Eq_Data : forall x, funcomp (ren_Data zeta_Data) sigma_Data x = theta_Data x)
(s : gproc) {struct s} :
ren_gproc zeta_proc zeta_Data (subst_gproc sigma_proc sigma_Data s) =
subst_gproc theta_proc theta_Data s :=
  match s with
  | gpr_success => congr_gpr_success
  | gpr_nil => congr_gpr_nil
  | gpr_output s0 s1 s2 =>
      congr_gpr_output
        (compSubstRen_Data sigma_Data zeta_Data theta_Data Eq_Data s0)
        (compSubstRen_Data sigma_Data zeta_Data theta_Data Eq_Data s1)
        (compSubstRen_proc sigma_proc sigma_Data zeta_proc zeta_Data
           theta_proc theta_Data Eq_proc Eq_Data s2)
  | gpr_input s0 s1 =>
      congr_gpr_input
        (compSubstRen_Data sigma_Data zeta_Data theta_Data Eq_Data s0)
        (compSubstRen_proc (up_Data_proc sigma_proc)
           (up_Data_Data sigma_Data) (upRen_Data_proc zeta_proc)
           (upRen_Data_Data zeta_Data) (up_Data_proc theta_proc)
           (up_Data_Data theta_Data) (up_subst_ren_Data_proc _ _ _ _ Eq_proc)
           (up_subst_ren_Data_Data _ _ _ Eq_Data) s1)
  | gpr_tau s0 =>
      congr_gpr_tau
        (compSubstRen_proc sigma_proc sigma_Data zeta_proc zeta_Data
           theta_proc theta_Data Eq_proc Eq_Data s0)
  | gpr_choice s0 s1 =>
      congr_gpr_choice
        (compSubstRen_gproc sigma_proc sigma_Data zeta_proc zeta_Data
           theta_proc theta_Data Eq_proc Eq_Data s0)
        (compSubstRen_gproc sigma_proc sigma_Data zeta_proc zeta_Data
           theta_proc theta_Data Eq_proc Eq_Data s1)
  end.

Lemma up_subst_subst_proc_proc (sigma : nat -> proc) (tau_proc : nat -> proc)
  (tau_Data : nat -> Data) (theta : nat -> proc)
  (Eq : forall x, funcomp (subst_proc tau_proc tau_Data) sigma x = theta x) :
  forall x,
  funcomp (subst_proc (up_proc_proc tau_proc) (up_proc_Data tau_Data))
    (up_proc_proc sigma) x = up_proc_proc theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_proc shift id (up_proc_proc tau_proc)
                (up_proc_Data tau_Data)
                (funcomp (up_proc_proc tau_proc) shift)
                (funcomp (up_proc_Data tau_Data) id) (fun x => eq_refl)
                (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_proc tau_proc tau_Data shift id
                      (funcomp (ren_proc shift id) tau_proc)
                      (funcomp (ren_Data id) tau_Data) (fun x => eq_refl)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_proc shift id) (Eq n')))
       | O => eq_refl
       end).
Qed.

Lemma up_subst_subst_proc_Data (sigma : nat -> Data) (tau_Data : nat -> Data)
  (theta : nat -> Data)
  (Eq : forall x, funcomp (subst_Data tau_Data) sigma x = theta x) :
  forall x,
  funcomp (subst_Data (up_proc_Data tau_Data)) (up_proc_Data sigma) x =
  up_proc_Data theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_Data id (up_proc_Data tau_Data)
            (funcomp (up_proc_Data tau_Data) id) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_Data tau_Data id
                  (funcomp (ren_Data id) tau_Data) (fun x => eq_refl)
                  (sigma n))) (ap (ren_Data id) (Eq n)))).
Qed.

Lemma up_subst_subst_Data_proc (sigma : nat -> proc) (tau_proc : nat -> proc)
  (tau_Data : nat -> Data) (theta : nat -> proc)
  (Eq : forall x, funcomp (subst_proc tau_proc tau_Data) sigma x = theta x) :
  forall x,
  funcomp (subst_proc (up_Data_proc tau_proc) (up_Data_Data tau_Data))
    (up_Data_proc sigma) x = up_Data_proc theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_proc id shift (up_Data_proc tau_proc)
            (up_Data_Data tau_Data) (funcomp (up_Data_proc tau_proc) id)
            (funcomp (up_Data_Data tau_Data) shift) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_proc tau_proc tau_Data id shift
                  (funcomp (ren_proc id shift) tau_proc)
                  (funcomp (ren_Data shift) tau_Data) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_proc id shift) (Eq n)))).
Qed.

Fixpoint compSubstSubst_proc (sigma_proc : nat -> proc)
(sigma_Data : nat -> Data) (tau_proc : nat -> proc) (tau_Data : nat -> Data)
(theta_proc : nat -> proc) (theta_Data : nat -> Data)
(Eq_proc : forall x,
           funcomp (subst_proc tau_proc tau_Data) sigma_proc x = theta_proc x)
(Eq_Data : forall x,
           funcomp (subst_Data tau_Data) sigma_Data x = theta_Data x)
(s : proc) {struct s} :
subst_proc tau_proc tau_Data (subst_proc sigma_proc sigma_Data s) =
subst_proc theta_proc theta_Data s :=
  match s with
  | var_proc s0 => Eq_proc s0
  | pr_rec s0 =>
      congr_pr_rec
        (compSubstSubst_proc (up_proc_proc sigma_proc)
           (up_proc_Data sigma_Data) (up_proc_proc tau_proc)
           (up_proc_Data tau_Data) (up_proc_proc theta_proc)
           (up_proc_Data theta_Data)
           (up_subst_subst_proc_proc _ _ _ _ Eq_proc)
           (up_subst_subst_proc_Data _ _ _ Eq_Data) s0)
  | pr_par s0 s1 =>
      congr_pr_par
        (compSubstSubst_proc sigma_proc sigma_Data tau_proc tau_Data
           theta_proc theta_Data Eq_proc Eq_Data s0)
        (compSubstSubst_proc sigma_proc sigma_Data tau_proc tau_Data
           theta_proc theta_Data Eq_proc Eq_Data s1)
  | pr_res s0 =>
      congr_pr_res
        (compSubstSubst_proc (up_Data_proc sigma_proc)
           (up_Data_Data sigma_Data) (up_Data_proc tau_proc)
           (up_Data_Data tau_Data) (up_Data_proc theta_proc)
           (up_Data_Data theta_Data)
           (up_subst_subst_Data_proc _ _ _ _ Eq_proc)
           (up_subst_subst_Data_Data _ _ _ Eq_Data) s0)
  | pr_if_then_else s0 s1 s2 =>
      congr_pr_if_then_else
        (compSubstSubst_Equation sigma_Data tau_Data theta_Data Eq_Data s0)
        (compSubstSubst_proc sigma_proc sigma_Data tau_proc tau_Data
           theta_proc theta_Data Eq_proc Eq_Data s1)
        (compSubstSubst_proc sigma_proc sigma_Data tau_proc tau_Data
           theta_proc theta_Data Eq_proc Eq_Data s2)
  | g s0 =>
      congr_g
        (compSubstSubst_gproc sigma_proc sigma_Data tau_proc tau_Data
           theta_proc theta_Data Eq_proc Eq_Data s0)
  end
with compSubstSubst_gproc (sigma_proc : nat -> proc)
(sigma_Data : nat -> Data) (tau_proc : nat -> proc) (tau_Data : nat -> Data)
(theta_proc : nat -> proc) (theta_Data : nat -> Data)
(Eq_proc : forall x,
           funcomp (subst_proc tau_proc tau_Data) sigma_proc x = theta_proc x)
(Eq_Data : forall x,
           funcomp (subst_Data tau_Data) sigma_Data x = theta_Data x)
(s : gproc) {struct s} :
subst_gproc tau_proc tau_Data (subst_gproc sigma_proc sigma_Data s) =
subst_gproc theta_proc theta_Data s :=
  match s with
  | gpr_success => congr_gpr_success
  | gpr_nil => congr_gpr_nil
  | gpr_output s0 s1 s2 =>
      congr_gpr_output
        (compSubstSubst_Data sigma_Data tau_Data theta_Data Eq_Data s0)
        (compSubstSubst_Data sigma_Data tau_Data theta_Data Eq_Data s1)
        (compSubstSubst_proc sigma_proc sigma_Data tau_proc tau_Data
           theta_proc theta_Data Eq_proc Eq_Data s2)
  | gpr_input s0 s1 =>
      congr_gpr_input
        (compSubstSubst_Data sigma_Data tau_Data theta_Data Eq_Data s0)
        (compSubstSubst_proc (up_Data_proc sigma_proc)
           (up_Data_Data sigma_Data) (up_Data_proc tau_proc)
           (up_Data_Data tau_Data) (up_Data_proc theta_proc)
           (up_Data_Data theta_Data)
           (up_subst_subst_Data_proc _ _ _ _ Eq_proc)
           (up_subst_subst_Data_Data _ _ _ Eq_Data) s1)
  | gpr_tau s0 =>
      congr_gpr_tau
        (compSubstSubst_proc sigma_proc sigma_Data tau_proc tau_Data
           theta_proc theta_Data Eq_proc Eq_Data s0)
  | gpr_choice s0 s1 =>
      congr_gpr_choice
        (compSubstSubst_gproc sigma_proc sigma_Data tau_proc tau_Data
           theta_proc theta_Data Eq_proc Eq_Data s0)
        (compSubstSubst_gproc sigma_proc sigma_Data tau_proc tau_Data
           theta_proc theta_Data Eq_proc Eq_Data s1)
  end.

Lemma renRen_proc (xi_proc : nat -> nat) (xi_Data : nat -> nat)
  (zeta_proc : nat -> nat) (zeta_Data : nat -> nat) (s : proc) :
  ren_proc zeta_proc zeta_Data (ren_proc xi_proc xi_Data s) =
  ren_proc (funcomp zeta_proc xi_proc) (funcomp zeta_Data xi_Data) s.
Proof.
exact (compRenRen_proc xi_proc xi_Data zeta_proc zeta_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renRen'_proc_pointwise (xi_proc : nat -> nat) (xi_Data : nat -> nat)
  (zeta_proc : nat -> nat) (zeta_Data : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_proc zeta_proc zeta_Data) (ren_proc xi_proc xi_Data))
    (ren_proc (funcomp zeta_proc xi_proc) (funcomp zeta_Data xi_Data)).
Proof.
exact (fun s =>
       compRenRen_proc xi_proc xi_Data zeta_proc zeta_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renRen_gproc (xi_proc : nat -> nat) (xi_Data : nat -> nat)
  (zeta_proc : nat -> nat) (zeta_Data : nat -> nat) (s : gproc) :
  ren_gproc zeta_proc zeta_Data (ren_gproc xi_proc xi_Data s) =
  ren_gproc (funcomp zeta_proc xi_proc) (funcomp zeta_Data xi_Data) s.
Proof.
exact (compRenRen_gproc xi_proc xi_Data zeta_proc zeta_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renRen'_gproc_pointwise (xi_proc : nat -> nat) (xi_Data : nat -> nat)
  (zeta_proc : nat -> nat) (zeta_Data : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_gproc zeta_proc zeta_Data) (ren_gproc xi_proc xi_Data))
    (ren_gproc (funcomp zeta_proc xi_proc) (funcomp zeta_Data xi_Data)).
Proof.
exact (fun s =>
       compRenRen_gproc xi_proc xi_Data zeta_proc zeta_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renSubst_proc (xi_proc : nat -> nat) (xi_Data : nat -> nat)
  (tau_proc : nat -> proc) (tau_Data : nat -> Data) (s : proc) :
  subst_proc tau_proc tau_Data (ren_proc xi_proc xi_Data s) =
  subst_proc (funcomp tau_proc xi_proc) (funcomp tau_Data xi_Data) s.
Proof.
exact (compRenSubst_proc xi_proc xi_Data tau_proc tau_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renSubst_proc_pointwise (xi_proc : nat -> nat) (xi_Data : nat -> nat)
  (tau_proc : nat -> proc) (tau_Data : nat -> Data) :
  pointwise_relation _ eq
    (funcomp (subst_proc tau_proc tau_Data) (ren_proc xi_proc xi_Data))
    (subst_proc (funcomp tau_proc xi_proc) (funcomp tau_Data xi_Data)).
Proof.
exact (fun s =>
       compRenSubst_proc xi_proc xi_Data tau_proc tau_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renSubst_gproc (xi_proc : nat -> nat) (xi_Data : nat -> nat)
  (tau_proc : nat -> proc) (tau_Data : nat -> Data) (s : gproc) :
  subst_gproc tau_proc tau_Data (ren_gproc xi_proc xi_Data s) =
  subst_gproc (funcomp tau_proc xi_proc) (funcomp tau_Data xi_Data) s.
Proof.
exact (compRenSubst_gproc xi_proc xi_Data tau_proc tau_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renSubst_gproc_pointwise (xi_proc : nat -> nat) (xi_Data : nat -> nat)
  (tau_proc : nat -> proc) (tau_Data : nat -> Data) :
  pointwise_relation _ eq
    (funcomp (subst_gproc tau_proc tau_Data) (ren_gproc xi_proc xi_Data))
    (subst_gproc (funcomp tau_proc xi_proc) (funcomp tau_Data xi_Data)).
Proof.
exact (fun s =>
       compRenSubst_gproc xi_proc xi_Data tau_proc tau_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_proc (sigma_proc : nat -> proc) (sigma_Data : nat -> Data)
  (zeta_proc : nat -> nat) (zeta_Data : nat -> nat) (s : proc) :
  ren_proc zeta_proc zeta_Data (subst_proc sigma_proc sigma_Data s) =
  subst_proc (funcomp (ren_proc zeta_proc zeta_Data) sigma_proc)
    (funcomp (ren_Data zeta_Data) sigma_Data) s.
Proof.
exact (compSubstRen_proc sigma_proc sigma_Data zeta_proc zeta_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_proc_pointwise (sigma_proc : nat -> proc)
  (sigma_Data : nat -> Data) (zeta_proc : nat -> nat)
  (zeta_Data : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_proc zeta_proc zeta_Data)
       (subst_proc sigma_proc sigma_Data))
    (subst_proc (funcomp (ren_proc zeta_proc zeta_Data) sigma_proc)
       (funcomp (ren_Data zeta_Data) sigma_Data)).
Proof.
exact (fun s =>
       compSubstRen_proc sigma_proc sigma_Data zeta_proc zeta_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_gproc (sigma_proc : nat -> proc) (sigma_Data : nat -> Data)
  (zeta_proc : nat -> nat) (zeta_Data : nat -> nat) (s : gproc) :
  ren_gproc zeta_proc zeta_Data (subst_gproc sigma_proc sigma_Data s) =
  subst_gproc (funcomp (ren_proc zeta_proc zeta_Data) sigma_proc)
    (funcomp (ren_Data zeta_Data) sigma_Data) s.
Proof.
exact (compSubstRen_gproc sigma_proc sigma_Data zeta_proc zeta_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_gproc_pointwise (sigma_proc : nat -> proc)
  (sigma_Data : nat -> Data) (zeta_proc : nat -> nat)
  (zeta_Data : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_gproc zeta_proc zeta_Data)
       (subst_gproc sigma_proc sigma_Data))
    (subst_gproc (funcomp (ren_proc zeta_proc zeta_Data) sigma_proc)
       (funcomp (ren_Data zeta_Data) sigma_Data)).
Proof.
exact (fun s =>
       compSubstRen_gproc sigma_proc sigma_Data zeta_proc zeta_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_proc (sigma_proc : nat -> proc) (sigma_Data : nat -> Data)
  (tau_proc : nat -> proc) (tau_Data : nat -> Data) (s : proc) :
  subst_proc tau_proc tau_Data (subst_proc sigma_proc sigma_Data s) =
  subst_proc (funcomp (subst_proc tau_proc tau_Data) sigma_proc)
    (funcomp (subst_Data tau_Data) sigma_Data) s.
Proof.
exact (compSubstSubst_proc sigma_proc sigma_Data tau_proc tau_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_proc_pointwise (sigma_proc : nat -> proc)
  (sigma_Data : nat -> Data) (tau_proc : nat -> proc)
  (tau_Data : nat -> Data) :
  pointwise_relation _ eq
    (funcomp (subst_proc tau_proc tau_Data)
       (subst_proc sigma_proc sigma_Data))
    (subst_proc (funcomp (subst_proc tau_proc tau_Data) sigma_proc)
       (funcomp (subst_Data tau_Data) sigma_Data)).
Proof.
exact (fun s =>
       compSubstSubst_proc sigma_proc sigma_Data tau_proc tau_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_gproc (sigma_proc : nat -> proc) (sigma_Data : nat -> Data)
  (tau_proc : nat -> proc) (tau_Data : nat -> Data) (s : gproc) :
  subst_gproc tau_proc tau_Data (subst_gproc sigma_proc sigma_Data s) =
  subst_gproc (funcomp (subst_proc tau_proc tau_Data) sigma_proc)
    (funcomp (subst_Data tau_Data) sigma_Data) s.
Proof.
exact (compSubstSubst_gproc sigma_proc sigma_Data tau_proc tau_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_gproc_pointwise (sigma_proc : nat -> proc)
  (sigma_Data : nat -> Data) (tau_proc : nat -> proc)
  (tau_Data : nat -> Data) :
  pointwise_relation _ eq
    (funcomp (subst_gproc tau_proc tau_Data)
       (subst_gproc sigma_proc sigma_Data))
    (subst_gproc (funcomp (subst_proc tau_proc tau_Data) sigma_proc)
       (funcomp (subst_Data tau_Data) sigma_Data)).
Proof.
exact (fun s =>
       compSubstSubst_gproc sigma_proc sigma_Data tau_proc tau_Data _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_proc_proc (xi : nat -> nat) (sigma : nat -> proc)
  (Eq : forall x, funcomp (var_proc) xi x = sigma x) :
  forall x, funcomp (var_proc) (upRen_proc_proc xi) x = up_proc_proc sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_proc shift id) (Eq n')
       | O => eq_refl
       end).
Qed.

Lemma rinstInst_up_proc_Data (xi : nat -> nat) (sigma : nat -> Data)
  (Eq : forall x, funcomp (var_Data) xi x = sigma x) :
  forall x, funcomp (var_Data) (upRen_proc_Data xi) x = up_proc_Data sigma x.
Proof.
exact (fun n => ap (ren_Data id) (Eq n)).
Qed.

Lemma rinstInst_up_Data_proc (xi : nat -> nat) (sigma : nat -> proc)
  (Eq : forall x, funcomp (var_proc) xi x = sigma x) :
  forall x, funcomp (var_proc) (upRen_Data_proc xi) x = up_Data_proc sigma x.
Proof.
exact (fun n => ap (ren_proc id shift) (Eq n)).
Qed.

Fixpoint rinst_inst_proc (xi_proc : nat -> nat) (xi_Data : nat -> nat)
(sigma_proc : nat -> proc) (sigma_Data : nat -> Data)
(Eq_proc : forall x, funcomp (var_proc) xi_proc x = sigma_proc x)
(Eq_Data : forall x, funcomp (var_Data) xi_Data x = sigma_Data x) (s : proc)
{struct s} : ren_proc xi_proc xi_Data s = subst_proc sigma_proc sigma_Data s
:=
  match s with
  | var_proc s0 => Eq_proc s0
  | pr_rec s0 =>
      congr_pr_rec
        (rinst_inst_proc (upRen_proc_proc xi_proc) (upRen_proc_Data xi_Data)
           (up_proc_proc sigma_proc) (up_proc_Data sigma_Data)
           (rinstInst_up_proc_proc _ _ Eq_proc)
           (rinstInst_up_proc_Data _ _ Eq_Data) s0)
  | pr_par s0 s1 =>
      congr_pr_par
        (rinst_inst_proc xi_proc xi_Data sigma_proc sigma_Data Eq_proc
           Eq_Data s0)
        (rinst_inst_proc xi_proc xi_Data sigma_proc sigma_Data Eq_proc
           Eq_Data s1)
  | pr_res s0 =>
      congr_pr_res
        (rinst_inst_proc (upRen_Data_proc xi_proc) (upRen_Data_Data xi_Data)
           (up_Data_proc sigma_proc) (up_Data_Data sigma_Data)
           (rinstInst_up_Data_proc _ _ Eq_proc)
           (rinstInst_up_Data_Data _ _ Eq_Data) s0)
  | pr_if_then_else s0 s1 s2 =>
      congr_pr_if_then_else
        (rinst_inst_Equation xi_Data sigma_Data Eq_Data s0)
        (rinst_inst_proc xi_proc xi_Data sigma_proc sigma_Data Eq_proc
           Eq_Data s1)
        (rinst_inst_proc xi_proc xi_Data sigma_proc sigma_Data Eq_proc
           Eq_Data s2)
  | g s0 =>
      congr_g
        (rinst_inst_gproc xi_proc xi_Data sigma_proc sigma_Data Eq_proc
           Eq_Data s0)
  end
with rinst_inst_gproc (xi_proc : nat -> nat) (xi_Data : nat -> nat)
(sigma_proc : nat -> proc) (sigma_Data : nat -> Data)
(Eq_proc : forall x, funcomp (var_proc) xi_proc x = sigma_proc x)
(Eq_Data : forall x, funcomp (var_Data) xi_Data x = sigma_Data x) (s : gproc)
{struct s} :
ren_gproc xi_proc xi_Data s = subst_gproc sigma_proc sigma_Data s :=
  match s with
  | gpr_success => congr_gpr_success
  | gpr_nil => congr_gpr_nil
  | gpr_output s0 s1 s2 =>
      congr_gpr_output (rinst_inst_Data xi_Data sigma_Data Eq_Data s0)
        (rinst_inst_Data xi_Data sigma_Data Eq_Data s1)
        (rinst_inst_proc xi_proc xi_Data sigma_proc sigma_Data Eq_proc
           Eq_Data s2)
  | gpr_input s0 s1 =>
      congr_gpr_input (rinst_inst_Data xi_Data sigma_Data Eq_Data s0)
        (rinst_inst_proc (upRen_Data_proc xi_proc) (upRen_Data_Data xi_Data)
           (up_Data_proc sigma_proc) (up_Data_Data sigma_Data)
           (rinstInst_up_Data_proc _ _ Eq_proc)
           (rinstInst_up_Data_Data _ _ Eq_Data) s1)
  | gpr_tau s0 =>
      congr_gpr_tau
        (rinst_inst_proc xi_proc xi_Data sigma_proc sigma_Data Eq_proc
           Eq_Data s0)
  | gpr_choice s0 s1 =>
      congr_gpr_choice
        (rinst_inst_gproc xi_proc xi_Data sigma_proc sigma_Data Eq_proc
           Eq_Data s0)
        (rinst_inst_gproc xi_proc xi_Data sigma_proc sigma_Data Eq_proc
           Eq_Data s1)
  end.

Lemma rinstInst'_proc (xi_proc : nat -> nat) (xi_Data : nat -> nat)
  (s : proc) :
  ren_proc xi_proc xi_Data s =
  subst_proc (funcomp (var_proc) xi_proc) (funcomp (var_Data) xi_Data) s.
Proof.
exact (rinst_inst_proc xi_proc xi_Data _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_proc_pointwise (xi_proc : nat -> nat) (xi_Data : nat -> nat)
  :
  pointwise_relation _ eq (ren_proc xi_proc xi_Data)
    (subst_proc (funcomp (var_proc) xi_proc) (funcomp (var_Data) xi_Data)).
Proof.
exact (fun s =>
       rinst_inst_proc xi_proc xi_Data _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_gproc (xi_proc : nat -> nat) (xi_Data : nat -> nat)
  (s : gproc) :
  ren_gproc xi_proc xi_Data s =
  subst_gproc (funcomp (var_proc) xi_proc) (funcomp (var_Data) xi_Data) s.
Proof.
exact (rinst_inst_gproc xi_proc xi_Data _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_gproc_pointwise (xi_proc : nat -> nat)
  (xi_Data : nat -> nat) :
  pointwise_relation _ eq (ren_gproc xi_proc xi_Data)
    (subst_gproc (funcomp (var_proc) xi_proc) (funcomp (var_Data) xi_Data)).
Proof.
exact (fun s =>
       rinst_inst_gproc xi_proc xi_Data _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_proc (s : proc) : subst_proc (var_proc) (var_Data) s = s.
Proof.
exact (idSubst_proc (var_proc) (var_Data) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_proc_pointwise :
  pointwise_relation _ eq (subst_proc (var_proc) (var_Data)) id.
Proof.
exact (fun s =>
       idSubst_proc (var_proc) (var_Data) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_gproc (s : gproc) : subst_gproc (var_proc) (var_Data) s = s.
Proof.
exact (idSubst_gproc (var_proc) (var_Data) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_gproc_pointwise :
  pointwise_relation _ eq (subst_gproc (var_proc) (var_Data)) id.
Proof.
exact (fun s =>
       idSubst_gproc (var_proc) (var_Data) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma rinstId'_proc (s : proc) : ren_proc id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_proc s) (rinstInst'_proc id id s)).
Qed.

Lemma rinstId'_proc_pointwise : pointwise_relation _ eq (@ren_proc id id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_proc s) (rinstInst'_proc id id s)).
Qed.

Lemma rinstId'_gproc (s : gproc) : ren_gproc id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_gproc s) (rinstInst'_gproc id id s)).
Qed.

Lemma rinstId'_gproc_pointwise :
  pointwise_relation _ eq (@ren_gproc id id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_gproc s) (rinstInst'_gproc id id s)).
Qed.

Lemma varL'_proc (sigma_proc : nat -> proc) (sigma_Data : nat -> Data)
  (x : nat) : subst_proc sigma_proc sigma_Data (var_proc x) = sigma_proc x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_proc_pointwise (sigma_proc : nat -> proc)
  (sigma_Data : nat -> Data) :
  pointwise_relation _ eq
    (funcomp (subst_proc sigma_proc sigma_Data) (var_proc)) sigma_proc.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_proc (xi_proc : nat -> nat) (xi_Data : nat -> nat) (x : nat) :
  ren_proc xi_proc xi_Data (var_proc x) = var_proc (xi_proc x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_proc_pointwise (xi_proc : nat -> nat) (xi_Data : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_proc xi_proc xi_Data) (var_proc))
    (funcomp (var_proc) xi_proc).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_gproc X Y :=
    up_gproc : X -> Y.

Class Up_proc X Y :=
    up_proc : X -> Y.

Class Up_Equation X Y :=
    up_Equation : X -> Y.

Class Up_Act X Y :=
    up_Act : X -> Y.

Class Up_ExtAction X Y :=
    up_ExtAction : X -> Y.

Class Up_Data X Y :=
    up_Data : X -> Y.

#[global] Instance Subst_gproc : (Subst2 _ _ _ _) := @subst_gproc.

#[global] Instance Subst_proc : (Subst2 _ _ _ _) := @subst_proc.

#[global] Instance Up_Data_proc : (Up_proc _ _) := @up_Data_proc.

#[global] Instance Up_proc_Data : (Up_Data _ _) := @up_proc_Data.

#[global] Instance Up_proc_proc : (Up_proc _ _) := @up_proc_proc.

#[global] Instance Ren_gproc : (Ren2 _ _ _ _) := @ren_gproc.

#[global] Instance Ren_proc : (Ren2 _ _ _ _) := @ren_proc.

#[global] Instance VarInstance_proc : (Var _ _) := @var_proc.

#[global]
Instance Subst_Equation : (Subst1 _ _ _) := @subst_Equation.

#[global] Instance Ren_Equation : (Ren1 _ _ _) := @ren_Equation.

#[global] Instance Subst_Act : (Subst1 _ _ _) := @subst_Act.

#[global]
Instance Subst_ExtAction : (Subst1 _ _ _) := @subst_ExtAction.

#[global] Instance Subst_Data : (Subst1 _ _ _) := @subst_Data.

#[global] Instance Up_Data_Data : (Up_Data _ _) := @up_Data_Data.

#[global] Instance Ren_Data : (Ren1 _ _ _) := @ren_Data.

#[global]
Instance VarInstance_Data : (Var _ _) := @var_Data.

Notation "[ sigma_proc ; sigma_Data ]" := (subst_gproc sigma_proc sigma_Data)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_proc ; sigma_Data ]" :=
(subst_gproc sigma_proc sigma_Data s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__gproc" := up_gproc (only printing)  : subst_scope.

Notation "[ sigma_proc ; sigma_Data ]" := (subst_proc sigma_proc sigma_Data)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_proc ; sigma_Data ]" :=
(subst_proc sigma_proc sigma_Data s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__proc" := up_proc (only printing)  : subst_scope.

Notation "↑__proc" := up_Data_proc (only printing)  : subst_scope.

Notation "↑__Data" := up_proc_Data (only printing)  : subst_scope.

Notation "↑__proc" := up_proc_proc (only printing)  : subst_scope.

Notation "⟨ xi_proc ; xi_Data ⟩" := (ren_gproc xi_proc xi_Data)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_proc ; xi_Data ⟩" := (ren_gproc xi_proc xi_Data s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "⟨ xi_proc ; xi_Data ⟩" := (ren_proc xi_proc xi_Data)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_proc ; xi_Data ⟩" := (ren_proc xi_proc xi_Data s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_proc ( at level 1, only printing)  : subst_scope.

Notation "x '__proc'" := (@ids _ _ VarInstance_proc x)
( at level 5, format "x __proc", only printing)  : subst_scope.

Notation "x '__proc'" := (var_proc x) ( at level 5, format "x __proc")  :
subst_scope.

Notation "[ sigma_Data ]" := (subst_Equation sigma_Data)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_Data ]" := (subst_Equation sigma_Data s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Equation" := up_Equation (only printing)  : subst_scope.

Notation "⟨ xi_Data ⟩" := (ren_Equation xi_Data)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_Data ⟩" := (ren_Equation xi_Data s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "[ sigma_Data ]" := (subst_Act sigma_Data)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_Data ]" := (subst_Act sigma_Data s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Act" := up_Act (only printing)  : subst_scope.

Notation "[ sigma_Data ]" := (subst_ExtAction sigma_Data)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_Data ]" := (subst_ExtAction sigma_Data s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__ExtAction" := up_ExtAction (only printing)  : subst_scope.

Notation "[ sigma_Data ]" := (subst_Data sigma_Data)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_Data ]" := (subst_Data sigma_Data s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Data" := up_Data (only printing)  : subst_scope.

Notation "↑__Data" := up_Data_Data (only printing)  : subst_scope.

Notation "⟨ xi_Data ⟩" := (ren_Data xi_Data)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_Data ⟩" := (ren_Data xi_Data s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_Data ( at level 1, only printing)  : subst_scope.

Notation "x '__Data'" := (@ids _ _ VarInstance_Data x)
( at level 5, format "x __Data", only printing)  : subst_scope.

Notation "x '__Data'" := (var_Data x) ( at level 5, format "x __Data")  :
subst_scope.

#[global]
Instance subst_gproc_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_gproc)).
Proof.
exact (fun f_proc g_proc Eq_proc f_Data g_Data Eq_Data s t Eq_st =>
       eq_ind s
         (fun t' =>
          subst_gproc f_proc f_Data s = subst_gproc g_proc g_Data t')
         (ext_gproc f_proc f_Data g_proc g_Data Eq_proc Eq_Data s) t Eq_st).
Qed.

#[global]
Instance subst_gproc_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_gproc)).
Proof.
exact (fun f_proc g_proc Eq_proc f_Data g_Data Eq_Data s =>
       ext_gproc f_proc f_Data g_proc g_Data Eq_proc Eq_Data s).
Qed.

#[global]
Instance subst_proc_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_proc)).
Proof.
exact (fun f_proc g_proc Eq_proc f_Data g_Data Eq_Data s t Eq_st =>
       eq_ind s
         (fun t' => subst_proc f_proc f_Data s = subst_proc g_proc g_Data t')
         (ext_proc f_proc f_Data g_proc g_Data Eq_proc Eq_Data s) t Eq_st).
Qed.

#[global]
Instance subst_proc_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_proc)).
Proof.
exact (fun f_proc g_proc Eq_proc f_Data g_Data Eq_Data s =>
       ext_proc f_proc f_Data g_proc g_Data Eq_proc Eq_Data s).
Qed.

#[global]
Instance ren_gproc_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@ren_gproc)).
Proof.
exact (fun f_proc g_proc Eq_proc f_Data g_Data Eq_Data s t Eq_st =>
       eq_ind s
         (fun t' => ren_gproc f_proc f_Data s = ren_gproc g_proc g_Data t')
         (extRen_gproc f_proc f_Data g_proc g_Data Eq_proc Eq_Data s) t Eq_st).
Qed.

#[global]
Instance ren_gproc_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@ren_gproc)).
Proof.
exact (fun f_proc g_proc Eq_proc f_Data g_Data Eq_Data s =>
       extRen_gproc f_proc f_Data g_proc g_Data Eq_proc Eq_Data s).
Qed.

#[global]
Instance ren_proc_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq))) (@ren_proc)).
Proof.
exact (fun f_proc g_proc Eq_proc f_Data g_Data Eq_Data s t Eq_st =>
       eq_ind s
         (fun t' => ren_proc f_proc f_Data s = ren_proc g_proc g_Data t')
         (extRen_proc f_proc f_Data g_proc g_Data Eq_proc Eq_Data s) t Eq_st).
Qed.

#[global]
Instance ren_proc_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@ren_proc)).
Proof.
exact (fun f_proc g_proc Eq_proc f_Data g_Data Eq_Data s =>
       extRen_proc f_proc f_Data g_proc g_Data Eq_proc Eq_Data s).
Qed.

#[global]
Instance subst_Equation_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Equation)).
Proof.
exact (fun f_Data g_Data Eq_Data s t Eq_st =>
       eq_ind s
         (fun t' => subst_Equation f_Data s = subst_Equation g_Data t')
         (ext_Equation f_Data g_Data Eq_Data s) t Eq_st).
Qed.

#[global]
Instance subst_Equation_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Equation)).
Proof.
exact (fun f_Data g_Data Eq_Data s => ext_Equation f_Data g_Data Eq_Data s).
Qed.

#[global]
Instance ren_Equation_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_Equation)).
Proof.
exact (fun f_Data g_Data Eq_Data s t Eq_st =>
       eq_ind s (fun t' => ren_Equation f_Data s = ren_Equation g_Data t')
         (extRen_Equation f_Data g_Data Eq_Data s) t Eq_st).
Qed.

#[global]
Instance ren_Equation_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Equation)).
Proof.
exact (fun f_Data g_Data Eq_Data s => extRen_Equation f_Data g_Data Eq_Data s).
Qed.

#[global]
Instance subst_Act_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Act)).
Proof.
exact (fun f_Data g_Data Eq_Data s t Eq_st =>
       eq_ind s (fun t' => subst_Act f_Data s = subst_Act g_Data t')
         (ext_Act f_Data g_Data Eq_Data s) t Eq_st).
Qed.

#[global]
Instance subst_Act_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Act)).
Proof.
exact (fun f_Data g_Data Eq_Data s => ext_Act f_Data g_Data Eq_Data s).
Qed.

#[global]
Instance subst_ExtAction_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_ExtAction)).
Proof.
exact (fun f_Data g_Data Eq_Data s t Eq_st =>
       eq_ind s
         (fun t' => subst_ExtAction f_Data s = subst_ExtAction g_Data t')
         (ext_ExtAction f_Data g_Data Eq_Data s) t Eq_st).
Qed.

#[global]
Instance subst_ExtAction_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_ExtAction)).
Proof.
exact (fun f_Data g_Data Eq_Data s => ext_ExtAction f_Data g_Data Eq_Data s).
Qed.

#[global]
Instance subst_Data_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Data)).
Proof.
exact (fun f_Data g_Data Eq_Data s t Eq_st =>
       eq_ind s (fun t' => subst_Data f_Data s = subst_Data g_Data t')
         (ext_Data f_Data g_Data Eq_Data s) t Eq_st).
Qed.

#[global]
Instance subst_Data_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Data)).
Proof.
exact (fun f_Data g_Data Eq_Data s => ext_Data f_Data g_Data Eq_Data s).
Qed.

#[global]
Instance ren_Data_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_Data)).
Proof.
exact (fun f_Data g_Data Eq_Data s t Eq_st =>
       eq_ind s (fun t' => ren_Data f_Data s = ren_Data g_Data t')
         (extRen_Data f_Data g_Data Eq_Data s) t Eq_st).
Qed.

#[global]
Instance ren_Data_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Data)).
Proof.
exact (fun f_Data g_Data Eq_Data s => extRen_Data f_Data g_Data Eq_Data s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_Data, Var, ids, Ren_Data, Ren1, ren1,
                      Up_Data_Data, Up_Data, up_Data, Subst_Data, Subst1,
                      subst1, Subst_ExtAction, Subst1, subst1, Subst_Act,
                      Subst1, subst1, Ren_Equation, Ren1, ren1,
                      Subst_Equation, Subst1, subst1, VarInstance_proc, Var,
                      ids, Ren_proc, Ren2, ren2, Ren_gproc, Ren2, ren2,
                      Up_proc_proc, Up_proc, up_proc, Up_proc_Data, Up_Data,
                      up_Data, Up_Data_proc, Up_proc, up_proc, Subst_proc,
                      Subst2, subst2, Subst_gproc, Subst2, subst2.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_Data, Var, ids,
                                            Ren_Data, Ren1, ren1,
                                            Up_Data_Data, Up_Data, up_Data,
                                            Subst_Data, Subst1, subst1,
                                            Subst_ExtAction, Subst1, subst1,
                                            Subst_Act, Subst1, subst1,
                                            Ren_Equation, Ren1, ren1,
                                            Subst_Equation, Subst1, subst1,
                                            VarInstance_proc, Var, ids,
                                            Ren_proc, Ren2, ren2, Ren_gproc,
                                            Ren2, ren2, Up_proc_proc,
                                            Up_proc, up_proc, Up_proc_Data,
                                            Up_Data, up_Data, Up_Data_proc,
                                            Up_proc, up_proc, Subst_proc,
                                            Subst2, subst2, Subst_gproc,
                                            Subst2, subst2 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_gproc_pointwise
                 | progress setoid_rewrite substSubst_gproc
                 | progress setoid_rewrite substSubst_proc_pointwise
                 | progress setoid_rewrite substSubst_proc
                 | progress setoid_rewrite substRen_gproc_pointwise
                 | progress setoid_rewrite substRen_gproc
                 | progress setoid_rewrite substRen_proc_pointwise
                 | progress setoid_rewrite substRen_proc
                 | progress setoid_rewrite renSubst_gproc_pointwise
                 | progress setoid_rewrite renSubst_gproc
                 | progress setoid_rewrite renSubst_proc_pointwise
                 | progress setoid_rewrite renSubst_proc
                 | progress setoid_rewrite renRen'_gproc_pointwise
                 | progress setoid_rewrite renRen_gproc
                 | progress setoid_rewrite renRen'_proc_pointwise
                 | progress setoid_rewrite renRen_proc
                 | progress setoid_rewrite substSubst_Equation_pointwise
                 | progress setoid_rewrite substSubst_Equation
                 | progress setoid_rewrite substRen_Equation_pointwise
                 | progress setoid_rewrite substRen_Equation
                 | progress setoid_rewrite renSubst_Equation_pointwise
                 | progress setoid_rewrite renSubst_Equation
                 | progress setoid_rewrite renRen'_Equation_pointwise
                 | progress setoid_rewrite renRen_Equation
                 | progress setoid_rewrite substSubst_Act_pointwise
                 | progress setoid_rewrite substSubst_Act
                 | progress setoid_rewrite substSubst_ExtAction_pointwise
                 | progress setoid_rewrite substSubst_ExtAction
                 | progress setoid_rewrite substSubst_Data_pointwise
                 | progress setoid_rewrite substSubst_Data
                 | progress setoid_rewrite substRen_Data_pointwise
                 | progress setoid_rewrite substRen_Data
                 | progress setoid_rewrite renSubst_Data_pointwise
                 | progress setoid_rewrite renSubst_Data
                 | progress setoid_rewrite renRen'_Data_pointwise
                 | progress setoid_rewrite renRen_Data
                 | progress setoid_rewrite varLRen'_proc_pointwise
                 | progress setoid_rewrite varLRen'_proc
                 | progress setoid_rewrite varL'_proc_pointwise
                 | progress setoid_rewrite varL'_proc
                 | progress setoid_rewrite rinstId'_gproc_pointwise
                 | progress setoid_rewrite rinstId'_gproc
                 | progress setoid_rewrite rinstId'_proc_pointwise
                 | progress setoid_rewrite rinstId'_proc
                 | progress setoid_rewrite instId'_gproc_pointwise
                 | progress setoid_rewrite instId'_gproc
                 | progress setoid_rewrite instId'_proc_pointwise
                 | progress setoid_rewrite instId'_proc
                 | progress setoid_rewrite rinstId'_Equation_pointwise
                 | progress setoid_rewrite rinstId'_Equation
                 | progress setoid_rewrite instId'_Equation_pointwise
                 | progress setoid_rewrite instId'_Equation
                 | progress setoid_rewrite instId'_Act_pointwise
                 | progress setoid_rewrite instId'_Act
                 | progress setoid_rewrite instId'_ExtAction_pointwise
                 | progress setoid_rewrite instId'_ExtAction
                 | progress setoid_rewrite varLRen'_Data_pointwise
                 | progress setoid_rewrite varLRen'_Data
                 | progress setoid_rewrite varL'_Data_pointwise
                 | progress setoid_rewrite varL'_Data
                 | progress setoid_rewrite rinstId'_Data_pointwise
                 | progress setoid_rewrite rinstId'_Data
                 | progress setoid_rewrite instId'_Data_pointwise
                 | progress setoid_rewrite instId'_Data
                 | progress
                    unfold up_Data_proc, up_proc_Data, up_proc_proc,
                     upRen_Data_proc, upRen_proc_Data, upRen_proc_proc,
                     up_Data_Data, upRen_Data_Data, up_ren
                 | progress
                    cbn[subst_gproc subst_proc ren_gproc ren_proc
                       subst_Equation ren_Equation subst_Act subst_ExtAction
                       subst_Data ren_Data]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_Data, Var, ids, Ren_Data, Ren1, ren1,
                  Up_Data_Data, Up_Data, up_Data, Subst_Data, Subst1, subst1,
                  Subst_ExtAction, Subst1, subst1, Subst_Act, Subst1, subst1,
                  Ren_Equation, Ren1, ren1, Subst_Equation, Subst1, subst1,
                  VarInstance_proc, Var, ids, Ren_proc, Ren2, ren2,
                  Ren_gproc, Ren2, ren2, Up_proc_proc, Up_proc, up_proc,
                  Up_proc_Data, Up_Data, up_Data, Up_Data_proc, Up_proc,
                  up_proc, Subst_proc, Subst2, subst2, Subst_gproc, Subst2,
                  subst2 in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_gproc_pointwise;
                  try setoid_rewrite rinstInst'_gproc;
                  try setoid_rewrite rinstInst'_proc_pointwise;
                  try setoid_rewrite rinstInst'_proc;
                  try setoid_rewrite rinstInst'_Equation_pointwise;
                  try setoid_rewrite rinstInst'_Equation;
                  try setoid_rewrite rinstInst'_Data_pointwise;
                  try setoid_rewrite rinstInst'_Data.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_gproc_pointwise;
                  try setoid_rewrite_left rinstInst'_gproc;
                  try setoid_rewrite_left rinstInst'_proc_pointwise;
                  try setoid_rewrite_left rinstInst'_proc;
                  try setoid_rewrite_left rinstInst'_Equation_pointwise;
                  try setoid_rewrite_left rinstInst'_Equation;
                  try setoid_rewrite_left rinstInst'_Data_pointwise;
                  try setoid_rewrite_left rinstInst'_Data.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_gproc: rewrite.

#[global] Hint Opaque subst_proc: rewrite.

#[global] Hint Opaque ren_gproc: rewrite.

#[global] Hint Opaque ren_proc: rewrite.

#[global] Hint Opaque subst_Equation: rewrite.

#[global] Hint Opaque ren_Equation: rewrite.

#[global] Hint Opaque subst_Act: rewrite.

#[global] Hint Opaque subst_ExtAction: rewrite.

#[global] Hint Opaque subst_Data: rewrite.

#[global] Hint Opaque ren_Data: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

