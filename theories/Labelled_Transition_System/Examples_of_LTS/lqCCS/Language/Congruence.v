(* begin hide *)
(*
   Copyright (c) 2026 Gaëtan Lopez <glopez@irif.fr>

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
*)
(* end hide *)
(* begin hide *)
(* * lqCCS: structural congruence

    The structural congruence of lqCCS (Ceragioli et al., POPL 2024,
    Figure 2), on the syntax with recursion, in the style of VACCS
    ([VACCS.Language.Congruence]): restricted channels are De Bruijn indices,
    so scope extrusion [(ν P) ∥ Q ≡ ν (P ∥ Q⁺)] has no side condition and
    the order of two restrictions is exchanged by a swap of indices.  Tags
    are kept: congruent processes have the same tags.  The congruence is
    closed under all contexts, recursion included.

    [≡*] is a bisimulation on the program LTS, with the same choices
    ([cgr_bisim]). *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets relations.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS.

#[local] Open Scope lqccs_scope.

(* ** Expressions that evaluate *)

(* [e ⇓ v]. *)
Definition exp_val (e : exp) (v : val) : Prop := eval e = Some v.

Inductive exp_eqv : exp → exp → Prop :=
| ee_refl e : exp_eqv e e
| ee_val e v : exp_val e v → exp_eqv e (EVal v).

Definition exps_eqv : list exp → list exp → Prop := Forall2 exp_eqv.

(* Same prefix, up to the evaluation of its expressions. *)
Inductive prefix_eqv : prefix → prefix → Prop :=
| pe_op t E es es' : exps_eqv es es' → prefix_eqv (POp t E es) (POp t E es')
| pe_meas t M es es' : exps_eqv es es' → prefix_eqv (PMeas t M es) (PMeas t M es')
| pe_init t es es' : exps_eqv es es' → prefix_eqv (PInit t es) (PInit t es').

(* ** One step of congruence *)

Inductive cs : proc → proc → Prop :=
| cs_par_nil P : cs (P ∥ 𝟘) P
| cs_par_comm P Q : cs (P ∥ Q) (Q ∥ P)
| cs_par_assoc P Q R : cs (P ∥ (Q ∥ R)) ((P ∥ Q) ∥ R)
| cs_ite_t e P Q : eval e = Some (VBool true) → cs (PIte e P Q) P
| cs_ite_f e P Q : eval e = Some (VBool false) → cs (PIte e P Q) Q
| cs_send_val t c e e' : exp_eqv e e' → cs (PSend t c e) (PSend t c e')
| cs_ite_val e e' P Q : exp_eqv e e' → cs (PIte e P Q) (PIte e' P Q)
| cs_res_nil es : cs (ν PG (GNil es)) (PG (GNil es))
| cs_res_swap P : cs (ν ν P) (ν ν (ren swap01 P))
| cs_res_scope P Q : cs ((ν P) ∥ Q) (ν (P ∥ ren S Q))
(* contexts *)
| cs_ite_l e P P' Q : cs P P' → cs (PIte e P Q) (PIte e P' Q)
| cs_ite_r e P Q Q' : cs Q Q' → cs (PIte e P Q) (PIte e P Q')
| cs_par_l P P' Q : cs P P' → cs (P ∥ Q) (P' ∥ Q)
| cs_par_r P Q Q' : cs Q Q' → cs (P ∥ Q) (P ∥ Q')
| cs_res P P' : cs P P' → cs (ν P) (ν P')
| cs_rec t X P P' : cs P P' → cs (PRec t X P) (PRec t X P')
| cs_guard g g' : gcs g g' → cs (PG g) (PG g')
with gcs : guard → guard → Prop :=
| gcs_sum_nil g es : gcs (g ⊕ GNil es) g
| gcs_sum_comm g h : gcs (g ⊕ h) (h ⊕ g)
| gcs_sum_assoc g h k : gcs (g ⊕ (h ⊕ k)) ((g ⊕ h) ⊕ k)
| gcs_nil_val es es' : exps_eqv es es' → gcs (GNil es) (GNil es')
| gcs_pre_val 𝜆 𝜆' P : prefix_eqv 𝜆 𝜆' → gcs (𝜆 ∙ P) (𝜆' ∙ P)
(* contexts *)
| gcs_pre 𝜆 P P' : cs P P' → gcs (𝜆 ∙ P) (𝜆 ∙ P')
| gcs_sum_l g g' h : gcs g g' → gcs (g ⊕ h) (g' ⊕ h)
| gcs_sum_r g h h' : gcs h h' → gcs (g ⊕ h) (g ⊕ h').

Scheme cs_mut_ind := Induction for cs Sort Prop
  with gcs_mut_ind := Induction for gcs Sort Prop.
Combined Scheme cs_gcs_ind from cs_mut_ind, gcs_mut_ind.

(* ** The congruence *)

Definition cgr : relation proc := rtsc cs.
Definition gcgr : relation guard := rtsc gcs.

Notation "P ≡* Q" := (cgr P Q) (at level 70) : lqccs_scope.

#[global] Instance cgr_equivalence : Equivalence cgr.
Proof. apply rtsc_equivalence. Qed.

#[global] Instance gcgr_equivalence : Equivalence gcgr.
Proof. apply rtsc_equivalence. Qed.

(* ** Evaluation *)

Lemma exp_eqv_eval e e' : exp_eqv e e' → eval e = eval e'.
Proof. destruct 1 as [|e v He]; [done|]. done. Qed.

Lemma exps_eqv_eval es es' : exps_eqv es es' → eval_qubits es = eval_qubits es'.
Proof.
  induction 1 as [|e e' es es' He _ IH]; [done|]. unfold eval_qubits in *. simpl.
  assert (E : eval_qubit e = eval_qubit e')
    by (unfold eval_qubit; by rewrite (exp_eqv_eval _ _ He)).
  by rewrite E, IH.
Qed.

(* ** Congruence under contexts *)

Lemma cgr_of_cs P Q : cs P Q → P ≡* Q.
Proof. apply rtsc_lr. Qed.

Lemma gcgr_of_gcs g h : gcs g h → gcgr g h.
Proof. apply rtsc_lr. Qed.

Lemma cgr_ctx (f : proc → proc) :
  (∀ P Q, cs P Q → cs (f P) (f Q)) → ∀ P Q, P ≡* Q → f P ≡* f Q.
Proof.
  intros Hf P Q. induction 1 as [P|P Q R [HPQ|HQP] _ IH]; [done| |].
  - etrans; [|exact IH]. apply rtsc_lr. by apply Hf.
  - etrans; [|exact IH]. apply rtsc_rl. by apply Hf.
Qed.

Lemma gcgr_ctx (f : guard → guard) :
  (∀ g h, gcs g h → gcs (f g) (f h)) → ∀ g h, gcgr g h → gcgr (f g) (f h).
Proof.
  intros Hf g h. induction 1 as [g|g h k [Hgh|Hhg] _ IH]; [done| |].
  - etrans; [|exact IH]. apply rtsc_lr. by apply Hf.
  - etrans; [|exact IH]. apply rtsc_rl. by apply Hf.
Qed.

Lemma cgr_par_l P P' Q : P ≡* P' → P ∥ Q ≡* P' ∥ Q.
Proof. apply (cgr_ctx (λ P, P ∥ Q)). intros. by constructor. Qed.

Lemma cgr_par_r P Q Q' : Q ≡* Q' → P ∥ Q ≡* P ∥ Q'.
Proof. apply (cgr_ctx (λ Q, P ∥ Q)). intros. by constructor. Qed.

Lemma cgr_res P P' : P ≡* P' → ν P ≡* ν P'.
Proof. apply (cgr_ctx (λ P, ν P)). intros. by constructor. Qed.

Lemma cgr_rec t X P P' : P ≡* P' → PRec t X P ≡* PRec t X P'.
Proof. apply (cgr_ctx (λ P, PRec t X P)). intros. by constructor. Qed.

Lemma cgr_ite_l e P P' Q : P ≡* P' → PIte e P Q ≡* PIte e P' Q.
Proof. apply (cgr_ctx (λ P, PIte e P Q)). intros. by constructor. Qed.

Lemma cgr_ite_r e P Q Q' : Q ≡* Q' → PIte e P Q ≡* PIte e P Q'.
Proof. apply (cgr_ctx (λ Q, PIte e P Q)). intros. by constructor. Qed.

Lemma cgr_par P P' Q Q' : P ≡* P' → Q ≡* Q' → P ∥ Q ≡* P' ∥ Q'.
Proof. intros. etrans; [by apply cgr_par_l|by apply cgr_par_r]. Qed.

Lemma cgr_ite e P P' Q Q' : P ≡* P' → Q ≡* Q' → PIte e P Q ≡* PIte e P' Q'.
Proof. intros. etrans; [by apply cgr_ite_l|by apply cgr_ite_r]. Qed.

Lemma cgr_guard g h : gcgr g h → PG g ≡* PG h.
Proof.
  induction 1 as [g|g h k [Hgh|Hhg] _ IH]; [done| |].
  - etrans; [|exact IH]. apply rtsc_lr. by constructor.
  - etrans; [|exact IH]. apply rtsc_rl. by constructor.
Qed.

Lemma gcgr_pre 𝜆 P P' : P ≡* P' → gcgr (𝜆 ∙ P) (𝜆 ∙ P').
Proof.
  induction 1 as [P|P Q R [HPQ|HQP] _ IH]; [done| |].
  - etrans; [|exact IH]. apply rtsc_lr. by constructor.
  - etrans; [|exact IH]. apply rtsc_rl. by constructor.
Qed.

Lemma gcgr_sum_l g g' h : gcgr g g' → gcgr (g ⊕ h) (g' ⊕ h).
Proof. apply (gcgr_ctx (λ g, g ⊕ h)). intros. by constructor. Qed.

Lemma gcgr_sum_r g h h' : gcgr h h' → gcgr (g ⊕ h) (g ⊕ h').
Proof. apply (gcgr_ctx (λ h, g ⊕ h)). intros. by constructor. Qed.

Lemma gcgr_sum g g' h h' : gcgr g g' → gcgr h h' → gcgr (g ⊕ h) (g' ⊕ h').
Proof. intros. etrans; [by apply gcgr_sum_l|by apply gcgr_sum_r]. Qed.

(* [(P ∥ Q) ∥ R ≡ (P ∥ R) ∥ Q] *)
Lemma cgr_par_swap P Q R : (P ∥ Q) ∥ R ≡* (P ∥ R) ∥ Q.
Proof.
  etrans; [apply rtsc_rl, cs_par_assoc|].
  etrans; [apply cgr_par_r, cgr_of_cs, cs_par_comm|].
  apply cgr_of_cs, cs_par_assoc.
Qed.

(* [(P ∥ Q) ∥ (R ∥ S) ≡ (P ∥ R) ∥ (Q ∥ S)] *)
Lemma cgr_par_inversion P Q R S : (P ∥ Q) ∥ (R ∥ S) ≡* (P ∥ R) ∥ (Q ∥ S).
Proof.
  etrans; [apply cgr_of_cs, cs_par_assoc|].
  etrans; [apply cgr_par_l, cgr_par_swap|].
  apply rtsc_rl, cs_par_assoc.
Qed.

(* ** Renamings of indices *)

Lemma ren_swap01_SS P : ren swap01 (ren S (ren S P)) = ren S (ren S P).
Proof. rewrite !ren_comp. apply ren_ext. intros i. apply swap01_SS. Qed.

Lemma ren_lift_lift_swap01 f P :
  ren (lift (lift f)) (ren swap01 P) = ren swap01 (ren (lift (lift f)) P).
Proof. rewrite !ren_comp. apply ren_ext. intros i. apply lift_lift_swap01. Qed.

Lemma cs_ren :
  (∀ P Q, cs P Q → ∀ f, cs (ren f P) (ren f Q))
  ∧ (∀ g h, gcs g h → ∀ f, gcs (gren f g) (gren f h)).
Proof.
  apply cs_gcs_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  - rewrite ren_lift_lift_swap01. apply cs_res_swap.
  - rewrite ren_lift_S. apply cs_res_scope.
  - destruct p; simpl; apply gcs_pre_val; by constructor.
Qed.

Lemma cgr_ren f P Q : P ≡* Q → ren f P ≡* ren f Q.
Proof. apply (cgr_ctx (ren f)). intros. by apply cs_ren. Qed.

(* ** Substitution and shift of values *)

Lemma exp_subst_closed k v e w : eval e = Some w → exp_subst k v e = e.
Proof.
  revert w. induction e; intros w He; simpl in He |- *; try done.
  all: repeat (destruct (eval _) as [[]|] eqn:? in He; try discriminate);
    repeat match goal with
    | IH : ∀ v, eval ?e = Some v → _, H : eval ?e = Some _ |- _ => rewrite (IH _ H); clear IH
    end; done.
Qed.

Lemma exp_shift_closed k e w : eval e = Some w → exp_shift k e = e.
Proof.
  revert w. induction e; intros w He; simpl in He |- *; try done.
  all: repeat (destruct (eval _) as [[]|] eqn:? in He; try discriminate);
    repeat match goal with
    | IH : ∀ v, eval ?e = Some v → _, H : eval ?e = Some _ |- _ => rewrite (IH _ H); clear IH
    end; done.
Qed.

Lemma exp_eqv_subst k v e e' : exp_eqv e e' → exp_eqv (exp_subst k v e) (exp_subst k v e').
Proof.
  destruct 1 as [|e w Hw]; [constructor|]. simpl.
  rewrite (exp_subst_closed k v e w) by apply Hw. by constructor.
Qed.

Lemma exp_eqv_shift k e e' : exp_eqv e e' → exp_eqv (exp_shift k e) (exp_shift k e').
Proof.
  destruct 1 as [|e w Hw]; [constructor|]. simpl.
  rewrite (exp_shift_closed k e w) by apply Hw. by constructor.
Qed.

Lemma exps_eqv_subst k v es es' :
  exps_eqv es es' → exps_eqv (map (exp_subst k v) es) (map (exp_subst k v) es').
Proof. induction 1; constructor; [by apply exp_eqv_subst|done]. Qed.

Lemma exps_eqv_shift k es es' :
  exps_eqv es es' → exps_eqv (map (exp_shift k) es) (map (exp_shift k) es').
Proof. induction 1; constructor; [by apply exp_eqv_shift|done]. Qed.

Lemma prefix_eqv_subst k v 𝜆 𝜆' :
  prefix_eqv 𝜆 𝜆' → prefix_eqv (prefix_subst k v 𝜆) (prefix_subst k v 𝜆').
Proof. destruct 1; simpl; constructor; by apply exps_eqv_subst. Qed.

Lemma prefix_eqv_shift k 𝜆 𝜆' :
  prefix_eqv 𝜆 𝜆' → prefix_eqv (prefix_shift k 𝜆) (prefix_shift k 𝜆').
Proof. destruct 1; simpl; constructor; by apply exps_eqv_shift. Qed.

Lemma prefix_eqv_binds 𝜆 𝜆' : prefix_eqv 𝜆 𝜆' → prefix_binds 𝜆 = prefix_binds 𝜆'.
Proof. by destruct 1. Qed.

Lemma cs_subst :
  (∀ P Q, cs P Q → ∀ k v, cs (subst k v P) (subst k v Q))
  ∧ (∀ g h, gcs g h → ∀ k v, gcs (gsubst k v g) (gsubst k v h)).
Proof.
  apply cs_gcs_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  - rewrite (exp_subst_closed _ _ _ _ e0). by apply cs_ite_t.
  - rewrite (exp_subst_closed _ _ _ _ e0). by apply cs_ite_f.
  - constructor. by apply exp_eqv_subst.
  - constructor. by apply exp_eqv_subst.
  - rewrite <- (proj1 ren_subst). apply cs_res_swap.
  - rewrite <- (proj1 ren_subst). apply cs_res_scope.
  - constructor. by apply exps_eqv_subst.
  - rewrite (prefix_eqv_binds _ _ p). apply gcs_pre_val. by apply prefix_eqv_subst.
Qed.

Lemma cgr_subst k v P Q : P ≡* Q → subst k v P ≡* subst k v Q.
Proof. apply (cgr_ctx (subst k v)). intros. by apply cs_subst. Qed.

Lemma cs_shiftv :
  (∀ P Q, cs P Q → ∀ k, cs (shiftv k P) (shiftv k Q))
  ∧ (∀ g h, gcs g h → ∀ k, gcs (gshiftv k g) (gshiftv k h)).
Proof.
  apply cs_gcs_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  - rewrite (exp_shift_closed _ _ _ e0). by apply cs_ite_t.
  - rewrite (exp_shift_closed _ _ _ e0). by apply cs_ite_f.
  - constructor. by apply exp_eqv_shift.
  - constructor. by apply exp_eqv_shift.
  - rewrite <- (proj1 ren_shiftv). apply cs_res_swap.
  - rewrite <- (proj1 ren_shiftv). apply cs_res_scope.
  - constructor. by apply exps_eqv_shift.
  - rewrite (prefix_eqv_binds _ _ p). apply gcs_pre_val. by apply prefix_eqv_shift.
Qed.

Lemma cgr_shiftv k P Q : P ≡* Q → shiftv k P ≡* shiftv k Q.
Proof. apply (cgr_ctx (shiftv k)). intros. by apply cs_shiftv. Qed.

Lemma cgr_shiftv_iter n P Q : P ≡* Q → Nat.iter n (shiftv 0) P ≡* Nat.iter n (shiftv 0) Q.
Proof. induction n; simpl; [done|]. intros. by apply cgr_shiftv, IHn. Qed.

(* ** Substitution of processes *)

Lemma cs_pr_subst_l :
  (∀ P P', cs P P' → ∀ X Q, cs (P ⦃ Q // X ⦄) (P' ⦃ Q // X ⦄))
  ∧ (∀ g g', gcs g g' → ∀ X Q, gcs (gpr_subst X g Q) (gpr_subst X g' Q)).
Proof.
  apply cs_gcs_ind; simpl; intros; try (constructor; done); try (by constructor; apply H).
  - replace ((ren swap01 P) ⦃ ren S (ren S Q) // X ⦄) with (ren swap01 (P ⦃ ren S (ren S Q) // X ⦄)).
    + apply cs_res_swap.
    + rewrite (proj1 (ren_pr_subst X)). by rewrite ren_swap01_SS.
  - rewrite <- (proj1 (ren_pr_subst X)). apply cs_res_scope.
  - case_decide; [by apply cs_rec|]. by constructor; apply H.
  - rewrite (prefix_eqv_binds _ _ p). by constructor.
Qed.

Lemma cgr_pr_subst_l P P' X Q : P ≡* P' → P ⦃ Q // X ⦄ ≡* P' ⦃ Q // X ⦄.
Proof. apply (cgr_ctx (λ P, P ⦃ Q // X ⦄)). intros. by apply cs_pr_subst_l. Qed.

Lemma cgr_pr_subst_r :
  (∀ P X Q Q', Q ≡* Q' → P ⦃ Q // X ⦄ ≡* P ⦃ Q' // X ⦄)
  ∧ (∀ g X Q Q', Q ≡* Q' → gcgr (gpr_subst X g Q) (gpr_subst X g Q')).
Proof.
  apply proc_guard_ind; simpl; intros; try done.
  - apply cgr_ite; auto.
  - apply cgr_par; auto.
  - apply cgr_res, H. by apply cgr_ren.
  - by case_decide.
  - case_decide; [done|]. apply cgr_rec. by apply H.
  - apply cgr_guard. by apply H.
  - apply gcgr_pre, H. by apply cgr_shiftv_iter.
  - apply gcgr_sum; auto.
Qed.

(* Unfolding congruent recursions gives congruent processes. *)
Lemma cgr_unfold t X P P' :
  P ≡* P' → P ⦃ PRec t X P // X ⦄ ≡* P' ⦃ PRec t X P' // X ⦄.
Proof.
  intros H. etrans; [by apply cgr_pr_subst_l|].
  apply (proj1 cgr_pr_subst_r). by apply cgr_rec.
Qed.

(* ** Facts on steps *)

Lemma gstep_nil es s l P' : ¬ prog_gstep (GNil es) s l P'.
Proof. by inversion 1. Qed.

Lemma pstep_nil es s l P' : ¬ prog_step (PG (GNil es)) s l P'.
Proof. inversion 1; subst. by eapply gstep_nil. Qed.

Lemma S_inj_fun : ∀ i j : nat, S i = S j → i = j.
Proof. intros i j [=]. done. Qed.

(* ** Structural congruence is a bisimulation *)

Definition fwd (P Q : proc) : Prop :=
  ∀ s l P', prog_step P s l P' → ∃ Q', prog_step Q s l Q' ∧ P' ≡* Q'.

Definition gfwd (g h : guard) : Prop :=
  ∀ s l P', prog_gstep g s l P' → ∃ Q', prog_gstep h s l Q' ∧ P' ≡* Q'.

Lemma fwd_refl_step P Q : (∀ s l P', prog_step P s l P' → prog_step Q s l P') → fwd P Q.
Proof. intros H s l P' Hs. exists P'. split; [by apply H|done]. Qed.

Lemma gfwd_refl_step g h : (∀ s l P', prog_gstep g s l P' → prog_gstep h s l P') → gfwd g h.
Proof. intros H s l P' Hs. exists P'. split; [by apply H|done]. Qed.

Lemma fwd_par_nil P : fwd (P ∥ 𝟘) P ∧ fwd P (P ∥ 𝟘).
Proof.
  split.
  - intros s l X Hs. inversion Hs as [| | | |? ? ? ? P' HP| | | | |]; subst;
      try (exfalso; by eapply pstep_nil).
    exists P'. split; [done|]. apply cgr_of_cs, cs_par_nil.
  - intros s l P' Hs. exists (P' ∥ 𝟘). split; [by apply pr_parL|].
    symmetry. apply cgr_of_cs, cs_par_nil.
Qed.

Lemma fwd_par_comm P Q : fwd (P ∥ Q) (Q ∥ P).
Proof.
  intros s l X Hs.
  inversion Hs as [| | | |? ? ? ? P' HP|? ? ? ? Q' HQ|? ? t t' c v P' Q' HP HQ|? ? t t' c v P' Q' HP HQ| |];
    subst.
  - exists (Q ∥ P'). split; [by apply pr_parR|]. apply cgr_of_cs, cs_par_comm.
  - exists (Q' ∥ P). split; [by apply pr_parL|]. apply cgr_of_cs, cs_par_comm.
  - exists (Q' ∥ P'). split; [rewrite cpair_comm; by eapply pr_syncR|]. apply cgr_of_cs, cs_par_comm.
  - exists (Q' ∥ P'). split; [rewrite cpair_comm; by eapply pr_syncL|]. apply cgr_of_cs, cs_par_comm.
Qed.

Lemma fwd_par_assoc P Q R :
  fwd (P ∥ (Q ∥ R)) ((P ∥ Q) ∥ R) ∧ fwd ((P ∥ Q) ∥ R) (P ∥ (Q ∥ R)).
Proof.
  split.
  - intros s l X Hs.
    inversion Hs as [| | | |? ? ? ? P' HP|? ? ? ? X' HX|? ? t t' c v P' X' HP HX|? ? t t' c v P' X' HP HX| |];
      subst.
    + exists ((P' ∥ Q) ∥ R). split; [by do 2 apply pr_parL|]. apply cgr_of_cs, cs_par_assoc.
    + inversion HX as [| | | |? ? ? ? Q' HQ|? ? ? ? R' HR|? ? t t' c v Q' R' HQ HR|? ? t t' c v Q' R' HQ HR| |];
        subst.
      * exists ((P ∥ Q') ∥ R). split; [by apply pr_parL, pr_parR|]. apply cgr_of_cs, cs_par_assoc.
      * exists ((P ∥ Q) ∥ R'). split; [by apply pr_parR|]. apply cgr_of_cs, cs_par_assoc.
      * exists ((P ∥ Q') ∥ R'). split; [eapply pr_syncL; [by apply pr_parR|done]|].
        apply cgr_of_cs, cs_par_assoc.
      * exists ((P ∥ Q') ∥ R'). split; [eapply pr_syncR; [by apply pr_parR|done]|].
        apply cgr_of_cs, cs_par_assoc.
    + inversion HX as [| | | |? ? ? ? Q' HQ|? ? ? ? R' HR| | | |]; subst.
      * exists ((P' ∥ Q') ∥ R). split; [apply pr_parL; by eapply pr_syncL|]. apply cgr_of_cs, cs_par_assoc.
      * exists ((P' ∥ Q) ∥ R'). split; [eapply pr_syncL; [by apply pr_parL|done]|].
        apply cgr_of_cs, cs_par_assoc.
    + inversion HX as [| | | |? ? ? ? Q' HQ|? ? ? ? R' HR| | | |]; subst.
      * exists ((P' ∥ Q') ∥ R). split; [apply pr_parL; by eapply pr_syncR|]. apply cgr_of_cs, cs_par_assoc.
      * exists ((P' ∥ Q) ∥ R'). split; [eapply pr_syncR; [by apply pr_parL|done]|].
        apply cgr_of_cs, cs_par_assoc.
  - intros s l X Hs.
    inversion Hs as [| | | |? ? ? ? X' HX|? ? ? ? R' HR|? ? t t' c v X' R' HX HR|? ? t t' c v X' R' HX HR| |];
      subst.
    + inversion HX as [| | | |? ? ? ? P' HP|? ? ? ? Q' HQ|? ? t t' c v P' Q' HP HQ|? ? t t' c v P' Q' HP HQ| |];
        subst.
      * exists (P' ∥ (Q ∥ R)). split; [by apply pr_parL|]. symmetry. apply cgr_of_cs, cs_par_assoc.
      * exists (P ∥ (Q' ∥ R)). split; [by apply pr_parR, pr_parL|]. symmetry. apply cgr_of_cs, cs_par_assoc.
      * exists (P' ∥ (Q' ∥ R)). split; [eapply pr_syncL; [done|by apply pr_parL]|].
        symmetry. apply cgr_of_cs, cs_par_assoc.
      * exists (P' ∥ (Q' ∥ R)). split; [eapply pr_syncR; [done|by apply pr_parL]|].
        symmetry. apply cgr_of_cs, cs_par_assoc.
    + exists (P ∥ (Q ∥ R')). split; [by do 2 apply pr_parR|]. symmetry. apply cgr_of_cs, cs_par_assoc.
    + inversion HX as [| | | |? ? ? ? P' HP|? ? ? ? Q' HQ| | | |]; subst.
      * exists (P' ∥ (Q ∥ R')). split; [eapply pr_syncL; [done|by apply pr_parR]|].
        symmetry. apply cgr_of_cs, cs_par_assoc.
      * exists (P ∥ (Q' ∥ R')). split; [apply pr_parR; by eapply pr_syncL|].
        symmetry. apply cgr_of_cs, cs_par_assoc.
    + inversion HX as [| | | |? ? ? ? P' HP|? ? ? ? Q' HQ| | | |]; subst.
      * exists (P' ∥ (Q ∥ R')). split; [eapply pr_syncR; [done|by apply pr_parR]|].
        symmetry. apply cgr_of_cs, cs_par_assoc.
      * exists (P ∥ (Q' ∥ R')). split; [apply pr_parR; by eapply pr_syncR|].
        symmetry. apply cgr_of_cs, cs_par_assoc.
Qed.

Lemma fwd_ite_t e P Q : eval e = Some (VBool true) → fwd (PIte e P Q) P ∧ fwd P (PIte e P Q).
Proof.
  intros He. split; apply fwd_refl_step; intros s l P' Hs.
  - inversion Hs; subst; [done|congruence].
  - by apply pr_iteT.
Qed.

Lemma fwd_ite_f e P Q : eval e = Some (VBool false) → fwd (PIte e P Q) Q ∧ fwd Q (PIte e P Q).
Proof.
  intros He. split; apply fwd_refl_step; intros s l P' Hs.
  - inversion Hs; subst; [congruence|done].
  - by apply pr_iteF.
Qed.

Lemma fwd_send_val t c e e' :
  exp_eqv e e' → fwd (PSend t c e) (PSend t c e') ∧ fwd (PSend t c e') (PSend t c e).
Proof.
  intros He. pose proof (exp_eqv_eval _ _ He) as E.
  split; apply fwd_refl_step; intros s l P' Hs; inversion Hs; subst; constructor; congruence.
Qed.

Lemma fwd_ite_val e e' P Q :
  exp_eqv e e' → fwd (PIte e P Q) (PIte e' P Q) ∧ fwd (PIte e' P Q) (PIte e P Q).
Proof.
  intros He. pose proof (exp_eqv_eval _ _ He) as E.
  split; apply fwd_refl_step; intros s l P' Hs; inversion Hs; subst;
    [apply pr_iteT|apply pr_iteF|apply pr_iteT|apply pr_iteF]; congruence.
Qed.

Lemma fwd_res_nil es : fwd (ν PG (GNil es)) (PG (GNil es)) ∧ fwd (PG (GNil es)) (ν PG (GNil es)).
Proof.
  split; intros s l P' Hs; inversion Hs; subst; exfalso; by eapply pstep_nil.
Qed.

Lemma ren_lbl_swap01_SS l : ren_lbl swap01 (ren_lbl S (ren_lbl S l)) = ren_lbl S (ren_lbl S l).
Proof. rewrite !ren_lbl_comp. apply ren_lbl_ext_fun. intros i. apply swap01_SS. Qed.

Lemma fwd_res_swap_1 P : fwd (ν ν P) (ν ν (ren swap01 P)).
Proof.
  intros s l X Hs. inversion Hs as [| | | | | | | |? ? ? Y HY|]; subst.
  inversion HY as [| | | | | | | |? ? ? P' HP|]; subst.
  pose proof (prog_step_ren swap01 _ _ _ _ HP) as HP'. rewrite ren_lbl_swap01_SS in HP'.
  exists (ν ν (ren swap01 P')). split; [by do 2 apply pr_res|].
  apply cgr_of_cs, cs_res_swap.
Qed.

Lemma fwd_res_swap P : fwd (ν ν P) (ν ν (ren swap01 P)) ∧ fwd (ν ν (ren swap01 P)) (ν ν P).
Proof.
  split; [apply fwd_res_swap_1|].
  rewrite <- (ren_swap01_invol P) at 2. apply fwd_res_swap_1.
Qed.

Lemma fwd_res_scope P Q : fwd ((ν P) ∥ Q) (ν (P ∥ ren S Q)) ∧ fwd (ν (P ∥ ren S Q)) ((ν P) ∥ Q).
Proof.
  split.
  - intros s l X Hs.
    inversion Hs as [| | | |? ? ? ? X' HX|? ? ? ? Q' HQ|? ? t t' c v X' Q' HX HQ|? ? t t' c v X' Q' HX HQ| |];
      subst.
    + inversion HX as [| | | | | | | |? ? ? P' HP|]; subst.
      exists (ν (P' ∥ ren S Q)). split; [by apply pr_res, pr_parL|]. apply cgr_of_cs, cs_res_scope.
    + exists (ν (P ∥ ren S Q')). split; [apply pr_res, pr_parR; by apply prog_step_ren|].
      apply cgr_of_cs, cs_res_scope.
    + inversion HX as [| | | | | | | |? ? ? P' HP|]; subst.
      pose proof (prog_step_ren S _ _ _ _ HQ) as HQ'. simpl in HQ'.
      exists (ν (P' ∥ ren S Q')). split; [apply pr_res; simpl; by eapply pr_syncL|].
      apply cgr_of_cs, cs_res_scope.
    + inversion HX as [| | | | | | | |? ? ? P' HP|]; subst.
      pose proof (prog_step_ren S _ _ _ _ HQ) as HQ'. simpl in HQ'.
      exists (ν (P' ∥ ren S Q')). split; [apply pr_res; simpl; by eapply pr_syncR|].
      apply cgr_of_cs, cs_res_scope.
  - intros s l X Hs. inversion Hs as [| | | | | | | |? ? ? Y HY|]; subst.
    inversion HY as [| | | |? ? ? ? P' HP|? ? ? ? Y' HQ|? ? t t' c v P' Y' HP HQ|? ? t t' c v P' Y' HP HQ| |];
      subst.
    + exists ((ν P') ∥ Q). split; [by apply pr_parL, pr_res|]. symmetry. apply cgr_of_cs, cs_res_scope.
    + destruct (prog_step_ren_inv S S_inj_fun _ _ _ _ HQ) as (l0 & Q' & El & -> & HQ0).
      apply ren_lbl_inj in El as ->; [|exact S_inj_fun].
      exists ((ν P) ∥ Q'). split; [by apply pr_parR|]. symmetry. apply cgr_of_cs, cs_res_scope.
    + destruct l; simpl in *; simplify_eq.
      destruct (prog_step_ren_inv S S_inj_fun _ _ _ _ HQ) as (l0 & Q' & El & -> & HQ0).
      destruct l0 as [[c0 v0|c0 v0| | |]|]; simpl in El; simplify_eq.
      exists ((ν P') ∥ Q'). split; [|symmetry; apply cgr_of_cs, cs_res_scope].
      eapply pr_syncL; [|exact HQ0]. by apply pr_res.
    + destruct l; simpl in *; simplify_eq.
      destruct (prog_step_ren_inv S S_inj_fun _ _ _ _ HQ) as (l0 & Q' & El & -> & HQ0).
      destruct l0 as [[c0 v0|c0 v0| | |]|]; simpl in El; simplify_eq.
      exists ((ν P') ∥ Q'). split; [|symmetry; apply cgr_of_cs, cs_res_scope].
      eapply pr_syncR; [|exact HQ0]. by apply pr_res.
Qed.

Lemma gfwd_sum_nil g es : gfwd (g ⊕ GNil es) g ∧ gfwd g (g ⊕ GNil es).
Proof.
  split; apply gfwd_refl_step; intros s l P' Hs.
  - inversion Hs; subst; [done|exfalso; by eapply gstep_nil].
  - by apply pg_sumL.
Qed.

Lemma gfwd_sum_comm g h : gfwd (g ⊕ h) (h ⊕ g).
Proof.
  apply gfwd_refl_step. intros s l P' Hs. inversion Hs; subst; [by apply pg_sumR|by apply pg_sumL].
Qed.

Lemma gfwd_sum_assoc g h k :
  gfwd (g ⊕ (h ⊕ k)) ((g ⊕ h) ⊕ k) ∧ gfwd ((g ⊕ h) ⊕ k) (g ⊕ (h ⊕ k)).
Proof.
  split; apply gfwd_refl_step; intros s l P' Hs.
  - inversion Hs as [| | | | |? ? ? ? ? H1|? ? ? ? ? H2]; subst.
    + by do 2 apply pg_sumL.
    + inversion H2; subst; [by apply pg_sumL, pg_sumR|by apply pg_sumR].
  - inversion Hs as [| | | | |? ? ? ? ? H1|? ? ? ? ? H2]; subst.
    + inversion H1; subst; [by apply pg_sumL|by apply pg_sumR, pg_sumL].
    + by do 2 apply pg_sumR.
Qed.

Lemma gfwd_nil_val es es' : gfwd (GNil es) (GNil es').
Proof. intros s l P' Hs. exfalso. by eapply gstep_nil. Qed.

Lemma gfwd_pre_val 𝜆 𝜆' P : prefix_eqv 𝜆 𝜆' → gfwd (𝜆 ∙ P) (𝜆' ∙ P) ∧ gfwd (𝜆' ∙ P) (𝜆 ∙ P).
Proof.
  intros H𝜆. destruct H𝜆 as [t E es es' Hes|t M es es' Hes|t es es' Hes];
    pose proof (exps_eqv_eval _ _ Hes) as Ev; split; apply gfwd_refl_step;
    intros s l X Hs; inversion Hs; subst; constructor; congruence.
Qed.

(* *** Contexts *)

Lemma fwd_ite_l e P P' Q : fwd P P' → fwd (PIte e P Q) (PIte e P' Q).
Proof.
  intros H s l X Hs. inversion Hs as [| |? ? ? ? ? ? He Hp|? ? ? ? ? ? He Hq| | | | | |]; subst.
  - destruct (H _ _ _ Hp) as (Y & Hs' & HY). exists Y. split; [|done]. by apply pr_iteT.
  - exists X. split; [by apply pr_iteF|done].
Qed.

Lemma fwd_ite_r e P Q Q' : fwd Q Q' → fwd (PIte e P Q) (PIte e P Q').
Proof.
  intros H s l X Hs. inversion Hs as [| |? ? ? ? ? ? He Hp|? ? ? ? ? ? He Hq| | | | | |]; subst.
  - exists X. split; [by apply pr_iteT|done].
  - destruct (H _ _ _ Hq) as (Y & Hs' & HY). exists Y. split; [|done]. by apply pr_iteF.
Qed.

Lemma fwd_par_l P P' Q : P ≡* P' → fwd P P' → fwd (P ∥ Q) (P' ∥ Q).
Proof.
  intros Hc H s l X Hs.
  inversion Hs as [| | | |? ? ? ? P1 HP|? ? ? ? Q1 HQ|? ? t t' c v P1 Q1 HP HQ|? ? t t' c v P1 Q1 HP HQ| |];
    subst.
  - destruct (H _ _ _ HP) as (Y & Hs' & HY). exists (Y ∥ Q). split; [by apply pr_parL|by apply cgr_par_l].
  - exists (P' ∥ Q1). split; [by apply pr_parR|by apply cgr_par_l].
  - destruct (H _ _ _ HP) as (Y & Hs' & HY). exists (Y ∥ Q1). split; [by eapply pr_syncL|by apply cgr_par_l].
  - destruct (H _ _ _ HP) as (Y & Hs' & HY). exists (Y ∥ Q1). split; [by eapply pr_syncR|by apply cgr_par_l].
Qed.

Lemma fwd_par_r P Q Q' : Q ≡* Q' → fwd Q Q' → fwd (P ∥ Q) (P ∥ Q').
Proof.
  intros Hc H s l X Hs.
  inversion Hs as [| | | |? ? ? ? P1 HP|? ? ? ? Q1 HQ|? ? t t' c v P1 Q1 HP HQ|? ? t t' c v P1 Q1 HP HQ| |];
    subst.
  - exists (P1 ∥ Q'). split; [by apply pr_parL|by apply cgr_par_r].
  - destruct (H _ _ _ HQ) as (Y & Hs' & HY). exists (P ∥ Y). split; [by apply pr_parR|by apply cgr_par_r].
  - destruct (H _ _ _ HQ) as (Y & Hs' & HY). exists (P1 ∥ Y). split; [by eapply pr_syncL|by apply cgr_par_r].
  - destruct (H _ _ _ HQ) as (Y & Hs' & HY). exists (P1 ∥ Y). split; [by eapply pr_syncR|by apply cgr_par_r].
Qed.

Lemma fwd_res P P' : fwd P P' → fwd (ν P) (ν P').
Proof.
  intros H s l X Hs. inversion Hs as [| | | | | | | |? ? ? P1 HP|]; subst.
  destruct (H _ _ _ HP) as (Y & Hs' & HY). exists (ν Y). split; [by apply pr_res|by apply cgr_res].
Qed.

Lemma fwd_rec t X P P' : P ≡* P' → fwd (PRec t X P) (PRec t X P').
Proof.
  intros H s l Y Hs. inversion Hs; subst.
  exists (P' ⦃ PRec t X P' // X ⦄). split; [constructor|by apply cgr_unfold].
Qed.

Lemma fwd_guard g g' : gfwd g g' → fwd (PG g) (PG g').
Proof.
  intros H s l X Hs. inversion Hs as [? ? ? ? Hg| | | | | | | | |]; subst.
  destruct (H _ _ _ Hg) as (Y & Hs' & HY). exists Y. split; [by constructor|done].
Qed.

Lemma gfwd_pre 𝜆 P P' : P ≡* P' → gfwd (𝜆 ∙ P) (𝜆 ∙ P').
Proof.
  intros Hc s l X Hs. inversion Hs; subst.
  - exists P'. split; [constructor|done].
  - exists (P' ⟦ v ⟧). split; [constructor|by apply cgr_subst].
  - exists P'. split; [by constructor|done].
  - exists (P' ⟦ VNat n ⟧). split; [by constructor|by apply cgr_subst].
  - exists P'. split; [by constructor|done].
Qed.

Lemma gfwd_sum_l g g' h : gfwd g g' → gfwd (g ⊕ h) (g' ⊕ h).
Proof.
  intros H s l X Hs. inversion Hs as [| | | | |? ? ? ? ? Hg|? ? ? ? ? Hh]; subst.
  - destruct (H _ _ _ Hg) as (Y & Hs' & HY). exists Y. split; [by apply pg_sumL|done].
  - exists X. split; [by apply pg_sumR|done].
Qed.

Lemma gfwd_sum_r g h h' : gfwd h h' → gfwd (g ⊕ h) (g ⊕ h').
Proof.
  intros H s l X Hs. inversion Hs as [| | | | |? ? ? ? ? Hg|? ? ? ? ? Hh]; subst.
  - exists X. split; [by apply pg_sumL|done].
  - destruct (H _ _ _ Hh) as (Y & Hs' & HY). exists Y. split; [by apply pg_sumR|done].
Qed.

(* *** The bisimulation *)

Theorem cs_bisim :
  (∀ P Q, cs P Q → fwd P Q ∧ fwd Q P) ∧ (∀ g h, gcs g h → gfwd g h ∧ gfwd h g).
Proof.
  apply cs_gcs_ind; intros.
  - apply fwd_par_nil.
  - split; apply fwd_par_comm.
  - apply fwd_par_assoc.
  - by apply fwd_ite_t.
  - by apply fwd_ite_f.
  - by apply fwd_send_val.
  - by apply fwd_ite_val.
  - apply fwd_res_nil.
  - apply fwd_res_swap.
  - apply fwd_res_scope.
  - destruct H. split; by apply fwd_ite_l.
  - destruct H. split; by apply fwd_ite_r.
  - destruct H. split; apply fwd_par_l; try done; [by apply cgr_of_cs|symmetry; by apply cgr_of_cs].
  - destruct H. split; apply fwd_par_r; try done; [by apply cgr_of_cs|symmetry; by apply cgr_of_cs].
  - destruct H. split; by apply fwd_res.
  - split; apply fwd_rec; [by apply cgr_of_cs|symmetry; by apply cgr_of_cs].
  - destruct H. split; by apply fwd_guard.
  - apply gfwd_sum_nil.
  - split; apply gfwd_sum_comm.
  - apply gfwd_sum_assoc.
  - split; apply gfwd_nil_val.
  - by apply gfwd_pre_val.
  - split; apply gfwd_pre; [by apply cgr_of_cs|symmetry; by apply cgr_of_cs].
  - destruct H. split; by apply gfwd_sum_l.
  - destruct H. split; by apply gfwd_sum_r.
Qed.

(* [≡*] is a bisimulation, with the same choices. *)
Theorem cgr_bisim P Q : P ≡* Q → fwd P Q.
Proof.
  induction 1 as [P|P Q R [H|H] _ IH]; [by apply fwd_refl_step| |].
  all: intros s l P' Hs.
  - destruct (proj1 (proj1 cs_bisim P Q H) s l P' Hs) as (Q' & Hs1 & H1).
    destruct (IH _ _ _ Hs1) as (R' & Hs2 & H2).
    exists R'. split; [done|by etrans].
  - destruct (proj2 (proj1 cs_bisim Q P H) s l P' Hs) as (Q' & Hs1 & H1).
    destruct (IH _ _ _ Hs1) as (R' & Hs2 & H2).
    exists R'. split; [done|by etrans].
Qed.
(* end hide *)
