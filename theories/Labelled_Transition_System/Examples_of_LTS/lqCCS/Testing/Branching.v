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
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Branching.
  Context `{lqP : lqCCS_Parameters} `{QM : QuantumModel}.

  Definition lbl_in (vs : list val) (ns : list nat) (𝜆 : Labels prog_action) : Prop :=
    match 𝜆 with
    | _ ? v => v ∈ vs
    | _ ⦅_⦆? n => n ∈ ns
    | _ => True
    end.

  Lemma lbl_in_weak vs vs' ns 𝜆 : lbl_in vs ns 𝜆 → lbl_in (vs ++ vs') ns 𝜆.
  Proof. destruct 𝜆 as [[]|]; simpl; try done. intros Hv. apply elem_of_app. by left. Qed.

  Lemma lbl_in_ren f vs ns 𝜆 : lbl_in vs ns 𝜆 → lbl_in vs ns (ren_lbl f 𝜆).
  Proof. destruct 𝜆 as [[]|]; done. Qed.

  Definition gsteps (g : guard) vs ns (x : Labels prog_action * prog) : Prop :=
    ∃ k, g ⟶ᵍ{x.1}[k] x.2 ∧ lbl_in vs ns x.1.

  Definition psteps (P : prog) vs ns (x : Labels prog_action * prog) : Prop :=
    ∃ k, P ⟶ₚ{x.1}[k] x.2 ∧ lbl_in vs ns x.1.

  Lemma gsteps_fin g : ∀ vs ns, fin (gsteps g vs ns).
  Proof.
    induction g as [es| |π P|g1 IH1 g2 IH2]; intros vs ns.
    - apply (fin_mono _ (λ _, False)); [|apply fin_false]. intros [𝜆 R] (k & Hs & _). simpl in Hs. inversion Hs.
    - apply (fin_mono _ (λ _, False)); [|apply fin_false]. intros [𝜆 R] (k & Hs & _). simpl in Hs. inversion Hs.
    - destruct π as [t|t c|t U es|t M es|t e].
      + apply (fin_mono _ (λ x, x = (τ, P))); [|apply fin_eq].
        intros [𝜆 R] (k & Hs & _). simpl in Hs. inversion Hs; subst. done.
      + apply (fin_mono _ (λ x, ∃ v, v ∈ vs ∧ x = (c ? v, P ⁅ v ⁆ᵥ))).
        * intros [𝜆 R] (k & Hs & Hl). simpl in *. inversion Hs; subst. simpl in Hl.
          eexists. split; [eassumption|reflexivity].
        * exact (fin_img (λ v, (c ? v, P ⁅ v ⁆ᵥ)) _ (fin_elem vs)).
      + apply (fin_mono _ (λ x, ∃ qs, eval_qubits es = Some qs ∧ x = (⦅qs⦆ ! U, P))).
        * intros [𝜆 R] (k & Hs & Hl). simpl in *. inversion Hs; subst.
          eexists. split; [eassumption|reflexivity].
        * apply (fin_img (λ qs, (⦅qs⦆ ! U, P)) (λ qs, eval_qubits es = Some qs)).
          apply fin_uniq. intros x y Hx Hy. congruence.
      + apply (fin_mono _ (λ x, ∃ qs, eval_qubits es = Some qs
                            ∧ ∃ n, n ∈ ns ∧ x = (M ⦅qs⦆? n, P ⁅ VNat n ⁆ᵥ))).
        * intros [𝜆 R] (k & Hs & Hl). simpl in *. inversion Hs; subst. simpl in Hl.
          eexists. split; [eassumption|]. eexists. split; [eassumption|reflexivity].
        * apply fin_bind; [apply fin_uniq; intros x y Hx Hy; congruence|]. intros qs _.
          exact (fin_img (λ n, (M ⦅qs⦆? n, P ⁅ VNat n ⁆ᵥ)) _ (fin_elem ns)).
      + apply (fin_mono _ (λ x, ∃ q, eval_qubit e = Some q ∧ x = (reinit q, P))).
        * intros [𝜆 R] (k & Hs & Hl). simpl in *. inversion Hs; subst.
          eexists. split; [eassumption|reflexivity].
        * apply (fin_img (λ q, (reinit q, P)) (λ q, eval_qubit e = Some q)).
          apply fin_uniq. intros x y Hx Hy. congruence.
    - apply (fin_mono _ (λ x, gsteps g1 vs ns x ∨ gsteps g2 vs ns x)); [|apply fin_or; [apply IH1|apply IH2]].
      intros [𝜆 R] (k & Hs & Hl). simpl in *. inversion Hs; subst; [left|right]; exists k; by split.
  Qed.

  Lemma outs_fin P : (∀ vs ns, fin (psteps P vs ns)) →
    fin (λ v, ∃ k c P', P ⟶ₚ{c ! v}[k] P').
  Proof.
    intros HP. apply (fin_mono _ (λ v, ∃ a, psteps P [] [] a ∧ ∃ c, a.1 = c ! v)).
    - intros v (k & c & P' & Hs). exists (c ! v, P'). split; [exists k; by split|by exists c].
    - apply fin_bind; [apply HP|]. intros a _. apply fin_uniq. intros x y (c & Hx) (c' & Hy). congruence.
  Qed.

  Lemma psteps_fin P : ∀ vs ns, fin (psteps P vs ns).
  Proof.
    induction P as [t c e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|X|t P IHP|g]; intros vs ns.
    - apply (fin_mono _ (λ x, ∃ v, 〚 e 〛 = v ∧ x = (c ! v, 𝟘))).
      + intros [𝜆 R] (k & Hs & Hl). simpl in *. inversion Hs; subst.
        eexists. split; [eassumption|reflexivity].
      + apply (fin_img (λ v, (c ! v, 𝟘)) (λ v, 〚 e 〛 = v)).
        apply fin_uniq. intros x y Hx Hy. congruence.
    - apply (fin_mono _ (λ x, psteps P vs ns x ∨ psteps Q vs ns x)); [|apply fin_or; [apply IHP|apply IHQ]].
      intros [𝜆 R] (k & Hs & Hl). simpl in *. inversion Hs; subst; [left|right]; exists k; by split.
    - destruct (outs_fin P IHP) as (lP & HlP). destruct (outs_fin Q IHQ) as (lQ & HlQ).
      apply (fin_mono _ (λ x,
          (∃ a, psteps P (vs ++ lP ++ lQ) ns a ∧ x = (a.1, a.2 ∥ Q))
        ∨ (∃ b, psteps Q (vs ++ lP ++ lQ) ns b ∧ x = (b.1, P ∥ b.2))
        ∨ (∃ a, psteps P (vs ++ lP ++ lQ) ns a ∧ ∃ b, psteps Q (vs ++ lP ++ lQ) ns b ∧ x = (τ, a.2 ∥ b.2)))).
      + intros [𝜆 R] (k & Hs & Hl). simpl in *.
        inversion Hs as [| | | |? ? ? ? P1 Hp|? ? ? ? Q1 Hq|? ? t1 t2 c1 v1 P1 Q1 Hp Hq|? ? t1 t2 c1 v1 P1 Q1 Hp Hq| | ]; subst.
        * left. exists (𝜆, P1). split; [|done]. exists k. split; [done|by apply lbl_in_weak].
        * right. left. exists (𝜆, Q1). split; [|done]. exists k. split; [done|by apply lbl_in_weak].
        * right. right. exists (c1 ! v1, P1). split; [exists ({[+ t1 +]}); by split|].
          exists (c1 ? v1, Q1). split; [|done]. exists ({[+ t2 +]}). split; [done|]. simpl.
          apply elem_of_app. right. apply elem_of_app. left. apply HlP. by exists ({[+ t1 +]}), c1, P1.
        * right. right. exists (c1 ? v1, P1). split.
          { exists ({[+ t1 +]}). split; [done|]. simpl.
            apply elem_of_app. right. apply elem_of_app. right. apply HlQ. by exists ({[+ t2 +]}), c1, Q1. }
          exists (c1 ! v1, Q1). split; [|done]. exists ({[+ t2 +]}). by split.
      + apply fin_or; [exact (fin_img (λ a : Labels prog_action * prog, (a.1, a.2 ∥ Q)) _ (IHP _ _))|].
        apply fin_or; [exact (fin_img (λ b : Labels prog_action * prog, (b.1, P ∥ b.2)) _ (IHQ _ _))|].
        apply (fin_bind _ _ (IHP _ _)). intros a _.
        exact (fin_img (λ b : Labels prog_action * prog, (τ, a.2 ∥ b.2)) _ (IHQ _ _)).
    - apply (fin_mono _ (λ x, ∃ a, psteps P vs ns a ∧ (ren_lbl S x.1 = a.1 ∧ x.2 = ν a.2))).
      + intros [𝜆 R] (k & Hs & Hl). simpl in *.
        inversion Hs as [| | | | | | | |? ? ? P1 Hp| ]; subst.
        exists (ren_lbl S 𝜆, P1). split; [|done]. exists k. split; [done|by apply lbl_in_ren].
      + apply (fin_bind _ _ (IHP vs ns)). intros a _. apply fin_uniq.
        intros [𝜆1 R1] [𝜆2 R2] [Ea1 Ea2] [Eb1 Eb2]. simpl in *. f_equal; [|congruence].
        apply (ren_lbl_inj S (λ i j Hij, eq_add_S i j Hij)). congruence.
    - apply (fin_mono _ (λ _, False)); [|apply fin_false]. intros [𝜆 R] (k & Hs & _). simpl in Hs. inversion Hs.
    - apply (fin_mono _ (λ x, x = (τ, P ⁅ (t ∶ rec ∙ P)↑ ⁆ₚ))); [|apply fin_eq].
      intros [𝜆 R] (k & Hs & _). simpl in Hs. inversion Hs; subst. done.
    - apply (fin_mono _ (gsteps g vs ns)); [|apply gsteps_fin].
      intros [𝜆 R] (k & Hs & Hl). simpl in *. exists k. split; [by apply prog_step_guard|done].
  Qed.

  Definition sched_of (ρ : St) (P : prog) (a : Labels prog_action * prog) (Δ : dist prog) : Prop :=
    match a.1 with
    | τ => Δ = [(a.2, ρ)]
    | ⦅qs⦆ ! U => Δ = [(a.2, sop_apply U qs ρ)]
    | reinit q => Δ = [(a.2, init_apply q ρ)]
    | M ⦅qs⦆? _ =>
        ∃ Rs, (length Rs = length (outs_nz (meas_of M qs) ρ)
               ∧ Forall (λ R', ∃ b, psteps P [] (outs_nz (meas_of M qs) ρ) b ∧ R' = b.2) Rs)
              ∧ Δ = zip_with (λ t R', (R', M ⦅qs⦆[t] · ρ)) (outs_nz (meas_of M qs) ρ) Rs
    | _ => False
    end.

  Lemma sched_fin ρ P : fin (λ Δ, ∃ k, sched_step ρ P k Δ).
  Proof.
    apply (fin_mono _ (λ Δ, ∃ a, psteps P [] [0] a ∧ sched_of ρ P a Δ)).
    - intros Δ (k & Hs). inversion Hs as [R' Hp|U qs R' Hp|q R' Hp|M qs Rs R0 Hp0 HF]; subst.
      + exists (τ, R'). split; [exists k; by split|done].
      + exists (⦅qs⦆ ! U, R'). split; [exists k; by split|done].
      + exists (reinit q, R'). split; [exists k; by split|done].
      + exists (M ⦅qs⦆? 0, R0). split; [exists k; split; [done|simpl; by left]|].
        exists Rs. split; [|done]. split; [symmetry; exact (Forall2_length _ _ _ HF)|].
        apply Forall_forall. intros R' HR'. destruct (Forall2_elem_of_r _ _ _ R' HF HR') as (t & Hk & Hst).
        exists (M ⦅qs⦆? t, R'). split; [|done]. exists k. split; [done|]. simpl.
        exact Hk.
    - apply (fin_bind _ _ (psteps_fin P [] [0])). intros [[[c v|c v|U qs|M qs n|q]|] R] _; unfold sched_of; simpl.
      + apply fin_false.
      + apply fin_false.
      + apply fin_eq.
      + exact (fin_img (λ Rs, zip_with (λ t R', (R', M ⦅qs⦆[t] · ρ)) (outs_nz (meas_of M qs) ρ) Rs) _
          (fin_lists _ _ (fin_img snd _ (psteps_fin P [] (outs_nz (meas_of M qs) ρ))))).
      + apply fin_eq.
      + apply fin_eq.
  Qed.

  Definition cell_of (O : node → list msg) (ρ : St) (z : node) (P : prog) (C : list msg)
      (o : offer) (Δ : dist comp) : Prop :=
    match o with
    | OffOut _ _ _ => False
    | OffIn _ _ => False
    | OffOp t U' qs => Δ = [((z ++ [CoOp t U' qs], (P, C)), sop_apply U' qs ρ)]
    | OffInit t q => Δ = [((z ++ [CoInit t q], (P, C)), init_apply q ρ)]
    | OffUnfold t => Δ = [((z ++ [CoUnfold t], (P, C)), ρ)]
    | OffMeas t M qs =>
        Δ = map (λ n, ((z ++ [CoMeas t M qs n], (P, C)),
                        M ⦅qs⦆[n] · ρ)) (outs_nz (meas_of M qs) ρ)
    end.

  Lemma cstep_fin J O ρ c :
    (∀ z, fin (λ o, J z o ∧ ∀ t c, o ≠ OffIn t c)) → (∀ z c, fin (λ t, J z (OffIn t c))) →
    fin (λ Δ, ∃ it, cstep J O ρ c it Δ).
  Proof.
    intros HJ HJi. destruct c as [z [P C]].
    apply (fin_mono _ (λ Δ,
        (∃ Δ0, (∃ k, sched_step ρ P k Δ0) ∧ Δ = map (λ Pρ, ((z, (Pρ.1, C)), Pρ.2)) Δ0)
      ∨ (∃ m, m ∈ O z ∧ ∃ a, psteps P (snd <$> O z) [] a ∧ Δ = [((z, (a.2, C ++ [m])), ρ)])
      ∨ (∃ o, (J z o ∧ ∀ t c, o ≠ OffIn t c) ∧ cell_of O ρ z P C o Δ)
      ∨ (∃ a, psteps P [] [] a ∧ ∃ c v, a.1 = c ! v ∧ ∃ t, J z (OffIn t c)
          ∧ Δ = [((z ++ [CoIn t c v], (a.2, C)), ρ)]))).
    - intros Δ (it & Hs).
      apply cstep_cases in Hs. inversion Hs as [z0 P0 C0 k Δ0 Hss|z0 P0 C0 t c v t' P' HE HkC Hp|z0 P0 C0 t c v t' P' HI Hp
                      |z0 P0 C0 t U' qs t' HI|z0 P0 C0 t q t' HI|z0 P0 C0 t M qs t' HI|z0 P0 C0 t t' HI]; subst.
      + left. exists Δ0. split; [by exists k|done].
      + right. left. exists (t, c, v). split; [done|]. exists (c ? v, P'). split; [|done].
        exists ({[+ t' +]}). split; [done|]. simpl. apply list_elem_of_fmap. by exists (t, c, v).
      + right. right. right. exists (c ! v, P'). split; [exists ({[+ t' +]}); by split|].
        exists c, v. split; [done|]. by exists t.
      + right. right. left. exists (OffOp t U' qs). by split.
      + right. right. left. exists (OffInit t q). by split.
      + right. right. left. exists (OffMeas t M qs). by split.
      + right. right. left. exists (OffUnfold t). by split.
    - apply fin_or; [exact (fin_img (map (λ Pρ : prog * St, ((z, (Pρ.1, C)), Pρ.2))) _ (sched_fin ρ P))|].
      apply fin_or.
      + apply (fin_bind _ _ (fin_elem (O z))). intros m _.
        exact (fin_img (λ a : Labels prog_action * prog, [((z, (a.2, C ++ [m])), ρ)]) _ (psteps_fin P _ _)).
      + apply fin_or.
        * apply (fin_bind _ _ (HJ z)). intros [t c v|t c|t U' qs|t M qs|t q|t] [_ Hni]; simpl.
          -- apply fin_false.
          -- by destruct (Hni t c).
          -- apply fin_eq.
          -- apply fin_eq.
          -- apply fin_eq.
          -- apply fin_eq.
        * apply (fin_bind _ _ (psteps_fin P [] [])). intros [[[c v|c v|U' qs|M qs n|q]|] R] _; simpl;
            try (apply (fin_mono _ (λ _, False)); [intros Δ (c0 & v0 & Ea & _); discriminate Ea|apply fin_false]).
          apply (fin_mono _ (λ Δ, ∃ t, J z (OffIn t c) ∧ Δ = [((z ++ [CoIn t c v], (R, C)), ρ)])).
          -- intros Δ (c0 & v0 & Ea & t & Hk & ->). injection Ea as <- <-. by exists t.
          -- exact (fin_img (λ t, [((z ++ [CoIn t c v], (R, C)), ρ)]) _ (HJi z c)).
  Qed.

  Theorem lq_rstep_fin O J S :
    (∀ z, fin (λ o, J z o ∧ ∀ t c, o ≠ OffIn t c)) → (∀ z c, fin (λ t, J z (OffIn t c))) →
    ∀ D, fin (rstep (mdlts (M := lq_menu O) J S) D).
  Proof. intros HJ HJi D. apply rstep_fin. intros ρ c. exact (cstep_fin J O ρ c HJ HJi). Qed.
End Branching.

(* end hide *)
