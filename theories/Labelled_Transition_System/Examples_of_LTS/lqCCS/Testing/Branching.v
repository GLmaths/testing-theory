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
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Branching.
  Context `{QM : QuantumModel}.

  Definition lbl_in (vs : list val) (ns : list nat) (l : Labels prog_action) : Prop :=
    match l with
    | ActExt (PrIn _ v) => v ∈ vs
    | ActExt (PrMeas _ _ n) => n ∈ ns
    | _ => True
    end.

  Lemma lbl_in_weak vs vs' ns l : lbl_in vs ns l → lbl_in (vs ++ vs') ns l.
  Proof. destruct l as [[]|]; simpl; try done. intros Hv. apply elem_of_app. by left. Qed.

  Lemma lbl_in_ren f vs ns l : lbl_in vs ns l → lbl_in vs ns (ren_lbl f l).
  Proof. destruct l as [[]|]; done. Qed.

  Definition gsteps (g : guard) vs ns (x : Labels prog_action * proc) : Prop :=
    ∃ s, prog_gstep g s x.1 x.2 ∧ lbl_in vs ns x.1.

  Definition psteps (P : proc) vs ns (x : Labels prog_action * proc) : Prop :=
    ∃ s, prog_step P s x.1 x.2 ∧ lbl_in vs ns x.1.

  Lemma gsteps_fin g : ∀ vs ns, fin (gsteps g vs ns).
  Proof.
    induction g as [es| |𝜆 P|g1 IH1 g2 IH2]; intros vs ns.
    - apply (fin_mono _ (λ _, False)); [|apply fin_false]. intros [l R] (s & Hs & _). simpl in Hs. inversion Hs.
    - apply (fin_mono _ (λ _, False)); [|apply fin_false]. intros [l R] (s & Hs & _). simpl in Hs. inversion Hs.
    - destruct 𝜆 as [t|t c|t E es|t M es|t es].
      + apply (fin_mono _ (λ x, x = (τ, P))); [|apply fin_eq].
        intros [l R] (s & Hs & _). simpl in Hs. inversion Hs; subst. done.
      + apply (fin_mono _ (λ x, ∃ v, v ∈ vs ∧ x = (ActExt (PrIn c v), P ⟦ v ⟧))).
        * intros [l R] (s & Hs & Hl). simpl in *. inversion Hs; subst. simpl in Hl.
          eexists. split; [eassumption|reflexivity].
        * exact (fin_img (λ v, (ActExt (PrIn c v), P ⟦ v ⟧)) _ (fin_elem vs)).
      + apply (fin_mono _ (λ x, ∃ qs, eval_qubits es = Some qs ∧ x = (ActExt (PrOp E qs), P))).
        * intros [l R] (s & Hs & Hl). simpl in *. inversion Hs; subst.
          eexists. split; [eassumption|reflexivity].
        * apply (fin_img (λ qs, (ActExt (PrOp E qs), P)) (λ qs, eval_qubits es = Some qs)).
          apply fin_uniq. intros x y Hx Hy. congruence.
      + apply (fin_mono _ (λ x, ∃ qs, eval_qubits es = Some qs
                            ∧ ∃ n, n ∈ ns ∧ x = (ActExt (PrMeas M qs n), P ⟦ VNat n ⟧))).
        * intros [l R] (s & Hs & Hl). simpl in *. inversion Hs; subst. simpl in Hl.
          eexists. split; [eassumption|]. eexists. split; [eassumption|reflexivity].
        * apply fin_bind; [apply fin_uniq; intros x y Hx Hy; congruence|]. intros qs _.
          exact (fin_img (λ n, (ActExt (PrMeas M qs n), P ⟦ VNat n ⟧)) _ (fin_elem ns)).
      + apply (fin_mono _ (λ x, ∃ qs, eval_qubits es = Some qs ∧ x = (ActExt (PrInit qs), P))).
        * intros [l R] (s & Hs & Hl). simpl in *. inversion Hs; subst.
          eexists. split; [eassumption|reflexivity].
        * apply (fin_img (λ qs, (ActExt (PrInit qs), P)) (λ qs, eval_qubits es = Some qs)).
          apply fin_uniq. intros x y Hx Hy. congruence.
    - apply (fin_mono _ (λ x, gsteps g1 vs ns x ∨ gsteps g2 vs ns x)); [|apply fin_or; [apply IH1|apply IH2]].
      intros [l R] (s & Hs & Hl). simpl in *. inversion Hs; subst; [left|right]; exists s; by split.
  Qed.

  Lemma outs_fin P : (∀ vs ns, fin (psteps P vs ns)) →
    fin (λ v, ∃ s c P', prog_step P s (ActExt (PrOut c v)) P').
  Proof.
    intros HP. apply (fin_mono _ (λ v, ∃ a, psteps P [] [] a ∧ ∃ c, a.1 = ActExt (PrOut c v))).
    - intros v (s & c & P' & Hs). exists (ActExt (PrOut c v), P'). split; [exists s; by split|by exists c].
    - apply fin_bind; [apply HP|]. intros a _. apply fin_uniq. intros x y (c & Hx) (c' & Hy). congruence.
  Qed.

  Lemma psteps_fin P : ∀ vs ns, fin (psteps P vs ns).
  Proof.
    induction P as [t c e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|X|t X P IHP|g]; intros vs ns.
    - apply (fin_mono _ (λ x, ∃ v, eval e = Some v ∧ x = (ActExt (PrOut c v), 𝟘))).
      + intros [l R] (s & Hs & Hl). simpl in *. inversion Hs; subst.
        eexists. split; [eassumption|reflexivity].
      + apply (fin_img (λ v, (ActExt (PrOut c v), 𝟘)) (λ v, eval e = Some v)).
        apply fin_uniq. intros x y Hx Hy. congruence.
    - apply (fin_mono _ (λ x, psteps P vs ns x ∨ psteps Q vs ns x)); [|apply fin_or; [apply IHP|apply IHQ]].
      intros [l R] (s & Hs & Hl). simpl in *. inversion Hs; subst; [left|right]; exists s; by split.
    - destruct (outs_fin P IHP) as (lP & HlP). destruct (outs_fin Q IHQ) as (lQ & HlQ).
      apply (fin_mono _ (λ x,
          (∃ a, psteps P (vs ++ lP ++ lQ) ns a ∧ x = (a.1, a.2 ∥ Q))
        ∨ (∃ b, psteps Q (vs ++ lP ++ lQ) ns b ∧ x = (b.1, P ∥ b.2))
        ∨ (∃ a, psteps P (vs ++ lP ++ lQ) ns a ∧ ∃ b, psteps Q (vs ++ lP ++ lQ) ns b ∧ x = (τ, a.2 ∥ b.2)))).
      + intros [l R] (s & Hs & Hl). simpl in *.
        inversion Hs as [ | | | | | | | | | |? ? ? ? P1 Hp|? ? ? ? Q1 Hq|? ? t1 t2 c1 v1 P1 Q1 Hp Hq|? ? t1 t2 c1 v1 P1 Q1 Hp Hq| | ]; subst.
        * left. exists (l, P1). split; [|done]. exists s. split; [done|by apply lbl_in_weak].
        * right. left. exists (l, Q1). split; [|done]. exists s. split; [done|by apply lbl_in_weak].
        * right. right. exists (ActExt (PrOut c1 v1), P1). split; [exists (CTag t1); by split|].
          exists (ActExt (PrIn c1 v1), Q1). split; [|done]. exists (CTag t2). split; [done|]. simpl.
          apply elem_of_app. right. apply elem_of_app. left. apply HlP. by exists (CTag t1), c1, P1.
        * right. right. exists (ActExt (PrIn c1 v1), P1). split.
          { exists (CTag t1). split; [done|]. simpl.
            apply elem_of_app. right. apply elem_of_app. right. apply HlQ. by exists (CTag t2), c1, Q1. }
          exists (ActExt (PrOut c1 v1), Q1). split; [|done]. exists (CTag t2). by split.
      + apply fin_or; [exact (fin_img (λ a : Labels prog_action * proc, (a.1, a.2 ∥ Q)) _ (IHP _ _))|].
        apply fin_or; [exact (fin_img (λ b : Labels prog_action * proc, (b.1, P ∥ b.2)) _ (IHQ _ _))|].
        apply (fin_bind _ _ (IHP _ _)). intros a _.
        exact (fin_img (λ b : Labels prog_action * proc, (τ, a.2 ∥ b.2)) _ (IHQ _ _)).
    - apply (fin_mono _ (λ x, ∃ a, psteps P vs ns a ∧ (ren_lbl S x.1 = a.1 ∧ x.2 = ν a.2))).
      + intros [l R] (s & Hs & Hl). simpl in *.
        inversion Hs as [ | | | | | | | | | | | | | |? ? ? P1 Hp| ]; subst.
        exists (ren_lbl S l, P1). split; [|done]. exists s. split; [done|by apply lbl_in_ren].
      + apply (fin_bind _ _ (IHP vs ns)). intros a _. apply fin_uniq.
        intros [l1 R1] [l2 R2] [Ea1 Ea2] [Eb1 Eb2]. simpl in *. f_equal; [|congruence].
        apply (ren_lbl_inj S (λ i j Hij, eq_add_S i j Hij)). congruence.
    - apply (fin_mono _ (λ _, False)); [|apply fin_false]. intros [l R] (s & Hs & _). simpl in Hs. inversion Hs.
    - apply (fin_mono _ (λ x, x = (τ, P ⦃ PRec t X P // X ⦄))); [|apply fin_eq].
      intros [l R] (s & Hs & _). simpl in Hs. inversion Hs; subst. done.
    - apply (fin_mono _ (gsteps g vs ns)); [|apply gsteps_fin].
      intros [l R] (s & Hs & Hl). simpl in *. exists s. by split.
  Qed.

  Definition sched_of (ρ : St) (P : proc) (a : Labels prog_action * proc) (Δ : dist proc) : Prop :=
    match a.1 with
    | τ => Δ = [(a.2, ρ)]
    | ActExt (PrOp E qs) => Δ = [(a.2, sop_apply E qs ρ)]
    | ActExt (PrInit qs) => Δ = [(a.2, init_apply qs ρ)]
    | ActExt (PrMeas M qs _) =>
        ∃ Rs, (length Rs = length (outs_nz M qs ρ)
               ∧ Forall (λ R', ∃ b, psteps P [] ((λ k, code _ k) <$> outs_nz M qs ρ) b ∧ R' = b.2) Rs)
              ∧ Δ = zip_with (λ k R', (R', meas_branch M qs k ρ)) (outs_nz M qs ρ) Rs
    | _ => False
    end.

  Lemma sched_fin ρ P : fin (λ Δ, ∃ s, sched_step ρ P s Δ).
  Proof.
    apply (fin_mono _ (λ Δ, ∃ a, psteps P [] [0] a ∧ sched_of ρ P a Δ)).
    - intros Δ (s & Hs). inversion Hs as [R' Hp|E qs R' Hp|qs R' Hp|M qs Rs R0 Hp0 HF]; subst.
      + exists (τ, R'). split; [exists s; by split|done].
      + exists (ActExt (PrOp E qs), R'). split; [exists s; by split|done].
      + exists (ActExt (PrInit qs), R'). split; [exists s; by split|done].
      + exists (ActExt (PrMeas M qs 0), R0). split; [exists s; split; [done|simpl; by left]|].
        exists Rs. split; [|done]. split; [symmetry; exact (Forall2_length _ _ _ HF)|].
        apply Forall_forall. intros R' HR'. destruct (Forall2_elem_of_r _ _ _ R' HF HR') as (k & Hk & Hst).
        exists (ActExt (PrMeas M qs (code _ k)), R'). split; [|done]. exists s. split; [done|]. simpl.
        apply list_elem_of_fmap. by exists k.
    - apply (fin_bind _ _ (psteps_fin P [] [0])). intros [[[c v|c v|E qs|M qs n|qs]|] R] _; unfold sched_of; simpl.
      + apply fin_false.
      + apply fin_false.
      + apply fin_eq.
      + exact (fin_img (λ Rs, zip_with (λ k R', (R', meas_branch M qs k ρ)) (outs_nz M qs ρ) Rs) _
          (fin_lists _ _ (fin_img snd _ (psteps_fin P [] ((λ k, code _ k) <$> outs_nz M qs ρ))))).
      + apply fin_eq.
      + apply fin_eq.
  Qed.

  Definition cell_of (O : node → list msg) (ρ : St) (n : node) (P : proc) (C : list msg)
      (o : offer) (Δ : dist comp) : Prop :=
    match o with
    | OffOut _ _ _ => False
    | OffIn _ _ => False
    | OffOp k E' qs => Δ = [((n ++ [CoOp k E' qs], (P, C, O (n ++ [CoOp k E' qs]))), sop_apply E' qs ρ)]
    | OffInit k qs => Δ = [((n ++ [CoInit k qs], (P, C, O (n ++ [CoInit k qs]))), init_apply qs ρ)]
    | OffMeas k M qs =>
        Δ = map (λ k', ((n ++ [CoMeas k M qs (code _ k')], (P, C, O (n ++ [CoMeas k M qs (code _ k')]))),
                        meas_branch M qs k' ρ)) (outs_nz M qs ρ)
    end.

  Lemma cstep_fin J O ρ c :
    (∀ n, fin (λ o, J n o ∧ ∀ k c, o ≠ OffIn k c)) → (∀ n c, fin (λ k, J n (OffIn k c))) →
    fin (λ Δ, ∃ it, cstep J O ρ c it Δ).
  Proof.
    intros HJ HJi. destruct c as [n [[P C] E]].
    apply (fin_mono _ (λ Δ,
        (∃ Δ0, (∃ s, sched_step ρ P s Δ0) ∧ Δ = map (λ Pρ, ((n, (Pρ.1, C, E)), Pρ.2)) Δ0)
      ∨ (∃ m, m ∈ E ∧ ∃ a, psteps P (snd <$> E) [] a ∧ Δ = [((n, (a.2, C ++ [m], E)), ρ)])
      ∨ (∃ o, (J n o ∧ ∀ k c, o ≠ OffIn k c) ∧ cell_of O ρ n P C o Δ)
      ∨ (∃ a, psteps P [] [] a ∧ ∃ c v, a.1 = ActExt (PrOut c v) ∧ ∃ k, J n (OffIn k c)
          ∧ Δ = [((n ++ [CoIn k c v], (a.2, C, O (n ++ [CoIn k c v]))), ρ)]))).
    - intros Δ (it & Hs).
      inversion Hs as [n0 P0 C0 E0 s Δ0 Hss|n0 P0 C0 E0 k c v t P' HE HkC Hp|n0 P0 C0 E0 k c v t P' HI Hp
                      |n0 P0 C0 E0 k E' qs t HI|n0 P0 C0 E0 k qs t HI|n0 P0 C0 E0 k M qs t HI]; subst.
      + left. exists Δ0. split; [by exists s|done].
      + right. left. exists (k, c, v). split; [done|]. exists (ActExt (PrIn c v), P'). split; [|done].
        exists (CTag t). split; [done|]. simpl. apply list_elem_of_fmap. by exists (k, c, v).
      + right. right. right. exists (ActExt (PrOut c v), P'). split; [exists (CTag t); by split|].
        exists c, v. split; [done|]. by exists k.
      + right. right. left. exists (OffOp k E' qs). by split.
      + right. right. left. exists (OffInit k qs). by split.
      + right. right. left. exists (OffMeas k M qs). by split.
    - apply fin_or; [exact (fin_img (map (λ Pρ : proc * St, ((n, (Pρ.1, C, E)), Pρ.2))) _ (sched_fin ρ P))|].
      apply fin_or.
      + apply (fin_bind _ _ (fin_elem E)). intros m _.
        exact (fin_img (λ a : Labels prog_action * proc, [((n, (a.2, C ++ [m], E)), ρ)]) _ (psteps_fin P _ _)).
      + apply fin_or.
        * apply (fin_bind _ _ (HJ n)). intros [k c v|k c|k E' qs|k M qs|k qs] [_ Hni]; simpl.
          -- apply fin_false.
          -- by destruct (Hni k c).
          -- apply fin_eq.
          -- apply fin_eq.
          -- apply fin_eq.
        * apply (fin_bind _ _ (psteps_fin P [] [])). intros [[[c v|c v|E' qs|M qs m|qs]|] R] _; simpl;
            try (apply (fin_mono _ (λ _, False)); [intros Δ (c0 & v0 & Ea & _); discriminate Ea|apply fin_false]).
          apply (fin_mono _ (λ Δ, ∃ k, J n (OffIn k c) ∧ Δ = [((n ++ [CoIn k c v], (R, C, O (n ++ [CoIn k c v]))), ρ)])).
          -- intros Δ (c0 & v0 & Ea & k & Hk & ->). injection Ea as <- <-. by exists k.
          -- exact (fin_img (λ k, [((n ++ [CoIn k c v], (R, C, O (n ++ [CoIn k c v]))), ρ)]) _ (HJi n c)).
  Qed.

  Theorem lq_rstep_fin O J S :
    (∀ n, fin (λ o, J n o ∧ ∀ k c, o ≠ OffIn k c)) → (∀ n c, fin (λ k, J n (OffIn k c))) →
    ∀ D, fin (rstep (mdlts (M := lq_menu O) J S) D).
  Proof. intros HJ HJi D. apply rstep_fin. intros ρ c. exact (cstep_fin J O ρ c HJ HJi). Qed.
End Branching.
(* end hide *)
