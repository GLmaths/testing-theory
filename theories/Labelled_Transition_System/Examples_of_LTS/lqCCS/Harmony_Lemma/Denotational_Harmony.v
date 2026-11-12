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
(* * Correspondence between the denotational semantics and the STS

    As Theorem 3.1 of Unruh, Valiron and Ying: the denotation of [P] under
    the word [w], applied to the memory [ρ], is the sum of the memories at
    the leaves of a tree of reductions of [⟨ρ, P⟩] following [w]
    ([sts_tree]): a node takes one reduction, or one reduction per outcome
    of a measurement, and a finished configuration is a leaf.  The reductions
    are those of [sts]; the labels of [sts_lab] only tell which successors
    are the outcomes of one measurement.

    [den_sound]: every denotation is realised by a tree;
    [den_complete]: every tree realises a denotation. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Language.Congruence lqCCS.Language.Denotational.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Memory_Harmony lqCCS.Harmony_Lemma.STS_Harmony.

#[local] Open Scope lqccs_scope.

Section Den_Harmony.
  Context `{QM : QuantumModel}.

  (* ** Trees of reductions following a word of choices *)

  Definition stable_conf (ρ : St) (P : proc) : Prop := ∀ s ρ' P', ¬ sts ρ P s ρ' P'.
  Definition enabled_conf (ρ : St) (P : proc) (s : choice) : Prop := ∃ ρ' P', sts ρ P s ρ' P'.

  Inductive sts_tree : St → proc → list choice → list St → Prop :=
  | tree_nil_stable ρ P : stable_conf ρ P → sts_tree ρ P [] [ρ]
  | tree_nil_run ρ P : ¬ stable_conf ρ P → sts_tree ρ P [] []
  | tree_stable ρ P s w : stable_conf ρ P → sts_tree ρ P (s :: w) [ρ]
  | tree_stay ρ P s w l :
      ¬ stable_conf ρ P → ¬ enabled_conf ρ P s → sts_tree ρ P w l → sts_tree ρ P (s :: w) l
  | tree_step ρ P s w ρ' P' l :
      sts_lab ρ P s MNone ρ' P' → sts_tree ρ' P' w l → sts_tree ρ P (s :: w) l
  | tree_meas ρ P t w M qs (Pls : list (proc * list St)) :
      Forall2 (λ k pl, sts_lab ρ P (CTag t) (MMeas M qs (code _ k)) (meas_branch M qs k ρ) pl.1
                       ∧ sts_tree (meas_branch M qs k ρ) pl.1 w pl.2)
        (outs (meas_of M qs)) Pls →
      sts_tree ρ P (CTag t :: w) (concat (map snd Pls)).

  (* ** Finished configurations are the finished programs *)

  Lemma mem_eff_internal ρ l ρ' κ : mem_eff ρ l ρ' κ → internal l.
  Proof. destruct 1; constructor. Qed.

  Lemma internal_mem_eff l ρ : internal l → ∃ ρ' κ, mem_eff ρ l ρ' κ.
  Proof. destruct 1; do 2 eexists; constructor. Qed.

  Lemma mem_eff_meas_inv ρ l ρ' M qs n :
    mem_eff ρ l ρ' (MMeas M qs n) →
    ∃ k : Out (meas_of M qs), n = code _ k ∧ l = ActExt (PrMeas M qs n).
  Proof. inversion 1; subst. by eexists. Qed.

  Lemma stable_conf_iff ρ P : stable_conf ρ P ↔ stable P.
  Proof.
    split.
    - intros Hs s l P' Hp Hi. destruct (internal_mem_eff _ ρ Hi) as (ρ' & κ & Hm).
      apply (Hs s ρ' P'). apply mstep_sts with κ. by exists l.
    - intros Hs s ρ' P' Hr.
      destruct (Reduction_Implies_Internal_sts _ _ _ _ _ Hr) as (κ & Q' & (l & Hp & Hm) & _).
      apply (Hs _ _ _ Hp). by eapply mem_eff_internal.
  Qed.

  Lemma enabled_conf_iff ρ P s : enabled_conf ρ P s ↔ enabled P s.
  Proof.
    split.
    - intros (ρ' & P' & Hr).
      destruct (Reduction_Implies_Internal_sts _ _ _ _ _ Hr) as (κ & Q' & (l & Hp & Hm) & _).
      exists l, Q'. split; [done|]. by eapply mem_eff_internal.
    - intros (l & P' & Hp & Hi). destruct (internal_mem_eff _ ρ Hi) as (ρ' & κ & Hm).
      exists ρ', P'. apply mstep_sts with κ. by exists l.
  Qed.

  (* ** Sums of memories *)

  Lemma ssum_app l1 l2 : ssum (l1 ++ l2) = sadd (ssum l1) (ssum l2).
  Proof.
    induction l1 as [|ρ l1 IH]; simpl; [by rewrite sadd_szero_l|]. by rewrite IH, sadd_assoc.
  Qed.

  Lemma ssum_single ρ : ssum [ρ] = ρ.
  Proof. simpl. apply sadd_szero_r. Qed.

  Lemma app_sum_zip m ρ : ∀ (ks : list (Out m)) (Fs : list T),
    app (sum (zip_with (λ k F, F ⋅ kraus m k) ks Fs)) ρ
    = ssum (zip_with (λ k F, app F (app (kraus m k) ρ)) ks Fs).
  Proof.
    intros ks. induction ks as [|k ks IH]; intros [|F Fs]; simpl; try apply app_zero.
    by rewrite app_add, app_comp, IH.
  Qed.

  (* ** Soundness: a denotation is the sum of the leaves of a tree *)

  Lemma sound_meas ρ P t w M qs :
    (∀ P' F, den P' w F → ∀ ρ0, ∃ l, sts_tree ρ0 P' w l ∧ app F ρ0 = ssum l) →
    ∀ (ks : list (Out (meas_of M qs))) (PFs : list (proc * T)),
      Forall2 (λ k pf, prog_step P (CTag t) (ActExt (PrMeas M qs (code _ k))) pf.1 ∧ den pf.1 w pf.2)
        ks PFs →
      ∃ Pls : list (proc * list St),
        Forall2 (λ k pl, sts_lab ρ P (CTag t) (MMeas M qs (code _ k)) (meas_branch M qs k ρ) pl.1
                         ∧ sts_tree (meas_branch M qs k ρ) pl.1 w pl.2) ks Pls
        ∧ ssum (concat (map snd Pls))
          = ssum (zip_with (λ k F, app F (app (kraus (meas_of M qs) k) ρ)) ks (map snd PFs)).
  Proof.
    intros IH ks PFs Hf.
    induction Hf as [|k pf ks PFs (Hp & Hd) _ (Pls & Hf' & E)].
    - by exists [].
    - destruct (IH _ _ Hd (meas_branch M qs k ρ)) as (l & Ht & El).
      exists ((pf.1, l) :: Pls). split.
      + constructor; [|done]. split; [|done].
        eapply Internal_Implies_Reduction; [exact Hp|constructor].
      + simpl. rewrite ssum_app, E. unfold meas_branch in El. by rewrite El.
  Qed.

  Theorem den_sound w : ∀ P F, den P w F → ∀ ρ, ∃ l, sts_tree ρ P w l ∧ app F ρ = ssum l.
  Proof.
    induction w as [|s w IH]; intros P F Hd ρ;
      inversion Hd as [? Hs|? Hs|? ? ? Hs|? ? ? ? Hs He Hd'|? ? ? P' ? Hp Hd'|? t ? U qs P' ? Hp Hd'
                       |? t ? qs P' ? Hp Hd'|? t ? M qs PFs Hf]; subst.
    - exists [ρ]. split; [apply tree_nil_stable; by apply stable_conf_iff|].
      by rewrite app_one, ssum_single.
    - exists []. split; [apply tree_nil_run; by rewrite stable_conf_iff|]. apply app_zero.
    - exists [ρ]. split; [apply tree_stable; by apply stable_conf_iff|].
      by rewrite app_one, ssum_single.
    - destruct (IH _ _ Hd' ρ) as (l & Ht & E). exists l. split; [|done].
      apply tree_stay; [by rewrite stable_conf_iff|by rewrite enabled_conf_iff|done].
    - destruct (IH _ _ Hd' ρ) as (l & Ht & E). exists l. split; [|done].
      eapply tree_step; [|exact Ht]. eapply Internal_Implies_Reduction; [exact Hp|constructor].
    - destruct (IH _ _ Hd' (sop_apply U qs ρ)) as (l & Ht & E). exists l. split.
      + eapply tree_step; [|exact Ht]. eapply Internal_Implies_Reduction; [exact Hp|constructor].
      + by rewrite app_comp.
    - destruct (IH _ _ Hd' (init_apply qs ρ)) as (l & Ht & E). exists l. split.
      + eapply tree_step; [|exact Ht]. eapply Internal_Implies_Reduction; [exact Hp|constructor].
      + by rewrite app_comp.
    - destruct (sound_meas ρ P t w M qs IH _ _ Hf) as (Pls & Hf' & E).
      exists (concat (map snd Pls)). split; [by apply (tree_meas ρ P t w M qs)|].
      unfold meas_sum. by rewrite app_sum_zip.
  Qed.

  (* ** Completeness: the leaves of a tree sum to a denotation *)

  Lemma complete_meas ρ P t w M qs :
    (∀ ρ0 P' l, sts_tree ρ0 P' w l → ∃ F, den P' w F ∧ app F ρ0 = ssum l) →
    ∀ (ks : list (Out (meas_of M qs))) (Pls : list (proc * list St)),
      Forall2 (λ k pl, sts_lab ρ P (CTag t) (MMeas M qs (code _ k)) (meas_branch M qs k ρ) pl.1
                       ∧ sts_tree (meas_branch M qs k ρ) pl.1 w pl.2) ks Pls →
      ∃ PFs : list (proc * T),
        Forall2 (λ k pf, prog_step P (CTag t) (ActExt (PrMeas M qs (code _ k))) pf.1 ∧ den pf.1 w pf.2)
          ks PFs
        ∧ ssum (zip_with (λ k F, app F (app (kraus (meas_of M qs) k) ρ)) ks (map snd PFs))
          = ssum (concat (map snd Pls)).
  Proof.
    intros IH ks Pls Hf.
    induction Hf as [|k pl ks Pls (Hr & Ht) _ (PFs & Hf' & E)].
    - by exists [].
    - destruct (Reduction_Implies_Internal _ _ _ _ _ _ Hr) as (Q' & (l & Hp & Hm) & HQ).
      destruct (mem_eff_meas_inv _ _ _ _ _ _ Hm) as (k' & Hk & ->).
      apply code_inj in Hk. subst k'.
      destruct (IH _ _ _ Ht) as (F & Hd & EF).
      exists ((Q', F) :: PFs). split.
      + constructor; [|done]. split; [done|]. eapply den_cgr; [by symmetry|exact Hd].
      + simpl. rewrite ssum_app, E. unfold meas_branch in EF. by rewrite EF.
  Qed.

  Theorem den_complete w : ∀ ρ P l, sts_tree ρ P w l → ∃ F, den P w F ∧ app F ρ = ssum l.
  Proof.
    induction w as [|s w IH]; intros ρ P l Ht;
      inversion Ht as [? ? Hs|? ? Hs|? ? ? ? Hs|? ? ? ? ? Hs He Ht'|? ? ? ? ρ' P' ? Hr Ht'
                       |? ? t ? M qs Pls Hf]; subst.
    - exists one. split; [apply den_nil_stable; by rewrite <- (stable_conf_iff ρ)|].
      by rewrite app_one, ssum_single.
    - exists zero. split; [apply den_nil_run; by rewrite <- stable_conf_iff|]. apply app_zero.
    - exists one. split; [apply den_stable; by rewrite <- (stable_conf_iff ρ)|].
      by rewrite app_one, ssum_single.
    - destruct (IH _ _ _ Ht') as (F & Hd & E). exists F. split; [|done].
      apply den_stay; [by rewrite <- stable_conf_iff|by rewrite <- enabled_conf_iff|done].
    - destruct (Reduction_Implies_Internal _ _ _ _ _ _ Hr) as (Q' & (l0 & Hp & Hm) & HQ).
      destruct (IH _ _ _ Ht') as (F & Hd & E).
      assert (Hd' : den Q' w F) by (eapply den_cgr; [by symmetry|exact Hd]).
      inversion Hm; subst.
      + exists F. split; [by eapply den_tau|done].
      + destruct (prog_step_ext_choice _ _ _ _ Hp) as (t & ->).
        exists (F ⋅ act (sop_act E0 qs)). split; [by eapply den_op|]. by rewrite app_comp.
      + destruct (prog_step_ext_choice _ _ _ _ Hp) as (t & ->).
        exists (F ⋅ act (init_act qs)). split; [by eapply den_init|]. by rewrite app_comp.
    - destruct (complete_meas ρ P t w M qs IH _ _ Hf) as (PFs & Hf' & E).
      exists (meas_sum M qs (map snd PFs)). split; [by apply (den_meas P t w M qs)|].
      unfold meas_sum. by rewrite app_sum_zip.
  Qed.

  (* ** The correspondence, as Theorem 3.1 of Unruh, Valiron and Ying *)

  Theorem den_sts_iff ρ P w σ :
    (∃ F, ⟦ P ⟧[ w ] F ∧ app F ρ = σ) ↔ (∃ l, sts_tree ρ P w l ∧ ssum l = σ).
  Proof.
    split.
    - intros (F & Hd & <-). destruct (den_sound _ _ _ Hd ρ) as (l & Ht & E). eauto.
    - intros (l & Ht & <-). destruct (den_complete _ _ _ _ Ht) as (F & Hd & E). eauto.
  Qed.
End Den_Harmony.
(* end hide *)
