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
From stdpp Require Import base countable decidable list sets relations.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Language.Congruence lqCCS.Language.Denotational.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Memory_Harmony lqCCS.Harmony_Lemma.STS_Harmony.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

(* ** Labels of the reductions: the outcome of a measurement, or nothing *)

Inductive mlabel : Type :=
| MNone
| MMeas (M : meas) (qs : list qubit) (n : nat).

Reserved Notation "⟨ ρ , P ⟩ ⟶[ s , κ ] ⟨ ρ' , P' ⟩" (at level 70).

Section Den_Harmony.
  Context `{QM : QuantumModel}.

  (* ** The effect of an internal action on the memory

      [mem_eff_lab ρ l ρ' κ]: the action [l] of a program (a silent move, or a
      request to the memory) takes the memory from [ρ] to [ρ'], with label
      [κ].  Channel actions have no effect: they are not internal. *)
  Inductive mem_eff_lab (ρ : St) : Labels prog_action → St → mlabel → Prop :=
  | mel_tau : mem_eff_lab ρ τ ρ MNone
  | mel_op E qs : mem_eff_lab ρ (ActExt (PrOp E qs)) (sop_apply E qs ρ) MNone
  | mel_init qs : mem_eff_lab ρ (ActExt (PrInit qs)) (init_apply qs ρ) MNone
  | mel_meas M qs (k : Out (meas_of M qs)) :
      mem_eff_lab ρ (ActExt (PrMeas M qs (code _ k))) (meas_branch M qs k ρ) (MMeas M qs (code _ k)).

  (* A step of the program with its effect on the memory. *)
  Definition mstep_lab (ρ : St) (P : proc) (s : choice) (κ : mlabel) (ρ' : St) (P' : proc) : Prop :=
    ∃ l, prog_step P s l P' ∧ mem_eff_lab ρ l ρ' κ.

  Lemma mem_eff_lab_ren ρ l ρ' κ f : mem_eff_lab ρ l ρ' κ → ren_lbl f l = l.
  Proof. by destruct 1. Qed.

  (* The same reductions, with the redex recorded. *)
  Inductive sts_lab : St → proc → choice → mlabel → St → proc → Prop :=
  | sl_com ρ t c e v t' P K :
      eval e = Some v →
      ⟨ρ, PSend t c e ∥ PG ((PRecv t' c ∙ P) + K)⟩ ⟶[cpair t t', MNone] ⟨ρ, 𝟘 ∥ (subst 0 v P)⟩
  | sl_tau ρ t P K :
      ⟨ρ, PG ((PTau t ∙ P) + K)⟩ ⟶[CTag t, MNone] ⟨ρ, P⟩
  | sl_op ρ t E es qs P K :
      eval_qubits es = Some qs →
      ⟨ρ, PG ((POp t E es ∙ P) + K)⟩ ⟶[CTag t, MNone] ⟨sop_apply E qs ρ, P⟩
  | sl_init ρ t es qs P K :
      eval_qubits es = Some qs →
      ⟨ρ, PG ((PInit t es ∙ P) + K)⟩ ⟶[CTag t, MNone] ⟨init_apply qs ρ, P⟩
  | sl_meas ρ t M es qs (k : Out (meas_of M qs)) P K :
      eval_qubits es = Some qs →
      ⟨ρ, PG ((PMeas t M es ∙ P) + K)⟩ ⟶[CTag t, MMeas M qs (code _ k)] ⟨meas_branch M qs k ρ, (subst 0 (VNat (code _ k)) P)⟩
  | sl_rec ρ t X P :
      ⟨ρ, PRec t X P⟩ ⟶[CTag t, MNone] ⟨ρ, P ⦃ PRec t X P // X ⦄⟩
  | sl_par ρ P s κ ρ' P' Q :
      ⟨ρ, P⟩ ⟶[s, κ] ⟨ρ', P'⟩ → ⟨ρ, P ∥ Q⟩ ⟶[s, κ] ⟨ρ', P' ∥ Q⟩
  | sl_res ρ P s κ ρ' P' :
      ⟨ρ, P⟩ ⟶[s, κ] ⟨ρ', P'⟩ → ⟨ρ, ν P⟩ ⟶[s, κ] ⟨ρ', ν P'⟩
  | sl_cong ρ P P1 s κ ρ' Q1 Q :
      P ≡* P1 → ⟨ρ, P1⟩ ⟶[s, κ] ⟨ρ', Q1⟩ → Q1 ≡* Q → ⟨ρ, P⟩ ⟶[s, κ] ⟨ρ', Q⟩
  where "⟨ ρ , P ⟩ ⟶[ s , κ ] ⟨ ρ' , P' ⟩" := (sts_lab ρ P s κ ρ' P') : lqccs_scope.

  Lemma sts_lab_sts ρ P s κ ρ' P' : ⟨ρ, P⟩ ⟶[s, κ] ⟨ρ', P'⟩ → ⟨ρ, P⟩ ⟶[s] ⟨ρ', P'⟩.
  Proof. induction 1; eauto using sts. Qed.

  Lemma sts_sts_lab ρ P s ρ' P' : ⟨ρ, P⟩ ⟶[s] ⟨ρ', P'⟩ → ∃ κ, ⟨ρ, P⟩ ⟶[s, κ] ⟨ρ', P'⟩.
  Proof.
    induction 1 as [| | | | | | ? ? ? ? ? ? _ (κ & Hs) | ? ? ? ? ? _ (κ & Hs)
                   | ? ? ? ? ? ? ? Hc _ (κ & Hs) Hc']; eexists; eauto using sts_lab.
  Qed.

  Lemma sts_lab_resn n ρ P s κ ρ' P' : ⟨ρ, P⟩ ⟶[s, κ] ⟨ρ', P'⟩ → ⟨ρ, Ѵ n P⟩ ⟶[s, κ] ⟨ρ', Ѵ n P'⟩.
  Proof. intros Hs. induction n; simpl; [done|]. by apply sl_res. Qed.

  (* ** From the LTS to the STS *)

  (* A communication between an output under [n] restrictions and an input
      under [m] restrictions: the restrictions are extruded one by one. *)
  Lemma Com_shapes_lab ρ n :
    ∀ m c e v t t' P1 K R R', eval e = Some v →
    sts_lab ρ (Ѵ n (PSend t (ren_chan (Nat.add n) c) e ∥ R)
           ∥ Ѵ m (PG ((PRecv t' (ren_chan (Nat.add m) c) ∙ P1) + K) ∥ R'))
        (cpair t t') MNone ρ (Ѵ n (𝟘 ∥ R) ∥ Ѵ m ((subst 0 v P1) ∥ R')).
  Proof.
    induction n as [|n IHn]; intros m.
    - induction m as [|m IHm]; intros c e v t t' P1 K R R' He; cbn [Ѵ].
      + rewrite !ren_chan_add_0.
        eapply sl_cong; [apply cgr_par_inversion| |apply cgr_par_inversion].
        apply sl_par. by apply sl_com.
      + eapply sl_cong.
        * etrans; [apply cgr_par_com|].
          etrans; [apply cgr_res_scope_rev|]. apply cgr_res, cgr_par_com.
        * apply sl_res. cbn [ren gren]. rewrite ren_chan_add_0.
          specialize (IHm (ren_chan S c) e v t t' P1 K (ren S R) R' He). cbn [Ѵ] in IHm.
          rewrite ren_chan_add_0, ren_chan_add_S in IHm. exact IHm.
        * etrans; [apply cgr_res, cgr_par_com|].
          change (𝟘 ∥ ren S R) with (ren S (𝟘 ∥ R)).
          etrans; [apply cgr_res_scope|]. apply cgr_par_com.
    - intros c e v t t' P1 K R R' He. cbn [Ѵ].
      eapply sl_cong.
      + apply cgr_res_scope_rev.
      + apply sl_res. rewrite ren_resn. cbn [ren gren prefix_ren].
        rewrite ren_chan_liftn, <- ren_chan_add_S.
        apply (IHn m (ren_chan S c) e v t t' (ren (liftn m S) P1) (gren (liftn m S) K) R
                 (ren (liftn m S) R') He).
      + rewrite <- (proj1 ren_subst).
        replace (Ѵ m (ren (liftn m S) ((subst 0 v P1)) ∥ ren (liftn m S) R'))
          with (ren S (Ѵ m ((subst 0 v P1) ∥ R'))) by (rewrite ren_resn; done).
        apply cgr_res_scope.
  Qed.

  (* A program step with its effect on the memory is a reduction. *)
  Lemma Internal_Implies_Reduction_lab P s l P' :
    prog_step P s l P' → ∀ ρ ρ' κ, mem_eff_lab ρ l ρ' κ → ⟨ρ, P⟩ ⟶[s, κ] ⟨ρ', P'⟩.
  Proof.
    induction 1 as [g s l P' Hg | t c e v He | e P Q s l P' He Hp IH | e P Q s l Q' He Hp IH
                   | P Q s l P' Hp IH | P Q s l Q' Hp IH
                   | P Q t t' c v P' Q' HpP _ HpQ _ | P Q t t' c v P' Q' HpP _ HpQ _
                   | P s l P' Hp IH | t X P] using prog_step_guard_ind; intros ρ ρ' κ Hm.
    - destruct (TransitionShapeForGuard _ _ _ _ Hg) as (𝜆 & Q & K & Hcg & Hs).
      eapply sl_cong; [apply cgr_guard, Hcg| |reflexivity].
      inversion Hs; subst; inversion Hm; subst.
      + apply sl_tau.
      + by apply sl_op.
      + by apply sl_meas.
      + by apply sl_init.
    - inversion Hm.
    - eapply sl_cong; [by apply cgr_if_true | by apply IH | reflexivity].
    - eapply sl_cong; [by apply cgr_if_false | by apply IH | reflexivity].
    - apply sl_par. by apply IH.
    - eapply sl_cong; [apply cgr_par_com | apply sl_par; by apply IH | apply cgr_par_com].
    - inversion Hm; subst.
      destruct (TransitionShapeForOutput _ _ _ _ _ HpP) as (t0 & e & R & n & He & Et & HP1 & HP2).
      destruct (TransitionShapeForInput _ _ _ _ _ HpQ) as (t0' & P1 & K & R' & m & Et' & HQ1 & HQ2).
      simplify_eq.
      eapply sl_cong; [by apply cgr_fullpar | by apply Com_shapes_lab | symmetry; by apply cgr_fullpar].
    - inversion Hm; subst.
      destruct (TransitionShapeForInput _ _ _ _ _ HpP) as (t0 & P1 & K & R & n & Et & HP1 & HP2).
      destruct (TransitionShapeForOutput _ _ _ _ _ HpQ) as (t0' & e & R' & m & He & Et' & HQ1 & HQ2).
      simplify_eq. rewrite cpair_comm.
      eapply sl_cong.
      + etrans; [apply cgr_par_com|]. by apply cgr_fullpar.
      + by apply Com_shapes_lab.
      + etrans; [apply cgr_par_com|]. symmetry. by apply cgr_fullpar.
    - apply sl_res. apply IH. by rewrite (mem_eff_lab_ren _ _ _ _ S Hm).
    - inversion Hm; subst. apply sl_rec.
  Qed.

  Lemma mstep_lab_sts_lab ρ P s κ ρ' P' : mstep_lab ρ P s κ ρ' P' → ⟨ρ, P⟩ ⟶[s, κ] ⟨ρ', P'⟩.
  Proof. intros (l & Hp & Hm). by eapply Internal_Implies_Reduction_lab. Qed.

  Lemma mstep_lab_sts ρ P s κ ρ' P' : mstep_lab ρ P s κ ρ' P' → ⟨ρ, P⟩ ⟶[s] ⟨ρ', P'⟩.
  Proof. intros Hm. eapply sts_lab_sts, mstep_lab_sts_lab, Hm. Qed.

  (* ** From the STS to the LTS *)

  (* The congruence is a simulation of the program steps with memory
      effect, with the same choice and label, up to congruence. *)
  Lemma mstep_lab_cgr ρ P P1 s κ ρ' Q1 :
    P ≡* P1 → mstep_lab ρ P1 s κ ρ' Q1 → ∃ Q, mstep_lab ρ P s κ ρ' Q ∧ Q ≡* Q1.
  Proof.
    intros Hc (l & Hp & Hm). assert (Hf : fwd P1 P) by (apply cgr_bisim; by symmetry).
    destruct (Hf _ _ _ Hp) as (Q & Hq & HQ).
    exists Q. split; [by exists l | by symmetry].
  Qed.

  Lemma Reduction_Implies_Internal_lab ρ P s κ ρ' Q :
    ⟨ρ, P⟩ ⟶[s, κ] ⟨ρ', Q⟩ → ∃ Q', mstep_lab ρ P s κ ρ' Q' ∧ Q' ≡* Q.
  Proof.
    induction 1 as [ρ t c e v t' P K He | ρ t P K | ρ t E es qs P K Hq | ρ t es qs P K Hq
                   | ρ t M es qs k P K Hq | ρ t X P
                   | ρ P s κ ρ' P' Q _ (P'' & (l & Hs & Hm) & HP)
                   | ρ P s κ ρ' P' _ (P'' & (l & Hs & Hm) & HP)
                   | ρ P P1 s κ ρ' Q1 Q Hc _ (Q1' & Hs & HQ) Hc'].
    - exists (𝟘 ∥ (subst 0 v P)). split; [|reflexivity]. exists τ. split; [|constructor].
      eapply pr_syncL; [by apply pr_send | apply pr_sumL, pr_recv].
    - exists P. split; [|reflexivity]. exists τ. split; [|constructor].
      apply pr_sumL, pr_tau.
    - exists P. split; [|reflexivity]. eexists. split; [|constructor].
      by apply pr_sumL, pr_op.
    - exists P. split; [|reflexivity]. eexists. split; [|constructor].
      by apply pr_sumL, pr_init.
    - exists ((subst 0 (VNat (code _ k)) P)). split; [|reflexivity]. eexists. split; [|constructor].
      by apply pr_sumL, pr_meas.
    - exists (P ⦃ PRec t X P // X ⦄). split; [|reflexivity]. exists τ. split; [|constructor].
      apply pr_rec.
    - exists (P'' ∥ Q). split; [|by apply cgr_par]. exists l. split; [by apply pr_parL | done].
    - exists (ν P''). split; [|by apply cgr_res]. exists l. split; [|done].
      apply pr_res. by rewrite (mem_eff_lab_ren _ _ _ _ S Hm).
    - destruct (mstep_lab_cgr _ _ _ _ _ _ _ Hc Hs) as (Q' & Hs' & HQ').
      exists Q'. split; [done|]. etrans; [exact HQ'|]. by etrans.
  Qed.

  Lemma Reduction_Implies_Internal_sts ρ P s ρ' Q :
    ⟨ρ, P⟩ ⟶[s] ⟨ρ', Q⟩ → ∃ κ Q', mstep_lab ρ P s κ ρ' Q' ∧ Q' ≡* Q.
  Proof.
    intros Hs. destruct (sts_sts_lab _ _ _ _ _ Hs) as (κ & Hl).
    destruct (Reduction_Implies_Internal_lab _ _ _ _ _ _ Hl) as (Q' & Hm & HQ). eauto.
  Qed.

  (* ** Trees of reductions following a word of choices *)

  Definition stable_conf (ρ : St) (P : proc) : Prop := ∀ s ρ' P', ¬ ⟨ρ, P⟩ ⟶[s] ⟨ρ', P'⟩.
  Definition enabled_conf (ρ : St) (P : proc) (s : choice) : Prop := ∃ ρ' P', ⟨ρ, P⟩ ⟶[s] ⟨ρ', P'⟩.

  Inductive sts_tree : St → proc → list choice → list St → Prop :=
  | tree_nil_stable ρ P : stable_conf ρ P → sts_tree ρ P [] [ρ]
  | tree_nil_run ρ P : ¬ stable_conf ρ P → sts_tree ρ P [] []
  | tree_stable ρ P s w : stable_conf ρ P → sts_tree ρ P (s :: w) [ρ]
  | tree_stay ρ P s w l :
      ¬ stable_conf ρ P → ¬ enabled_conf ρ P s → sts_tree ρ P w l → sts_tree ρ P (s :: w) l
  | tree_step ρ P s w ρ' P' l :
      ⟨ρ, P⟩ ⟶[s, MNone] ⟨ρ', P'⟩ → sts_tree ρ' P' w l → sts_tree ρ P (s :: w) l
  | tree_meas ρ P t w M qs (Pls : list (proc * list St)) :
      Forall2 (λ k pl, ⟨ρ, P⟩ ⟶[CTag t, MMeas M qs (code _ k)] ⟨meas_branch M qs k ρ, pl.1⟩
                       ∧ sts_tree (meas_branch M qs k ρ) pl.1 w pl.2)
        (outs (meas_of M qs)) Pls →
      sts_tree ρ P (CTag t :: w) (concat (map snd Pls)).

  (* ** Finished configurations are the finished programs *)

  Lemma mem_eff_lab_internal ρ l ρ' κ : mem_eff_lab ρ l ρ' κ → internal l.
  Proof. destruct 1; constructor. Qed.

  Lemma internal_mem_eff_lab l ρ : internal l → ∃ ρ' κ, mem_eff_lab ρ l ρ' κ.
  Proof. destruct 1; do 2 eexists; constructor. Qed.

  Lemma mem_eff_lab_meas_inv ρ l ρ' M qs n :
    mem_eff_lab ρ l ρ' (MMeas M qs n) →
    ∃ k : Out (meas_of M qs), n = code _ k ∧ l = ActExt (PrMeas M qs n).
  Proof. inversion 1; subst. by eexists. Qed.

  Lemma stable_conf_iff ρ P : stable_conf ρ P ↔ stable P.
  Proof.
    split.
    - intros Hs s l P' Hp Hi. destruct (internal_mem_eff_lab _ ρ Hi) as (ρ' & κ & Hm).
      apply (Hs s ρ' P'). apply mstep_lab_sts with κ. by exists l.
    - intros Hs s ρ' P' Hr.
      destruct (Reduction_Implies_Internal_sts _ _ _ _ _ Hr) as (κ & Q' & (l & Hp & Hm) & _).
      apply (Hs _ _ _ Hp). by eapply mem_eff_lab_internal.
  Qed.

  Lemma enabled_conf_iff ρ P s : enabled_conf ρ P s ↔ enabled P s.
  Proof.
    split.
    - intros (ρ' & P' & Hr).
      destruct (Reduction_Implies_Internal_sts _ _ _ _ _ Hr) as (κ & Q' & (l & Hp & Hm) & _).
      exists l, Q'. split; [done|]. by eapply mem_eff_lab_internal.
    - intros (l & P' & Hp & Hi). destruct (internal_mem_eff_lab _ ρ Hi) as (ρ' & κ & Hm).
      exists ρ', P'. apply mstep_lab_sts with κ. by exists l.
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
        Forall2 (λ k pl, ⟨ρ, P⟩ ⟶[CTag t, MMeas M qs (code _ k)] ⟨meas_branch M qs k ρ, pl.1⟩
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
        eapply Internal_Implies_Reduction_lab; [exact Hp|constructor].
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
      eapply tree_step; [|exact Ht]. eapply Internal_Implies_Reduction_lab; [exact Hp|constructor].
    - destruct (IH _ _ Hd' (sop_apply U qs ρ)) as (l & Ht & E). exists l. split.
      + eapply tree_step; [|exact Ht]. eapply Internal_Implies_Reduction_lab; [exact Hp|constructor].
      + by rewrite app_comp.
    - destruct (IH _ _ Hd' (init_apply qs ρ)) as (l & Ht & E). exists l. split.
      + eapply tree_step; [|exact Ht]. eapply Internal_Implies_Reduction_lab; [exact Hp|constructor].
      + by rewrite app_comp.
    - destruct (sound_meas ρ P t w M qs IH _ _ Hf) as (Pls & Hf' & E).
      exists (concat (map snd Pls)). split; [by apply (tree_meas ρ P t w M qs)|].
      unfold meas_sum. by rewrite app_sum_zip.
  Qed.

  (* ** Completeness: the leaves of a tree sum to a denotation *)

  Lemma complete_meas ρ P t w M qs :
    (∀ ρ0 P' l, sts_tree ρ0 P' w l → ∃ F, den P' w F ∧ app F ρ0 = ssum l) →
    ∀ (ks : list (Out (meas_of M qs))) (Pls : list (proc * list St)),
      Forall2 (λ k pl, ⟨ρ, P⟩ ⟶[CTag t, MMeas M qs (code _ k)] ⟨meas_branch M qs k ρ, pl.1⟩
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
    - destruct (Reduction_Implies_Internal_lab _ _ _ _ _ _ Hr) as (Q' & (l & Hp & Hm) & HQ).
      destruct (mem_eff_lab_meas_inv _ _ _ _ _ _ Hm) as (k' & Hk & ->).
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
    - destruct (Reduction_Implies_Internal_lab _ _ _ _ _ _ Hr) as (Q' & (l0 & Hp & Hm) & HQ).
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
Notation "⟨ ρ , P ⟩ ⟶[ s , κ ] ⟨ ρ' , P' ⟩" := (sts_lab ρ P s κ ρ' P') (at level 70) : lqccs_scope.
(* end hide *)
