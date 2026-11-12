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
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Final.

#[local] Open Scope lqccs_scope.

Section Characterisation.
  Context `{QM : QuantumModel} (p q : proc * St).

  Definition run_against (T : proc) (r : nat → dist comp) (w : nat → item) : Prop :=
    run_word (M := lq_menu (O_T T)) (menu T) (S_T T) (dinit (O_T T) q) r w.

  Definition used (T : proc) (r : nat → dist comp) (w : nat → item) : node → offer → Prop :=
    cells (M := lq_menu (O_T T)) (S_T T) r w.

  Definition refused_by (T : proc) (r : nat → dist comp) (w : nat → item) : node → offer → Prop :=
    refused (M := lq_menu (O_T T)) (used T r w) (S_T T) r w.

  Definition admissible (T : proc) : offer → Prop :=
    real_off p q (λ c, c ∈ out_chans T) (kinds_of T).

  Definition canon_menu (T : proc) (r : nat → dist comp) (w : nat → item) : node → offer → Prop :=
    Jstar (M := lq_menu (O_T T)) (admissible T) (used T r w) (S_T T) r w.

  Definition canon_succ (T : proc) (r : nat → dist comp) (w : nat → item) : node → bool :=
    Sstar (M := lq_menu (O_T T)) (admissible T) (used T r w) (S_T T) r w.

  Definition canon_sts (T : proc) (r : nat → dist comp) (w : nat → item) : SchedSts comp item :=
    mdlts (M := lq_menu (O_T T)) (canon_menu T r w) (canon_succ T r w).

  Lemma canon_menu_spec T r w n o :
    canon_menu T r w n o ↔ used T r w n o ∨ (admissible T o ∧ ¬ refused_by T r w n o).
  Proof. done. Qed.

  Lemma canon_succ_spec T r w n :
    canon_succ T r w n = true ↔
    S_T T n = true ∨ ∃ m a m2, n = m ++ [a] ++ m2 ∧ canon_menu T r w m (offer_of a) ∧ ¬ used T r w m (offer_of a).
  Proof.
    split.
    - intros Hs. exact (Sstar_inv (M := lq_menu (O_T T)) _ _ _ _ _ _ Hs).
    - intros [Hs|Hc]; [by apply Sstar_S|by apply Sstar_crossed].
  Qed.

  Definition alt_canon : Prop :=
    ∀ T, obs_for p q T → ∀ r w, run_against T r w →
      ∃ r', is_run (SchedSts0 := canon_sts T r w) Stay (dinit (O_T T) p) r'
          ∧ run_le (SchedSts0 := canon_sts T r w) r' r.

  Theorem characterisation (DC : dep_choice) :
    q.2 ≠ szero →
    (ctx_pre_sm_on Stay (obs_for p q) p q ↔ alt_canon).
  Proof.
    intros Hz. split.
    - intros Hc T HT r w Hr.
      apply (proj1 (alt_free_obs_iff DC p q Hz) Hc (O_T T) (λ c, c ∈ out_chans T) (kinds_of T) (menu T) (S_T T));
        [|exact Hr].
      split; [|intros n o Hm; exact (menu_real p q T n o HT Hm)].
      exists T. split; [done|]. split; [done|]. split; [done|]. split; [done|]. split; [done|].
      intros k x Hin. exact (kinds_of_tagged T k x (proj1 HT) Hin).
    - intros Ha. apply (alt_pre_obs_iff Stay DC p q). intros T HT r2 Hr2.
      destruct (is_run_word (M := lq_menu (O_T T)) DC (menu T) (S_T T) _ r2 Hr2) as (w & Hw).
      destruct (Ha T HT r2 w Hw) as (rs & Hrs & Hle).
      refine (free_down (M := lq_menu (O_T T)) (admissible T) DC (dinit (O_T T) p) (dinit (O_T T) q)
                (menu T) (S_T T) r2 w rs _ _ _ Hw Hrs Hle).
      + intros x ->%list_elem_of_singleton. done.
      + intros x ->%list_elem_of_singleton. exact Hz.
      + intros n o Hm. exact (menu_real p q T n o HT Hm).
  Qed.
End Characterisation.
(* end hide *)
