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
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list gmap.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths
  lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum lqCCS.Language.Syntax lqCCS.Language.Program
  lqCCS.Language.Succ lqCCS.Language.FwLTS lqCCS.Testing.Observer.LTS lqCCS.Testing.Observer.Tests
  lqCCS.Language.Label_Abstraction.
From TestingTheory Require Import ActTau gLts Bisimulation Testing_Predicate Subset_Act
  Label_Abstraction.LabelAbstraction.
From TestingTheory Require Completeness CompletenessASco TestSpecBridge.

Section lqCCS_Class_Tests.

Context `{QM : QuantumModel} `{SC : !Countable St}.

Definition pfx_𝔸 (μ : lact) : option prefix :=
  match μ with
  | LIn c _ => Some (PRecv 0 c 0)
  | LOp E qs => Some (POp 0 E (qexps qs))
  | LMeas M qs _ => Some (PMeas 0 M (qexps qs) 0)
  | LOut _ _ => None
  end.

Fixpoint sumg_𝔸 (l : list (lact / 𝔸ʟǫ)) : guard :=
  match l with
  | [] => GNil []
  | x :: l =>
      match pfx_𝔸 (`x) with
      | Some p => GSum (GPre p succP) (sumg_𝔸 l)
      | None => sumg_𝔸 l
      end
  end.

Definition ta_𝔸 (E : gset (lact / 𝔸ʟǫ)) : list lact → proc := gen (PG (sumg_𝔸 (elements E))).

Lemma class_of_repr_lq (x : lact / 𝔸ʟǫ) : ρ[𝔸ʟǫ] (`x) = x.
Proof. exact (@LA_repr_spec _ _ _ (LA_class_surj _) x). Qed.

Lemma sumg_𝔸_fv l : gfv (sumg_𝔸 l) = [].
Proof.
  induction l as [|x l IH]; simpl; [done|].
  destruct x as [[c v|c v|E qs|M qs n] hx]; simpl; rewrite ?IH, ?qexps_fv; done.
Qed.

Lemma sumg_𝔸_ungood l : ggoodb (sumg_𝔸 l) = false.
Proof.
  induction l as [|x l IH]; simpl; [done|].
  destruct x as [[c v|c v|E qs|M qs n] hx]; simpl; rewrite ?IH; done.
Qed.

Lemma sumg_𝔸_tau l : gsucc (sumg_𝔸 l) UTau = [].
Proof.
  induction l as [|x l IH]; simpl; [done|].
  destruct x as [[c v|c v|E qs|M qs n] hx]; simpl; rewrite ?IH; done.
Qed.

Lemma sumg_𝔸_out l c v : gsucc (sumg_𝔸 l) (UAct (AOut c v)) = [].
Proof.
  induction l as [|x l IH]; simpl; [done|].
  destruct x as [[c' v'|c' v'|E qs|M qs n] hx]; simpl; rewrite ?IH; done.
Qed.

Lemma pfx_𝔸_inv μx p : pfx_𝔸 μx = Some p →
  (∃ c v, μx = LIn c v ∧ p = PRecv 0 c 0) ∨ (∃ E qs, μx = LOp E qs ∧ p = POp 0 E (qexps qs))
  ∨ (∃ M qs n, μx = LMeas M qs n ∧ p = PMeas 0 M (qexps qs) 0).
Proof.
  destruct μx as [c v|c v|E qs|M qs n]; simpl; intros [=<-]; [left | right; left | right; right]; eauto.
Qed.

Lemma pfx_𝔸_none μ : pfx_𝔸 μ = None → is_out μ.
Proof. by destruct μ. Qed.

Lemma ker_out μ μ' : lq_ker μ μ' → is_out μ' → is_out μ.
Proof. by destruct μ, μ'. Qed.

Lemma tstep_sum_r g1 g2 μ Q : tstep (PG g2) (ActExt μ) Q → tstep (PG (GSum g1 g2)) (ActExt μ) Q.
Proof.
  destruct μ as [c v|c v|E qs|M qs n]; simpl.
  - intros h. apply succ_spec. simpl. apply elem_of_app. right. exact (proj2 (succ_spec _ _ _) h).
  - intros h. apply succ_spec. simpl. apply elem_of_app. right. exact (proj2 (succ_spec _ _ _) h).
  - intros h. apply succ_spec. simpl. apply elem_of_app. right. exact (proj2 (succ_spec _ _ _) h).
  - intros (y & Q0 & h & HQ). exists y, Q0. split; [| done].
    apply succ_spec. simpl. apply elem_of_app. right. exact (proj2 (succ_spec _ _ _) h).
Qed.

Ltac nil_absurd := match goal with h : _ ∈ _ |- _ => simpl in h; by apply elem_of_nil in h end.

Lemma sumg_𝔸_step_inv l μ Q :
  tstep (PG (sumg_𝔸 l)) (ActExt μ) Q → (∃ x, x ∈ l ∧ ρ[𝔸ʟǫ] μ = x) ∧ ¬ is_out μ ∧ Q = succP.
Proof.
  revert Q. induction l as [|x l IH]; intros Q Hs.
  - destruct μ as [c v|c v|E qs|M qs n]; simpl in Hs.
    + apply succ_spec in Hs. nil_absurd.
    + apply succ_spec in Hs. nil_absurd.
    + apply succ_spec in Hs. nil_absurd.
    + destruct Hs as (y & Q0 & Hs & _). apply succ_spec in Hs. nil_absurd.
  - assert (Hrec : ∀ Q, tstep (PG (sumg_𝔸 l)) (ActExt μ) Q →
                (∃ y, y ∈ x :: l ∧ ρ[𝔸ʟǫ] μ = y) ∧ ¬ is_out μ ∧ Q = succP).
    { intros Q' Hs'. destruct (IH Q' Hs') as ((y & hy & hc) & ho & hq).
      split; [| done]. exists y. split; [by apply list_elem_of_further | done]. }
    assert (Hhere : ∀ μ', ρ[𝔸ʟǫ] μ' = ρ[𝔸ʟǫ] (`x) → ∃ y, y ∈ x :: l ∧ ρ[𝔸ʟǫ] μ' = y).
    { intros μ' e. exists x. split; [apply list_elem_of_here | by rewrite e, class_of_repr_lq]. }
    clear IH. destruct x as [μx hx]. simpl in Hs, Hhere.
    destruct (pfx_𝔸 μx) as [p|] eqn:Hp; [| exact (Hrec Q Hs)].
    apply pfx_𝔸_inv in Hp as [(c' & v' & Ex & ->) | [(E' & qs' & Ex & ->) | (M' & qs' & n' & Ex & ->)]].
    + destruct μ as [c v|c v|E qs|M qs n]; simpl in Hs.
      * apply succ_spec in Hs. simpl in Hs. rewrite sumg_𝔸_out in Hs. nil_absurd.
      * apply succ_spec in Hs. simpl in Hs. apply elem_of_app in Hs as [Hq|Hq].
        -- case_decide as Hc; [| nil_absurd]. apply list_elem_of_singleton in Hq as ->.
           split_and!; [| by intros ? | done].
           apply Hhere. rewrite Ex. apply (class_eq_lq (LIn c v) (LIn c' v')). simpl. by symmetry.
        -- apply Hrec. by apply succ_spec.
      * apply succ_spec in Hs. simpl in Hs. try (apply elem_of_app in Hs as [Hq|Hq]; [nil_absurd |]).
        apply Hrec. by apply succ_spec.
      * destruct Hs as (y & Q0 & Hs & HQ). apply succ_spec in Hs. simpl in Hs.
        try (apply elem_of_app in Hs as [Hq|Hq]; [nil_absurd |]).
        apply Hrec. exists y, Q0. split; [by apply succ_spec | done].
    + destruct μ as [c v|c v|E qs|M qs n]; simpl in Hs.
      * apply succ_spec in Hs. simpl in Hs. rewrite sumg_𝔸_out in Hs. nil_absurd.
      * apply succ_spec in Hs. simpl in Hs. try (apply elem_of_app in Hs as [Hq|Hq]; [nil_absurd |]).
        apply Hrec. by apply succ_spec.
      * apply succ_spec in Hs. simpl in Hs. apply elem_of_app in Hs as [Hq|Hq].
        -- case_decide; [| nil_absurd]. apply list_elem_of_singleton in Hq as ->.
           split_and!; [| by intros ? | done].
           apply Hhere. rewrite Ex. by apply (class_eq_lq (LOp E qs) (LOp E' qs')).
        -- apply Hrec. by apply succ_spec.
      * destruct Hs as (y & Q0 & Hs & HQ). apply succ_spec in Hs. simpl in Hs.
        try (apply elem_of_app in Hs as [Hq|Hq]; [nil_absurd |]).
        apply Hrec. exists y, Q0. split; [by apply succ_spec | done].
    + destruct μ as [c v|c v|E qs|M qs n]; simpl in Hs.
      * apply succ_spec in Hs. simpl in Hs. rewrite sumg_𝔸_out in Hs. nil_absurd.
      * apply succ_spec in Hs. simpl in Hs. try (apply elem_of_app in Hs as [Hq|Hq]; [nil_absurd |]).
        apply Hrec. by apply succ_spec.
      * apply succ_spec in Hs. simpl in Hs. try (apply elem_of_app in Hs as [Hq|Hq]; [nil_absurd |]).
        apply Hrec. by apply succ_spec.
      * destruct Hs as (y & Q0 & Hs & HQ). apply succ_spec in Hs. simpl in Hs.
        apply elem_of_app in Hs as [Hq|Hq].
        -- case_decide as Hd; [| nil_absurd]. destruct Hd as (HM & Hy & Hq').
           rewrite eval_qexps in Hq'. injection Hq' as Hqs.
           apply list_elem_of_singleton in Hq as HQ0. rewrite HQ, HQ0, <- Hy.
           split_and!; [| by intros ? | done].
           apply Hhere. rewrite Ex. apply (class_eq_lq (LMeas M qs n) (LMeas M' qs' n')).
           simpl. split; by symmetry.
        -- apply Hrec. exists y, Q0. split; [by apply succ_spec | done].
Qed.

Lemma sumg_𝔸_step_ex l x : x ∈ l → ¬ is_out (`x) →
  tstep (PG (sumg_𝔸 l)) (ActExt (`x)) succP.
Proof.
  induction l as [|y l IH]; intros Hx Ho; [by apply elem_of_nil in Hx |].
  apply elem_of_cons in Hx as [-> | Hx].
  - destruct y as [μy hy]. simpl in Ho |- *.
    destruct (pfx_𝔸 μy) as [p|] eqn:Hp; [| by apply pfx_𝔸_none in Hp].
    apply pfx_𝔸_inv in Hp as [(c & v & Ey & ->) | [(E & qs & Ey & ->) | (M & qs & n & Ey & ->)]];
      rewrite Ey.
    + apply succ_spec. simpl. rewrite decide_True by done. simpl. first [by apply list_elem_of_here | apply elem_of_app; left; by left].
    + apply succ_spec. simpl. rewrite eval_qexps, decide_True by done. simpl.
      first [by apply list_elem_of_here | apply elem_of_app; left; by left].
    + exists 0, succP. split; [| done]. apply succ_spec. simpl.
      rewrite eval_qexps, decide_True by done. simpl. first [by apply list_elem_of_here | apply elem_of_app; left; by left].
  - pose proof (IH Hx Ho) as Hs. destruct y as [μy hy]. simpl.
    destruct (pfx_𝔸 μy) as [p|]; [by apply tstep_sum_r | exact Hs].
Qed.

#[global] Instance ta_𝔸_spec :
  CompletenessASco.test_co_acceptance_set_spec ta_𝔸 ρ[𝔸ʟǫ].
Proof.
  constructor.
  - intros E. apply TestSpecBridge.test_spec_of_plain, gen_test_spec.
    + simpl. apply sumg_𝔸_fv.
    + simpl. apply sumg_𝔸_ungood.
  - intros E Ht. apply Ht. change (gsucc (sumg_𝔸 (elements E)) UTau = []). apply sumg_𝔸_tau.
  - intros E η Hη. destruct η as [c v| | |]; try done.
    intros Ht. apply Ht. change (gsucc (sumg_𝔸 (elements E)) (UAct (AOut c v)) = []). apply sumg_𝔸_out.
  - intros E β e hb Hs. apply obs_step_def in Hs.
    apply sumg_𝔸_step_inv in Hs as ((x & hx & ->) & _ & _). by apply elem_of_elements.
  - intros E x hx (β & hb & e).
    assert (Ho : ¬ is_out (`x)).
    { intros ho. rewrite <- (class_of_repr_lq x) in e.
      apply (class_eq_lq_inv β (`x)) in e. exact (hb (ker_out _ _ e ho)). }
    exists succP, (`x). split; [| apply class_of_repr_lq].
    apply obs_step_def. apply sumg_𝔸_step_ex; [by apply elem_of_elements | exact Ho].
  - intros β e' E hb Hs. apply obs_step_def in Hs.
    apply sumg_𝔸_step_inv in Hs as (_ & _ & ->). done.
Qed.

End lqCCS_Class_Tests.
(* end hide *)
