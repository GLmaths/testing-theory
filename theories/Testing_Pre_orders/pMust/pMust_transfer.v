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
(* * Probabilistic must: transfer of runs along a stuttering simulation

    Two scheduled systems whose distributions are related by [R], with the
    same successful mass.  A step of the source is matched, after a finite
    path of target steps that stay related to the source (measured by [ν]),
    by one target step, or by no target step when the source stutters
    (measured by [μ]); a stable source distribution leads, after such a
    path, to a stable target.  Then every run of the source is mirrored by a
    run of the target with the same successful masses, in both directions.
    Building the run of the target from the one of the source needs
    dependent choice. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Lia Wf_nat.
From stdpp Require Import base decidable list.
From TestingTheory Require Import pMust_scheduled pMust_almost_sure.

Definition dep_choice : Prop :=
  ∀ (A : Type) (N : A → A → Prop) (a : A),
    (∀ x, ∃ y, N x y) → ∃ f : nat → A, f 0 = a ∧ ∀ n, N (f n) (f (S n)).

Lemma Forall2_elem_of_l {A B} (R : A → B → Prop) (l : list A) (k : list B) x :
  Forall2 R l k → x ∈ l → ∃ y, y ∈ k ∧ R x y.
Proof.
  induction 1 as [|a b l k Hab _ IH]; intros Hx; [by apply elem_of_nil in Hx|].
  apply elem_of_cons in Hx as [->|Hx]; [exists b; split; [by left|done]|].
  destruct (IH Hx) as (y & Hy & Hxy). exists y. split; [by right|done].
Qed.

Lemma Forall2_elem_of_r {A B} (R : A → B → Prop) (l : list A) (k : list B) y :
  Forall2 R l k → y ∈ k → ∃ x, x ∈ l ∧ R x y.
Proof.
  induction 1 as [|a b l k Hab _ IH]; intros Hy; [by apply elem_of_nil in Hy|].
  apply elem_of_cons in Hy as [->|Hy]; [exists a; split; [by left|done]|].
  destruct (IH Hy) as (x & Hx & Hxy). exists x. split; [by right|done].
Qed.

(* A property of the weights preserved by the steps of the components holds
    along the runs. *)
Lemma run_weights `{Weights} {C Sch : Type} `{!SchedSts C Sch} (L : lifting) (good : weight → Prop) :
  (∀ ρ c σ Δ, good ρ → sstep ρ c σ Δ → ∀ x, x ∈ Δ → good x.2) →
  ∀ 𝔇 r, is_run L 𝔇 r → (∀ x, x ∈ 𝔇 → good x.2) → ∀ n x, x ∈ r n → good x.2.
Proof.
  intros Hstep 𝔇 r [E Hr] H0 n. induction n as [|n IH]; [by rewrite E|].
  destruct (Hr n) as [(σ & _ & Δs & HF & ->)|(_ & ->)]; [|done].
  intros x Hx. unfold dsum in Hx. apply list_elem_of_In, in_concat in Hx as (Δ & HΔ & Hx).
  apply list_elem_of_In in HΔ, Hx.
  destruct (Forall2_elem_of_r _ _ _ _ HF HΔ) as (cρ & Hc & [(_ & Hs)|(_ & ->)]).
  - exact (Hstep _ _ _ _ (IH cρ Hc) Hs x Hx).
  - apply elem_of_rest in Hx. subst x. destruct cρ as [c ρ]. by apply IH.
Qed.

Section Transfer.
  Context `{Weights} {C1 Sch1 C2 Sch2 : Type} `{!SchedSts C1 Sch1} `{!SchedSts C2 Sch2}.
  Context (L : lifting) (DC : dep_choice).
  Context (R : dist C1 → dist C2 → Prop) (μ : dist C1 → nat) (ν : dist C2 → nat).

  Definition step1 (Δ Δ' : dist C1) : Prop := ∃ σ, dstep L Δ σ Δ'.
  Definition step2 (Θ Θ' : dist C2) : Prop := ∃ σ, dstep L Θ σ Θ'.

  (* A path of target steps related to the same source, decreasing [ν]. *)
  Inductive pre (Δ : dist C1) : dist C2 → dist C2 → Prop :=
  | pre_nil Θ : pre Δ Θ Θ
  | pre_step Θ Θ1 Θ2 :
      step2 Θ Θ1 → R Δ Θ1 → ν Θ1 < ν Θ → pre Δ Θ1 Θ2 → pre Δ Θ Θ2.

  Hypothesis Hmass : ∀ Δ Θ, R Δ Θ → dmass_of psuccess Δ = dmass_of psuccess Θ.
  Hypothesis Hstep : ∀ Δ Θ Δ', R Δ Θ → step1 Δ Δ' →
    ∃ Θ1, pre Δ Θ Θ1 ∧ ((∃ Θ', step2 Θ1 Θ' ∧ R Δ' Θ') ∨ (R Δ' Θ1 ∧ μ Δ' < μ Δ)).
  Hypothesis Hstable : ∀ Δ Θ, R Δ Θ → dstable Δ → ∃ Θ1, pre Δ Θ Θ1 ∧ dstable Θ1.

  Section Run.
    Context (r : nat → dist C1) (Δ0 : dist C1) (Hr : is_run L Δ0 r).

    (* One transition of the mirrored run: the source stutters from [i] to
        [j], then the target does a pre-step, a matched step, or stays. *)
    Definition witness (i : nat) (Θ : dist C2) (j i' : nat) (Θ' : dist C2) : Prop :=
      i ≤ j ∧ (∀ k, i ≤ k → k ≤ j → R (r k) Θ) ∧
      ((step2 Θ Θ' ∧ R (r j) Θ' ∧ ν Θ' < ν Θ ∧ i' = j)
       ∨ (step1 (r j) (r (S j)) ∧ step2 Θ Θ' ∧ R (r (S j)) Θ' ∧ i' = S j)
       ∨ (dstable (r j) ∧ dstable Θ ∧ Θ' = Θ ∧ i' = S j)).

    (* The states of the mirrored run: an index of the source and a related target. *)
    Definition rstate : Type := { x : nat * dist C2 | R (r x.1) x.2 }.

    Definition next (x y : rstate) : Prop :=
      ∃ j, witness (`x).1 (`x).2 j (`y).1 (`y).2.

    Lemma run_stay i : dstable (r i) → r (S i) = r i.
    Proof.
      intros Hst. destruct Hr as [_ Hs]. destruct (Hs i) as [(σ & Hd)|[_ ->]]; [|done].
      exfalso. exact (dstep_not_stable _ _ _ _ Hd Hst).
    Qed.

    Lemma next_exists : ∀ n i Θ, μ (r i) = n → R (r i) Θ → ∃ j i' Θ', witness i Θ j i' Θ'.
    Proof.
      intros n. induction (lt_wf n) as [n _ IH]. intros i Θ Hn HR. subst n.
      destruct Hr as [_ Hs]. destruct (Hs i) as [(σ & Hd)|[Hst Heq]].
      - destruct (Hstep _ _ _ HR (ex_intro _ σ Hd)) as (Θ1 & Hpre & Hc).
        inversion Hpre as [|? Θa ? Hs2 HRa Hν Hpre']; subst.
        + destruct Hc as [(Θ' & Hs2 & HR')|(HR' & Hμ)].
          * exists i, (S i), Θ'. split; [lia|]. split; [intros k ? ?; by replace k with i by lia|].
            right. left. repeat split; [by exists σ|done|done].
          * destruct (IH (μ (r (S i))) ltac:(lia) (S i) _ eq_refl HR') as (j & i' & Θ' & Hij & Hcov & Hcase).
            exists j, i', Θ'. split; [lia|]. split; [|done].
            intros k Hik Hkj. destruct (decide (k = i)) as [->|]; [done|]. apply Hcov; lia.
        + exists i, i, Θa. split; [lia|]. split; [intros k ? ?; by replace k with i by lia|]. by left.
      - destruct (Hstable _ _ HR Hst) as (Θ1 & Hpre & Hst1).
        inversion Hpre as [|? Θa ? Hs2 HRa Hν Hpre']; subst.
        + exists i, (S i), Θ1. split; [lia|]. split; [intros k ? ?; by replace k with i by lia|].
          right. right. done.
        + exists i, i, Θa. split; [lia|]. split; [intros k ? ?; by replace k with i by lia|]. by left.
    Qed.

    Lemma witness_rel i Θ j i' Θ' : R (r i) Θ → witness i Θ j i' Θ' → R (r i') Θ'.
    Proof.
      intros HR (Hij & Hcov & [(_ & HR' & _ & ->)|[(_ & _ & HR' & ->)|(Hst & _ & -> & ->)]]); [done|done|].
      rewrite run_stay; [|done]. apply Hcov; lia.
    Qed.

    Lemma next_total (x : rstate) : ∃ y, next x y.
    Proof.
      destruct x as [[i Θ] HR]. simpl in HR.
      destruct (next_exists _ _ _ eq_refl HR) as (j & i' & Θ' & Hw).
      exists ((i', Θ') ↾ witness_rel i Θ j i' Θ' HR Hw). by exists j.
    Qed.

    Context (Θ0 : dist C2) (HR0 : R Δ0 Θ0).

    Lemma mirror :
      ∃ r' : nat → dist C2, is_run L Θ0 r' ∧
        (∀ m, ∃ n, succ_mass r' m = succ_mass r n) ∧ (∀ n, ∃ m, succ_mass r n = succ_mass r' m).
    Proof.
      assert (HR0' : R (r (0, Θ0).1) (0, Θ0).2) by (simpl; destruct Hr as [E _]; by rewrite E).
      destruct (DC _ next ((0, Θ0) ↾ HR0') next_total) as (f & Hf0 & Hf).
      set (g := λ m, ` (f m)).
      assert (Hinv : ∀ m, R (r (g m).1) (g m).2) by (intros m; apply (proj2_sig (f m))).
      assert (Hg0 : g 0 = (0, Θ0)) by (unfold g; by rewrite Hf0).
      assert (Hg : ∀ m, ∃ j, witness (g m).1 (g m).2 j (g (S m)).1 (g (S m)).2) by (intros m; apply (Hf m)).
      clearbody g. clear f Hf0 Hf.
      exists (λ m, (g m).2). split; [|split].
      - split; [by rewrite Hg0|]. intros m.
        destruct (Hg m) as (j & Hij & Hcov & [((σ & Hd) & _)|[(_ & (σ & Hd) & _)|(_ & Hst & Heq & _)]]).
        + left. by exists σ.
        + left. by exists σ.
        + right. split; [done|]. by rewrite Heq.
      - intros m. exists (g m).1. unfold succ_mass. symmetry. by apply Hmass.
      - assert (Hcov : ∀ n, ∃ m j, witness (g m).1 (g m).2 j (g (S m)).1 (g (S m)).2 ∧ (g m).1 ≤ n ∧ n ≤ j).
        { intros n. induction n as [|n (m & j & Hw & Hmn & Hnj)].
          - destruct (Hg 0) as (j & Hw). exists 0, j. split; [done|]. rewrite Hg0. simpl. lia.
          - assert (Hsucc : ∀ v m j, witness (g m).1 (g m).2 j (g (S m)).1 (g (S m)).2 →
              (g m).1 ≤ n → n ≤ j → ν (g m).2 ≤ v →
              ∃ m' j', witness (g m').1 (g m').2 j' (g (S m')).1 (g (S m')).2 ∧ (g m').1 ≤ S n ∧ S n ≤ j').
            { intros v. induction v as [|v IHv]; intros m0 j0 Hw0 Hm0 Hnj0 Hv;
                destruct (decide (n < j0)) as [Hlt|Hge]; try (exists m0, j0; split; [done|lia]).
              - destruct Hw0 as (_ & _ & [(_ & _ & Hν & _)|[(_ & _ & _ & Hi')|(_ & _ & _ & Hi')]]); [lia| |];
                  destruct (Hg (S m0)) as (j1 & Hw1); exists (S m0), j1;
                  (split; [done|]); destruct Hw1 as (Hle & _); lia.
              - destruct Hw0 as (_ & _ & [(_ & _ & Hν & Hi')|[(_ & _ & _ & Hi')|(_ & _ & _ & Hi')]]).
                + destruct (Hg (S m0)) as (j1 & Hw1).
                  apply (IHv (S m0) j1 Hw1); [lia| |lia]. destruct Hw1 as (Hle & _). lia.
                + destruct (Hg (S m0)) as (j1 & Hw1). exists (S m0), j1.
                  split; [done|]. destruct Hw1 as (Hle & _). lia.
                + destruct (Hg (S m0)) as (j1 & Hw1). exists (S m0), j1.
                  split; [done|]. destruct Hw1 as (Hle & _). lia. }
            eapply Hsucc; [exact Hw|done|done|done]. }
        intros n. destruct (Hcov n) as (m & j & (Hij & Hk & _) & Hmn & Hnj).
        exists m. unfold succ_mass. apply Hmass. by apply Hk.
    Qed.
  End Run.

  Theorem run_transfer Δ Θ r :
    R Δ Θ → is_run L Δ r →
    ∃ r', is_run L Θ r' ∧
      (∀ m, ∃ n, succ_mass r' m = succ_mass r n) ∧ (∀ n, ∃ m, succ_mass r n = succ_mass r' m).
  Proof. intros HR Hr. by apply (mirror r Δ Hr Θ HR). Qed.

  Lemma pmust_as_transfer Δ Θ :
    R Δ Θ → dmass Δ = dmass Θ → pmust_as L Θ → pmust_as L Δ.
  Proof.
    intros HR Hm Has r Hr w Hw.
    destruct (run_transfer Δ Θ r HR Hr) as (r' & Hr' & HM & _).
    assert (Hw' : w <ₚ dmass (r' 0)).
    { destruct Hr as [E _]. destruct Hr' as [E' _]. rewrite E', <- Hm, <- E. exact Hw. }
    destruct (Has r' Hr' w Hw') as (n & Hn). destruct (HM n) as (m & E).
    exists m. by rewrite <- E.
  Qed.
End Transfer.
(* end hide *)
