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
From Stdlib.Logic Require Import Classical_Prop Classical_Pred_Type.
Import ListNotations.
From stdpp Require Import base decidable list.
From TestingTheory Require Import pMust_scheduled pMust_smyth pMust_transfer pMust_canonical.

Section Inductive.
  Context `{WeightLaws} {C Sch : Type} `{SS : !SchedSts C Sch}.

  Inductive pmust (L : lifting) (R : prob → Prop) : dist C → Prop :=
  | pm_now D : R (dmass_of psuccess D) → pmust L R D
  | pm_step D : ¬ dstable D → (∀ σ D', dstep L D σ D' → pmust L R D') → pmust L R D.

  Definition reaches (R : prob → Prop) (r : nat → dist C) : Prop := ∃ n, R (succ_mass r n).

  Lemma pmust_mono L (R R' : prob → Prop) D : (∀ x, R x → R' x) → pmust L R D → pmust L R' D.
  Proof.
    intros HR. induction 1 as [D Hx|D Hns Hs IH]; [apply pm_now, HR, Hx|apply pm_step; [done|exact IH]].
  Qed.

  Lemma pmust_reaches L R D r : pmust L R D → is_run L D r → reaches R r.
  Proof.
    intros Hm. revert r. induction Hm as [D HR|D Hns Hs IH]; intros r [Hr0 Hr].
    - exists 0. unfold succ_mass. rewrite Hr0. exact HR.
    - destruct (Hr 0) as [(σ & Hst)|[Hst _]]; [|rewrite Hr0 in Hst; contradiction].
      rewrite Hr0 in Hst. destruct (IH σ (r 1) Hst (λ i, r (S i))) as (n & Hn).
      + split; [done|]. intros i. exact (Hr (S i)).
      + exists (S n). exact Hn.
  Qed.

  Lemma reaches_pmust (DC : dep_choice) L R D : (∀ r, is_run L D r → reaches R r) → pmust L R D.
  Proof.
    intros Hr. apply NNPP. intros Hn.
    destruct (DC _ (λ x y, ¬ pmust L R x → ((∃ σ, dstep L x σ y) ∨ (dstable x ∧ y = x)) ∧ ¬ pmust L R y) D)
      as (f & Hf0 & Hf).
    { intros x. destruct (classic (pmust L R x)) as [Hx|Hx]; [exists x; intros Hc; by exfalso|].
      destruct (classic (dstable x)) as [Hst|Hst].
      - exists x. intros _. split; [by right|done].
      - destruct (classic (∃ σ D', dstep L x σ D' ∧ ¬ pmust L R D')) as [(σ & D' & Hs & HD')|Hno].
        + exists D'. intros _. split; [left; by exists σ|done].
        + exfalso. apply Hx. apply pm_step; [done|]. intros σ D' Hs. apply NNPP. intros HD'.
          apply Hno. by exists σ, D'. }
    assert (Hall : ∀ i, ¬ pmust L R (f i)).
    { intros i. induction i as [|i IH]; [by rewrite Hf0|]. exact (proj2 (Hf i IH)). }
    destruct (Hr f) as (n & Hn').
    - split; [done|]. intros i. exact (proj1 (Hf i (Hall i))).
    - apply (Hall n). apply pm_now. exact Hn'.
  Qed.

  Theorem pmust_iff (DC : dep_choice) L R D : pmust L R D ↔ ∀ r, is_run L D r → reaches R r.
  Proof.
    split; [intros Hm r Hr; exact (pmust_reaches L R D r Hm Hr)|exact (reaches_pmust DC L R D)].
  Qed.

  Lemma dstep_exists L D σ : dmoves D σ → ∃ D', dstep L D σ D'.
  Proof.
    intros Hm. assert (HΔ : ∃ Δs, Forall2 (λ cρ Δ, comp_step L cρ.2 cρ.1 σ Δ) D Δs).
    { clear Hm. induction D as [|[c ρ] D IH].
      - exists []. constructor.
      - destruct IH as (Δs & HΔs).
        destruct (classic (¬ psuccess c ∧ ∃ Δ, sstep ρ c σ Δ)) as [(Hn & Δ & Hs)|Hn].
        + exists (Δ :: Δs). constructor; [simpl; left; by split|done].
        + exists (rest L c ρ :: Δs). constructor; [|done]. simpl. right. split; [|done].
          destruct (classic (psuccess c)) as [Hc|Hc]; [by left|right].
          intros Δ' Hs. apply Hn. split; [done|]. by exists Δ'. }
    destruct HΔ as (Δs & HΔs). exists (dsum Δs). split; [done|]. by exists Δs.
  Qed.

  Definition pmust_pre (Dp Dq : dist C) : Prop :=
    ∀ v, pmust Stay (λ x, v <ₚ x) Dp → pmust Stay (λ x, v ≤ₚ x) Dq.

  Definition below (r2 : nat → dist C) (D : dist C) : Prop :=
    ∀ w, w <ₚ dmass_of psuccess D → ∃ m, w ≤ₚ succ_mass r2 m.

  Lemma path_cons (good : dist C → Prop) D D' N :
    rstep SS D D' → good D → path SS good D' N → path SS good D (S N).
  Proof.
    intros Hs Hg (f & Hf0 & Hfs & Hfg). exists (λ i, match i with 0 => D | S j => f j end).
    split; [done|]. split.
    - intros [|i] Hi; simpl; [by rewrite Hf0|apply Hfs; lia].
    - intros [|i] Hi; simpl; [done|apply Hfg; lia].
  Qed.

  Lemma le_lt_trans a b c : a ≤ₚ b → b <ₚ c → a <ₚ c.
  Proof. intros Hab [Hbc Hcb]. split; [by etransitivity|]. intros Hca. apply Hcb. by etransitivity. Qed.

  Lemma not_below r2 D : ¬ below r2 D → ∃ w, (∀ m, ¬ w ≤ₚ succ_mass r2 m) ∧ pmust Stay (λ x, w <ₚ x) D.
  Proof.
    intros Hb. apply not_all_ex_not in Hb as (w & Hw). apply imply_to_and in Hw as [Hlt Hno].
    exists w. split; [intros m Hm; apply Hno; by exists m|]. apply pm_now. exact Hlt.
  Qed.

  Hypothesis prob_total : ∀ a b : prob, a ≤ₚ b ∨ b ≤ₚ a.

  Lemma min_list (l : list (dist C)) (P : dist C → Prop) (Q : dist C → prob → Prop) :
    (∀ x, x ∈ l → P x → ∃ w, Q x w) → (∃ x, x ∈ l ∧ P x) →
    ∃ v, (∃ x, x ∈ l ∧ P x ∧ Q x v) ∧ ∀ x, x ∈ l → P x → ∃ w, Q x w ∧ v ≤ₚ w.
  Proof.
    induction l as [|x l IH]; intros HQ (y & Hy & HPy); [by apply elem_of_nil in Hy|].
    assert (Hx0 : x ∈ x :: l) by by left.
    destruct (classic (∃ z, z ∈ l ∧ P z)) as [Hz|Hz].
    - destruct IH as (v1 & (z & Hzl & HPz & HQz) & Hb1); [intros u Hu; apply HQ; by right|done|].
      destruct (classic (P x)) as [Hx|Hx].
      + destruct (HQ x Hx0 Hx) as (w0 & Hw0). destruct (prob_total v1 w0) as [Hle|Hle].
        * exists v1. split; [exists z; split; [by right|done]|].
          intros u Hu HPu. apply elem_of_cons in Hu as [->|Hu]; [by exists w0|exact (Hb1 u Hu HPu)].
        * exists w0. split; [by exists x|].
          intros u Hu HPu. apply elem_of_cons in Hu as [->|Hu]; [by exists w0|].
          destruct (Hb1 u Hu HPu) as (w & Hw & Hvw). exists w. split; [done|]. by etransitivity.
      + exists v1. split; [exists z; split; [by right|done]|].
        intros u Hu HPu. apply elem_of_cons in Hu as [->|Hu]; [done|exact (Hb1 u Hu HPu)].
    - assert (HPx : P x).
      { apply elem_of_cons in Hy as [->|Hy]; [done|]. exfalso. apply Hz. by exists y. }
      destruct (HQ x Hx0 HPx) as (w0 & Hw0). exists w0. split; [by exists x|].
      intros u Hu HPu. apply elem_of_cons in Hu as [->|Hu]; [by exists w0|].
      exfalso. apply Hz. by exists u.
  Qed.

  Hypothesis Hfin : ∀ D, ∃ l : list (dist C), ∀ D', rstep SS D D' → D' ∈ l.

  Lemma bad_threshold r2 N : ∀ D, ¬ path SS (below r2) D N →
    ∃ w, (∀ m, ¬ w ≤ₚ succ_mass r2 m) ∧ pmust Stay (λ x, w <ₚ x) D.
  Proof.
    induction N as [|N IH]; intros D Hb; (destruct (classic (below r2 D)) as [Hg|Hg]; [|exact (not_below r2 D Hg)]).
    - exfalso. apply Hb. exists (λ _, D). split; [done|]. split; intros i Hi; [lia|exact Hg].
    - destruct (classic (dstable D)) as [Hst|Hst].
      + apply IH. intros Hp. apply Hb. apply (path_cons _ D D N); [by right|done|done].
      + destruct (Hfin D) as (l & Hl).
        assert (Hσ : ∃ σ, dmoves D σ).
        { apply not_all_ex_not in Hst as (σ & Hσ). exists σ. by apply NNPP. }
        destruct Hσ as (σ0 & Hσ0). destruct (dstep_exists Stay D σ0 Hσ0) as (D0 & Hs0).
        destruct (min_list l (rstep SS D) (λ D' w, (∀ m, ¬ w ≤ₚ succ_mass r2 m) ∧ pmust Stay (λ x, w <ₚ x) D'))
          as (v & (x & _ & _ & Hv) & Hbound).
        { intros D' _ Hs. apply IH. intros Hp. apply Hb. exact (path_cons _ D D' N Hs Hg Hp). }
        { exists D0. split; [apply Hl; left; by exists σ0|left; by exists σ0]. }
        exists v. split; [exact (proj1 Hv)|]. apply pm_step; [done|]. intros σ D' Hs.
        assert (Hr : rstep SS D D') by (left; by exists σ).
        destruct (Hbound D' (Hl D' Hr) Hr) as (w & (_ & Hw) & Hvw).
        exact (pmust_mono Stay _ _ D' (λ y Hy, le_lt_trans v w y Hvw Hy) Hw).
  Qed.

  Theorem smyth_pmust (DC : dep_choice) (Dp Dq : dist C) :
    smyth_le Stay Dp Dq ↔ pmust_pre Dp Dq.
  Proof.
    split.
    - intros Hs v Hp. apply (reaches_pmust DC). intros r2 Hr2. destruct (Hs r2 Hr2) as (r1 & Hr1 & Hle).
      destruct (pmust_reaches _ _ _ _ Hp Hr1) as (n & Hn). exact (Hle n v Hn).
    - intros Hp r2 Hr2. destruct (konig SS (below r2) Hfin DC Dp) as (r1 & Hr1 & Hg).
      + intros N. apply NNPP. intros Hb. destruct (bad_threshold r2 N Dp Hb) as (w & Hw & Hpw).
        destruct (pmust_reaches _ _ _ _ (Hp w Hpw) Hr2) as (m & Hm). exact (Hw m Hm).
      + exists r1. split; [done|]. intros n w Hw. exact (Hg n w Hw).
  Qed.
End Inductive.
(* end hide *)
