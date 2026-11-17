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
From Stdlib.Logic Require Import Classical_Prop ClassicalDescription.
Import ListNotations.
From stdpp Require Import base decidable list.
From TestingTheory Require Import pMust_scheduled pMust_smyth pMust_transfer pMust_canonical.

Section KonigUpto.
  Context `{WeightLaws} {C Sch : Type} (SS : SchedSts C Sch) (good : dist C → Prop).

  Definition succ_eqv (D1 D2 : dist C) : Prop :=
    Forall2 (λ x y, x = y ∨ (psuccess (SchedSts := SS) x.1 ∧ psuccess (SchedSts := SS) y.1 ∧ x.2 = y.2)) D1 D2.

  Lemma succ_eqv_sym D1 D2 : succ_eqv D1 D2 → succ_eqv D2 D1.
  Proof.
    induction 1 as [|x y D1 D2 Hxy _ IH]; constructor; [|exact IH].
    destruct Hxy as [->|(Hx & Hy & Ew)]; [by left|right; done].
  Qed.

  Lemma succ_eqv_refl D : succ_eqv D D.
  Proof. induction D as [|x D IH]; constructor; [by left|exact IH]. Qed.

  Lemma succ_eqv_mass (g : C → Prop) `{∀ c, Decision (g c)} D1 D2 :
    (∀ c, psuccess (SchedSts := SS) c → g c) → succ_eqv D1 D2 → dmass_of g D1 = dmass_of g D2.
  Proof.
    intros Hg. induction 1 as [|x y D1 D2 Hxy _ IH]; [done|]. simpl. rewrite IH.
    destruct Hxy as [->|(Hx & Hy & Ew)]; [done|].
    rewrite (decide_True (P := g x.1)) by (by apply Hg). rewrite (decide_True (P := g y.1)) by (by apply Hg).
    by rewrite Ew.
  Qed.

  Lemma comps_eqv σ D1 D2 Δs1 : succ_eqv D1 D2 →
    Forall2 (λ cρ Δ, comp_step (SchedSts0 := SS) Stay cρ.2 cρ.1 σ Δ) D1 Δs1 →
    ∃ Δs2, Forall2 (λ cρ Δ, comp_step (SchedSts0 := SS) Stay cρ.2 cρ.1 σ Δ) D2 Δs2 ∧ succ_eqv (dsum Δs1) (dsum Δs2).
  Proof.
    intros HE. revert Δs1. induction HE as [|x y D1 D2 Hxy _ IH]; intros Δs1 HF.
    - inversion HF; subst. exists []. split; constructor.
    - inversion HF as [|? Δ ? Δs1' Hc HF']; subst.
      destruct (IH Δs1' HF') as (Δs2 & HF2 & HE2).
      destruct Hxy as [<-|(Hx & Hy & Ew)].
      + exists (Δ :: Δs2). split; [by constructor|]. rewrite !dsum_cons. apply Forall2_app; [|exact HE2].
        apply succ_eqv_refl.
      + exists ([y] :: Δs2). split.
        * constructor; [|exact HF2]. right. split; [by left|]. destruct y; done.
        * rewrite !dsum_cons. apply Forall2_app; [|exact HE2].
          destruct Hc as [(Hns & _)|(_ & ->)]; [exfalso; exact (Hns Hx)|].
          constructor; [|constructor]. right. destruct x, y; simpl in *. done.
  Qed.

  Lemma partner D1 D2 x : succ_eqv D1 D2 → x ∈ D1 → ¬ psuccess (SchedSts := SS) x.1 → x ∈ D2.
  Proof.
    intros HE Hx Hns. destruct (Forall2_elem_of_l _ _ _ _ HE Hx) as (y & Hy & [->|(Hs & _)]); [done|].
    by exfalso.
  Qed.

  Lemma rstep_eqv D1 D2 D1' : succ_eqv D1 D2 → rstep SS D1 D1' → ∃ D2', rstep SS D2 D2' ∧ succ_eqv D1' D2'.
  Proof.
    intros HE [(σ & Hm & Δs & HF & ->)|(Hst & ->)].
    - destruct (comps_eqv σ D1 D2 Δs HE HF) as (Δs2 & HF2 & HE2). exists (dsum Δs2). split; [|exact HE2].
      left. exists σ. split; [|by exists Δs2].
      destruct Hm as (c & ρ & Δ & Hin & Hns & Hs). exists c, ρ, Δ.
      split; [exact (partner D1 D2 (c, ρ) HE Hin Hns)|done].
    - exists D2. split; [|exact HE]. right. split; [|done].
      intros σ (c & ρ & Δ & Hin & Hns & Hs). apply (Hst σ). exists c, ρ, Δ.
      split; [exact (partner D2 D1 (c, ρ) (succ_eqv_sym _ _ HE) Hin Hns)|done].
  Qed.

  Hypothesis Hgood : ∀ D1 D2, succ_eqv D1 D2 → good D1 → good D2.
  Hypothesis Hfin : ∀ D, ∃ l : list (dist C), ∀ D', rstep SS D D' → ∃ D'', D'' ∈ l ∧ succ_eqv D' D''.

  Lemma path_cons D D' N : rstep SS D D' → good D → path SS good D' N → path SS good D (S N).
  Proof.
    intros Hs Hg (f & Hf0 & Hfs & Hfg). exists (λ i, match i with 0 => D | S i => f i end).
    split; [done|]. split.
    - intros i Hi. destruct i as [|i]; simpl; [by rewrite Hf0|]. apply Hfs. lia.
    - intros i Hi. destruct i as [|i]; [done|]. apply Hfg. lia.
  Qed.

  Lemma path_eqv N : ∀ D1 D2, succ_eqv D1 D2 → path SS good D1 N → path SS good D2 N.
  Proof.
    induction N as [|N IH]; intros D1 D2 HE Hp.
    - destruct Hp as (f & Hf0 & _ & Hg). exists (λ _, D2). split; [done|]. split; [intros; lia|].
      intros i Hi. apply (Hgood D1); [done|]. rewrite <- Hf0. apply Hg. lia.
    - destruct (path_succ SS good D1 N Hp) as (D1' & Hs & Hp').
      destruct (rstep_eqv D1 D2 D1' HE Hs) as (D2' & Hs2 & HE2).
      apply (path_cons D2 D2'); [done| |exact (IH D1' D2' HE2 Hp')].
      destruct Hp as (f & Hf0 & _ & Hg). apply (Hgood D1); [done|]. rewrite <- Hf0. apply Hg. lia.
  Qed.

  Lemma path_step_upto D : (∀ N, path SS good D N) → ∃ D', rstep SS D D' ∧ ∀ N, path SS good D' N.
  Proof.
    intros Hp. destruct (Hfin D) as (l & Hl). apply NNPP. intros Hn.
    destruct (bound_list SS good l (λ x, ∃ D', rstep SS D D' ∧ succ_eqv D' x)) as (M & HM).
    { intros x _ (D' & Hs & HE). apply NNPP. intros Hc. apply Hn. exists D'. split; [done|]. intros N.
      apply (path_eqv N x D'); [exact (succ_eqv_sym _ _ HE)|]. apply NNPP. intros HN. apply Hc. by exists N. }
    destruct (path_succ SS good D M (Hp (S M))) as (D' & Hs & HD').
    destruct (Hl D' Hs) as (x & Hx & HE). exact (HM x Hx (ex_intro _ D' (conj Hs HE)) (path_eqv M D' x HE HD')).
  Qed.

  Theorem konig_upto (DC : dep_choice) D :
    (∀ N, path SS good D N) → ∃ r, is_run (SchedSts0 := SS) Stay D r ∧ ∀ i, good (r i).
  Proof.
    intros Hp.
    destruct (DC _ (λ x y, (∀ N, path SS good x N) → rstep SS x y ∧ ∀ N, path SS good y N) D) as (f & Hf0 & Hf).
    { intros x. destruct (classic (∀ N, path SS good x N)) as [Hx|Hx].
      - destruct (path_step_upto x Hx) as (y & Hy). exists y. intros _. exact Hy.
      - exists x. intros Hc. by exfalso. }
    assert (Hall : ∀ i N, path SS good (f i) N).
    { intros i. induction i as [|i IH]; [by rewrite Hf0|]. exact (proj2 (Hf i IH)). }
    exists f. split; [split; [done|]|].
    - intros i. destruct (proj1 (Hf i (Hall i))) as [Hs|Hs]; [by left|by right].
    - intros i. destruct (Hall i 0) as (g & Hg0 & _ & Hg). rewrite <- Hg0. apply Hg. lia.
  Qed.
End KonigUpto.

Section CoTrace.
  Context `{WeightLaws} {C Sch A Off : Type} `{M : !MenuSts C Sch A Off} (Ok : Off → Prop).
  Notation node := (list A).

  Definition co_dist (D : dist C) : dist node := (λ x, (mnode x.1, x.2)) <$> D.

  Definition co_run (I : node → Off → Prop) (S : node → bool) (D : dist C)
      (π : nat → dist node) (R : node → Off → Prop) : Prop :=
    ∃ r w, run_word I S D r w ∧ π = (λ i, co_dist (r i)) ∧ R = refused I S r w.

  Definition co_trace (S : node → bool) (D : dist C)
      (π : nat → dist node) (U R : node → Off → Prop) : Prop :=
    ∃ r w, run_word (cells S r w) S D r w ∧ π = (λ i, co_dist (r i))
         ∧ U = cells S r w ∧ R = refused (cells S r w) S r w.

  Definition co_menu (U R : node → Off → Prop) (n : node) (o : Off) : Prop := U n o ∨ (Ok o ∧ ¬ R n o).

  Definition co_left (J U : node → Off → Prop) (n : node) : Prop :=
    ∃ m a m2, n = m ++ [a] ++ m2 ∧ J m (moffer a) ∧ ¬ U m (moffer a).

  Definition co_success (S : node → bool) (J U : node → Off → Prop) (n : node) : bool :=
    S n || (if excluded_middle_informative (co_left J U n) then true else false).

  Definition co_le (S1 S2 : node → bool) (π1 π2 : nat → dist node) : Prop :=
    ∀ n x, x <ₚ dmass_of (λ m, S1 m = true) (π1 n) → ∃ m, x ≤ₚ dmass_of (λ m, S2 m = true) (π2 m).

  Definition co_below (S : node → bool) (U R : node → Off → Prop) (π : nat → dist node)
      (I : node → Off → Prop) (π' : nat → dist node) (R' : node → Off → Prop) : Prop :=
    (∀ n o, I n o → co_menu U R n o) ∧ (∀ n o, co_menu U R n o → ¬ R' n o)
    ∧ co_le (co_success S (co_menu U R) U) S π' π.

  Definition malt_cotrace (Dp Dq : dist C) : Prop :=
    ∀ S, mext_closed S → ∀ π U R, co_trace S Dq π U R → (∀ n o, U n o → Ok o) →
      ∃ I π' R', co_run I (co_success S (co_menu U R) U) Dp π' R'
        ∧ co_below S U R π I π' R'.

  Lemma co_dist_mass (S : node → bool) (D : dist C) :
    dmass_of (λ m, S m = true) (co_dist D) = dmass_of (λ c, S (mnode c) = true) D.
  Proof. induction D as [|x D IH]; [done|]. simpl. by rewrite IH. Qed.

  Lemma refused_not_menu I S r w n o : refused I S r w n o → ¬ I n o.
  Proof.
    intros (i & c & ρ & Hin & Hs & Hc) HI.
    assert (Hup : ∀ σ Δ, mstep (single n o) ρ c σ Δ → mstep I ρ c σ Δ).
    { intros σ Δ Hsg. destruct (mstep_cell _ _ _ _ _ Hsg) as [[Hall _]|(o' & [En Eo] & HJ & _)]; [apply Hall|].
      apply HJ. rewrite En, Eo. exact HI. }
    destruct Hc as [(_ & Hno & Δ & Hsg)|(Hst & σ & Δ & Hsg)].
    - exact (Hno Δ (Hup _ _ Hsg)).
    - apply (Hst σ). exists c, ρ, Δ. split; [done|]. split; [|exact (Hup _ _ Hsg)].
      simpl. rewrite Hs. done.
  Qed.

  Section Fixed.
    Context (Dp : dist C) (S : node → bool) (r : nat → dist C) (w : nat → Sch).
    Notation U := (cells S r w).
    Notation R := (refused (cells S r w) S r w).
    Hypothesis Hrun : run_word U S (r 0) r w.
    Hypothesis Hq0 : ∀ x, x ∈ r 0 → mnode x.1 = [].
    Hypothesis HokU : ∀ n o, U n o → Ok o.

    Lemma co_q_mass i :
      succ_mass (SchedSts0 := mdlts (Jstar Ok U S r w) (Sstar Ok U S r w)) r i
      = dmass_of (λ m, S m = true) (co_dist (r i)).
    Proof.
      rewrite co_dist_mass. unfold succ_mass. apply dmass_of_congr. intros c ρ Hin. simpl.
      rewrite (Sstar_visited Ok U S r w Hrun (init_visited (r 0) U Hq0) i c ρ Hin). done.
    Qed.

    Lemma co_fwd (DC : dep_choice) :
      (∃ r', is_run (SchedSts0 := mdlts (Jstar Ok U S r w) (Sstar Ok U S r w)) Stay Dp r'
           ∧ run_le (SchedSts0 := mdlts (Jstar Ok U S r w) (Sstar Ok U S r w)) r' r) →
      ∃ I π' R', co_run I (co_success S (co_menu U R) U) Dp π' R'
        ∧ co_below S U R (λ i, co_dist (r i)) I π' R'.
    Proof.
      intros (r' & Hr' & Hle). destruct (is_run_word DC _ _ _ _ Hr') as (w' & Hw').
      exists (co_menu U R), (λ i, co_dist (r' i)), (refused (co_menu U R) (co_success S (co_menu U R) U) r' w').
      split; [by exists r', w'|]. split; [done|]. split; [intros n o Hn HR; exact (refused_not_menu _ _ _ _ _ _ HR Hn)|].
      intros n x Hx. rewrite co_dist_mass in Hx. destruct (Hle n x Hx) as (m & Hm). exists m.
      rewrite <- co_q_mass. exact Hm.
    Qed.

    Lemma co_bwd :
      (∃ I π' R', co_run I (co_success S (co_menu U R) U) Dp π' R'
        ∧ co_below S U R (λ i, co_dist (r i)) I π' R') →
      ∃ r', is_run (SchedSts0 := mdlts (Jstar Ok U S r w) (Sstar Ok U S r w)) Stay Dp r'
           ∧ run_le (SchedSts0 := mdlts (Jstar Ok U S r w) (Sstar Ok U S r w)) r' r.
    Proof.
      intros (I & π' & R' & (r' & w' & Hw' & -> & ->) & HIJ & HJR & Hle). exists r'. split.
      - assert (Hr : run_word I (Sstar Ok U S r w) (r' 0) r' w') by (split; [done|apply Hw']).
        pose proof (run_sandwich Ok I (Sstar Ok U S r w) r' w' Hr (Jstar Ok U S r w) (Sstar Ok U S r w)
          (λ _ _ _ _, eq_refl) (λ i c ρ o _ _ Ho, HIJ _ _ Ho)) as Hs.
        apply run_word_is_run with w'. rewrite <- (proj1 Hw'). apply Hs.
        intros i c ρ o _ _ Hn. right. split; [|exact (HJR _ _ Hn)].
        destruct Hn as [Hn|[Ho _]]; [exact (HokU _ _ Hn)|exact Ho].
      - intros n x Hx. unfold succ_mass in Hx.
        rewrite (dmass_of_congr _ (λ c, co_success S (co_menu U R) U (mnode c) = true)) in Hx; [|done].
        rewrite <- co_dist_mass in Hx.
        destruct (Hle n x Hx) as (m & Hm). exists m. rewrite co_q_mass. exact Hm.
    Qed.
  End Fixed.

  Theorem malt_cotrace_iff (DC : dep_choice) (Dp Dq : dist C) :
    (∀ x, x ∈ Dq → mnode x.1 = []) → (malt_free Ok Dp Dq ↔ malt_cotrace Dp Dq).
  Proof.
    intros Hq. split.
    - intros Hf S HS π U R (r & w & Hw & -> & -> & ->) HokU.
      assert (Hr : run_word (cells S r w) S (r 0) r w) by (split; [done|apply Hw]).
      assert (Hr0 : ∀ x, x ∈ r 0 → mnode x.1 = []) by (rewrite (proj1 Hw); exact Hq).
      exact (co_fwd Dp S r w Hr Hr0 DC (Hf S HS r w HokU Hw)).
    - intros Hc S HS r w HokU Hw.
      assert (Hr : run_word (cells S r w) S (r 0) r w) by (split; [done|apply Hw]).
      assert (Hr0 : ∀ x, x ∈ r 0 → mnode x.1 = []) by (rewrite (proj1 Hw); exact Hq).
      refine (co_bwd Dp S r w Hr Hr0 HokU _). apply (Hc S HS); [by exists r, w|exact HokU].
  Qed.

  Lemma mstep_depth J ρ c σ Δ y : mstep J ρ c σ Δ → y ∈ Δ → length (mnode y.1) ≤ S (length (mnode c)).
  Proof.
    intros Hs Hy. destruct (mstep_cell _ _ _ _ _ Hs) as [[_ Hn]|(o & _ & _ & Hn)].
    - rewrite (Hn y Hy). lia.
    - destruct (Hn y Hy) as (a & _ & ->). rewrite length_app. simpl. lia.
  Qed.

  Lemma comps_depth I Sx (D : dist C) σ Δs k :
    Forall2 (λ cρ Δ, comp_step (SchedSts0 := mdlts I Sx) Stay cρ.2 cρ.1 σ Δ) D Δs →
    (∀ x, x ∈ D → length (mnode x.1) ≤ k) → ∀ x, x ∈ dsum Δs → length (mnode x.1) ≤ S k.
  Proof.
    induction 1 as [|[c ρ] Δ D Δs Hc _ IH]; intros HD x Hx; [by apply elem_of_nil in Hx|].
    change (x ∈ Δ ++ dsum Δs) in Hx. apply elem_of_app in Hx as [Hx|Hx].
    - assert (Hc0 : length (mnode c) ≤ k) by (apply (HD (c, ρ)); by left).
      destruct Hc as [[_ Hs]|[_ ->]].
      + pose proof (mstep_depth _ _ _ _ _ x Hs Hx). simpl in *. lia.
      + apply list_elem_of_singleton in Hx. subst x. simpl. lia.
    - apply IH; [|done]. intros y Hy. apply HD. by right.
  Qed.

  Lemma run_depth I Sx (D : dist C) r : is_run (SchedSts0 := mdlts I Sx) Stay D r →
    (∀ x, x ∈ D → mnode x.1 = []) → ∀ i x, x ∈ r i → length (mnode x.1) ≤ i.
  Proof.
    intros [E Hr] HD i. induction i as [|i IH].
    - intros x Hx. rewrite E in Hx. rewrite (HD x Hx). simpl. lia.
    - destruct (Hr i) as [(σ & _ & Δs & HF & ->)|[_ ->]].
      + exact (comps_depth _ _ _ _ _ _ HF IH).
      + intros x Hx. pose proof (IH x Hx). lia.
  Qed.

  Lemma agree_depth (I J : node → Off → Prop) (SI SJ : node → bool) (D : dist C) N :
    (∀ n o, length n < N → (I n o ↔ J n o)) → (∀ n, length n < N → SI n = SJ n) →
    (∀ x, x ∈ D → length (mnode x.1) < N) → agree_on (mdlts I SI) (mdlts J SJ) D.
  Proof.
    intros HIJ HS HD c ρ Hin. pose proof (HD (c, ρ) Hin) as Hl. simpl in Hl. split.
    - simpl. rewrite (HS _ Hl). done.
    - intros _ σ Δ. simpl. split; intros Hs.
      + destruct (mstep_cell _ _ _ _ _ Hs) as [[Hall _]|(o & Ho & HJ & _)]; [apply Hall|].
        apply HJ. apply HIJ; done.
      + destruct (mstep_cell _ _ _ _ _ Hs) as [[Hall _]|(o & Ho & HJ & _)]; [apply Hall|].
        apply HJ. apply HIJ; done.
  Qed.

  Theorem menu_limit (DC : dep_choice) (J : node → Off → Prop) (Sj : node → bool) (Dp : dist C)
      (good : dist C → Prop) :
    (∀ D, ∃ l : list (dist C), ∀ D', rstep (mdlts J Sj) D D' → ∃ D'', D'' ∈ l ∧ succ_eqv (mdlts J Sj) D' D'') →
    (∀ D1 D2, succ_eqv (mdlts J Sj) D1 D2 → good D1 → good D2) →
    (∀ x, x ∈ Dp → mnode x.1 = []) →
    (∀ N, ∃ JN SN r', is_run (SchedSts0 := mdlts JN SN) Stay Dp r'
        ∧ (∀ n o, length n < N → (JN n o ↔ J n o)) ∧ (∀ n, length n < N → SN n = Sj n)
        ∧ ∀ i, i ≤ N → good (r' i)) →
    ∃ r', is_run (SchedSts0 := mdlts J Sj) Stay Dp r' ∧ ∀ i, good (r' i).
  Proof.
    intros Hfin Hgood Hp0 Hfam. apply (konig_upto (mdlts J Sj) good Hgood Hfin DC Dp). intros N.
    destruct (Hfam N) as (JN & SN & r' & Hr' & HJ & HS & Hg).
    exists r'. split; [exact (proj1 Hr')|]. split; [|exact Hg].
    intros i Hi.
    assert (Hag : agree_on (mdlts JN SN) (mdlts J Sj) (r' i)).
    { apply (agree_depth _ _ _ _ _ N HJ HS).
      intros x Hx. pose proof (run_depth _ _ _ _ Hr' Hp0 i x Hx). lia. }
    destruct (proj2 Hr' i) as [(σ & Hs)|[Hst E]].
    - left. exists σ. exact (agree_dstep _ _ Stay _ σ _ Hag Hs).
    - right. split; [exact (agree_dstable _ _ _ Hag Hst)|exact E].
  Qed.

  Theorem co_limit (DC : dep_choice) (Dp Dq : dist C) S π U R :
    co_trace S Dq π U R → (∀ x, x ∈ Dq → mnode x.1 = []) → (∀ x, x ∈ Dp → mnode x.1 = []) →
    (∀ D, ∃ l : list (dist C), ∀ D', rstep (mdlts (co_menu U R) (co_success S (co_menu U R) U)) D D' →
       ∃ D'', D'' ∈ l ∧ succ_eqv (mdlts (co_menu U R) (co_success S (co_menu U R) U)) D' D'') →
    (∀ N, ∃ SN πN UN RN I π' R', co_trace SN Dq πN UN RN ∧ (∀ n o, UN n o → Ok o)
        ∧ co_run I (co_success SN (co_menu UN RN) UN) Dp π' R' ∧ co_below SN UN RN πN I π' R'
        ∧ (∀ n o, length n < N → (co_menu UN RN n o ↔ co_menu U R n o))
        ∧ (∀ n, length n ≤ N → co_success SN (co_menu UN RN) UN n = co_success S (co_menu U R) U n)
        ∧ ∀ m, ∃ m', dmass_of (λ n, SN n = true) (πN m) ≤ₚ dmass_of (λ n, S n = true) (π m')) →
    ∃ I π' R', co_run I (co_success S (co_menu U R) U) Dp π' R' ∧ co_below S U R π I π' R'.
  Proof.
    intros (r & w & Hw & -> & -> & ->) Hq Hp0 Hfin Hfam.
    assert (Hr : run_word (cells S r w) S (r 0) r w) by (split; [done|apply Hw]).
    assert (Hr0 : ∀ x, x ∈ r 0 → mnode x.1 = []) by (rewrite (proj1 Hw); exact Hq).
    apply (co_fwd Dp S r w Hr Hr0 DC).
    set (J := co_menu (cells S r w) (refused (cells S r w) S r w)).
    set (Sj := co_success S J (cells S r w)).
    assert (Hgood : ∀ D1 D2, succ_eqv (mdlts J Sj) D1 D2 →
      (∀ v, v <ₚ dmass_of (λ c, Sj (mnode c) = true) D1 → ∃ m, v ≤ₚ succ_mass (SchedSts0 := mdlts J Sj) r m) →
      (∀ v, v <ₚ dmass_of (λ c, Sj (mnode c) = true) D2 → ∃ m, v ≤ₚ succ_mass (SchedSts0 := mdlts J Sj) r m)).
    { intros D1 D2 HE Hg v Hv. apply Hg.
      rewrite (succ_eqv_mass (mdlts J Sj) (λ c, Sj (mnode c) = true) D1 D2 (λ c Hc, Hc) HE). exact Hv. }
    destruct (menu_limit DC J Sj Dp
      (λ D, ∀ v, v <ₚ dmass_of (λ c, Sj (mnode c) = true) D →
         ∃ m, v ≤ₚ succ_mass (SchedSts0 := mdlts J Sj) r m) Hfin Hgood Hp0) as (r' & Hr' & Hg).
    - intros N.
      destruct (Hfam N) as (SN & πN & UN & RN & I & π' & R' & (rN & wN & HwN & -> & -> & ->) & HokN
        & Hrun & Hbel & HJ & HS & Hm).
      assert (HrN : run_word (cells SN rN wN) SN (rN 0) rN wN) by (split; [done|apply HwN]).
      assert (HrN0 : ∀ x, x ∈ rN 0 → mnode x.1 = []) by (rewrite (proj1 HwN); exact Hq).
      destruct (co_bwd Dp SN rN wN HrN HrN0 HokN (ex_intro _ I (ex_intro _ π' (ex_intro _ R' (conj Hrun Hbel)))))
        as (r1 & Hr1 & Hle1).
      exists (Jstar Ok (cells SN rN wN) SN rN wN), (Sstar Ok (cells SN rN wN) SN rN wN), r1.
      split; [exact Hr1|]. split; [exact HJ|]. split; [intros n Hn; apply HS; lia|].
      intros i Hi v Hv.
      assert (Hc : ∀ c ρ, (c, ρ) ∈ r1 i →
        Sj (mnode c) = true ↔ psuccess (SchedSts := mdlts (Jstar Ok (cells SN rN wN) SN rN wN)
                                                     (Sstar Ok (cells SN rN wN) SN rN wN)) c).
      { intros c ρ Hin. simpl. pose proof (run_depth _ _ _ _ Hr1 Hp0 i (c, ρ) Hin) as Hl. simpl in Hl.
        unfold Sj, J. rewrite <- (HS (mnode c)); [done|lia]. }
      rewrite (dmass_of_congr _ _ (r1 i) Hc) in Hv.
      destruct (Hle1 i v Hv) as (m & Hvm). destruct (Hm m) as (m' & Hm').
      exists m'. rewrite (co_q_mass S r w Hr Hr0).
      rewrite (co_q_mass SN rN wN HrN HrN0) in Hvm. etrans; [exact Hvm|exact Hm'].
    - exists r'. split; [exact Hr'|]. intros n v Hv. exact (Hg n v Hv).
  Qed.
End CoTrace.
(* end hide *)
