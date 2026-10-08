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

(** * lqCCS: the almost-sure must is a must on supports

    lqCCS has no recursion: every step consumes a prefix, so every run is
    finite.  The almost-sure must then only asks that, at the end of every
    run, every component of non-zero weight has succeeded.  Which branches
    of a measurement are taken with non-zero probability is all that
    matters, and the admissibility of schedulers plays no role: a component
    that fails can be followed by a scheduler that ignores the others.

    Main result ([must_as_iff_must_supp]): [ρ • (P, Q)] passes the
    almost-sure must iff [must_supp (P, Q) ρ], the classical must of the
    *branch* steps [bstep], where a measurement is a non-deterministic choice
    of an outcome, weighted by [M_k(ρ)], and branches of zero weight are
    ignored. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets.
From TestingTheory Require Import Lifted Paths States pMust_almost_sure lqCCS_Quantum.
From TestingTheory Require Import lqCCS_Syntax lqCCS_Program lqCCS_Composition.

(** ** Sizes: every step makes a configuration smaller *)

Fixpoint psize (P : proc) : nat :=
  match P with
  | PSend _ _ _ => 1
  | PIte _ P Q | PPar P Q => psize P + psize Q
  | PRes P _ => psize P
  | PG g => gsize g
  end
with gsize (g : guard) : nat :=
  match g with
  | GNil _ | GSucc => 0
  | GPre _ P => S (psize P)
  | GSum g1 g2 => gsize g1 + gsize g2
  end.

Definition csize (C : conf) : nat := psize C.1 + psize C.2.

Lemma psize_gsize_subst x v :
  (∀ P, psize (subst P x v) = psize P) ∧ (∀ g, gsize (gsubst g x v) = gsize g).
Proof.
  apply proc_guard_ind; simpl; intros; try lia. case_decide; simpl; lia.
Qed.

Lemma psize_subst P x v : psize (subst P x v) = psize P.
Proof. apply psize_gsize_subst. Qed.

Lemma gstep_size g l P' : gstep g l P' → psize P' < gsize g.
Proof. induction 1; simpl; rewrite ?psize_subst; lia. Qed.

Lemma pstep_size P l P' : pstep P l P' → psize P' < psize P.
Proof.
  induction 1; simpl; try lia.
  by eapply gstep_size.
Qed.

Section Supports.
  Context `{QM : QuantumModel}.

  (** ** Branch steps

      One branch of a step of the composition: a measurement chooses one
      outcome [k], with weight [M_k(ρ)]. *)

  Inductive bstep (ρ : St) : conf → conf → St → Prop :=
  | bs_tauL P Q s P' :
      pstep P (LTau s) P' → bstep ρ (P, Q) (P', Q) ρ
  | bs_tauR P Q s Q' :
      pstep Q (LTau s) Q' → bstep ρ (P, Q) (P, Q') ρ
  | bs_opL P Q t E qs P' :
      pstep P (LAct t (AOp E qs)) P' → bstep ρ (P, Q) (P', Q) (sop_apply E qs ρ)
  | bs_opR P Q t E qs Q' :
      pstep Q (LAct t (AOp E qs)) Q' → bstep ρ (P, Q) (P, Q') (sop_apply E qs ρ)
  | bs_measL P Q t M qs x P' (k : Out (meas_of M qs)) :
      pstep P (LAct t (AMeas M qs x)) P' →
      bstep ρ (P, Q) (subst P' x (VNat (code _ k)), Q) (meas_branch M qs k ρ)
  | bs_measR P Q t M qs x Q' (k : Out (meas_of M qs)) :
      pstep Q (LAct t (AMeas M qs x)) Q' →
      bstep ρ (P, Q) (P, subst Q' x (VNat (code _ k))) (meas_branch M qs k ρ)
  | bs_comLR P Q t t' c v P' Q' :
      pstep P (LAct t (AOut c v)) P' → pstep Q (LAct t' (AIn c v)) Q' →
      bstep ρ (P, Q) (P', Q') ρ
  | bs_comRL P Q t t' c v P' Q' :
      pstep P (LAct t (AIn c v)) P' → pstep Q (LAct t' (AOut c v)) Q' →
      bstep ρ (P, Q) (P', Q') ρ.

  Lemma bstep_size ρ C C' ρ' : bstep ρ C C' ρ' → csize C' < csize C.
  Proof.
    unfold csize. destruct 1; simpl;
      repeat match goal with H : pstep _ _ _ |- _ => apply pstep_size in H end;
      rewrite ?psize_subst; lia.
  Qed.

  (** The components of a step are its branches, and conversely. *)
  Lemma cstep_branches ρ C s Δ C' ρ' :
    cstep ρ C s Δ → (C', ρ') ∈ Δ → bstep ρ C C' ρ'.
  Proof.
    destruct 1; intros Hin;
      unfold dpoint, meas_dist, dsum in Hin;
      rewrite ?list_elem_of_singleton in Hin; simplify_eq;
      try (econstructor; eassumption).
    - apply list_elem_of_In, in_concat in Hin as (l & Hl & Hin).
      apply in_map_iff in Hl as (k & <- & _).
      destruct Hin as [[= <- <-]|[]]. by econstructor.
    - apply list_elem_of_In, in_concat in Hin as (l & Hl & Hin).
      apply in_map_iff in Hl as (k & <- & _).
      destruct Hin as [[= <- <-]|[]]. by econstructor.
  Qed.

  Lemma branch_cstep ρ C C' ρ' :
    bstep ρ C C' ρ' → ∃ s Δ, cstep ρ C s Δ ∧ (C', ρ') ∈ Δ.
  Proof.
    destruct 1; do 2 eexists; (split; [econstructor; eassumption|]);
      unfold dpoint, meas_dist, dsum; try by apply list_elem_of_singleton.
    - apply list_elem_of_In, in_concat. eexists. split.
      + apply in_map_iff. exists k. split; [done|]. apply outs_all.
      + by left.
    - apply list_elem_of_In, in_concat. eexists. split.
      + apply in_map_iff. exists k. split; [done|]. apply outs_all.
      + by left.
  Qed.

  (** ** The must on supports *)

  Inductive must_supp : conf → St → Prop :=
  | ms_now C ρ : conf_good C → must_supp C ρ
  | ms_zero C ρ : tr ρ = W_zero → must_supp C ρ
  | ms_step C ρ :
      ¬ conf_good C →
      (∃ s Δ, cstep ρ C s Δ) →
      (∀ C' ρ', bstep ρ C C' ρ' → must_supp C' ρ') →
      must_supp C ρ.

  (** ** Mass *)

  Lemma dmass_app (Δ Θ : dist conf) : dmass (Δ ++ Θ) = W_add (dmass Δ) (dmass Θ).
  Proof.
    induction Δ as [|[c w] Δ IH]; simpl; [by rewrite W_add_zero|].
    unfold dmass in *. simpl in *. rewrite IH. apply W_add_assoc.
  Qed.

  Lemma dmass_concat (Δs : list (dist conf)) :
    dmass (concat Δs) = fold_right W_add W_zero (map dmass Δs).
  Proof.
    induction Δs as [|Δ Δs IH]; cbn [concat map fold_right]; [done|].
    by rewrite dmass_app, IH.
  Qed.

  Lemma meas_dist_mass {C} M qs ρ (g : nat → C) : dmass (meas_dist M qs ρ g) = tr ρ.
  Proof.
    rewrite <- (meas_tr M qs ρ), br_sum.
    fold (sum (map (λ k, one ⋅ kraus (meas_of M qs) k) (outs (meas_of M qs)))).
    rewrite app_ssum, tr_ssum, !map_map. unfold meas_dist, dsum, dpoint.
    induction (outs (meas_of M qs)) as [|k l IH]; simpl; [done|].
    rewrite comp_1l. unfold dmass in *. simpl in *. rewrite IH. done.
  Qed.

  Lemma cstep_mass ρ C s Δ : cstep ρ C s Δ → dmass Δ = tr ρ.
  Proof.
    destruct 1; try apply meas_dist_mass;
      unfold dmass, dpoint; simpl; rewrite ?W_add_zero_r; try done;
      apply sop_tr.
  Qed.

  (** ** Termination

      A step moves at least one non-successful component, and replaces each
      moved component by smaller ones.  The histogram of the sizes of the
      non-successful components, read from the largest size down, decreases
      lexicographically. *)

  Definition count_size (i : nat) (Δ : dist conf) : nat :=
    length (filter (λ cρ : conf * St, ¬ conf_good cρ.1 ∧ csize cρ.1 = i) Δ).

  Lemma count_size_cons i x Δ :
    count_size i (x :: Δ)
    = (if decide (¬ conf_good x.1 ∧ csize x.1 = i) then 1 else 0) + count_size i Δ.
  Proof.
    unfold count_size. rewrite filter_cons.
    repeat case_decide; simpl; first [lia | tauto].
  Qed.

  Lemma count_size_nil i : count_size i [] = 0.
  Proof. done. Qed.

  (** Close an arithmetic goal on counts, splitting the [decide]s (two of
      them may differ only by [weight] vs [St], which [lia] cannot see). *)
  Ltac count_solve :=
    rewrite ?count_size_nil; repeat case_decide; simpl in *; first [lia | tauto].

  Lemma count_size_app i Δ Θ : count_size i (Δ ++ Θ) = count_size i Δ + count_size i Θ.
  Proof. unfold count_size. by rewrite filter_app, length_app. Qed.

  Lemma count_size_small i Δ :
    (∀ x, x ∈ Δ → csize x.1 < i) → count_size i Δ = 0.
  Proof.
    induction Δ as [|x Δ IH]; intros Hsm; [done|]. rewrite count_size_cons.
    case_decide as Hd.
    - exfalso. destruct Hd as [_ Hd]. specialize (Hsm x ltac:(set_solver)). lia.
    - apply IH. intros y Hy. apply Hsm. set_solver.
  Qed.

  (** [x] is moved by [σ]. *)
  Definition moved (σ : Sched) (x : conf * St) : Prop :=
    ¬ conf_good x.1 ∧ ∃ Δ, cstep x.2 x.1 σ Δ.

  Lemma comp_step_cases σ x Δx :
    comp_step x.2 x.1 σ Δx →
    (moved σ x ∧ cstep x.2 x.1 σ Δx) ∨ (¬ moved σ x ∧ Δx = [x]).
  Proof.
    destruct x as [c ρ]. intros [[Hg Hs]|[Hst ->]].
    - left. split; [|done]. split; [done|]. by eexists.
    - right. split; [|done]. intros [Hg [Δ Hs]].
      destruct Hst as [Hst|Hst]; [done|]. by eapply Hst.
  Qed.

  Lemma moved_targets_small σ x Δx :
    cstep x.2 x.1 σ Δx → ∀ y, y ∈ Δx → csize y.1 < csize x.1.
  Proof.
    intros Hs [C' ρ'] Hy. eapply bstep_size, cstep_branches; [exact Hs|exact Hy].
  Qed.

  (** Sizes above the largest moved one are untouched; at that size, the
      count goes down. *)
  Lemma count_above σ Δ Δs m :
    Forall2 (λ cρ Δ, comp_step cρ.2 cρ.1 σ Δ) Δ Δs →
    (∀ x, x ∈ Δ → moved σ x → csize x.1 ≤ m) →
    ∀ i, m < i → count_size i (concat Δs) = count_size i Δ.
  Proof.
    intros HF Hmax i Hi. revert Hmax.
    induction HF as [|x Δx Δ Δs Hx HF IH]; intros Hmax; [done|].
    cbn [concat]. rewrite count_size_app, count_size_cons.
    rewrite IH by (intros y Hy; apply Hmax; set_solver).
    destruct (comp_step_cases σ x Δx Hx) as [[Hm Hs]|[_ ->]].
    - rewrite count_size_small.
      + case_decide as Hd; [|done]. destruct Hd as [_ Hd].
        assert (csize x.1 ≤ m) by (apply Hmax; [set_solver|done]). lia.
      + intros y Hy. assert (csize y.1 < csize x.1) by (by apply (moved_targets_small σ x Δx Hs y)).
        assert (csize x.1 ≤ m) by (apply Hmax; [set_solver|done]). lia.
    - rewrite count_size_cons. count_solve.
  Qed.

  Lemma count_at σ Δ Δs m :
    Forall2 (λ cρ Δ, comp_step cρ.2 cρ.1 σ Δ) Δ Δs →
    (∀ x, x ∈ Δ → moved σ x → csize x.1 ≤ m) →
    (∃ x, x ∈ Δ ∧ moved σ x ∧ csize x.1 = m) →
    count_size m (concat Δs) < count_size m Δ.
  Proof.
    intros HF Hmax. revert Hmax. induction HF as [|x Δx Δ Δs Hx HF IH]; intros Hmax.
    { intros (y & Hy & _). set_solver. }
    intros (y & Hy & Hmy & Hsy).
    cbn [concat]. rewrite count_size_app, count_size_cons.
    assert (Hle : count_size m (concat Δs) ≤ count_size m Δ).
    { clear IH Hy. assert (Hmax' : ∀ w, w ∈ Δ → moved σ w → csize w.1 ≤ m)
        by (intros w Hw; apply Hmax; set_solver).
      clear Hmax. revert Hmax'.
      induction HF as [|z Δz Δ' Δs' Hz HF' IH']; intros Hmax; [done|].
      cbn [concat]. rewrite count_size_app, count_size_cons.
      pose proof (IH' ltac:(intros w Hw; apply Hmax; set_solver)) as IHle.
      destruct (comp_step_cases σ z Δz Hz) as [[Hm Hs]|[_ ->]].
      - rewrite count_size_small; [count_solve|]. intros w Hw.
        assert (csize w.1 < csize z.1) by (by apply (moved_targets_small σ z Δz Hs w)).
        assert (csize z.1 ≤ m) by (apply Hmax; [set_solver|done]). lia.
      - rewrite count_size_cons. count_solve. }
    destruct (comp_step_cases σ x Δx Hx) as [[Hm Hs]|[Hnm ->]].
    - assert (Hz0 : count_size m Δx = 0).
      { apply count_size_small. intros w Hw.
        assert (csize w.1 < csize x.1) by (by apply (moved_targets_small σ x Δx Hs w)).
        assert (csize x.1 ≤ m) by (apply Hmax; [set_solver|done]). lia. }
      rewrite Hz0. apply elem_of_cons in Hy as [->|Hy].
      + case_decide as Hd; [count_solve|]. exfalso. apply Hd. split; [apply Hmy|done].
      + specialize (IH ltac:(intros w Hw; apply Hmax; set_solver)
                       ltac:(by exists y)). count_solve.
    - rewrite count_size_cons. apply elem_of_cons in Hy as [->|Hy]; [by destruct Hnm|].
      specialize (IH ltac:(intros w Hw; apply Hmax; set_solver)
                     ltac:(by exists y)). count_solve.
  Qed.

  Lemma moved_max_or_none σ Δ Δs :
    Forall2 (λ cρ Δ, comp_step cρ.2 cρ.1 σ Δ) Δ Δs →
    (∀ x, x ∈ Δ → ¬ moved σ x)
    ∨ ∃ m, (∃ x, x ∈ Δ ∧ moved σ x ∧ csize x.1 = m)
           ∧ (∀ x, x ∈ Δ → moved σ x → csize x.1 ≤ m).
  Proof.
    induction 1 as [|x Δx Δ Δs Hx HF IH]; [left; set_solver|].
    destruct (comp_step_cases σ x Δx Hx) as [[Hm _]|[Hnm _]];
      destruct IH as [Hnone|(m & (y & Hy & Hmy & <-) & Hmax)].
    - right. exists (csize x.1). split; [exists x; set_solver|].
      intros z Hz Hmz. apply elem_of_cons in Hz as [->|Hz]; [done|].
      by destruct (Hnone z Hz).
    - right. destruct (decide (csize y.1 ≤ csize x.1)).
      + exists (csize x.1). split; [exists x; set_solver|].
        intros z Hz Hmz. apply elem_of_cons in Hz as [->|Hz]; [done|].
        assert (csize z.1 ≤ csize y.1) by (by apply Hmax). simpl in *. lia.
      + exists (csize y.1). split; [exists y; set_solver|].
        intros z Hz Hmz. apply elem_of_cons in Hz as [->|Hz]; [simpl in *; lia|].
        by apply Hmax.
    - left. intros z Hz. apply elem_of_cons in Hz as [->|Hz]; [done|]. by apply Hnone.
    - right. exists (csize y.1). split; [exists y; set_solver|].
      intros z Hz Hmz. apply elem_of_cons in Hz as [->|Hz]; [done|]. by apply Hmax.
  Qed.

  (** Histogram of the sizes [N, N-1, …, 0]. *)
  Fixpoint hist (N : nat) (Δ : dist conf) : list nat :=
    match N with
    | 0 => [count_size 0 Δ]
    | S N' => count_size N Δ :: hist N' Δ
    end.

  Lemma hist_length N Δ : length (hist N Δ) = S N.
  Proof. induction N; simpl; auto. Qed.

  Fixpoint lex_lt (l1 l2 : list nat) : Prop :=
    match l1, l2 with
    | a :: l1, b :: l2 => a < b ∨ (a = b ∧ lex_lt l1 l2)
    | _, _ => False
    end.

  Lemma lex_lt_wf n :
    ∀ l, length l = n → Acc (λ x y, length x = n ∧ lex_lt x y) l.
  Proof.
    induction n as [|n IH]; intros l Hl.
    - destruct l; [|done]. constructor. by intros [] [_ ?].
    - destruct l as [|a l]; [done|]. simpl in Hl. injection Hl as Hl.
      assert (Hacc : Acc (λ x y, length x = n ∧ lex_lt x y) l) by (apply IH; done).
      revert l Hl Hacc. induction a as [a IHa] using lt_wf_ind. intros l Hl Hacc.
      revert Hl. induction Hacc as [l _ IHl]. intros Hl.
      constructor. intros [|b y] [Hy Hlt]; [done|]. simpl in Hy, Hlt.
      injection Hy as Hy. destruct Hlt as [Hlt|[-> Hlt]].
      + apply IHa; [done|done|]. by apply IH.
      + apply IHl; [|done]. by split.
  Qed.

  Lemma hist_lex N Δ Δ' m :
    m ≤ N →
    (∀ i, m < i → count_size i Δ' = count_size i Δ) →
    count_size m Δ' < count_size m Δ →
    lex_lt (hist N Δ') (hist N Δ).
  Proof.
    intros Hm Habove Hat. induction N as [|N IH]; simpl.
    - assert (m = 0) as -> by lia. by left.
    - destruct (decide (m = S N)) as [->|Hne]; [by left|].
      right. split; [apply Habove; lia|]. apply IH. lia.
  Qed.

  Lemma Forall2_elem_r {A B} (R : A → B → Prop) l1 l2 y :
    Forall2 R l1 l2 → y ∈ l2 → ∃ x, x ∈ l1 ∧ R x y.
  Proof.
    induction 1 as [|x z l1 l2 Hxz HF IH]; intros Hy; [set_solver|].
    apply elem_of_cons in Hy as [->|Hy]; [exists x; set_solver|].
    destruct (IH Hy) as (w & ? & ?). exists w. set_solver.
  Qed.

  Definition bounded (N : nat) (Δ : dist conf) : Prop := ∀ x, x ∈ Δ → csize x.1 ≤ N.

  Lemma dstep_bounded N Δ σ Δ' : bounded N Δ → dstep Δ σ Δ' → bounded N Δ'.
  Proof.
    intros Hb [_ (Δs & HF & ->)] y Hy.
    apply list_elem_of_In, in_concat in Hy as (Δx & HΔx & Hy).
    apply list_elem_of_In in HΔx, Hy.
    destruct (Forall2_elem_r _ _ _ _ HF HΔx) as (x & Hx & Hxs).
    destruct (comp_step_cases σ x Δx Hxs) as [[_ Hs]|[_ ->]].
    - assert (csize y.1 < csize x.1) by (by apply (moved_targets_small σ x Δx Hs y)). specialize (Hb x Hx). lia.
    - apply list_elem_of_singleton in Hy as ->. by apply Hb.
  Qed.

  Lemma dstep_hist N Δ σ Δ' :
    bounded N Δ → dstep Δ σ Δ' → lex_lt (hist N Δ') (hist N Δ).
  Proof.
    intros Hb [(c & ρ & Δc & Hin & Hg & Hs) (Δs & HF & ->)].
    destruct (moved_max_or_none σ Δ Δs HF) as [Hnone|(m & Hw & Hmax)].
    { exfalso. apply (Hnone (c, ρ) Hin). split; [done|]. by eexists. }
    apply (hist_lex N Δ (concat Δs) m).
    - destruct Hw as (x & Hx & _ & <-). by apply Hb.
    - by apply (count_above σ Δ Δs m).
    - by apply (count_at σ Δ Δs m).
  Qed.

  (** Every run reaches a stable distribution. *)
  Lemma dstep_sn N Δ :
    bounded N Δ → Acc (λ Δ' Δ, ∃ σ, dstep Δ σ Δ') Δ.
  Proof.
    intros Hb.
    pose proof (lex_lt_wf (S N) (hist N Δ) (hist_length N Δ)) as Hacc.
    remember (hist N Δ) as h eqn:Eh. revert Δ Hb Eh.
    induction Hacc as [h _ IH]. intros Δ Hb ->.
    constructor. intros Δ' (σ & Hst).
    eapply IH; [|by eapply dstep_bounded|done].
    split; [apply hist_length|]. by eapply dstep_hist.
  Qed.

  Lemma run_stable N Δ r :
    bounded N Δ → is_run Δ r → ∃ n, dstable (r n).
  Proof.
    intros Hb Hr. pose proof (dstep_sn N Δ Hb) as Hacc.
    revert r Hb Hr. induction Hacc as [Δ _ IH]. intros r Hb [Hr0 Hr].
    destruct (Hr 0) as [(σ & Hst)|[Hst _]]; [|by exists 0].
    rewrite Hr0 in Hst.
    destruct (IH (r 1) ltac:(by exists σ) (λ n, r (S n))) as [n Hn].
    - by eapply dstep_bounded.
    - split; [done|]. intros n. apply (Hr (S n)).
    - by exists (S n).
  Qed.

  (** ** From the must on supports to the almost-sure must *)

  Lemma dmass_cons x (Δ : dist conf) : dmass (x :: Δ) = W_add (tr x.2) (dmass Δ).
  Proof. done. Qed.

  Lemma dmass_of_cons x (Δ : dist conf) :
    dmass_of conf_good (x :: Δ)
    = if decide (conf_good x.1) then W_add (tr x.2) (dmass_of conf_good Δ)
      else dmass_of conf_good Δ.
  Proof. done. Qed.

  Lemma zero_branch ρ C C' ρ' : tr ρ = W_zero → bstep ρ C C' ρ' → tr ρ' = W_zero.
  Proof.
    intros Hz Hb. apply tr_zero_inv in Hz as ->.
    destruct Hb; try apply tr_szero;
      unfold sop_apply, meas_branch; rewrite app_szero; apply tr_szero.
  Qed.

  (** Every component satisfies the must on supports. *)
  Definition all_supp (Δ : dist conf) : Prop := ∀ C ρ, (C, ρ) ∈ Δ → must_supp C ρ.

  Lemma concat_elem {A} (y : A) Δs : y ∈ concat Δs → ∃ Δx, Δx ∈ Δs ∧ y ∈ Δx.
  Proof.
    intros Hy. apply list_elem_of_In, in_concat in Hy as (Δx & ? & ?).
    exists Δx. split; by apply list_elem_of_In.
  Qed.

  Lemma all_supp_step Δ σ Δ' : all_supp Δ → dstep Δ σ Δ' → all_supp Δ'.
  Proof.
    intros HA [_ (Δs & HF & ->)] C' ρ' Hy. unfold dsum in Hy.
    destruct (concat_elem _ _ Hy) as (Δx & HΔx & Hy').
    destruct (Forall2_elem_r _ _ _ _ HF HΔx) as ([C ρ] & Hx & Hxs).
    destruct (comp_step_cases σ (C, ρ) Δx Hxs) as [[[Hg _] Hs]|[_ ->]].
    - simpl in *. pose proof (cstep_branches ρ C σ Δx C' ρ' Hs Hy') as Hb.
      specialize (HA C ρ Hx). inversion HA; subst.
      + done.
      + apply ms_zero. by eapply zero_branch.
      + by eauto.
    - apply list_elem_of_singleton in Hy' as [= -> ->]. by apply HA.
  Qed.

  Lemma dstep_mass Δ σ Δ' : dstep Δ σ Δ' → dmass Δ' = dmass Δ.
  Proof.
    intros [_ (Δs & HF & ->)]. induction HF as [|x Δx Δ Δs Hx HF IH]; [done|].
    unfold dsum in *. cbn [concat]. rewrite dmass_app, IH, dmass_cons. f_equal.
    destruct (comp_step_cases σ x Δx Hx) as [[_ Hs]|[_ ->]].
    - by eapply cstep_mass.
    - rewrite dmass_cons. apply W_add_zero_r.
  Qed.

  Lemma run_mass Δ r n : is_run Δ r → dmass (r n) = dmass (r 0).
  Proof.
    intros [_ Hr]. induction n as [|n IH]; [done|].
    destruct (Hr n) as [(σ & Hst)|[_ ->]]; [|done].
    by rewrite (dstep_mass _ _ _ Hst).
  Qed.

  Lemma run_all_supp Δ r n : is_run Δ r → all_supp Δ → all_supp (r n).
  Proof.
    intros [Hr0 Hr] HA. induction n as [|n IH]; [by rewrite Hr0|].
    destruct (Hr n) as [(σ & Hst)|[_ ->]]; [|done].
    by eapply all_supp_step.
  Qed.

  (** In a stable distribution of components passing the must on supports,
      all the mass has succeeded. *)
  Lemma stable_succ Δ : all_supp Δ → dstable Δ → dmass_of conf_good Δ = dmass Δ.
  Proof.
    intros HA Hst. induction Δ as [|[C ρ] Δ IH]; [done|].
    assert (IH' : dmass_of conf_good Δ = dmass Δ).
    { apply IH.
      - intros C' ρ' Hin. apply HA. set_solver.
      - intros σ (c & ρ0 & Δ0 & Hin & Hg & Hs). apply (Hst σ).
        exists c, ρ0, Δ0. split; [set_solver|done]. }
    rewrite dmass_of_cons, dmass_cons, IH'. case_decide as Hg; [done|].
    specialize (HA C ρ ltac:(set_solver)). inversion HA; subst.
    - done.
    - simpl. by rewrite H3, W_add_zero.
    - exfalso. destruct H4 as (s & Δc & Hs). apply (Hst s).
      exists C, ρ, Δc. split; [set_solver|]. by split.
  Qed.

  Theorem must_supp_must_as C ρ : must_supp C ρ → pmust_as (dpoint C ρ).
  Proof.
    intros Hm r Hr w Hw.
    assert (Hb : bounded (csize C) (dpoint C ρ)).
    { intros x Hx. apply list_elem_of_singleton in Hx as ->. done. }
    assert (HA : all_supp (dpoint C ρ)).
    { intros C' ρ' Hx. by apply list_elem_of_singleton in Hx as [= -> ->]. }
    destruct (run_stable _ _ _ Hb Hr) as [n Hn].
    exists n. unfold succ_mass.
    change (dmass_of psuccess (r n)) with (dmass_of conf_good (r n)).
    rewrite (stable_succ (r n)), (run_mass _ r n Hr); [|by eapply run_all_supp|done].
    apply Hw.
  Qed.
End Supports.

(** ** From the almost-sure must to the must on supports

    By contraposition: a component that fails the must on supports is
    followed, with its own schedulers, until it is stuck; the run is then
    completed until it is stable.  This uses the excluded middle (to extract
    a failing path from [¬ must_supp]) and two properties of the
    probabilities, true in [[0,1]]: strict positivity and density. *)

Section Converse.
  Context `{QM : QuantumModel}.
  Context (XM : ∀ P : Prop, P ∨ ¬ P).
  Context (W_strict : ∀ a b, W_le (W_add a b) a → b = W_zero).
  Context (W_dense : ∀ a b : W, a <ₚ b → ∃ c, a <ₚ c ∧ c <ₚ b).

  Lemma W_add_mono_r a b c : W_le b c → W_le (W_add a b) (W_add a c).
  Proof. intros Hbc. rewrite !(W_add_comm a). by apply W_add_mono. Qed.

  Lemma W_le_add_l a b : W_le b (W_add a b).
  Proof. rewrite <- (W_add_zero b) at 1. apply W_add_mono, W_zero_le. Qed.

  (** *** Building steps *)

  Lemma Forall2_elem_l {A B} (R : A → B → Prop) l1 l2 x :
    Forall2 R l1 l2 → x ∈ l1 → ∃ y, y ∈ l2 ∧ R x y.
  Proof.
    induction 1 as [|a b l1 l2 Hab HF IH]; intros Hx; [set_solver|].
    apply elem_of_cons in Hx as [->|Hx]; [exists b; set_solver|].
    destruct (IH Hx) as (w & ? & ?). exists w. set_solver.
  Qed.

  Lemma elem_concat {A} (y : A) Δx Δs : Δx ∈ Δs → y ∈ Δx → y ∈ concat Δs.
  Proof.
    intros Hx Hy. apply list_elem_of_In, in_concat.
    exists Δx. split; by apply list_elem_of_In.
  Qed.

  Lemma comp_steps_with σ (x0 : conf * St) Δ0 (Δ : dist conf) :
    ¬ conf_good x0.1 → cstep x0.2 x0.1 σ Δ0 →
    ∃ Δs, Forall2 (λ cρ Δ, comp_step cρ.2 cρ.1 σ Δ) Δ Δs
          ∧ (x0 ∈ Δ → ∀ y, y ∈ Δ0 → y ∈ concat Δs).
  Proof.
    intros Hg Hs. induction Δ as [|x Δ IH].
    { exists []. split; [constructor|]. intros Hin. set_solver. }
    destruct IH as (Δs & HF & Hsub).
    destruct (decide (x = x0)) as [->|Hne].
    - exists (Δ0 :: Δs). split.
      + constructor; [|done]. left. by split.
      + intros _ y Hy. cbn [concat]. set_solver.
    - destruct (XM (¬ conf_good x.1 ∧ ∃ Δx, cstep x.2 x.1 σ Δx))
        as [[Hgx [Δx Hsx]]|Hno].
      + exists (Δx :: Δs). split.
        * constructor; [|done]. left. by split.
        * intros Hin y Hy. apply elem_of_cons in Hin as [->|Hin]; [done|].
          cbn [concat]. specialize (Hsub Hin y Hy). set_solver.
      + exists ([x] :: Δs). split.
        * constructor; [|done]. right. split; [|by destruct x].
          destruct (decide (conf_good x.1)) as [Hgx|Hgx]; [by left|right].
          intros Δ' Hs'. apply Hno. split; [done|]. by exists Δ'.
        * intros Hin y Hy. apply elem_of_cons in Hin as [->|Hin]; [done|].
          cbn [concat]. specialize (Hsub Hin y Hy). set_solver.
  Qed.

  Lemma dstep_with σ x0 Δ0 (Δ : dist conf) :
    x0 ∈ Δ → ¬ conf_good x0.1 → cstep x0.2 x0.1 σ Δ0 →
    ∃ Δ', dstep Δ σ Δ' ∧ ∀ y, y ∈ Δ0 → y ∈ Δ'.
  Proof.
    intros Hin Hg Hs. destruct (comp_steps_with σ x0 Δ0 Δ Hg Hs) as (Δs & HF & Hsub).
    exists (concat Δs). split; [|by apply Hsub].
    split; [|by exists Δs]. destruct x0 as [c ρ]. exists c, ρ, Δ0. done.
  Qed.

  Definition stuck (x : conf * St) : Prop := ∀ s Δ, ¬ cstep x.2 x.1 s Δ.

  Lemma stuck_stays x Δ σ Δ' : x ∈ Δ → stuck x → dstep Δ σ Δ' → x ∈ Δ'.
  Proof.
    intros Hin Hst [_ (Δs & HF & ->)].
    destruct (Forall2_elem_l _ _ _ _ HF Hin) as (Δx & HΔx & Hx).
    destruct (comp_step_cases σ x Δx Hx) as [[_ Hs]|[_ ->]].
    - by destruct (Hst σ Δx).
    - eapply elem_concat; [exact HΔx|]. set_solver.
  Qed.

  (** *** Chains of steps, and the runs they give *)

  Fixpoint is_chain (Δ : dist conf) (l : list (dist conf)) : Prop :=
    match l with
    | [] => True
    | Δ' :: l => (∃ σ, dstep Δ σ Δ') ∧ is_chain Δ' l
    end.

  Notation lastd Δ l := (List.last (Δ :: l) Δ).

  Lemma last_cons_cons {A} (a b : A) l d : List.last (a :: b :: l) d = List.last (b :: l) b.
  Proof.
    simpl. revert b. induction l as [|c l IH]; intros b; [done|].
    simpl. destruct l; [done|]. apply IH.
  Qed.

  Lemma nth_length_last {A} (x : A) l d : nth (length l) (x :: l) d = List.last (x :: l) x.
  Proof.
    revert x. induction l as [|y l IH]; intros x; [done|].
    rewrite last_cons_cons. apply IH.
  Qed.

  Lemma is_chain_app Δ l1 l2 :
    is_chain Δ l1 → is_chain (lastd Δ l1) l2 → is_chain Δ (l1 ++ l2).
  Proof.
    revert Δ. induction l1 as [|Δ1 l1 IH]; intros Δ Hc1 Hc2; [done|].
    destruct Hc1 as [Hst Hc1]. split; [done|]. apply IH; [done|].
    by rewrite last_cons_cons in Hc2.
  Qed.

  Lemma lastd_app (Δ : dist conf) (l1 l2 : list (dist conf)) :
    lastd Δ (l1 ++ l2) = lastd (lastd Δ l1) l2.
  Proof.
    revert Δ. induction l1 as [|Δ1 l1 IH]; intros Δ; [done|].
    rewrite <- app_comm_cons, !last_cons_cons. apply IH.
  Qed.

  Lemma chain_keeps Δ l x : is_chain Δ l → x ∈ Δ → stuck x → x ∈ lastd Δ l.
  Proof.
    revert Δ. induction l as [|Δ1 l IH]; intros Δ Hc Hin Hst; [done|].
    destruct Hc as [(σ & Hs) Hc]. rewrite last_cons_cons.
    apply IH; [done| |done]. by eapply stuck_stays.
  Qed.

  Definition chain_run (Δ : dist conf) (l : list (dist conf)) : nat → dist conf :=
    λ n, nth n (Δ :: l) (lastd Δ l).

  Lemma chain_is_run Δ l :
    is_chain Δ l → dstable (lastd Δ l) → is_run Δ (chain_run Δ l).
  Proof.
    intros Hc Hst. split; [done|]. unfold chain_run.
    revert Δ Hc Hst. induction l as [|Δ1 l IH]; intros Δ Hc Hst n.
    - right. destruct n; simpl; [done|]. destruct n; done.
    - destruct Hc as [(σ & Hs) Hc]. rewrite last_cons_cons in *.
      destruct n as [|n]; [left; by exists σ|]. simpl. apply IH; done.
  Qed.

  (** *** Phase 1: follow a failing component until it is stuck *)

  Lemma follow C ρ (Δ : dist conf) :
    (C, ρ) ∈ Δ → ¬ must_supp C ρ →
    ∃ l Cf ρf, is_chain Δ l ∧ (Cf, ρf) ∈ lastd Δ l ∧ ¬ conf_good Cf
               ∧ tr ρf ≠ W_zero ∧ stuck (Cf, ρf).
  Proof.
    remember (csize C) as n eqn:En. revert C ρ Δ En.
    induction n as [n IH] using lt_wf_ind. intros C ρ Δ -> Hin Hm.
    assert (Hg : ¬ conf_good C) by (intros Hg; apply Hm; by constructor).
    assert (Hz : tr ρ ≠ W_zero) by (intros Hz; apply Hm; by apply ms_zero).
    destruct (XM (∃ s Δc, cstep ρ C s Δc)) as [Hex|Hno].
    2:{ exists [], C, ρ. repeat split; try done. intros s Δc Hs. apply Hno. eauto. }
    destruct (XM (∃ C' ρ', bstep ρ C C' ρ' ∧ ¬ must_supp C' ρ'))
      as [(C' & ρ' & Hb & Hm')|Hall].
    2:{ exfalso. apply Hm. apply ms_step; [done|done|]. intros C' ρ' Hb.
        destruct (XM (must_supp C' ρ')) as [?|Hn]; [done|].
        exfalso. apply Hall. eauto. }
    destruct (branch_cstep ρ C C' ρ' Hb) as (s & Δc & Hs & HinC).
    destruct (dstep_with s (C, ρ) Δc Δ Hin Hg Hs) as (Δ' & Hst & Hsub).
    destruct (IH (csize C') (bstep_size _ _ _ _ Hb) C' ρ' Δ' eq_refl (Hsub _ HinC) Hm')
      as (l & Cf & ρf & Hc & Hf & Hfg & Hfz & Hfs).
    exists (Δ' :: l), Cf, ρf. rewrite last_cons_cons. repeat split; try done.
    by exists s.
  Qed.

  (** *** Phase 2: complete a run until it is stable *)

  Lemma complete_run N (Δ : dist conf) :
    bounded N Δ → ∃ l, is_chain Δ l ∧ dstable (lastd Δ l).
  Proof.
    intros Hb. pose proof (dstep_sn N Δ Hb) as Hacc. revert Hb.
    induction Hacc as [Δ _ IH]. intros Hb.
    destruct (XM (∃ σ, dmoves Δ σ)) as [(σ & c & ρ & Δc & Hin & Hg & Hs)|Hno].
    2:{ exists []. split; [done|]. intros σ Hσ. apply Hno. by exists σ. }
    destruct (dstep_with σ (c, ρ) Δc Δ Hin Hg Hs) as (Δ' & Hst & _).
    destruct (IH Δ' ltac:(by exists σ) ltac:(by eapply dstep_bounded)) as (l & Hc & Hl).
    exists (Δ' :: l). rewrite last_cons_cons. split; [|done]. split; [|done].
    by exists σ.
  Qed.

  (** *** Masses *)

  Lemma dmass_of_app (Δ Θ : dist conf) :
    dmass_of conf_good (Δ ++ Θ) = W_add (dmass_of conf_good Δ) (dmass_of conf_good Θ).
  Proof.
    induction Δ as [|x Δ IH]; [symmetry; apply W_add_zero|].
    rewrite <- app_comm_cons, !dmass_of_cons, IH.
    case_decide; [apply W_add_assoc|done].
  Qed.

  Lemma dmass_of_le (Δ : dist conf) : W_le (dmass_of conf_good Δ) (dmass Δ).
  Proof.
    induction Δ as [|x Δ IH]; [done|]. rewrite dmass_of_cons, dmass_cons.
    case_decide; [by apply W_add_mono_r|]. etrans; [exact IH|]. apply W_le_add_l.
  Qed.

  Lemma dmass_of_failing x (Δ : dist conf) :
    x ∈ Δ → ¬ conf_good x.1 →
    W_le (W_add (dmass_of conf_good Δ) (tr x.2)) (dmass Δ).
  Proof.
    induction Δ as [|y Δ IH]; intros Hin Hg; [set_solver|].
    rewrite dmass_of_cons, dmass_cons.
    apply elem_of_cons in Hin as [->|Hin].
    - case_decide; [done|]. rewrite W_add_comm. by apply W_add_mono_r, dmass_of_le.
    - specialize (IH Hin Hg). case_decide.
      + rewrite <- W_add_assoc. by apply W_add_mono_r.
      + etrans; [exact IH|]. apply W_le_add_l.
  Qed.

  Lemma dstep_succ_mono Δ σ Δ' :
    dstep Δ σ Δ' → W_le (dmass_of conf_good Δ) (dmass_of conf_good Δ').
  Proof.
    intros [_ (Δs & HF & ->)]. unfold dsum.
    induction HF as [|x Δx Δ Δs Hx HF IH]; [done|].
    cbn [concat]. rewrite dmass_of_app, dmass_of_cons.
    destruct (comp_step_cases σ x Δx Hx) as [[[Hg _] _]|[_ ->]].
    - case_decide; [done|]. etrans; [exact IH|]. apply W_le_add_l.
    - rewrite dmass_of_cons. case_decide.
      + change (dmass_of conf_good []) with W_zero. rewrite W_add_zero_r.
        by apply W_add_mono_r.
      + change (dmass_of conf_good []) with W_zero. by rewrite W_add_zero.
  Qed.

  Lemma chain_succ_le Δ l n :
    is_chain Δ l →
    W_le (dmass_of conf_good (chain_run Δ l n)) (dmass_of conf_good (lastd Δ l)).
  Proof.
    unfold chain_run. revert Δ n. induction l as [|Δ1 l IH]; intros Δ n Hc.
    - destruct n as [|[]]; done.
    - destruct Hc as [(σ & Hs) Hc]. rewrite last_cons_cons.
      destruct n as [|n].
      + etrans; [by eapply dstep_succ_mono|]. apply (IH Δ1 0 Hc).
      + simpl. apply (IH Δ1 n Hc).
  Qed.

  (** *** The converse *)

  Theorem must_as_must_supp C ρ : pmust_as (dpoint C ρ) → must_supp C ρ.
  Proof.
    intros Has. destruct (XM (must_supp C ρ)) as [?|Hm]; [done|exfalso].
    destruct (follow C ρ (dpoint C ρ) ltac:(set_solver) Hm)
      as (l1 & Cf & ρf & Hc1 & Hf & Hfg & Hfz & Hfs).
    assert (Hb : bounded (csize C) (lastd (dpoint C ρ) l1)).
    { assert (Hb0 : bounded (csize C) (dpoint C ρ)).
      { intros x Hx. apply list_elem_of_singleton in Hx as ->. done. }
      clear Hf. revert Hc1 Hb0. generalize (dpoint C ρ) as Δ.
      induction l1 as [|Δ1 l1 IH]; intros Δ Hc Hb0; [done|].
      destruct Hc as [(σ & Hs) Hc]. rewrite last_cons_cons.
      apply IH; [done|]. by eapply dstep_bounded. }
    destruct (complete_run _ _ Hb) as (l2 & Hc2 & Hst).
    set (l := l1 ++ l2).
    assert (Hc : is_chain (dpoint C ρ) l) by (by apply is_chain_app).
    assert (Hlast : lastd (dpoint C ρ) l = lastd (lastd (dpoint C ρ) l1) l2)
      by apply lastd_app.
    assert (Hfin : (Cf, ρf) ∈ lastd (dpoint C ρ) l)
      by (rewrite Hlast; by apply chain_keeps).
    assert (Hrun : is_run (dpoint C ρ) (chain_run (dpoint C ρ) l))
      by (apply chain_is_run; [done|by rewrite Hlast]).
    set (Δf := lastd (dpoint C ρ) l) in *.
    set (s := dmass_of conf_good Δf).
    set (m := dmass (dpoint C ρ)).
    assert (Hmf : dmass Δf = m).
    { (* the last distribution is reached by the run *)
      assert (E : chain_run (dpoint C ρ) l (length l) = Δf).
      { unfold chain_run. apply nth_length_last. }
      rewrite <- E. apply (run_mass _ _ _ Hrun). }
    assert (Hsm : s <ₚ m).
    { split.
      - rewrite <- Hmf. apply dmass_of_le.
      - intros Hms. apply Hfz. apply (W_strict s).
        etrans; [|exact Hms]. rewrite <- Hmf.
        apply (dmass_of_failing (Cf, ρf) Δf Hfin Hfg). }
    destruct (W_dense s m Hsm) as (w & [Hsw Hws] & Hwm).
    destruct (Has _ Hrun w Hwm) as [n Hn].
    apply Hws. etrans; [exact Hn|]. apply (chain_succ_le _ _ n Hc).
  Qed.

  (** ** The characterisation *)

  Theorem must_as_iff_must_supp C ρ : pmust_as (dpoint C ρ) ↔ must_supp C ρ.
  Proof. split; [apply must_as_must_supp|apply must_supp_must_as]. Qed.

  (** For lqCCS: [(P, ρ) must_as Q] iff the must on supports of [(P, Q)]
      in memory [ρ]. *)
  Corollary lq_must_as_iff P ρ Q : (P, ρ) must_as Q ↔ must_supp (P, Q) ρ.
  Proof. apply must_as_iff_must_supp. Qed.
End Converse.
