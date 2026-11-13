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
From Stdlib.Bool Require Import Bool.
From Stdlib.Logic Require Import Classical ClassicalDescription.
From Stdlib Require Import Lia.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Pull lqCCS.Testing.Head lqCCS.Testing.Modes lqCCS.Testing.Syn lqCCS.Testing.Assembly lqCCS.Testing.Final lqCCS.Testing.Trace lqCCS.Testing.Build.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Asm.
  Context `{QM : QuantumModel} (p q : proc * St).
  Context (O : node → list msg) (S : node → bool) (Ch : channel → Prop) (K : tag → okind).
  Context (r : nat → dist comp) (w : nat → item).
  Context (cl : node → list offer) (VL : list val) (f0 : nat).

  Notation U := (used_by O S r w).
  Notation Ok := (real_off p q Ch K).

  Hypothesis Hcoh : coherent p q O S Ch K r w.
  Hypothesis Hrun : run_word (M := lq_menu O) U S (dinit O q) r w.
  Hypothesis Hcl1 : ∀ n, NoDup (cl n).
  Hypothesis Hcl2 : ∀ n o, o ∈ cl n ↔ U n o.
  Hypothesis Hfuel : ∀ n, S n = false → length n < f0.
  Hypothesis Hun : ∀ n a, unlisted VL a → S (n ++ [a]) = true.

  Definition TG (x : tag * okind) : Prop := K x.1 = x.2 ∧ x.1 ∉ tags p.1 ∧ x.1 ∉ tags q.1.

  Definition T : proc := BT S O cl VL f0.

  Lemma cHS : ext_closed S.
  Proof. exact (proj1 Hcoh). Qed.

  Lemma cHOf n x y : S n = false → x ∈ O n → y ∈ O n → mtag x = mtag y → x = y.
  Proof.
    destruct Hcoh as (_ & _ & _ & _ & HOf & _). destruct x as [[k c] v], y as [[k' c'] v']. unfold mtag. simpl.
    intros Hs Hx Hy <-. by destruct (HOf n k c v c' v' Hs Hx Hy) as [-> ->].
  Qed.

  Lemma cHOm n a x : S (n ++ [a]) = false → x ∈ O n → x ∈ O (n ++ [a]).
  Proof. destruct Hcoh as (_ & _ & _ & _ & _ & HOm). apply HOm. Qed.

  Lemma U_cell n o : U n o → S n = false ∧ ∀ k c v, o ≠ OffOut k c v.
  Proof.
    unfold used_by, cells. intros (i & c & ρ & Δ & Hin & Hs & Hnf & Hne & Hst & _). simpl in Hst, Hs, Hnf.
    destruct (w i) as [s|k t]; [by destruct Hnf|].
    inversion Hst; subst; match goal with Hsg : single _ _ _ _ |- _ => destruct Hsg as [E1 E2] end;
      simpl in *; subst; split; done.
  Qed.

  Lemma cHclo n k c v : OffOut k c v ∉ cl n.
  Proof. intros Hin%Hcl2. destruct (U_cell _ _ Hin) as [_ Hn]. by apply (Hn k c v). Qed.

  Lemma Hrun0 : run_word (M := lq_menu O) U S (r 0) r w.
  Proof. destruct Hrun as [E Hr]. split; [done|exact Hr]. Qed.

  Lemma Hinit x : x ∈ r 0 → visited_ok (M := lq_menu O) U (mnode (MenuSts := lq_menu O) x.1).
  Proof.
    rewrite (proj1 Hrun). intros ->%list_elem_of_singleton m a m2 E. simpl in E. destruct m; discriminate E.
  Qed.

  Lemma q_clpath i x : x ∈ r i → clpath S cl x.1.1.
  Proof.
    intros Hx. pose proof (visited_run (M := lq_menu O) U S r w Hrun0 Hinit i x Hx) as Hv.
    intros m a m2 E. pose proof (Hv m a m2 E) as Hu. simpl in Hu.
    split; [exact (proj1 (U_cell _ _ Hu))|by apply Hcl2].
  Qed.

  Lemma T_inv m : (∀ X, X ∈ tnodes T m → inv S O cl VL f0 m X) ∧ length (tnodes T m) ≤ 1.
  Proof. exact (bt_inv S O cl VL f0 Hfuel Hun Hcl1 cHOf cHOm m). Qed.

  Lemma T_S n : clpath S cl n → S_T T n = S n.
  Proof. exact (bt_S S O cl VL f0 cHS Hfuel Hun Hcl1 cHOf cHOm cHclo n). Qed.

  Lemma T_menu n o : plain n → (∀ k c v, o ≠ OffOut k c v) → (menu T n o ↔ clpath S cl n ∧ S n = false ∧ o ∈ cl n).
  Proof. exact (bt_menu S O cl VL f0 Hfuel Hun Hcl1 cHOf cHOm cHclo n o). Qed.

  Lemma T_syn : syn TG (λ c, Ch c) (λ c, ¬ Ch c) T.
  Proof.
    destruct Hcoh as (_ & _ & Hreal & HOk & _).
    apply (bt_syn S O cl VL TG (λ c, Ch c) (λ c, ¬ Ch c)).
    - intros n o Hin. destruct (Hreal n o (proj1 (Hcl2 n o) Hin)) as (Hty & Hp & Hq & Hc).
      split; [|exact Hc]. split; [by symmetry|by split].
    - intros n k c v Hs Hin. destruct (HOk n k c v Hs Hin) as (Hk & Hp & Hq & Hc). split; [|done]. by split.
  Qed.

  Lemma T_observer : observer T.
  Proof.
    destruct T_syn as (Hob & Htg & Hoc & Hic). split; [split; [done|]|split; [|split]].
    - intros c Hc Hc'. exact (Hic c Hc' (Hoc c Hc)).
    - intros k x y Hx Hy. pose proof (proj1 (Htg _ Hx)) as E1. pose proof (proj1 (Htg _ Hy)) as E2.
      simpl in E1, E2. congruence.
    - intros n. exact (proj2 (T_inv n)).
    - intros n m k c v c' v' Y HY.
      exact (bt_gone S O cl VL f0 Hfuel Hun Hcl1 cHOf cHOm n m k c v c' v' Y HY).
  Qed.

  Lemma T_for : obs_for p q T.
  Proof.
    split; [exact T_observer|]. intros t Ht. unfold tags in Ht. apply list_elem_of_fmap in Ht as ([k x] & -> & Hin).
    exact (proj2 (proj1 (proj2 T_syn) _ Hin)).
  Qed.

  Lemma T_ok n o : menu T n o → Ok o.
  Proof.
    intros Hm. destruct T_syn as (Hob & Htg & Hoc & Hic).
    destruct (Htg _ (menu_kind T T_observer n o Hm)) as (Hk & Hp & Hq). simpl in Hk, Hp, Hq.
    split; [by symmetry|]. split; [done|]. split; [done|]. intros k c -> Hc1.
    destruct Hm as (T' & a & HT' & Ha & Hne). destruct a as [|k' c' v| | |]; try discriminate Ha.
    simpl in Ha. injection Ha as -> ->.
    destruct (co_succ T' (CoIn k c v)) as [|T'' l] eqn:E; [done|].
    assert (HT'' : T'' ∈ co_succ T' (CoIn k c v)) by (rewrite E; by left).
    pose proof (prog_step_in_chan T' k c v T'' (proj1 (tnodes_obs T (proj1 T_observer) n T' HT'))
                  (co_succ_sound _ _ _ HT'')) as Hc.
    exact (Hic c (proj2 (tnodes_chans T (proj1 T_observer) n T' HT') c Hc) Hc1).
  Qed.

  Lemma T_real : RealT p q O Ch K (menu T) (S_T T).
  Proof.
    split; [|exact T_ok]. exists T. split; [exact T_for|]. split; [|split; [done|split; [done|split]]].
    - intros n m Hpl Hs. destruct (classic (clpath S cl n)) as [Hc|Hc].
      + rewrite (T_S n Hc) in Hs. symmetry.
        exact (bt_O S O cl VL f0 Hfuel Hun Hcl1 cHOf cHOm cHclo n m Hc Hs).
      + destruct Hcoh as (_ & Hoff & _).
        assert (Hnv : ¬ visited r n).
        { intros (i & c & ρ & Hin & <-). apply Hc. exact (q_clpath i (c, ρ) Hin). }
        rewrite (proj2 (Hoff n Hnv)). unfold O_T, T.
        rewrite (bt_nostate S O cl VL f0 Hfuel Hun Hcl1 cHOf cHOm n Hpl Hc). done.
    - intros c Hc. exact (proj1 (proj2 (proj2 T_syn)) c Hc).
    - intros k x Hin. exact (proj1 (proj1 (proj2 T_syn) _ Hin)).
  Qed.

  Lemma no_refuse_out n k c v : ¬ refused (M := lq_menu O) U S r w n (OffOut k c v).
  Proof.
    intros (i & c0 & ρ & Hin & Hs & [(Hd & Hno & Δ & Hst)|(Hst & σ & Δ & Hs')]).
    - simpl in Hst. destruct (w i) as [s|k' t].
      + apply (Hno Δ). simpl. exact (proj1 (cstep_ich _ _ _ _ _ _ Hst) _).
      + inversion Hst; subst; match goal with Hsg : single _ _ _ _ |- _ => destruct Hsg as [_ Hsg']; discriminate Hsg' end.
    - simpl in Hs'. destruct σ as [s|k' t].
      + apply (Hst (ICh s)). exists c0, ρ, Δ. split; [done|]. split; [intros Hx; simpl in *; congruence|].
        simpl. exact (proj1 (cstep_ich _ _ _ _ _ _ Hs') _).
      + inversion Hs'; subst; match goal with Hsg : single _ _ _ _ |- _ => destruct Hsg as [_ Hsg']; discriminate Hsg' end.
  Qed.

  Lemma q_run : run_word (M := lq_menu O) (menu T) (S_T T) (dinit O q) r w.
  Proof.
    rewrite <- (proj1 Hrun). refine (run_sandwich (M := lq_menu O) Ok U S r w Hrun0 (menu T) (S_T T) _ _ _).
    - intros i c ρ Hin. exact (T_S _ (q_clpath i (c, ρ) Hin)).
    - intros i c ρ o Hin Hs Hu. pose proof (q_clpath i (c, ρ) Hin) as Hc. simpl in *.
      apply T_menu; [exact (clpath_plain S cl cHclo _ Hc)|exact (proj2 (U_cell _ _ Hu))|].
      split; [done|]. split; [done|by apply Hcl2].
    - intros i c ρ o Hin Hs Hm. pose proof (q_clpath i (c, ρ) Hin) as Hc. simpl in *.
      assert (Hd : (∃ k c v, o = OffOut k c v) ∨ ∀ k c v, o ≠ OffOut k c v).
      { destruct o; [left; by eauto|right; done..]. }
      destruct Hd as [(k & c0 & v & ->)|Hd].
      + right. split; [exact (T_ok _ _ Hm)|apply no_refuse_out].
      + left. apply Hcl2. exact (proj2 (proj2 (proj1 (T_menu _ o (clpath_plain S cl cHclo _ Hc) Hd) Hm))).
  Qed.

  Notation ST := (S_T T).
  Notation UT := (cells (M := lq_menu O) (S_T T) r w).
  Notation JA := (Jstar (M := lq_menu O) Ok UT ST r w).
  Notation JB := (Jstar (M := lq_menu O) Ok U S r w).
  Notation SsA := (Sstar (M := lq_menu O) Ok UT ST r w).
  Notation SsB := (Sstar (M := lq_menu O) Ok U S r w).
  Notation SA := (mdlts (M := lq_menu O) JA SsA).
  Notation SB := (mdlts (M := lq_menu O) JB SsB).

  Lemma q_S i c ρ : (c, ρ) ∈ r i → ST c.1 = S c.1.
  Proof. intros Hin. exact (T_S _ (q_clpath i (c, ρ) Hin)). Qed.

  Lemma cells_eq n o : UT n o ↔ U n o.
  Proof.
    unfold used_by, cells. split; intros (i & c & ρ & Δ & Hin & Hs & Hrest); exists i, c, ρ, Δ;
      (split; [done|]); (split; [|exact Hrest]); pose proof (q_S i c ρ Hin) as E.
    - change (S c.1 = false). change (ST c.1 = false) in Hs. congruence.
    - change (ST c.1 = false). change (S c.1 = false) in Hs. congruence.
  Qed.

  Lemma q_agree i : agree_on (mdlts (M := lq_menu O) UT ST) (mdlts (M := lq_menu O) U S) (r i).
  Proof.
    intros c ρ Hin. pose proof (q_S i c ρ Hin) as E. split.
    - change (ST c.1 = true ↔ S c.1 = true). by rewrite E.
    - intros _ σ Δ. split; apply (mstep_mono (M := lq_menu O)); intros n o; apply cells_eq.
  Qed.

  Lemma q_agree' i : agree_on (mdlts (M := lq_menu O) U S) (mdlts (M := lq_menu O) UT ST) (r i).
  Proof.
    intros c ρ Hin. pose proof (q_S i c ρ Hin) as E. split.
    - change (S c.1 = true ↔ ST c.1 = true). by rewrite E.
    - intros _ σ Δ. split; apply (mstep_mono (M := lq_menu O)); intros n o; apply cells_eq.
  Qed.

  Lemma refused_eq n o : refused (M := lq_menu O) UT ST r w n o ↔ refused (M := lq_menu O) U S r w n o.
  Proof.
    unfold refused. split; intros (i & c & ρ & Hin & Hs & Hd); exists i, c, ρ; (split; [done|]);
      pose proof (q_S i c ρ Hin) as E.
    - split; [change (S c.1 = false); change (ST c.1 = false) in Hs; congruence|].
      destruct Hd as [(Hd & Hno & Hex)|(Hst & Hex)]; [left|right].
      + split; [exact (agree_dstep _ _ Stay _ _ _ (q_agree i) Hd)|]. split; [|done].
        intros Δ Hm. apply (Hno Δ). revert Hm. apply (mstep_mono (M := lq_menu O)). intros n' o'. apply cells_eq.
      + split; [exact (agree_dstable _ _ _ (q_agree i) Hst)|done].
    - split; [change (ST c.1 = false); change (S c.1 = false) in Hs; congruence|].
      destruct Hd as [(Hd & Hno & Hex)|(Hst & Hex)]; [left|right].
      + split; [exact (agree_dstep _ _ Stay _ _ _ (q_agree' i) Hd)|]. split; [|done].
        intros Δ Hm. apply (Hno Δ). revert Hm. apply (mstep_mono (M := lq_menu O)). intros n' o'. apply cells_eq.
      + split; [exact (agree_dstable _ _ _ (q_agree' i) Hst)|done].
  Qed.

  Lemma Jstar_eq n o : JA n o ↔ JB n o.
  Proof. unfold Jstar. rewrite cells_eq, refused_eq. done. Qed.

  Lemma crossed_eq n : crossed (M := lq_menu O) Ok UT ST r w n ↔ crossed (M := lq_menu O) Ok U S r w n.
  Proof.
    unfold crossed. split; intros (m & a & m2 & E & HJ & HnI); exists m, a, m2; (split; [done|]); split.
    - by apply Jstar_eq.
    - intros Hu. apply HnI. by apply cells_eq.
    - by apply Jstar_eq.
    - intros Hu. apply HnI. by apply cells_eq.
  Qed.

  Lemma path_clpath n :
    visited_ok (M := lq_menu O) JA n → ¬ crossed (M := lq_menu O) Ok U S r w n → clpath S cl n.
  Proof.
    intros Hv Hnc m a m2 E. destruct (classic (U m (offer_of a))) as [Hu|Hnu].
    - split; [exact (proj1 (U_cell _ _ Hu))|by apply Hcl2].
    - exfalso. apply Hnc. exists m, a, m2. split; [exact E|]. split; [|exact Hnu].
      apply Jstar_eq. exact (Hv m a m2 E).
  Qed.

  Lemma Sstar_eq n : visited_ok (M := lq_menu O) JA n → SsA n = SsB n.
  Proof.
    intros Hv. apply eq_true_iff_eq. split; intros Hs.
    - destruct (classic (crossed (M := lq_menu O) Ok U S r w n)) as [Hc|Hc]; [by apply Sstar_crossed|].
      apply Sstar_S. apply Sstar_inv in Hs as [Hs|Hs]; [|destruct Hc; by apply crossed_eq].
      rewrite <- (T_S n (path_clpath n Hv Hc)). done.
    - destruct (classic (crossed (M := lq_menu O) Ok U S r w n)) as [Hc|Hc].
      { apply Sstar_crossed. by apply crossed_eq. }
      apply Sstar_S. apply Sstar_inv in Hs as [Hs|Hs]; [|done].
      rewrite (T_S n (path_clpath n Hv Hc)). done.
  Qed.

  Lemma q_path i c ρ : (c, ρ) ∈ r i → visited_ok (M := lq_menu O) JA c.1.
  Proof.
    intros Hin. pose proof (visited_run (M := lq_menu O) U S r w Hrun0 Hinit i (c, ρ) Hin) as Hv.
    intros m a m2 E. left. apply cells_eq. exact (Hv m a m2 E).
  Qed.

  Lemma asm_complete : alt_free_obs p q →
    ∃ r', is_run (SchedSts0 := trace_sts p q O S Ch K r w) Stay (dinit O p) r'
        ∧ run_le (SchedSts0 := trace_sts p q O S Ch K r w) r' r.
  Proof.
    intros Hfree. destruct (Hfree O Ch K (menu T) (S_T T) T_real r w q_run) as (r' & Hr' & Hle).
    assert (Hpath : ∀ i x, x ∈ r' i → visited_ok (M := lq_menu O) JA x.1.1).
    { refine (run_inv SA (λ c, visited_ok (M := lq_menu O) JA c.1) _ (dinit O p) r' Hr' _).
      - intros ρ c σ Δ Hv Hs y Hy. exact (visited_step (M := lq_menu O) JA ρ c σ Δ y Hv Hs Hy).
      - intros x ->%list_elem_of_singleton m a m2 E. simpl in E. destruct m; discriminate E. }
    assert (Hag : ∀ i, agree_on SA SB (r' i)).
    { intros i c ρ Hin. split.
      - change (SsA c.1 = true ↔ SsB c.1 = true). rewrite (Sstar_eq c.1 (Hpath i (c, ρ) Hin)). done.
      - intros _ σ Δ. split; apply (mstep_mono (M := lq_menu O)); intros n o; apply Jstar_eq. }
    exists r'. split; [exact (agree_run SA SB Stay _ r' Hag Hr')|].
    intros n v Hv. unfold trace_sts, trace_menu, trace_succ in Hv.
    pose proof (agree_succ_mass SA SB r' n (Hag n)) as E. rewrite <- E in Hv.
    destruct (Hle n v Hv) as (m & Hm). exists m. unfold trace_sts, trace_menu, trace_succ, succ_mass in *.
    erewrite dmass_of_congr; [exact Hm|].
    intros c ρ Hin. change (SsB c.1 = true ↔ SsA c.1 = true). rewrite (Sstar_eq c.1 (q_path m c ρ Hin)). done.
  Qed.
End Asm.

Lemma stable_const `{QM : QuantumModel} O I S D (r : nat → dist comp) w N :
  run_word (M := lq_menu O) I S D r w → dstable (SchedSts0 := mdlts (M := lq_menu O) I S) (r N) →
  ∀ i, r (N + i) = r N.
Proof.
  intros [_ Hr] Hst i. induction i as [|i IH]; [by rewrite Nat.add_0_r|]. rewrite Nat.add_succ_r.
  destruct (Hr (N + i)) as [Hd|[_ E]].
  - exfalso. rewrite IH in Hd. exact (dstep_not_stable _ _ _ _ Hd Hst).
  - by rewrite E.
Qed.

Definition f0d (L : list node) : nat := Datatypes.S (foldr (λ m acc, length m + acc) 0 L).

Definition VLd (L : list node) : list val := concat (map valsof L).

Definition LO (L : list node) : list offer := omap (λ m : node, offer_of <$> last m) L.

Definition cld `{QM : QuantumModel} (O : node → list msg) (S : node → bool) (r : nat → dist comp)
    (w : nat → item) (L : list node) (n : node) : list offer :=
  List.filter (λ o, if excluded_middle_informative (used_by O S r w n o) then true else false)
    (remove_dups (LO L)).

Section Data.
  Context `{QM : QuantumModel} (p q : proc * St).
  Context (O : node → list msg) (S : node → bool) (Ch : channel → Prop) (K : tag → okind).
  Context (r : nat → dist comp) (w : nat → item) (L : list node).

  Notation U := (used_by O S r w).

  Hypothesis Hcoh : coherent p q O S Ch K r w.
  Hypothesis HL : ∀ n, visited r n → n ∈ L.

  Lemma Lv_spec n : visited r n → n ∈ L.
  Proof. exact (HL n). Qed.

  Lemma not_vis n : S n = false → visited r n.
  Proof.
    intros Hs. destruct (classic (visited r n)) as [Hv|Hv]; [done|].
    destruct Hcoh as (_ & Hoff & _). rewrite (proj1 (Hoff n Hv)) in Hs. discriminate Hs.
  Qed.

  Lemma d_fuel n : S n = false → length n < f0d L.
  Proof.
    intros Hs. pose proof (len_le_sum (L) n (Lv_spec n (not_vis n Hs))) as Hl. unfold f0d. lia.
  Qed.

  Lemma d_un n a : unlisted (VLd L) a → S (n ++ [a]) = true.
  Proof.
    intros Hu. destruct (S (n ++ [a])) eqn:E; [done|]. exfalso.
    pose proof (Lv_spec _ (not_vis _ E)) as Hin.
    assert (Hsub : ∀ v, v ∈ valsof (n ++ [a]) → v ∈ VLd L).
    { intros v Hv. unfold VLd. apply list_elem_of_In, in_concat. exists (valsof (n ++ [a])).
      split; [|by apply list_elem_of_In]. apply in_map_iff. exists (n ++ [a]). split; [done|by apply list_elem_of_In]. }
    destruct a as [k c v|k c v|k E0 qs|k M qs i|k qs]; simpl in Hu; try done.
    - apply Hu, Hsub. unfold valsof. rewrite omap_app. apply elem_of_app. right. by left.
    - apply Hu, Hsub. unfold valsof. rewrite omap_app. apply elem_of_app. right. by left.
  Qed.

  Lemma d_cl1 n : NoDup (cld O S r w L n).
  Proof. unfold cld. apply NoDup_ListNoDup, List.NoDup_filter, NoDup_ListNoDup, NoDup_remove_dups. Qed.

  Lemma d_cl2 n o : o ∈ cld O S r w L n ↔ U n o.
  Proof.
    unfold cld. rewrite list_elem_of_In, filter_In. split.
    - intros [_ Hb]. by destruct (excluded_middle_informative (U n o)).
    - intros Hu. split; [|by destruct (excluded_middle_informative (U n o))].
      apply list_elem_of_In, elem_of_remove_dups.
      destruct Hu as (i & c & ρ & Δ & Hin & Hs & Hnf & Hne & Hstp & Hall). simpl in Hstp, Hnf.
      destruct (w i) as [s|k t]; [by destruct Hnf|].
      destruct (cstep_off _ _ _ _ _ _ _ Hstp) as (o' & [En Eo] & _ & Hy). subst o'.
      destruct Δ as [|[cy ρy] Δ]; [done|]. destruct (Hy (cy, ρy) ltac:(by left)) as (a & Ea & Eny). simpl in Eny.
      unfold LO. apply list_elem_of_omap. exists (c.1 ++ [a]). split.
      + rewrite <- Eny. apply Lv_spec. exists (Datatypes.S i), cy, ρy. split; [|done]. apply Hall. by left.
      + rewrite last_snoc. simpl. by rewrite Ea.
  Qed.
End Data.

Theorem trace_complete `{QM : QuantumModel} (DC : dep_choice) (p q : proc * St) :
  q.2 ≠ szero →
  ctx_pre_sm_on Stay (obs_for p q) p q → alt_trace p q.
Proof.
  intros Hz Hc O S Ch K r w Hcoh [Hrun (L & HL)].
  refine (asm_complete p q O S Ch K r w (cld O S r w L) (VLd L) (f0d L) Hcoh Hrun _ _ _ _
            (proj1 (alt_free_obs_iff DC p q Hz) Hc)).
  - intros n. apply d_cl1.
  - intros n o. eapply d_cl2; eassumption.
  - intros n. eapply d_fuel; eassumption.
  - intros n a. eapply d_un; eassumption.
Qed.
(* end hide *)
