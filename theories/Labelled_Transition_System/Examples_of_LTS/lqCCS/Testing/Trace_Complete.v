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
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Pull lqCCS.Testing.Head lqCCS.Testing.Modes lqCCS.Testing.Syn lqCCS.Testing.Assembly lqCCS.Testing.Final lqCCS.Testing.Trace lqCCS.Testing.Build.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Trace_Complete.
  Context `{lqP : lqCCS_Parameters}.

Section Asm.
  Context `{QM : QuantumModel} (p q : prog * St).
  Context (O : node → list msg) (S : node → bool) (Ch : channel → Prop) (K : tag → okind).
  Context (r : nat → dist comp) (w : nat → item).
  Context (cl : node → list offer) (VL : list val) (f0 : nat).

  Notation U := (used_by O S r w).
  Notation Ok := (real_off p q Ch K).

  Hypothesis Hcoh : coherent p q O S Ch K r w.
  Hypothesis Hrun : run_word (M := lq_menu O) U S (dinit q) r w.
  Hypothesis Hcl1 : ∀ z, NoDup (cl z).
  Hypothesis Hcl2 : ∀ z o, o ∈ cl z ↔ U z o.
  Hypothesis Hfuel : ∀ z, S z = false → length z < f0.
  Hypothesis Hun : ∀ z a, unlisted VL a → S (z ++ [a]) = true.
  Hypothesis HKr : ∀ t, K t ≠ KRec.

  Definition TG (x : tag * okind) : Prop := K x.1 = x.2 ∧ x.1 ∉ otags p.1 ∧ x.1 ∉ otags q.1.

  Definition T : prog := BT S O cl VL f0.

  Lemma cHS : ext_closed S.
  Proof. exact (proj1 Hcoh). Qed.

  Lemma cHOf z x y : S z = false → x ∈ O z → y ∈ O z → mtag x = mtag y → x = y.
  Proof.
    destruct Hcoh as (_ & _ & _ & _ & HOf & _). destruct x as [[t c] v], y as [[t' c'] v']. unfold mtag. simpl.
    intros Hs Hx Hy <-. by destruct (HOf z t c v c' v' Hs Hx Hy) as [-> ->].
  Qed.

  Lemma cHOm z a x : S (z ++ [a]) = false → x ∈ O z → x ∈ O (z ++ [a]).
  Proof. destruct Hcoh as (_ & _ & _ & _ & _ & HOm). apply HOm. Qed.

  Lemma U_cell z o : U z o → S z = false ∧ ∀ t c v, o ≠ OffOut t c v.
  Proof.
    unfold used_by, cells. intros (n & c & ρ & Δ & Hin & Hs & Hnf & Hne & Hst & _). simpl in Hst, Hs, Hnf.
    destruct (w n) as [k|t t']; [by destruct Hnf|].
    apply cstep_cases in Hst. inversion Hst; subst; match goal with Hsg : single _ _ _ _ |- _ => destruct Hsg as [E1 E2] end;
      simpl in *; subst; split; done.
  Qed.

  Lemma cHclo z t c v : OffOut t c v ∉ cl z.
  Proof. intros Hin%Hcl2. destruct (U_cell _ _ Hin) as [_ Hn]. by apply (Hn t c v). Qed.

  Lemma cHclu z t : OffUnfold t ∉ cl z.
  Proof.
    intros Hin%Hcl2. destruct Hcoh as (_ & _ & Hcs & _). destruct (Hcs z _ Hin) as (Hty & _).
    unfold typed in Hty. simpl in Hty. apply (HKr t). congruence.
  Qed.

  Lemma Hrun0 : run_word (M := lq_menu O) U S (r 0) r w.
  Proof. destruct Hrun as [E Hr]. split; [done|exact Hr]. Qed.

  Lemma Hinit x : x ∈ r 0 → visited_ok (M := lq_menu O) U (mnode (MenuSts := lq_menu O) x.1).
  Proof.
    rewrite (proj1 Hrun). intros ->%list_elem_of_singleton z' a z2 E. simpl in E. destruct z'; discriminate E.
  Qed.

  Lemma q_clpath n x : x ∈ r n → clpath S cl x.1.1.
  Proof.
    intros Hx. pose proof (visited_run (M := lq_menu O) U S r w Hrun0 Hinit n x Hx) as Hv.
    intros z' a z2 E. pose proof (Hv z' a z2 E) as Hu. simpl in Hu.
    split; [exact (proj1 (U_cell _ _ Hu))|by apply Hcl2].
  Qed.

  Lemma T_inv z' : (∀ X, X ∈ tnodes T z' → inv S O cl VL f0 z' X) ∧ length (tnodes T z') ≤ 1.
  Proof. exact (bt_inv S O cl VL f0 Hfuel Hun Hcl1 cHclu cHOf cHOm z'). Qed.

  Lemma T_S z : clpath S cl z → S_T T z = S z.
  Proof. exact (bt_S S O cl VL f0 cHS Hfuel Hun Hcl1 cHclu cHOf cHOm cHclo z). Qed.

  Lemma T_menu z o : plain z → (∀ t c v, o ≠ OffOut t c v) → (menu T z o ↔ clpath S cl z ∧ S z = false ∧ o ∈ cl z).
  Proof. exact (bt_menu S O cl VL f0 Hfuel Hun Hcl1 cHclu cHOf cHOm cHclo z o). Qed.

  Lemma T_syn : syn TG (λ c, Ch c) (λ c, ¬ Ch c) T.
  Proof.
    destruct Hcoh as (_ & _ & Hreal & HOk & _).
    apply (bt_syn S O cl VL TG (λ c, Ch c) (λ c, ¬ Ch c)).
    - intros z o Hin. destruct (Hreal z o (proj1 (Hcl2 z o) Hin)) as (Hty & Hp & Hq & Hc).
      split; [|exact Hc]. split; [by symmetry|by split].
    - intros z t c v Hs Hin. destruct (HOk z t c v Hs Hin) as (Hk & Hp & Hq & Hc). split; [|done]. by split.
  Qed.

  Lemma T_observer : observer T.
  Proof.
    destruct T_syn as (Hob & Htg & Hoc & Hic). split; [split; [done|]|split; [|split]].
    - intros c Hc Hc'. exact (Hic c Hc' (Hoc c Hc)).
    - intros t x y Hx Hy. pose proof (proj1 (Htg _ Hx)) as E1. pose proof (proj1 (Htg _ Hy)) as E2.
      simpl in E1, E2. congruence.
    - intros z. exact (proj2 (T_inv z)).
    - intros z z' t c v c' v' Y HY.
      exact (bt_gone S O cl VL f0 Hfuel Hun Hcl1 cHclu cHOf cHOm z z' t c v c' v' Y HY).
  Qed.

  Lemma T_for : obs_for p q T.
  Proof.
    split; [exact T_observer|]. intros t' Ht. unfold tags in Ht. apply list_elem_of_fmap in Ht as ([t x] & -> & Hin).
    exact (proj2 (proj1 (proj2 T_syn) _ Hin)).
  Qed.

  Lemma T_ok z o : menu T z o → Ok o.
  Proof.
    intros Hm. destruct T_syn as (Hob & Htg & Hoc & Hic).
    destruct (Htg _ (menu_kind T T_observer z o Hm)) as (Hk & Hp & Hq). simpl in Hk, Hp, Hq.
    split; [by symmetry|]. split; [done|]. split; [done|]. intros t c -> Hc1.
    destruct Hm as (T' & a & HT' & Ha & Hne). destruct a as [|t' c' v| | | |]; try discriminate Ha.
    simpl in Ha. injection Ha as -> ->.
    destruct (co_succ T' (CoIn t c v)) as [|T'' l] eqn:E; [done|].
    assert (HT'' : T'' ∈ co_succ T' (CoIn t c v)) by (rewrite E; by left).
    pose proof (prog_step_in_chan T' t c v T'' (proj1 (tnodes_obs T (proj1 T_observer) z T' HT'))
                  (co_succ_sound _ _ _ (proj1 (tnodes_obs T (proj1 T_observer) z T' HT')) HT'')) as Hc.
    exact (Hic c (proj2 (tnodes_chans T (proj1 T_observer) z T' HT') c Hc) Hc1).
  Qed.

  Lemma T_real : RealT p q O Ch K (menu T) (S_T T).
  Proof.
    split; [|exact T_ok]. exists T. split; [exact T_for|]. split; [|split; [done|split; [done|split]]].
    - intros z z' Hpl Hs. destruct (classic (clpath S cl z)) as [Hc|Hc].
      + rewrite (T_S z Hc) in Hs. symmetry.
        exact (bt_O S O cl VL f0 Hfuel Hun Hcl1 cHclu cHOf cHOm cHclo z z' Hc Hs).
      + destruct Hcoh as (_ & Hoff & _).
        assert (Hnv : ¬ visited r z).
        { intros (n & c & ρ & Hin & <-). apply Hc. exact (q_clpath n (c, ρ) Hin). }
        rewrite (proj2 (Hoff z Hnv)). unfold O_T, T.
        rewrite (bt_nostate S O cl VL f0 Hfuel Hun Hcl1 cHclu cHOf cHOm z Hpl Hc). done.
    - intros c Hc. exact (proj1 (proj2 (proj2 T_syn)) c Hc).
    - intros t x Hin. exact (proj1 (proj1 (proj2 T_syn) _ Hin)).
  Qed.

  Lemma no_refuse_out z t c v : ¬ refused (M := lq_menu O) U S r w z (OffOut t c v).
  Proof.
    intros (n & c0 & ρ & Hin & Hs & [(Hd & Hno & Δ & Hst)|(Hst & σ & Δ & Hs')]).
    - simpl in Hst. destruct (w n) as [k|t' t''].
      + apply (Hno Δ). simpl. exact (proj1 (cstep_ich _ _ _ _ _ _ Hst) _).
      + apply cstep_cases in Hst. inversion Hst; subst; match goal with Hsg : single _ _ _ _ |- _ => destruct Hsg as [_ Hsg']; discriminate Hsg' end.
    - simpl in Hs'. destruct σ as [k|t' t''].
      + apply (Hst (ICh k)). exists c0, ρ, Δ. split; [done|]. split; [intros Hx; simpl in *; congruence|].
        simpl. exact (proj1 (cstep_ich _ _ _ _ _ _ Hs') _).
      + apply cstep_cases in Hs'. inversion Hs'; subst; match goal with Hsg : single _ _ _ _ |- _ => destruct Hsg as [_ Hsg']; discriminate Hsg' end.
  Qed.

  Lemma q_run : run_word (M := lq_menu O) (menu T) (S_T T) (dinit q) r w.
  Proof.
    rewrite <- (proj1 Hrun). refine (run_sandwich (M := lq_menu O) Ok U S r w Hrun0 (menu T) (S_T T) _ _ _).
    - intros n c ρ Hin. exact (T_S _ (q_clpath n (c, ρ) Hin)).
    - intros n c ρ o Hin Hs Hu. pose proof (q_clpath n (c, ρ) Hin) as Hc. simpl in *.
      apply T_menu; [exact (clpath_plain S cl cHclo _ Hc)|exact (proj2 (U_cell _ _ Hu))|].
      split; [done|]. split; [done|by apply Hcl2].
    - intros n c ρ o Hin Hs Hm. pose proof (q_clpath n (c, ρ) Hin) as Hc. simpl in *.
      assert (Hd : (∃ t c v, o = OffOut t c v) ∨ ∀ t c v, o ≠ OffOut t c v).
      { destruct o; [left; by eauto|right; done..]. }
      destruct Hd as [(t & c0 & v & ->)|Hd].
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

  Lemma q_S n c ρ : (c, ρ) ∈ r n → ST c.1 = S c.1.
  Proof. intros Hin. exact (T_S _ (q_clpath n (c, ρ) Hin)). Qed.

  Lemma cells_eq z o : UT z o ↔ U z o.
  Proof.
    unfold used_by, cells. split; intros (n & c & ρ & Δ & Hin & Hs & Hrest); exists n, c, ρ, Δ;
      (split; [done|]); (split; [|exact Hrest]); pose proof (q_S n c ρ Hin) as E.
    - change (S c.1 = false). change (ST c.1 = false) in Hs. congruence.
    - change (ST c.1 = false). change (S c.1 = false) in Hs. congruence.
  Qed.

  Lemma q_agree n : agree_on (mdlts (M := lq_menu O) UT ST) (mdlts (M := lq_menu O) U S) (r n).
  Proof.
    intros c ρ Hin. pose proof (q_S n c ρ Hin) as E. split.
    - change (ST c.1 = true ↔ S c.1 = true). by rewrite E.
    - intros _ σ Δ. split; apply (mstep_mono (M := lq_menu O)); intros z o; apply cells_eq.
  Qed.

  Lemma q_agree' n : agree_on (mdlts (M := lq_menu O) U S) (mdlts (M := lq_menu O) UT ST) (r n).
  Proof.
    intros c ρ Hin. pose proof (q_S n c ρ Hin) as E. split.
    - change (S c.1 = true ↔ ST c.1 = true). by rewrite E.
    - intros _ σ Δ. split; apply (mstep_mono (M := lq_menu O)); intros z o; apply cells_eq.
  Qed.

  Lemma refused_eq z o : refused (M := lq_menu O) UT ST r w z o ↔ refused (M := lq_menu O) U S r w z o.
  Proof.
    unfold refused. split; intros (n & c & ρ & Hin & Hs & Hd); exists n, c, ρ; (split; [done|]);
      pose proof (q_S n c ρ Hin) as E.
    - split; [change (S c.1 = false); change (ST c.1 = false) in Hs; congruence|].
      destruct Hd as [(Hd & Hno & Hex)|(Hst & Hex)]; [left|right].
      + split; [exact (agree_dstep _ _ Stay _ _ _ (q_agree n) Hd)|]. split; [|done].
        intros Δ Hm. apply (Hno Δ). revert Hm. apply (mstep_mono (M := lq_menu O)). intros z1 o'. apply cells_eq.
      + split; [exact (agree_dstable _ _ _ (q_agree n) Hst)|done].
    - split; [change (ST c.1 = false); change (S c.1 = false) in Hs; congruence|].
      destruct Hd as [(Hd & Hno & Hex)|(Hst & Hex)]; [left|right].
      + split; [exact (agree_dstep _ _ Stay _ _ _ (q_agree' n) Hd)|]. split; [|done].
        intros Δ Hm. apply (Hno Δ). revert Hm. apply (mstep_mono (M := lq_menu O)). intros z1 o'. apply cells_eq.
      + split; [exact (agree_dstable _ _ _ (q_agree' n) Hst)|done].
  Qed.

  Lemma Jstar_eq z o : JA z o ↔ JB z o.
  Proof. unfold Jstar. rewrite cells_eq, refused_eq. done. Qed.

  Lemma crossed_eq z : crossed (M := lq_menu O) Ok UT ST r w z ↔ crossed (M := lq_menu O) Ok U S r w z.
  Proof.
    unfold crossed. split; intros (z' & a & z2 & E & HJ & HnI); exists z', a, z2; (split; [done|]); split.
    - by apply Jstar_eq.
    - intros Hu. apply HnI. by apply cells_eq.
    - by apply Jstar_eq.
    - intros Hu. apply HnI. by apply cells_eq.
  Qed.

  Lemma path_clpath z :
    visited_ok (M := lq_menu O) JA z → ¬ crossed (M := lq_menu O) Ok U S r w z → clpath S cl z.
  Proof.
    intros Hv Hnc z' a z2 E. destruct (classic (U z' (offer_of a))) as [Hu|Hnu].
    - split; [exact (proj1 (U_cell _ _ Hu))|by apply Hcl2].
    - exfalso. apply Hnc. exists z', a, z2. split; [exact E|]. split; [|exact Hnu].
      apply Jstar_eq. exact (Hv z' a z2 E).
  Qed.

  Lemma Sstar_eq z : visited_ok (M := lq_menu O) JA z → SsA z = SsB z.
  Proof.
    intros Hv. apply eq_true_iff_eq. split; intros Hs.
    - destruct (classic (crossed (M := lq_menu O) Ok U S r w z)) as [Hc|Hc]; [by apply Sstar_crossed|].
      apply Sstar_S. apply Sstar_inv in Hs as [Hs|Hs]; [|destruct Hc; by apply crossed_eq].
      rewrite <- (T_S z (path_clpath z Hv Hc)). done.
    - destruct (classic (crossed (M := lq_menu O) Ok U S r w z)) as [Hc|Hc].
      { apply Sstar_crossed. by apply crossed_eq. }
      apply Sstar_S. apply Sstar_inv in Hs as [Hs|Hs]; [|done].
      rewrite (T_S z (path_clpath z Hv Hc)). done.
  Qed.

  Lemma q_path n c ρ : (c, ρ) ∈ r n → visited_ok (M := lq_menu O) JA c.1.
  Proof.
    intros Hin. pose proof (visited_run (M := lq_menu O) U S r w Hrun0 Hinit n (c, ρ) Hin) as Hv.
    intros z' a z2 E. left. apply cells_eq. exact (Hv z' a z2 E).
  Qed.

  Lemma asm_complete : alt_free_obs p q →
    ∃ r', is_run (SchedSts0 := trace_sts p q O S Ch K r w) Stay (dinit p) r'
        ∧ run_le (SchedSts0 := trace_sts p q O S Ch K r w) r' r.
  Proof.
    intros Hfree. destruct (Hfree O Ch K HKr (menu T) (S_T T) T_real r w q_run) as (r' & Hr' & Hle).
    assert (Hpath : ∀ n x, x ∈ r' n → visited_ok (M := lq_menu O) JA x.1.1).
    { refine (run_inv SA (λ c, visited_ok (M := lq_menu O) JA c.1) _ (dinit p) r' Hr' _).
      - intros ρ c σ Δ Hv Hs y Hy. exact (visited_step (M := lq_menu O) JA ρ c σ Δ y Hv Hs Hy).
      - intros x ->%list_elem_of_singleton z' a z2 E. simpl in E. destruct z'; discriminate E. }
    assert (Hag : ∀ n, agree_on SA SB (r' n)).
    { intros n c ρ Hin. split.
      - change (SsA c.1 = true ↔ SsB c.1 = true). rewrite (Sstar_eq c.1 (Hpath n (c, ρ) Hin)). done.
      - intros _ σ Δ. split; apply (mstep_mono (M := lq_menu O)); intros z o; apply Jstar_eq. }
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
  ∀ n, r (N + n) = r N.
Proof.
  intros [_ Hr] Hst n. induction n as [|n IH]; [by rewrite Nat.add_0_r|]. rewrite Nat.add_succ_r.
  destruct (Hr (N + n)) as [Hd|[_ E]].
  - exfalso. rewrite IH in Hd. exact (dstep_not_stable _ _ _ _ Hd Hst).
  - by rewrite E.
Qed.

Definition f0d (L : list node) : nat := Datatypes.S (foldr (λ z' acc, length z' + acc) 0 L).

Definition VLd (L : list node) : list val := concat (map valsof L).

Definition LO (L : list node) : list offer := omap (λ z' : node, offer_of <$> last z') L.

Definition cld `{QM : QuantumModel} (O : node → list msg) (S : node → bool) (r : nat → dist comp)
    (w : nat → item) (L : list node) (z : node) : list offer :=
  List.filter (λ o, if excluded_middle_informative (used_by O S r w z o) then true else false)
    (remove_dups (LO L)).

Section Data.
  Context `{QM : QuantumModel} (p q : prog * St).
  Context (O : node → list msg) (S : node → bool) (Ch : channel → Prop) (K : tag → okind).
  Context (r : nat → dist comp) (w : nat → item) (L : list node).

  Notation U := (used_by O S r w).

  Hypothesis Hcoh : coherent p q O S Ch K r w.
  Hypothesis HL : ∀ z, visited r z → z ∈ L.

  Lemma Lv_spec z : visited r z → z ∈ L.
  Proof. exact (HL z). Qed.

  Lemma not_vis z : S z = false → visited r z.
  Proof.
    intros Hs. destruct (classic (visited r z)) as [Hv|Hv]; [done|].
    destruct Hcoh as (_ & Hoff & _). rewrite (proj1 (Hoff z Hv)) in Hs. discriminate Hs.
  Qed.

  Lemma d_fuel z : S z = false → length z < f0d L.
  Proof.
    intros Hs. pose proof (len_le_sum (L) z (Lv_spec z (not_vis z Hs))) as Hl. unfold f0d. lia.
  Qed.

  Lemma d_un z a : unlisted (VLd L) a → S (z ++ [a]) = true.
  Proof.
    intros Hu. destruct (S (z ++ [a])) eqn:E; [done|]. exfalso.
    pose proof (Lv_spec _ (not_vis _ E)) as Hin.
    assert (Hsub : ∀ v, v ∈ valsof (z ++ [a]) → v ∈ VLd L).
    { intros v Hv. unfold VLd. apply list_elem_of_In, in_concat. exists (valsof (z ++ [a])).
      split; [|by apply list_elem_of_In]. apply in_map_iff. exists (z ++ [a]). split; [done|by apply list_elem_of_In]. }
    destruct a as [t c v|t c v|t U0 qs|t M qs n|t q0|t]; simpl in Hu; try done.
    - apply Hu, Hsub. unfold valsof. rewrite omap_app. apply elem_of_app. right. by left.
    - apply Hu, Hsub. unfold valsof. rewrite omap_app. apply elem_of_app. right. by left.
  Qed.

  Lemma d_cl1 z : NoDup (cld O S r w L z).
  Proof. unfold cld. apply NoDup_ListNoDup, List.NoDup_filter, NoDup_ListNoDup, NoDup_remove_dups. Qed.

  Lemma d_cl2 z o : o ∈ cld O S r w L z ↔ U z o.
  Proof.
    unfold cld. rewrite list_elem_of_In, filter_In. split.
    - intros [_ Hb]. by destruct (excluded_middle_informative (U z o)).
    - intros Hu. split; [|by destruct (excluded_middle_informative (U z o))].
      apply list_elem_of_In, elem_of_remove_dups.
      destruct Hu as (n & c & ρ & Δ & Hin & Hs & Hnf & Hne & Hstp & Hall). simpl in Hstp, Hnf.
      destruct (w n) as [k|t t']; [by destruct Hnf|].
      destruct (cstep_off _ _ _ _ _ _ _ Hstp) as (o' & [En Eo] & _ & Hy). subst o'.
      destruct Δ as [|[cy ρy] Δ]; [done|]. destruct (Hy (cy, ρy) ltac:(by left)) as (a & Ea & Eny). simpl in Eny.
      unfold LO. apply list_elem_of_omap. exists (c.1 ++ [a]). split.
      + rewrite <- Eny. apply Lv_spec. exists (Datatypes.S n), cy, ρy. split; [|done]. apply Hall. by left.
      + rewrite last_snoc. simpl. by rewrite Ea.
  Qed.
End Data.

Theorem trace_complete `{QM : QuantumModel} (DC : dep_choice) (p q : prog * St) :
  q.2 ≠ szero →
  ctx_pre_sm_on Stay (obs_for p q) p q → alt_trace p q.
Proof.
  intros Hz Hc O S Ch K r w HKr Hcoh [Hrun (L & HL)].
  refine (asm_complete p q O S Ch K r w (cld O S r w L) (VLd L) (f0d L) Hcoh Hrun _ _ _ _ HKr
            (proj1 (alt_free_obs_iff DC p q Hz) Hc)).
  - intros z. apply d_cl1.
  - intros z o. eapply d_cl2; eassumption.
  - intros z. eapply d_fuel; eassumption.
  - intros z a. eapply d_un; eassumption.
Qed.

End Trace_Complete.

(* end hide *)
