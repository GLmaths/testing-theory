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
From Stdlib.Bool Require Import Bool.
From Stdlib.Logic Require Import Classical_Prop.
From Stdlib Require Import Lia.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Branching lqCCS.Testing.Truncation lqCCS.Testing.Pull lqCCS.Testing.Head lqCCS.Testing.Modes lqCCS.Testing.Syn.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Lemma co_succ_offer X a a' : offer_of a = offer_of a' → co_succ X a = [] → co_succ X a' = [].
Proof.
  intros Ho. induction X as [t c e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t x P IHP|g]; simpl.
  - destruct a, a'; simpl in *; try done; inversion Ho; subst; done.
  - destruct (eval e) as [[[]| |]|]; done.
  - intros E. apply app_eq_nil in E as [E1 E2]. apply fmap_nil_inv in E1. apply fmap_nil_inv in E2.
    by rewrite (IHP E1), (IHQ E2).
  - done.
  - done.
  - done.
  - rewrite !gco_heads. by apply omap_nil_offer.
Qed.

Lemma menu_step T m a : menu T m (offer_of a) → tnodes T (m ++ [a]) ≠ [].
Proof.
  intros (T' & a' & HT' & Eo & Hne). destruct (co_succ T' a) as [|T'' l] eqn:E.
  - exfalso. apply Hne. by apply (co_succ_offer T' a a').
  - intros Enil. assert (Hin : T'' ∈ tnodes T (m ++ [a])).
    { apply tnodes_app_elem. exists T'. split; [done|]. rewrite E. by left. }
    rewrite Enil in Hin. by apply elem_of_nil in Hin.
Qed.

Lemma step_menu T m a : tnodes T (m ++ [a]) ≠ [] → menu T m (offer_of a).
Proof.
  intros Hne. destruct (tnodes T (m ++ [a])) as [|T'' l] eqn:E; [done|].
  assert (Hin : T'' ∈ tnodes T (m ++ [a])) by (rewrite E; by left).
  apply tnodes_app_elem in Hin as (T' & HT' & Hin). exists T', a. split; [done|]. split; [done|].
  intros En. rewrite En in Hin. by apply elem_of_nil in Hin.
Qed.

Lemma plain_app_l (m l : node) : plain (m ++ l) → plain m.
Proof. intros Hp k c v Hin. apply (Hp k c v). apply elem_of_app. by left. Qed.

Lemma nout_plain (n : list coact) : plain n → nout n = n.
Proof.
  induction n as [|a n IH]; intros Hp; [done|].
  assert (Ha : isout a = false).
  { destruct a; try done. exfalso. apply (Hp k c v). by left. }
  unfold nout in *. rewrite list.filter_cons_True by exact Ha. f_equal. apply IH.
  intros k c v Hin. apply (Hp k c v). by right.
Qed.

Lemma S_T_app T n l : S_T T n = true → S_T T (n ++ l) = true.
Proof.
  intros Hs. induction l as [|a l IH] using rev_ind; [by rewrite app_nil_r|]. rewrite app_assoc. by apply S_T_ext.
Qed.

Lemma succ_prefix T m l : succ_at T m = true → S_T T (m ++ l) = true.
Proof. intros Hs. apply S_T_app. by apply succ_at_S. Qed.

Lemma cstep_plain `{QM : QuantumModel} I O ρ c σ Δ : cstep I O ρ c σ Δ → plain c.1 → ∀ y, y ∈ Δ → plain y.1.1.
Proof.
  intros Hs Hpl y Hy.
  inversion Hs as [n P C E s Δ0 Hss|n P C E k d v t P' Hin HkC Hp|n P C E k d v t P' HI Hp
                  |n P C E k E' qs t HI|n P C E k qs t HI|n P C E k M qs t HI]; subst; simpl in *.
  - apply list_elem_of_fmap in Hy as (x & -> & _). done.
  - apply list_elem_of_singleton in Hy. by subst.
  - apply list_elem_of_singleton in Hy. subst. by apply plain_app.
  - apply list_elem_of_singleton in Hy. subst. by apply plain_app.
  - apply list_elem_of_singleton in Hy. subst. by apply plain_app.
  - apply list_elem_of_fmap in Hy as (x & -> & _). by apply plain_app.
Qed.

Definition relevant (c : comp) (o : offer) : Prop :=
  match o with
  | OffOut _ _ _ => False
  | OffIn _ ch => ∃ t v P', prog_step c.2.1.1 (CTag t) (ActExt (PrOut ch v)) P'
  | _ => True
  end.

Lemma cstep_menu_eq `{QM : QuantumModel} I J O ρ c σ Δ :
  (∀ o, relevant c o → I c.1 o → J c.1 o) → cstep I O ρ c σ Δ → cstep J O ρ c σ Δ.
Proof.
  intros Hrel Hs.
  inversion Hs as [n P C E s Δ0 Hss|n P C E k d v t P' Hin HkC Hp|n P C E k d v t P' HI Hp
                  |n P C E k E' qs t HI|n P C E k qs t HI|n P C E k M qs t HI]; subst; simpl in *.
  - by constructor.
  - by apply cs_recv.
  - apply cs_in; [|done]. apply Hrel; [|done]. by exists t, v, P'.
  - apply cs_op. by apply Hrel.
  - apply cs_init. by apply Hrel.
  - apply cs_meas. by apply Hrel.
Qed.

Section Asm.
  Context `{QM : QuantumModel} (p q : proc * St) (T : proc) (Ch : channel → Prop) (K : tag → okind).
  Context (O : node → list msg) (r : nat → dist comp) (w : nat → item) (F : list tag) (Mo : option meas).
  Context (VL : list val) (reps : node → list offer) (wrapb : node → offer → bool) (f0 : nat).
  Context (LV : node → Prop) (CL : channel → Prop) (N : nat).

  Notation Sx := (S_T T).
  Notation U := (cells (M := lq_menu O) (S_T T) r w).
  Notation Ok := (real_off p q Ch K).
  Notation Js := (Jstar (M := lq_menu O) (real_off p q Ch K) (cells (M := lq_menu O) (S_T T) r w) (S_T T) r w).
  Notation Ss := (Sstar (M := lq_menu O) (real_off p q Ch K) (cells (M := lq_menu O) (S_T T) r w) (S_T T) r w).
  Notation J0 := (Truncation.J0 p q T Ch K O r w F Mo).
  Notation TN := (tn VL reps wrapb f0 [] T).
  Notation STN := (mdlts (M := lq_menu O) (menu (tn VL reps wrapb f0 [] T)) (S_T (tn VL reps wrapb f0 [] T))).
  Notation SJ0 := (mdlts (M := lq_menu O) (Truncation.J0 p q T Ch K O r w F Mo)
    (Sstar (M := lq_menu O) (real_off p q Ch K) (cells (M := lq_menu O) (S_T T) r w) (S_T T) r w)).

  Hypothesis HT : obs_for p q T.
  Hypothesis Hrun : run_word (M := lq_menu O) (menu T) Sx (dinit O q) r w.
  Hypothesis Hnz : ∀ i x, x ∈ r i → x.2 ≠ weight_zero.
  Hypothesis HokT : ∀ n o, menu T n o → Ok o.
  Hypothesis HO : ∀ n m, plain n → Sx n = false → (m ∈ O n ↔ m ∈ O_T T n).
  Hypothesis HCh : ∀ c, c ∈ out_chans T → Ch c.
  Hypothesis HK : ∀ k x, (k, x) ∈ tagged T → K k = x.
  Hypothesis Hnd : ∀ m, NoDup (reps m).
  Hypothesis HR2 : ∀ m o, o ∈ reps m → J0 m o ∧ ¬ menu T m o.
  Hypothesis HR3 : ∀ m o, LV (m) → J0 m o → ¬ menu T m o → (∀ k c, o = OffIn k c → CL c) → o ∈ reps m.
  Hypothesis HW1 : ∀ m o, wrapb m o = true → ¬ U m o.
  Hypothesis HW2 : ∀ m o, LV (m) → menu T m o → ¬ U m o → wrapb m o = true.
  Hypothesis HLVp : ∀ n m, LV (n ++ m) → LV (n).
  Hypothesis HVL : ∀ n a, LV (n) → a ∈ n → ¬ unlisted VL a.
  Hypothesis Hf0 : ∀ n, LV (n) → length n < f0.

  Lemma T_len n : length (tnodes T n) ≤ 1.
  Proof. exact (proj1 (proj2 (proj2 (proj1 HT))) n). Qed.

  Lemma rep_ok m o : o ∈ reps m → Ok o.
  Proof.
    intros Hin. destruct (HR2 m o Hin) as [HJ HnM]. destruct HJ as [HM|[HJ _]]; [done|].
    destruct HJ as [HU|[Hok _]]; [|done]. destruct HnM. exact (U_menu q T O r w Hrun m o HU).
  Qed.

  Definition TG (x : tag * okind) : Prop := x ∈ tagged T ∨ ∃ m o, o ∈ reps m ∧ x = (off_tag o, off_kind o).
  Definition OC (c : channel) : Prop := c ∈ out_chans T.
  Definition IC (c : channel) : Prop := c ∈ in_chans T ∨ ∃ m k, OffIn k c ∈ reps m.

  Lemma TN_syn : syn TG OC IC TN.
  Proof.
    apply tn_syn.
    - intros m o Hin. split; [right; by exists m, o|]. intros k c ->. right. by exists m, k.
    - split; [exact (proj1 (proj1 (proj1 HT)))|]. split; [intros x Hx; by left|].
      split; [intros c Hc; exact Hc|intros c Hc; by left].
  Qed.

  Lemma TG_kind k x : TG (k, x) → K k = x.
  Proof.
    intros [Hin|(m & o & Hin & E)]; [exact (HK k x Hin)|]. injection E as -> ->.
    destruct (rep_ok m o Hin) as (Hty & _). symmetry. exact Hty.
  Qed.

  Lemma TG_tag k x : TG (k, x) → k ∉ tags p.1 ∧ k ∉ tags q.1.
  Proof.
    intros [Hin|(m & o & Hin & E)].
    - apply (proj2 HT). unfold tags. apply list_elem_of_fmap. by exists (k, x).
    - injection E as -> ->. destruct (rep_ok m o Hin) as (_ & Hp & Hq & _). done.
  Qed.

  Lemma TN_observer : observer TN.
  Proof.
    destruct TN_syn as (Hob & Htg & Hoc & Hic). destruct HT as [(Hobs & Hk2 & Hk3 & Hk4) Htags].
    split; [split; [done|]|split; [|split]].
    - intros c Hc Hc'. destruct (Hic c Hc') as [Hin|(m & k & Hin)].
      + exact (proj2 Hobs c (Hoc c Hc) Hin).
      + destruct (rep_ok m _ Hin) as (_ & _ & _ & Hch). exact (Hch k c eq_refl (HCh c (Hoc c Hc))).
    - intros k x y Hx Hy. rewrite <- (TG_kind k x (Htg _ Hx)). exact (TG_kind k y (Htg _ Hy)).
    - exact (tn_len VL reps wrapb Hnd T f0 T_len).
    - intros n m k c v c' v' Y HY. exact (tn_gone VL reps wrapb Hnd T f0 T_len n m k c v c' v' Y Hk4 HY).
  Qed.

  Lemma TN_real : RealT p q O Ch K (menu TN) (S_T TN).
  Proof.
    split.
    - exists TN. split; [split; [exact TN_observer|]|].
      + intros t Ht. unfold tags in Ht. apply list_elem_of_fmap in Ht as ([k x] & -> & Hin).
        exact (TG_tag k x (proj1 (proj2 TN_syn) _ Hin)).
      + split; [|split; [done|split; [done|split]]].
        * intros n [[k c] v] Hpl HS. assert (HST : Sx n = false).
          { destruct (Sx n) eqn:E; [|done]. rewrite (tn_S_up VL reps wrapb Hnd T f0 T_len n E) in HS. discriminate HS. }
          rewrite (HO n _ Hpl HST). symmetry. exact (tn_O VL reps wrapb Hnd T f0 T_len n k c v HS).
        * intros c Hc. apply HCh. exact (proj1 (proj2 (proj2 TN_syn)) c Hc).
        * intros k x Hin. exact (TG_kind k x (proj1 (proj2 TN_syn) _ Hin)).
    - intros n o Hm. destruct (tn_menu_any VL reps wrapb Hnd T f0 T_len n o Hm) as [HM|[Hin|(n0 & HM)]].
      + exact (HokT n o HM).
      + exact (rep_ok _ o Hin).
      + exact (HokT n0 o HM).
  Qed.

  Lemma Hr0 : run_word (M := lq_menu O) (menu T) Sx (r 0) r w.
  Proof. split; [done|apply Hrun]. Qed.

  Lemma Hi0 : ∀ x, x ∈ r 0 → visited_ok (M := lq_menu O) (menu T) (mnode (MenuSts := lq_menu O) x.1).
  Proof. rewrite (proj1 Hrun). apply init_visited. intros x ->%list_elem_of_singleton. done. Qed.

  Lemma HrU : run_word (M := lq_menu O) U Sx (r 0) r w.
  Proof. exact (run_cells (M := lq_menu O) (menu T) Sx r w Hr0 Hi0 Hnz). Qed.

  Lemma HiU : ∀ x, x ∈ r 0 → visited_ok (M := lq_menu O) U (mnode (MenuSts := lq_menu O) x.1).
  Proof. rewrite (proj1 Hrun). apply init_visited. intros x ->%list_elem_of_singleton. done. Qed.

  Lemma q_vis i x : x ∈ r i → visited_ok (M := lq_menu O) U x.1.1.
  Proof. exact (visited_run (M := lq_menu O) U Sx r w HrU HiU i x). Qed.

  Lemma q_plain i x : x ∈ r i → plain x.1.1.
  Proof.
    apply (run_inv (mdlts (M := lq_menu O) (menu T) Sx) (λ c, plain c.1)) with (D := dinit O q).
    - intros ρ c σ Δ Hp Hs y Hy. exact (cstep_plain _ _ _ _ _ _ Hs Hp y Hy).
    - exact (run_word_is_run (M := lq_menu O) _ _ _ r w Hrun).
    - intros y ->%list_elem_of_singleton. intros k c v Hin. by apply elem_of_nil in Hin.
  Qed.

  Lemma clean_node n : plain n → visited_ok (M := lq_menu O) U n → ¬ wpath wrapb T n ∧ ¬ rpath reps n.
  Proof.
    intros Hpl Hv. split.
    - intros (m & a & m2 & E & Ha & Hw & _). subst n. rewrite nout_plain in Hw by (exact (plain_app_l _ _ Hpl)).
      apply (HW1 m _ Hw). exact (Hv m a m2 eq_refl).
    - intros (m & a & m2 & E & Ha & Hin). subst n. rewrite nout_plain in Hin by (exact (plain_app_l _ _ Hpl)).
      destruct (HR2 m _ Hin) as [_ HnM]. apply HnM. apply (U_menu q T O r w Hrun). exact (Hv m a m2 eq_refl).
  Qed.

  Lemma clean_S n : ¬ wpath wrapb T n → ¬ rpath reps n → S_T TN n = Sx n.
  Proof.
    intros Hw Hr. apply eq_true_iff_eq. split.
    - intros HS. destruct (tn_S_cases VL reps wrapb Hnd T f0 T_len n HS) as [Hc|[Hc|Hc]]; done.
    - exact (tn_S_up VL reps wrapb Hnd T f0 T_len n).
  Qed.

  Lemma q_S i c ρ : (c, ρ) ∈ r i → S_T TN c.1 = Sx c.1.
  Proof.
    intros Hin. destruct (clean_node c.1 (q_plain i (c, ρ) Hin) (q_vis i (c, ρ) Hin)) as [Hw Hr]. by apply clean_S.
  Qed.

  Lemma q_run : is_run (SchedSts0 := STN) Stay (dinit O q) r.
  Proof.
    apply (run_word_is_run (M := lq_menu O) _ _ _ r w). split; [exact (proj1 Hrun)|].
    refine (proj2 (run_sandwich (M := lq_menu O) Ok U Sx r w HrU (menu TN) (S_T TN) _ _ _)).
    - intros i c ρ Hin. exact (q_S i c ρ Hin).
    - intros i c ρ o Hin HS HU. assert (HSN : S_T TN c.1 = false) by (rewrite (q_S i c ρ Hin); exact HS).
      apply (proj1 (tn_menu_low VL reps wrapb Hnd T f0 T_len c.1 o HSN)). exact (U_menu q T O r w Hrun _ o HU).
    - intros i c ρ o Hin HS Hm. assert (HSN : S_T TN c.1 = false) by (rewrite (q_S i c ρ Hin); exact HS).
      destruct (proj2 (tn_menu_low VL reps wrapb Hnd T f0 T_len c.1 o HSN) Hm) as [HM|Hin'].
      + exact (menu_star p q T Ch K O r w Hrun Hnz HokT _ o HM).
      + rewrite nout_plain in Hin' by (exact (q_plain i (c, ρ) Hin)).
        exact (J0_sub p q T Ch K O r w F Mo Hrun Hnz HokT _ o (proj1 (HR2 _ o Hin'))).
  Qed.

  Lemma q_Sstar i c ρ : (c, ρ) ∈ r i → S_T TN c.1 = Ss c.1.
  Proof.
    intros Hin. rewrite (q_S i c ρ Hin). symmetry.
    exact (Sstar_visited (M := lq_menu O) Ok U Sx r w HrU HiU i c ρ Hin).
  Qed.

  Lemma np_cause n : LV (n) → plain n → Sx n = false → ¬ pcause VL T f0 n.
  Proof.
    intros Hin Hpl HS [Hf|[Hs|(a & Ha & Hu)]].
    - rewrite nout_plain in Hf by done. pose proof (Hf0 n Hin). lia.
    - congruence.
    - exact (HVL n a Hin Ha Hu).
  Qed.

  Lemma p_succ n : LV (n) → plain n → visited_ok (M := lq_menu O) (menu TN) n → (S_T TN n = true ↔ Ss n = true).
  Proof.
    intros Hin Hpl Hv. split.
    - intros HS. destruct (tn_S_cases VL reps wrapb Hnd T f0 T_len n HS)
        as [Hc|[(m & a & m2 & E & Ha & Hw & HTne)|(m & a & m2 & E & Ha & Hr)]].
      + by apply Sstar_S.
      + apply Sstar_crossed. subst n. exists m, a, m2. split; [done|].
        rewrite nout_plain in Hw by (exact (plain_app_l _ _ Hpl)). split.
        * apply (menu_star p q T Ch K O r w Hrun Hnz HokT). by apply step_menu.
        * exact (HW1 m _ Hw).
      + apply Sstar_crossed. subst n. exists m, a, m2. split; [done|].
        rewrite nout_plain in Hr by (exact (plain_app_l _ _ Hpl)). destruct (HR2 m _ Hr) as [HJ HnM]. split.
        * exact (J0_sub p q T Ch K O r w F Mo Hrun Hnz HokT m _ HJ).
        * intros HU. apply HnM. exact (U_menu q T O r w Hrun m _ HU).
    - intros HS. apply Sstar_inv in HS as [HS|(m & a & m2 & E & HJ & HnU)];
        [exact (tn_S_up VL reps wrapb Hnd T f0 T_len n HS)|].
      destruct (Sx n) eqn:EST; [exact (tn_S_up VL reps wrapb Hnd T f0 T_len n EST)|].
      assert (E' : n = (m ++ [a]) ++ m2) by (rewrite E; by rewrite <- app_assoc).
      assert (HinP : LV (m ++ [a])) by (apply (HLVp _ m2); by rewrite <- E').
      assert (HplP : plain (m ++ [a])) by (apply (plain_app_l _ m2); by rewrite <- E').
      assert (HSP : Sx (m ++ [a]) = false).
      { destruct (Sx (m ++ [a])) eqn:E2; [|done]. pose proof (S_T_app T _ m2 E2) as Hx. rewrite <- E' in Hx. congruence. }
      assert (Ha : ∀ k c v, a ≠ CoOut k c v).
      { intros k c v ->. apply (HplP k c v). apply elem_of_app. right. by left. }
      assert (HneN : tnodes TN (m ++ [a]) ≠ []) by (apply menu_step; exact (Hv m a m2 E)).
      rewrite E'. destruct (tnodes T (m ++ [a])) as [|X lx] eqn:ET.
      + exact (succ_prefix TN _ m2 (tn_rep_succ VL reps wrapb Hnd T f0 T_len (m ++ [a]) ET HneN)).
      + apply succ_prefix. apply (tn_wrap_succ VL reps wrapb Hnd T f0 T_len m a Ha);
          [|by rewrite ET|done|exact (np_cause _ HinP HplP HSP)].
        rewrite nout_plain by (exact (plain_app_l _ _ HplP)). apply (HW2 m); [exact (HLVp m [a] HinP)| |exact HnU].
        apply step_menu. by rewrite ET.
  Qed.

  Lemma p_steps n ρ P C E :
    LV (n) → plain n → visited_ok (M := lq_menu O) (menu TN) n →
    (∀ t ch v P', prog_step P (CTag t) (ActExt (PrOut ch v)) P' → CL ch) → S_T TN n = false →
    ∀ σ Δ, cstep (menu TN) O ρ (n, (P, C, E)) σ Δ ↔ cstep J0 O ρ (n, (P, C, E)) σ Δ.
  Proof.
    intros Hin Hpl Hv HCLc HS σ Δ.
    assert (HST : Sx n = false).
    { destruct (Sx n) eqn:E0; [|done]. rewrite (tn_S_up VL reps wrapb Hnd T f0 T_len n E0) in HS. discriminate HS. }
    assert (Hne : tnodes TN n ≠ []).
    { clear -Hv. destruct n as [|a m _] using rev_ind; [done|]. apply menu_step. exact (Hv m a [] eq_refl). }
    assert (Heq : ∀ o, relevant (n, (P, C, E)) o → (menu TN n o ↔ J0 n o)).
    { intros o Hrel. rewrite (tn_menu_head VL reps wrapb Hnd T f0 T_len n o HS (np_cause n Hin Hpl HST) Hne).
      rewrite nout_plain by done. split.
      - intros [HM|[Hin' _]]; [by left|exact (proj1 (HR2 n o Hin'))].
      - intros HJ. destruct (classic (menu T n o)) as [HM|HnM]; [by left|right]. split.
        + apply HR3; try done. intros k ch ->. destruct Hrel as (t & v & P' & Hp). exact (HCLc t ch v P' Hp).
        + intros k c v ->. exact Hrel. }
    split; apply cstep_menu_eq; intros o Hrel; apply (Heq o Hrel).
  Qed.

  Definition goodc (x : comp * weight) : Prop :=
    LV (x.1.1) ∧ plain x.1.1 ∧ visited_ok (M := lq_menu O) (menu TN) x.1.1
    ∧ ∀ t ch v P', prog_step x.1.2.1.1 (CTag t) (ActExt (PrOut ch v)) P' → CL ch.

  Lemma p_agree (D : dist comp) : (∀ x, x ∈ D → goodc x) → agree_on STN SJ0 D.
  Proof.
    intros HD c ρ Hin. destruct (HD (c, ρ) Hin) as (Hg1 & Hg2 & Hg3 & Hg4). split; [exact (p_succ c.1 Hg1 Hg2 Hg3)|].
    intros Hns σ Δ. destruct c as [n [[P C] E]]. apply p_steps; try done.
    destruct (S_T TN n) eqn:E0; [by destruct Hns|done].
  Qed.

  Fixpoint reach (k : nat) (D : dist comp) : Prop :=
    match k with
    | 0 => D = dinit O p
    | S k => ∃ D0, reach k D0 ∧ rstep SJ0 D0 D
    end.

  Hypothesis HLV : ∀ k D x, k ≤ N → reach k D → x ∈ D → LV (x.1.1).
  Hypothesis HCL : ∀ k D x t ch v P', k ≤ N → reach k D → x ∈ D →
    prog_step x.1.2.1.1 (CTag t) (ActExt (PrOut ch v)) P' → CL ch.

  Theorem p_good r0 : is_run (SchedSts0 := STN) Stay (dinit O p) r0 →
    ∀ i, i ≤ N → agree_on STN SJ0 (r0 i).
  Proof.
    intros Hrun0.
    assert (Hpl : ∀ i x, x ∈ r0 i → plain x.1.1).
    { apply (run_inv STN (λ c, plain c.1)) with (D := dinit O p); [|done|].
      - intros ρ c σ Δ Hp Hs y Hy. exact (cstep_plain _ _ _ _ _ _ Hs Hp y Hy).
      - intros y ->%list_elem_of_singleton. intros k c v Hin. by apply elem_of_nil in Hin. }
    assert (Hvis : ∀ i x, x ∈ r0 i → visited_ok (M := lq_menu O) (menu TN) x.1.1).
    { apply (run_inv STN (λ c, visited_ok (M := lq_menu O) (menu TN) c.1)) with (D := dinit O p); [|done|].
      - intros ρ c σ Δ Hv Hs y Hy. exact (visited_step (M := lq_menu O) (menu TN) ρ c σ Δ y Hv Hs Hy).
      - intros y ->%list_elem_of_singleton. intros m a m2 E. by destruct m. }
    assert (Hag : ∀ i, i ≤ N → reach i (r0 i) → agree_on STN SJ0 (r0 i)).
    { intros i Hi Hre. apply p_agree. intros x Hx. split; [exact (HLV i _ x Hi Hre Hx)|].
      split; [exact (Hpl i x Hx)|]. split; [exact (Hvis i x Hx)|].
      intros t ch v P' Hp. exact (HCL i _ x t ch v P' Hi Hre Hx Hp). }
    assert (Hre : ∀ i, i ≤ N → reach i (r0 i)).
    { induction i as [|i IH]; intros Hi; [exact (proj1 Hrun0)|].
      assert (Hi' : i ≤ N) by lia. exists (r0 i). split; [exact (IH Hi')|].
      destruct (proj2 Hrun0 i) as [(σ & Hs)|[Hst E]].
      - left. exists σ. exact (agree_dstep _ _ Stay _ σ _ (Hag i Hi' (IH Hi')) Hs).
      - right. split; [exact (agree_dstable _ _ _ (Hag i Hi' (IH Hi')) Hst)|done]. }
    intros i Hi. exact (Hag i Hi (Hre i Hi)).
  Qed.
End Asm.
(* end hide *)
