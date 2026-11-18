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
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Branching lqCCS.Testing.Truncation lqCCS.Testing.Pull lqCCS.Testing.Head lqCCS.Testing.Modes lqCCS.Testing.Syn.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Assembly.
  Context `{lqP : lqCCS_Parameters}.

Lemma co_succ_offer X a a' : offer_of a = offer_of a' → co_succ X a = [] → co_succ X a' = [].
Proof.
  intros Ho. induction X as [t c e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t P IHP|g]; simpl.
  - destruct a, a'; simpl in *; try done; inversion Ho; subst; done.
  - destruct (eval e) as [[[]| |]|]; done.
  - intros E. apply app_eq_nil in E as [E1 E2]. apply fmap_nil_inv in E1. apply fmap_nil_inv in E2.
    by rewrite (IHP E1), (IHQ E2).
  - done.
  - done.
  - destruct a, a'; simpl in *; try done; inversion Ho; subst; done.
  - rewrite !gco_heads. by apply omap_nil_offer.
Qed.

Lemma menu_step T z' a : menu T z' (offer_of a) → tnodes T (z' ++ [a]) ≠ [].
Proof.
  intros (T' & a' & HT' & Eo & Hne). destruct (co_succ T' a) as [|T'' l] eqn:E.
  - exfalso. apply Hne. by apply (co_succ_offer T' a a').
  - intros Enil. assert (Hin : T'' ∈ tnodes T (z' ++ [a])).
    { apply tnodes_app_elem. exists T'. split; [done|]. rewrite E. by left. }
    rewrite Enil in Hin. by apply elem_of_nil in Hin.
Qed.

Lemma step_menu T z' a : tnodes T (z' ++ [a]) ≠ [] → menu T z' (offer_of a).
Proof.
  intros Hne. destruct (tnodes T (z' ++ [a])) as [|T'' l] eqn:E; [done|].
  assert (Hin : T'' ∈ tnodes T (z' ++ [a])) by (rewrite E; by left).
  apply tnodes_app_elem in Hin as (T' & HT' & Hin). exists T', a. split; [done|]. split; [done|].
  intros En. rewrite En in Hin. by apply elem_of_nil in Hin.
Qed.

Lemma plain_app_l (z' l : node) : plain (z' ++ l) → plain z'.
Proof. intros Hp t c v Hin. apply (Hp t c v). apply elem_of_app. by left. Qed.

Lemma nout_plain (z : list coact) : plain z → nout z = z.
Proof.
  induction z as [|a z IH]; intros Hp; [done|].
  assert (Ha : isout a = false).
  { destruct a; try done. exfalso. apply (Hp t c v). by left. }
  unfold nout in *. rewrite list.filter_cons_True by exact Ha. f_equal. apply IH.
  intros t c v Hin. apply (Hp t c v). by right.
Qed.

Lemma S_T_app T z l : S_T T z = true → S_T T (z ++ l) = true.
Proof.
  intros Hs. induction l as [|a l IH] using rev_ind; [by rewrite app_nil_r|]. rewrite app_assoc. by apply S_T_ext.
Qed.

Lemma succ_prefix T z' l : succ_at T z' = true → S_T T (z' ++ l) = true.
Proof. intros Hs. apply S_T_app. by apply succ_at_S. Qed.

Definition relevant (c : comp) (o : offer) : Prop :=
  match o with
  | OffOut _ _ _ => False
  | OffIn _ ch => ∃ t v P', c.2.1 ⟶ₚ{ch ! v}[{[+ t +]}] P'
  | _ => True
  end.

Lemma cstep_menu_eq `{QM : QuantumModel} I J O ρ c σ Δ :
  (∀ o, relevant c o → I c.1 o → J c.1 o) → cstep I O ρ c σ Δ → cstep J O ρ c σ Δ.
Proof.
  intros Hrel Hs.
  apply cstep_cases in Hs. inversion Hs as [z P C k Δ0 Hss|z P C t d v t' P' Hin HkC Hp|z P C t d v t' P' HI Hp
                  |z P C t U' qs t' HI|z P C t q t' HI|z P C t M qs t' HI|z P C t t' HI]; subst; simpl in *.
  - by constructor.
  - by apply cs_recv.
  - apply cs_in; [|done]. apply Hrel; [|done]. by exists t', v, P'.
  - apply cs_op. by apply Hrel.
  - apply cs_init. by apply Hrel.
  - apply cs_meas. by apply Hrel.
  - apply cs_unfold. by apply Hrel.
Qed.

Section Asm.
  Context `{QM : QuantumModel} (p q : prog * St) (T : prog) (Ch : channel → Prop) (K : tag → okind).
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
  Hypothesis Hrun : run_word (M := lq_menu O) (menu T) Sx (dinit q) r w.
  Hypothesis Hnz : ∀ n x, x ∈ r n → x.2 ≠ weight_zero.
  Hypothesis HokT : ∀ z o, menu T z o → Ok o.
  Hypothesis HO : ∀ z m, plain z → Sx z = false → (m ∈ O z ↔ m ∈ O_T T z).
  Hypothesis HCh : ∀ c, c ∈ out_chans T → Ch c.
  Hypothesis HK : ∀ t x, (t, x) ∈ tagged T → K t = x.
  Hypothesis Hnd : ∀ z', NoDup (reps z').
  Hypothesis HR2 : ∀ z' o, o ∈ reps z' → J0 z' o ∧ ¬ menu T z' o.
  Hypothesis HR3 : ∀ z' o, LV (z') → J0 z' o → ¬ menu T z' o → (∀ t c, o = OffIn t c → CL c) → o ∈ reps z'.
  Hypothesis HW1 : ∀ z' o, wrapb z' o = true → ¬ U z' o.
  Hypothesis HW2 : ∀ z' o, LV (z') → menu T z' o → ¬ U z' o → wrapb z' o = true.
  Hypothesis HLVp : ∀ z z', LV (z ++ z') → LV (z).
  Hypothesis HVL : ∀ z a, LV (z) → a ∈ z → ¬ unlisted VL a.
  Hypothesis Hf0 : ∀ z, LV (z) → length z < f0.
  Hypothesis HKr : ∀ t, K t ≠ KRec.

  Lemma T_len z : length (tnodes T z) ≤ 1.
  Proof. exact (proj1 (proj2 (proj2 (proj1 HT))) z). Qed.

  Lemma rep_ok z' o : o ∈ reps z' → Ok o.
  Proof.
    intros Hin. destruct (HR2 z' o Hin) as [HJ HnM]. destruct HJ as [HM|[HJ _]]; [done|].
    destruct HJ as [HU|[Hok _]]; [|done]. destruct HnM. exact (U_menu q T O r w Hrun z' o HU).
  Qed.

  Lemma reps_nounf z' t : OffUnfold t ∉ reps z'.
  Proof. intros Hin. destruct (rep_ok z' _ Hin) as (Hty & _). unfold typed in Hty. simpl in Hty. apply (HKr t). congruence. Qed.

  Lemma T_ob : obsb T = true.
  Proof. exact (proj1 (proj1 (proj1 HT))). Qed.

  Definition TG (x : tag * okind) : Prop := x ∈ tagged T ∨ ∃ z' o, o ∈ reps z' ∧ x = (off_tag o, off_kind o).
  Definition OC (c : channel) : Prop := c ∈ out_chans T.
  Definition IC (c : channel) : Prop := c ∈ in_chans T ∨ ∃ z' t, OffIn t c ∈ reps z'.

  Lemma TN_syn : syn TG OC IC TN.
  Proof.
    apply tn_syn.
    - intros z' o Hin. split; [right; by exists z', o|]. intros t c ->. right. by exists z', t.
    - split; [exact (proj1 (proj1 (proj1 HT)))|]. split; [intros x Hx; by left|].
      split; [intros c Hc; exact Hc|intros c Hc; by left].
  Qed.

  Lemma TG_kind t x : TG (t, x) → K t = x.
  Proof.
    intros [Hin|(z' & o & Hin & E)]; [exact (HK t x Hin)|]. injection E as -> ->.
    destruct (rep_ok z' o Hin) as (Hty & _). symmetry. exact Hty.
  Qed.

  Lemma TG_tag t x : TG (t, x) → t ∉ otags p.1 ∧ t ∉ otags q.1.
  Proof.
    intros [Hin|(z' & o & Hin & E)].
    - apply (proj2 HT). unfold tags. apply list_elem_of_fmap. by exists (t, x).
    - injection E as -> ->. destruct (rep_ok z' o Hin) as (_ & Hp & Hq & _). done.
  Qed.

  Lemma TN_observer : observer TN.
  Proof.
    destruct TN_syn as (Hob & Htg & Hoc & Hic). destruct HT as [(Hobs & Hk2 & Hk3 & Hk4) Htags].
    split; [split; [done|]|split; [|split]].
    - intros c Hc Hc'. destruct (Hic c Hc') as [Hin|(z' & t & Hin)].
      + exact (proj2 Hobs c (Hoc c Hc) Hin).
      + destruct (rep_ok z' _ Hin) as (_ & _ & _ & Hch). exact (Hch t c eq_refl (HCh c (Hoc c Hc))).
    - intros t x y Hx Hy. rewrite <- (TG_kind t x (Htg _ Hx)). exact (TG_kind t y (Htg _ Hy)).
    - exact (tn_len VL reps wrapb Hnd reps_nounf T f0 T_len T_ob).
    - intros z z' t c v c' v' Y HY. exact (tn_gone VL reps wrapb Hnd reps_nounf T f0 T_len T_ob z z' t c v c' v' Y Hk4 HY).
  Qed.

  Lemma TN_real : RealT p q O Ch K (menu TN) (S_T TN).
  Proof.
    split.
    - exists TN. split; [split; [exact TN_observer|]|].
      + intros t' Ht. unfold tags in Ht. apply list_elem_of_fmap in Ht as ([t x] & -> & Hin).
        exact (TG_tag t x (proj1 (proj2 TN_syn) _ Hin)).
      + split; [|split; [done|split; [done|split]]].
        * intros z [[t c] v] Hpl HS. assert (HST : Sx z = false).
          { destruct (Sx z) eqn:E; [|done]. rewrite (tn_S_up VL reps wrapb Hnd reps_nounf T f0 T_len T_ob z E) in HS. discriminate HS. }
          rewrite (HO z _ Hpl HST). symmetry. exact (tn_O VL reps wrapb Hnd reps_nounf T f0 T_len T_ob z t c v HS).
        * intros c Hc. apply HCh. exact (proj1 (proj2 (proj2 TN_syn)) c Hc).
        * intros t x Hin. exact (TG_kind t x (proj1 (proj2 TN_syn) _ Hin)).
    - intros z o Hm. destruct (tn_menu_any VL reps wrapb Hnd reps_nounf T f0 T_len T_ob z o Hm) as [HM|[Hin|(n0 & HM)]].
      + exact (HokT z o HM).
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

  Lemma q_vis n x : x ∈ r n → visited_ok (M := lq_menu O) U x.1.1.
  Proof. exact (visited_run (M := lq_menu O) U Sx r w HrU HiU n x). Qed.

  Lemma q_plain n x : x ∈ r n → plain x.1.1.
  Proof.
    apply (run_inv (mdlts (M := lq_menu O) (menu T) Sx) (λ c, plain c.1)) with (D := dinit q).
    - intros ρ c σ Δ Hp Hs y Hy. exact (cstep_plain _ _ _ _ _ _ Hs Hp y Hy).
    - exact (run_word_is_run (M := lq_menu O) _ _ _ r w Hrun).
    - intros y ->%list_elem_of_singleton. intros t c v Hin. by apply elem_of_nil in Hin.
  Qed.

  Lemma clean_node z : plain z → visited_ok (M := lq_menu O) U z → ¬ wpath wrapb T z ∧ ¬ rpath reps z.
  Proof.
    intros Hpl Hv. split.
    - intros (z' & a & z2 & E & Ha & Hw & _). subst z. rewrite nout_plain in Hw by (exact (plain_app_l _ _ Hpl)).
      apply (HW1 z' _ Hw). exact (Hv z' a z2 eq_refl).
    - intros (z' & a & z2 & E & Ha & Hin). subst z. rewrite nout_plain in Hin by (exact (plain_app_l _ _ Hpl)).
      destruct (HR2 z' _ Hin) as [_ HnM]. apply HnM. apply (U_menu q T O r w Hrun). exact (Hv z' a z2 eq_refl).
  Qed.

  Lemma clean_S z : ¬ wpath wrapb T z → ¬ rpath reps z → S_T TN z = Sx z.
  Proof.
    intros Hw Hr. apply eq_true_iff_eq. split.
    - intros HS. destruct (tn_S_cases VL reps wrapb Hnd reps_nounf T f0 T_len T_ob z HS) as [Hc|[Hc|Hc]]; done.
    - exact (tn_S_up VL reps wrapb Hnd reps_nounf T f0 T_len T_ob z).
  Qed.

  Lemma q_S n c ρ : (c, ρ) ∈ r n → S_T TN c.1 = Sx c.1.
  Proof.
    intros Hin. destruct (clean_node c.1 (q_plain n (c, ρ) Hin) (q_vis n (c, ρ) Hin)) as [Hw Hr]. by apply clean_S.
  Qed.

  Lemma q_run : is_run (SchedSts0 := STN) Stay (dinit q) r.
  Proof.
    apply (run_word_is_run (M := lq_menu O) _ _ _ r w). split; [exact (proj1 Hrun)|].
    refine (proj2 (run_sandwich (M := lq_menu O) Ok U Sx r w HrU (menu TN) (S_T TN) _ _ _)).
    - intros n c ρ Hin. exact (q_S n c ρ Hin).
    - intros n c ρ o Hin HS HU. assert (HSN : S_T TN c.1 = false) by (rewrite (q_S n c ρ Hin); exact HS).
      apply (proj1 (tn_menu_low VL reps wrapb Hnd reps_nounf T f0 T_len T_ob c.1 o HSN)). exact (U_menu q T O r w Hrun _ o HU).
    - intros n c ρ o Hin HS Hm. assert (HSN : S_T TN c.1 = false) by (rewrite (q_S n c ρ Hin); exact HS).
      destruct (proj2 (tn_menu_low VL reps wrapb Hnd reps_nounf T f0 T_len T_ob c.1 o HSN) Hm) as [HM|Hin'].
      + exact (menu_star p q T Ch K O r w Hrun Hnz HokT _ o HM).
      + rewrite nout_plain in Hin' by (exact (q_plain n (c, ρ) Hin)).
        exact (J0_sub p q T Ch K O r w F Mo Hrun Hnz HokT _ o (proj1 (HR2 _ o Hin'))).
  Qed.

  Lemma q_Sstar n c ρ : (c, ρ) ∈ r n → S_T TN c.1 = Ss c.1.
  Proof.
    intros Hin. rewrite (q_S n c ρ Hin). symmetry.
    exact (Sstar_visited (M := lq_menu O) Ok U Sx r w HrU HiU n c ρ Hin).
  Qed.

  Lemma np_cause z : LV (z) → plain z → Sx z = false → ¬ pcause VL T f0 z.
  Proof.
    intros Hin Hpl HS [Hf|[Hs|(a & Ha & Hu)]].
    - rewrite nout_plain in Hf by done. pose proof (Hf0 z Hin). lia.
    - congruence.
    - exact (HVL z a Hin Ha Hu).
  Qed.

  Lemma p_succ z : LV (z) → plain z → visited_ok (M := lq_menu O) (menu TN) z → (S_T TN z = true ↔ Ss z = true).
  Proof.
    intros Hin Hpl Hv. split.
    - intros HS. destruct (tn_S_cases VL reps wrapb Hnd reps_nounf T f0 T_len T_ob z HS)
        as [Hc|[(z' & a & z2 & E & Ha & Hw & HTne)|(z' & a & z2 & E & Ha & Hr)]].
      + by apply Sstar_S.
      + apply Sstar_crossed. subst z. exists z', a, z2. split; [done|].
        rewrite nout_plain in Hw by (exact (plain_app_l _ _ Hpl)). split.
        * apply (menu_star p q T Ch K O r w Hrun Hnz HokT). by apply step_menu.
        * exact (HW1 z' _ Hw).
      + apply Sstar_crossed. subst z. exists z', a, z2. split; [done|].
        rewrite nout_plain in Hr by (exact (plain_app_l _ _ Hpl)). destruct (HR2 z' _ Hr) as [HJ HnM]. split.
        * exact (J0_sub p q T Ch K O r w F Mo Hrun Hnz HokT z' _ HJ).
        * intros HU. apply HnM. exact (U_menu q T O r w Hrun z' _ HU).
    - intros HS. apply Sstar_inv in HS as [HS|(z' & a & z2 & E & HJ & HnU)];
        [exact (tn_S_up VL reps wrapb Hnd reps_nounf T f0 T_len T_ob z HS)|].
      destruct (Sx z) eqn:EST; [exact (tn_S_up VL reps wrapb Hnd reps_nounf T f0 T_len T_ob z EST)|].
      assert (E' : z = (z' ++ [a]) ++ z2) by (rewrite E; by rewrite <- app_assoc).
      assert (HinP : LV (z' ++ [a])) by (apply (HLVp _ z2); by rewrite <- E').
      assert (HplP : plain (z' ++ [a])) by (apply (plain_app_l _ z2); by rewrite <- E').
      assert (HSP : Sx (z' ++ [a]) = false).
      { destruct (Sx (z' ++ [a])) eqn:E2; [|done]. pose proof (S_T_app T _ z2 E2) as Hx. rewrite <- E' in Hx. congruence. }
      assert (Ha : ∀ t c v, a ≠ CoOut t c v).
      { intros t c v ->. apply (HplP t c v). apply elem_of_app. right. by left. }
      assert (HneN : tnodes TN (z' ++ [a]) ≠ []) by (apply menu_step; exact (Hv z' a z2 E)).
      rewrite E'. destruct (tnodes T (z' ++ [a])) as [|X lx] eqn:ET.
      + exact (succ_prefix TN _ z2 (tn_rep_succ VL reps wrapb Hnd reps_nounf T f0 T_len T_ob (z' ++ [a]) ET HneN)).
      + apply succ_prefix. apply (tn_wrap_succ VL reps wrapb Hnd reps_nounf T f0 T_len T_ob z' a Ha);
          [|by rewrite ET|done|exact (np_cause _ HinP HplP HSP)].
        rewrite nout_plain by (exact (plain_app_l _ _ HplP)). apply (HW2 z'); [exact (HLVp z' [a] HinP)| |exact HnU].
        apply step_menu. by rewrite ET.
  Qed.

  Lemma p_steps z ρ P C :
    LV (z) → plain z → visited_ok (M := lq_menu O) (menu TN) z →
    (∀ t' ch v P', P ⟶ₚ{ch ! v}[{[+ t' +]}] P' → CL ch) → S_T TN z = false →
    ∀ σ Δ, cstep (menu TN) O ρ (z, (P, C)) σ Δ ↔ cstep J0 O ρ (z, (P, C)) σ Δ.
  Proof.
    intros Hin Hpl Hv HCLc HS σ Δ.
    assert (HST : Sx z = false).
    { destruct (Sx z) eqn:E0; [|done]. rewrite (tn_S_up VL reps wrapb Hnd reps_nounf T f0 T_len T_ob z E0) in HS. discriminate HS. }
    assert (Hne : tnodes TN z ≠ []).
    { clear -Hv. destruct z as [|a z' _] using rev_ind; [done|]. apply menu_step. exact (Hv z' a [] eq_refl). }
    assert (Heq : ∀ o, relevant (z, (P, C)) o → (menu TN z o ↔ J0 z o)).
    { intros o Hrel. rewrite (tn_menu_head VL reps wrapb Hnd reps_nounf T f0 T_len T_ob z o HS (np_cause z Hin Hpl HST) Hne).
      rewrite nout_plain by done. split.
      - intros [HM|[Hin' _]]; [by left|exact (proj1 (HR2 z o Hin'))].
      - intros HJ. destruct (classic (menu T z o)) as [HM|HnM]; [by left|right]. split.
        + apply HR3; try done. intros t ch ->. destruct Hrel as (t' & v & P' & Hp). exact (HCLc t' ch v P' Hp).
        + intros t c v ->. exact Hrel. }
    split; apply cstep_menu_eq; intros o Hrel; apply (Heq o Hrel).
  Qed.

  Definition goodc (x : comp * weight) : Prop :=
    LV (x.1.1) ∧ plain x.1.1 ∧ visited_ok (M := lq_menu O) (menu TN) x.1.1
    ∧ ∀ t ch v P', x.1.2.1 ⟶ₚ{ch ! v}[{[+ t +]}] P' → CL ch.

  Lemma p_agree (D : dist comp) : (∀ x, x ∈ D → goodc x) → agree_on STN SJ0 D.
  Proof.
    intros HD c ρ Hin. destruct (HD (c, ρ) Hin) as (Hg1 & Hg2 & Hg3 & Hg4). split; [exact (p_succ c.1 Hg1 Hg2 Hg3)|].
    intros Hns σ Δ. destruct c as [z [P C]]. apply p_steps; try done.
    destruct (S_T TN z) eqn:E0; [by destruct Hns|done].
  Qed.

  Fixpoint reach (n : nat) (D : dist comp) : Prop :=
    match n with
    | 0 => D = dinit p
    | S n => ∃ D0, reach n D0 ∧ rstep SJ0 D0 D
    end.

  Hypothesis HLV : ∀ n D x, n ≤ N → reach n D → x ∈ D → LV (x.1.1).
  Hypothesis HCL : ∀ n D x t ch v P', n ≤ N → reach n D → x ∈ D →
    x.1.2.1 ⟶ₚ{ch ! v}[{[+ t +]}] P' → CL ch.

  Theorem p_good r0 : is_run (SchedSts0 := STN) Stay (dinit p) r0 →
    ∀ n, n ≤ N → agree_on STN SJ0 (r0 n).
  Proof.
    intros Hrun0.
    assert (Hpl : ∀ n x, x ∈ r0 n → plain x.1.1).
    { apply (run_inv STN (λ c, plain c.1)) with (D := dinit p); [|done|].
      - intros ρ c σ Δ Hp Hs y Hy. exact (cstep_plain _ _ _ _ _ _ Hs Hp y Hy).
      - intros y ->%list_elem_of_singleton. intros t c v Hin. by apply elem_of_nil in Hin. }
    assert (Hvis : ∀ n x, x ∈ r0 n → visited_ok (M := lq_menu O) (menu TN) x.1.1).
    { apply (run_inv STN (λ c, visited_ok (M := lq_menu O) (menu TN) c.1)) with (D := dinit p); [|done|].
      - intros ρ c σ Δ Hv Hs y Hy. exact (visited_step (M := lq_menu O) (menu TN) ρ c σ Δ y Hv Hs Hy).
      - intros y ->%list_elem_of_singleton. intros z' a z2 E. by destruct z'. }
    assert (Hag : ∀ n, n ≤ N → reach n (r0 n) → agree_on STN SJ0 (r0 n)).
    { intros n Hi Hre. apply p_agree. intros x Hx. split; [exact (HLV n _ x Hi Hre Hx)|].
      split; [exact (Hpl n x Hx)|]. split; [exact (Hvis n x Hx)|].
      intros t' ch v P' Hp. exact (HCL n _ x t' ch v P' Hi Hre Hx Hp). }
    assert (Hre : ∀ n, n ≤ N → reach n (r0 n)).
    { induction n as [|n IH]; intros Hi; [exact (proj1 Hrun0)|].
      assert (Hi' : n ≤ N) by lia. exists (r0 n). split; [exact (IH Hi')|].
      destruct (proj2 Hrun0 n) as [(σ & Hs)|[Hst E]].
      - left. exists σ. exact (agree_dstep _ _ Stay _ σ _ (Hag n Hi' (IH Hi')) Hs).
      - right. split; [exact (agree_dstable _ _ _ (Hag n Hi' (IH Hi')) Hst)|done]. }
    intros n Hi. exact (Hag n Hi (Hre n Hi)).
  Qed.
End Asm.

End Assembly.

(* end hide *)
