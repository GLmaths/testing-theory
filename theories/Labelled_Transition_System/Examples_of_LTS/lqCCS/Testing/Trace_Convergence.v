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
From Stdlib.Logic Require Import Classical.
From Stdlib Require Import Lia.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_scheduled pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Final lqCCS.Testing.Trace lqCCS.Testing.Trace_Complete lqCCS.Testing.Trace_Sound.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section SN.
  Context `{Weights} {C Sch : Type} (SS : SchedSts C Sch) (μ : C → nat) (Inv : C → Prop).
  Hypothesis Hμ : ∀ ρ c σ Δ, Inv c → ¬ psuccess c → sstep ρ c σ Δ → ∀ y, y ∈ Δ → μ y.1 < μ c ∧ Inv y.1.

  Inductive SN : dist C → Prop :=
  | SN_intro D : (∀ σ D', dstep Stay D σ D' → SN D') → SN D.

  Lemma no_move (D : dist C) σ Δs :
    Forall2 (λ cρ Δ, comp_step Stay cρ.2 cρ.1 σ Δ) D Δs → ¬ dmoves D σ → dsum Δs = D.
  Proof.
    induction 1 as [|[c ρ] Δ D Δs Hc _ IH]; intros Hn; [done|]. change (dsum (Δ :: Δs)) with (Δ ++ dsum Δs).
    destruct Hc as [(Hns & Hs)|(_ & ->)].
    - exfalso. apply Hn. exists c, ρ, Δ. split; [by left|done].
    - simpl. f_equal. apply IH. intros (c' & ρ' & Δ' & Hin & Hr). apply Hn. exists c', ρ', Δ'. split; [by right|done].
  Qed.

  Lemma dstep_app (D1 D2 : dist C) σ D' : dstep Stay (D1 ++ D2) σ D' →
    (∃ D1', D' = D1' ++ D2 ∧ dstep Stay D1 σ D1')
    ∨ (∃ D2', D' = D1 ++ D2' ∧ dstep Stay D2 σ D2')
    ∨ (∃ D1' D2', D' = D1' ++ D2' ∧ dstep Stay D1 σ D1' ∧ dstep Stay D2 σ D2').
  Proof.
    intros (Hm & Δs & HF & ->). apply Forall2_app_inv_l in HF as (Δ1 & Δ2 & HF1 & HF2 & ->).
    assert (E : dsum (Δ1 ++ Δ2) = dsum Δ1 ++ dsum Δ2) by (unfold dsum; by rewrite concat_app).
    rewrite E. destruct (classic (dmoves D1 σ)) as [Hm1|Hm1], (classic (dmoves D2 σ)) as [Hm2|Hm2].
    - right. right. exists (dsum Δ1), (dsum Δ2). split; [done|]. split; (split; [done|]); eauto.
    - left. exists (dsum Δ1). rewrite (no_move D2 σ Δ2 HF2 Hm2). split; [done|]. split; [done|]. eauto.
    - right. left. exists (dsum Δ2). rewrite (no_move D1 σ Δ1 HF1 Hm1). split; [done|]. split; [done|]. eauto.
    - exfalso. destruct Hm as (c & ρ & Δ & Hin & Hr). apply elem_of_app in Hin as [Hin|Hin].
      + apply Hm1. by exists c, ρ, Δ.
      + apply Hm2. by exists c, ρ, Δ.
  Qed.

  Lemma SN_app D1 D2 : SN D1 → SN D2 → SN (D1 ++ D2).
  Proof.
    intros Hs1. revert D2. induction Hs1 as [D1 Hs1 IH1]. intros D2 Hs2. induction Hs2 as [D2 Hs2 IH2].
    constructor. intros σ D' Hd.
    destruct (dstep_app _ _ _ _ Hd) as [(D1' & -> & Hd1)|[(D2' & -> & Hd2)|(D1' & D2' & -> & Hd1 & Hd2)]].
    - apply (IH1 σ D1' Hd1). by constructor.
    - exact (IH2 σ D2' Hd2).
    - exact (IH1 σ D1' Hd1 D2' (Hs2 σ D2' Hd2)).
  Qed.

  Lemma SN_nil : SN [].
  Proof. constructor. intros σ D' ((c & ρ & Δ & Hin & _) & _). by apply elem_of_nil in Hin. Qed.

  Lemma SN_all (Δ : dist C) : (∀ y, y ∈ Δ → SN [y]) → SN Δ.
  Proof.
    induction Δ as [|y Δ IH]; intros Hall; [apply SN_nil|]. change (SN ([y] ++ Δ)). apply SN_app.
    - apply Hall. by left.
    - apply IH. intros z Hz. apply Hall. by right.
  Qed.

  Lemma SN_point m : ∀ c ρ, Inv c → μ c < m → SN [(c, ρ)].
  Proof.
    induction m as [|m IH]; intros c ρ Hi Hlt; [lia|]. constructor. intros σ D' (Hm & Δs & HF & ->).
    inversion HF as [|x Δ l Δs' Hc HF']; subst. inversion HF'; subst.
    change (SN (Δ ++ [])). rewrite app_nil_r. simpl in Hc.
    destruct Hm as (c' & ρ' & Δ' & Hin & Hns & Hs). apply list_elem_of_singleton in Hin. injection Hin as -> ->.
    destruct Hc as [(_ & Hs0)|(Hst & _)].
    - apply SN_all. intros [cy ρy] Hy. destruct (Hμ _ _ _ _ Hi Hns Hs0 _ Hy) as [Hlt' Hi']. simpl in *.
      apply IH; [done|lia].
    - exfalso. destruct Hst as [Hsc|Hno]; [by apply Hns|by apply (Hno Δ')].
  Qed.

  Lemma SN_any (D : dist C) : (∀ x, x ∈ D → Inv x.1) → SN D.
  Proof.
    intros HD. apply SN_all. intros [c ρ] Hin. apply (SN_point (Datatypes.S (μ c))); [exact (HD _ Hin)|lia].
  Qed.

  Lemma sn_stable D r : SN D → is_run Stay D r → ∃ N, dstable (r N).
  Proof.
    intros Hsn. revert r. induction Hsn as [D _ IH]. intros r [E Hr].
    destruct (Hr 0) as [(σ & Hd)|[Hst _]]; [|by exists 0]. rewrite E in Hd.
    destruct (IH σ (r 1) Hd (λ i, r (Datatypes.S i))) as [N HN]; [split; [done|intros n; apply Hr]|].
    by exists (Datatypes.S N).
  Qed.
End SN.

Fixpoint sz (P : proc) : nat :=
  match P with
  | PSend _ _ _ => 1
  | PIte _ P Q | P ∥ Q => sz P + sz Q
  | ν P | PRec _ _ P => sz P
  | PVar _ => 0
  | PG g => gsz g
  end
with gsz (g : guard) : nat :=
  match g with
  | GNil _ | ① => 0
  | 𝜆 ∙ P => Datatypes.S (sz P)
  | (g1 + g2)%lq => gsz g1 + gsz g2
  end.

Fixpoint norec (P : proc) : bool :=
  match P with
  | PSend _ _ _ | PVar _ => true
  | PIte _ P Q | P ∥ Q => norec P && norec Q
  | ν P => norec P
  | PRec _ _ _ => false
  | PG g => gnorec g
  end
with gnorec (g : guard) : bool :=
  match g with
  | GNil _ | ① => true
  | 𝜆 ∙ P => norec P
  | (g1 + g2)%lq => gnorec g1 && gnorec g2
  end.

Lemma sz_subst : (∀ P k v, sz (subst k v P) = sz P) ∧ (∀ g k v, gsz (gsubst k v g) = gsz g).
Proof. apply proc_guard_ind; simpl; intros; congruence. Qed.

Lemma norec_subst : (∀ P k v, norec (subst k v P) = norec P) ∧ (∀ g k v, gnorec (gsubst k v g) = gnorec g).
Proof. apply proc_guard_ind; simpl; intros; congruence. Qed.

Lemma obs_norec : (∀ P, obsb P = true → norec P = true) ∧ (∀ g, gobsb g = true → gnorec g = true).
Proof.
  apply proc_guard_ind; simpl; try done.
  - intros e P IHP Q IHQ [Hp Hq]%andb_prop. by rewrite IHP, IHQ.
  - intros P IHP Q IHQ [Hp Hq]%andb_prop. by rewrite IHP, IHQ.
  - intros 𝜆 P IHP Hob. destruct 𝜆; try done; by apply IHP.
  - intros g1 IH1 g2 IH2 [[Hg1 Hg2]%andb_prop _]%andb_prop. by rewrite IH1, IH2.
Qed.

Lemma gstep_sz g s l P' : gnorec g = true → prog_gstep g s l P' → sz P' < gsz g ∧ norec P' = true.
Proof.
  intros Hn Hs. revert Hn. induction Hs as [| | | | | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs] using prog_gstep_ind; simpl; intros Hn;
    rewrite ?(proj1 sz_subst), ?(proj1 norec_subst); try (split; [lia|done]).
  - apply andb_prop in Hn as [Hn1 Hn2]. destruct (IHHs Hn1). split; [lia|done].
  - apply andb_prop in Hn as [Hn1 Hn2]. destruct (IHHs Hn2). split; [lia|done].
Qed.

Lemma step_sz P s l P' : norec P = true → prog_step P s l P' → sz P' < sz P ∧ norec P' = true.
Proof.
  intros Hn Hs. revert Hn. induction Hs as [? ? ? ? H | ? ? ? ? ? | ? ? ? ? ? ? ? ? IHHs | ? ? ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? IHHs | ? ? ? ? ? ? ? ? ? IHHs1 ? IHHs2 | ? ? ? ? ? ? ? ? ? IHHs1 ? IHHs2 | ? ? ? ? ? IHHs | ? ? ?] using prog_step_guard_ind; simpl; intros Hn.
  - by eapply gstep_sz.
  - split; [lia|done].
  - apply andb_prop in Hn as [Hn1 Hn2]. destruct (IHHs Hn1). split; [lia|done].
  - apply andb_prop in Hn as [Hn1 Hn2]. destruct (IHHs Hn2). split; [lia|done].
  - apply andb_prop in Hn as [Hn1 Hn2]. destruct (IHHs Hn1) as [Hl Hr]. split; [lia|by rewrite Hr, Hn2].
  - apply andb_prop in Hn as [Hn1 Hn2]. destruct (IHHs Hn2) as [Hl Hr]. split; [lia|by rewrite Hr, Hn1].
  - apply andb_prop in Hn as [Hn1 Hn2]. destruct (IHHs1 Hn1) as [Hl1 Hr1], (IHHs2 Hn2) as [Hl2 Hr2].
    split; [lia|by rewrite Hr1, Hr2].
  - apply andb_prop in Hn as [Hn1 Hn2]. destruct (IHHs1 Hn1) as [Hl1 Hr1], (IHHs2 Hn2) as [Hl2 Hr2].
    split; [lia|by rewrite Hr1, Hr2].
  - by apply IHHs.
  - discriminate Hn.
Qed.

Lemma zip_elem {A B X} (R : A → B → Prop) (f : A → B → X) (l : list A) (k : list B) x :
  Forall2 R l k → x ∈ zip_with f l k → ∃ a b, R a b ∧ x = f a b.
Proof.
  induction 1 as [|a b l k Hab _ IH]; simpl; intros Hx; [by apply elem_of_nil in Hx|].
  apply elem_of_cons in Hx as [->|Hx]; [by exists a, b|by apply IH].
Qed.

Lemma sched_sz `{QM : QuantumModel} ρ P s (Δ : list (proc * St)) :
  norec P = true → sched_step ρ P s Δ → ∀ x : proc * St, x ∈ Δ → sz x.1 < sz P ∧ norec x.1 = true.
Proof.
  intros Hn Hs x Hx. inversion Hs as [R' Hp|E qs R' Hp|qs R' Hp|M qs Rs R0 Hp0 Hf]; subst.
  - apply list_elem_of_singleton in Hx. subst x. exact (step_sz _ _ _ _ Hn Hp).
  - apply list_elem_of_singleton in Hx. subst x. exact (step_sz _ _ _ _ Hn Hp).
  - apply list_elem_of_singleton in Hx. subst x. exact (step_sz _ _ _ _ Hn Hp).
  - destruct (zip_elem _ _ _ _ x Hf Hx) as (k & R' & Hp & ->). exact (step_sz _ _ _ _ Hn Hp).
Qed.

Lemma tnodes_sz T n X : norec T = true → X ∈ tnodes T n → sz X + length n ≤ sz T ∧ norec X = true.
Proof.
  intros HT. revert X. induction n as [|a n IH] using rev_ind; intros X HX.
  - rewrite tnodes_nil in HX. apply list_elem_of_singleton in HX. subst X. simpl. split; [lia|done].
  - apply tnodes_app_elem in HX as (X0 & HX0 & HX). destruct (IH X0 HX0) as [Hl Hr].
    destruct (step_sz _ _ _ _ Hr (co_succ_sound _ _ _ HX)) as [Hl' Hr']. rewrite length_app. simpl.
    split; [lia|done].
Qed.

Lemma menu_depth T n o : norec T = true → menu T n o → length n < sz T.
Proof.
  intros HT (X & a & HX & _ & Hne). destruct (co_succ X a) as [|X' l] eqn:E; [done|].
  destruct (tnodes_sz T n X HT HX) as [Hl Hr].
  assert (HX' : X' ∈ co_succ X a) by (rewrite E; by left).
  destruct (step_sz _ _ _ _ Hr (co_succ_sound _ _ _ HX')) as [Hl' _]. lia.
Qed.

Lemma cstep_measure `{QM : QuantumModel} T O ρ (c : comp) σ Δ :
  norec T = true → norec c.2.1.1 = true → cstep (menu T) O ρ c σ Δ →
  ∀ y, y ∈ Δ → sz y.1.2.1.1 + (sz T - length y.1.1) < sz c.2.1.1 + (sz T - length c.1) ∧ norec y.1.2.1.1 = true.
Proof.
  intros HT Hc Hs y Hy.
  inversion Hs as [n P C E s Δ0 Hss|n P C E k d v t P' Hin HkC Hp|n P C E k d v t P' HI Hp
                  |n P C E k E' qs t HI|n P C E k qs t HI|n P C E k M qs t HI]; subst; simpl in *.
  - apply list_elem_of_fmap in Hy as (x & -> & Hx). simpl.
    destruct (sched_sz ρ P s Δ0 Hc Hss x Hx) as [Hl Hr]. split; [lia|done].
  - apply list_elem_of_singleton in Hy. subst y. simpl. destruct (step_sz _ _ _ _ Hc Hp) as [Hl Hr]. split; [lia|done].
  - apply list_elem_of_singleton in Hy. subst y. simpl. destruct (step_sz _ _ _ _ Hc Hp) as [Hl Hr].
    rewrite length_app. simpl. split; [lia|done].
  - apply list_elem_of_singleton in Hy. subst y. simpl. pose proof (menu_depth T n _ HT HI) as Hd.
    rewrite length_app. simpl. split; [lia|done].
  - apply list_elem_of_singleton in Hy. subst y. simpl. pose proof (menu_depth T n _ HT HI) as Hd.
    rewrite length_app. simpl. split; [lia|done].
  - apply list_elem_of_fmap in Hy as (x & -> & Hx). simpl. pose proof (menu_depth T n _ HT HI) as Hd.
    rewrite length_app. simpl. split; [lia|done].
Qed.

Lemma stable_fin `{QM : QuantumModel} O I S D (r : nat → dist comp) w N :
  run_word (M := lq_menu O) I S D r w → dstable (SchedSts0 := mdlts (M := lq_menu O) I S) (r N) →
  fin (visited r).
Proof.
  intros Hrun Hst. exists (concat (map (λ j, map (λ x : comp * St, x.1.1) (r j)) (seq 0 (Datatypes.S N)))).
  intros n (i & c & ρ & Hin & <-).
  assert (Hj : ∃ j, j ≤ N ∧ (c, ρ) ∈ r j).
  { destruct (le_lt_dec i N) as [Hle|Hlt]; [by exists i|]. exists N. split; [lia|].
    replace i with (N + (i - N)) in Hin by lia. by rewrite (stable_const O I S _ r w N Hrun Hst) in Hin. }
  destruct Hj as (j & Hj & Hinj). apply list_elem_of_In, in_concat.
  exists (map (λ x : comp * St, x.1.1) (r j)). split.
  - apply in_map_iff. exists j. split; [done|]. apply in_seq. lia.
  - apply in_map_iff. exists (c, ρ). split; [done|]. by apply list_elem_of_In.
Qed.

Theorem norec_finitary `{QM : QuantumModel} (p q : proc * St) : norec q.1 = true → finitary p q.
Proof.
  intros Hq O Ch K I S r w ((T & HT & _ & -> & -> & _) & _) Hw.
  assert (HTn : norec T = true) by exact (proj1 obs_norec T (proj1 (proj1 (proj1 HT)))).
  assert (Hsn : SN (mdlts (M := lq_menu O) (menu T) (S_T T)) (dinit O q)).
  { apply (SN_any (mdlts (M := lq_menu O) (menu T) (S_T T))
             (λ c : comp, sz c.2.1.1 + (sz T - length c.1)) (λ c : comp, norec c.2.1.1 = true)).
    - intros ρ c σ Δ Hi _ Hs y Hy. exact (cstep_measure T O ρ c σ Δ HTn Hi Hs y Hy).
    - intros x ->%list_elem_of_singleton. exact Hq. }
  destruct (sn_stable (mdlts (M := lq_menu O) (menu T) (S_T T)) (dinit O q) r Hsn
              (run_word_is_run (M := lq_menu O) _ _ _ _ _ Hw)) as [N HN].
  exact (stable_fin O (menu T) (S_T T) (dinit O q) r w N Hw HN).
Qed.

Theorem trace_characterisation_norec `{QM : QuantumModel} (DC : dep_choice) (p q : proc * St) :
  q.2 ≠ szero → norec q.1 = true →
  (ctx_pre_sm_on Stay (obs_for p q) p q ↔ alt_trace p q).
Proof.
  intros Hz Hn. exact (trace_characterisation DC p q Hz (norec_finitary p q Hn)).
Qed.
(* end hide *)
