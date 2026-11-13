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
From Stdlib.Logic Require Import Classical_Prop.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Branching.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Definition goffs (g : guard) (o : offer) : Prop := ∃ a, offer_of a = o ∧ gco_succ g a ≠ [].

Definition offs (T : proc) (o : offer) : Prop := ∃ a, offer_of a = o ∧ co_succ T a ≠ [].

Lemma goffs_fin g : fin (goffs g).
Proof.
  induction g as [es| |𝜆 P|g1 IH1 g2 IH2].
  - apply (fin_mono _ (λ _, False)); [|apply fin_false]. intros o (a & _ & Hne). done.
  - apply (fin_mono _ (λ _, False)); [|apply fin_false]. intros o (a & _ & Hne). done.
  - destruct 𝜆 as [t|t c|t E es|t M es|t es].
    + apply (fin_mono _ (λ _, False)); [|apply fin_false]. intros o (a & _ & Hne). simpl in Hne. by destruct a.
    + apply (fin_mono _ (λ o, o = OffIn t c)); [|apply fin_eq].
      intros o (a & <- & Hne). simpl in Hne. destruct a; try done. case_decide as Hd; [|done].
      destruct Hd as [-> ->]. done.
    + apply (fin_mono _ (λ o, ∃ qs, eval_qubits es = Some qs ∧ o = OffOp t E qs)).
      * intros o (a & <- & Hne). simpl in Hne. destruct a; try done. case_decide as Hd; [|done].
        destruct Hd as (-> & -> & Hq). eexists. split; [exact Hq|done].
      * apply (fin_img (λ qs, OffOp t E qs) (λ qs, eval_qubits es = Some qs)).
        apply fin_uniq. intros x y Hx Hy. congruence.
    + apply (fin_mono _ (λ o, ∃ qs, eval_qubits es = Some qs ∧ o = OffMeas t M qs)).
      * intros o (a & <- & Hne). simpl in Hne. destruct a; try done. case_decide as Hd; [|done].
        destruct Hd as (-> & -> & Hq). eexists. split; [exact Hq|done].
      * apply (fin_img (λ qs, OffMeas t M qs) (λ qs, eval_qubits es = Some qs)).
        apply fin_uniq. intros x y Hx Hy. congruence.
    + apply (fin_mono _ (λ o, ∃ qs, eval_qubits es = Some qs ∧ o = OffInit t qs)).
      * intros o (a & <- & Hne). simpl in Hne. destruct a; try done. case_decide as Hd; [|done].
        destruct Hd as (-> & Hq). eexists. split; [exact Hq|done].
      * apply (fin_img (λ qs, OffInit t qs) (λ qs, eval_qubits es = Some qs)).
        apply fin_uniq. intros x y Hx Hy. congruence.
  - apply (fin_mono _ (λ o, goffs g1 o ∨ goffs g2 o)); [|apply fin_or; [exact IH1|exact IH2]].
    intros o (a & Ea & Hne). simpl in Hne. destruct (gco_succ g1 a) as [|x l] eqn:E1.
    + right. exists a. split; [done|]. exact Hne.
    + left. exists a. split; [done|]. by rewrite E1.
Qed.

Lemma offs_fin T : fin (offs T).
Proof.
  induction T as [t c e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|X|t X P IHP|g].
  - apply (fin_mono _ (λ o, ∃ v, eval e = Some v ∧ o = OffOut t c v)).
    + intros o (a & <- & Hne). simpl in Hne. destruct a; try done. case_decide as Hd; [|done].
      destruct Hd as (-> & -> & Hv). eexists. split; [exact Hv|done].
    + apply (fin_img (λ v, OffOut t c v) (λ v, eval e = Some v)).
      apply fin_uniq. intros x y Hx Hy. congruence.
  - apply (fin_mono _ (λ o, offs P o ∨ offs Q o)); [|apply fin_or; [exact IHP|exact IHQ]].
    intros o (a & Ea & Hne). simpl in Hne. destruct (eval e) as [[[]| |]|]; try done; [left|right]; by exists a.
  - apply (fin_mono _ (λ o, offs P o ∨ offs Q o)); [|apply fin_or; [exact IHP|exact IHQ]].
    intros o (a & Ea & Hne). simpl in Hne. destruct (co_succ P a) as [|x l] eqn:E1.
    + right. exists a. split; [done|]. intros E2. rewrite E2 in Hne. done.
    + left. exists a. split; [done|]. by rewrite E1.
  - apply (fin_mono _ (λ _, False)); [|apply fin_false]. intros o (a & _ & Hne). done.
  - apply (fin_mono _ (λ _, False)); [|apply fin_false]. intros o (a & _ & Hne). done.
  - apply (fin_mono _ (λ _, False)); [|apply fin_false]. intros o (a & _ & Hne). done.
  - exact (goffs_fin g).
Qed.

Lemma menu_fin T n : fin (menu T n).
Proof.
  apply (fin_mono _ (λ o, ∃ T', T' ∈ tnodes T n ∧ offs T' o)).
  - intros o (T' & a & HT' & Ea & Hne). exists T'. split; [done|]. by exists a.
  - apply (fin_bind _ _ (fin_elem (tnodes T n))). intros T' _. apply offs_fin.
Qed.

Definition alike (o o' : offer) : Prop :=
  match o, o' with
  | OffIn _ c, OffIn _ c' => c = c'
  | OffOp _ _ _, OffOp _ _ _ | OffInit _ _, OffInit _ _ | OffMeas _ _ _, OffMeas _ _ _ => True
  | _, _ => False
  end.

Lemma alike_kind o o' : alike o o' → off_kind o = off_kind o'.
Proof. destruct o, o'; done. Qed.

Lemma cstep_off_cell `{QM : QuantumModel} J O ρ c k t Δ :
  cstep J O ρ c (IOff k t) Δ →
  ∃ o, J c.1 o ∧ off_tag o = k ∧ alike o o ∧ cstep (single c.1 o) O ρ c (IOff k t) Δ.
Proof.
  intros Hcv%cstep_cases. inversion Hcv as [| |n P C k' d v t' P' HI Hp|n P C k' E' qs t' HI|n P C k' qs t' HI|n P C k' M qs t' HI]; subst; simpl.
  - exists (OffIn k d). split; [done|]. split; [done|]. split; [done|]. apply cs_in; [by split|done].
  - exists (OffOp k E' qs). split; [done|]. split; [done|]. split; [done|]. apply cs_op. by split.
  - exists (OffInit k qs). split; [done|]. split; [done|]. split; [done|]. apply cs_init. by split.
  - exists (OffMeas k M qs). split; [done|]. split; [done|]. split; [done|]. apply cs_meas. by split.
Qed.

Lemma single_swap `{QM : QuantumModel} O n o o' ρ c σ Δ :
  alike o o' → cstep (single n o') O ρ c σ Δ →
  ∃ σ' Δ', cstep (single n o) O ρ c σ' Δ' ∧ (off_tag o = off_tag o' → σ' = σ).
Proof.
  intros Hal Hs.
  apply cstep_cases in Hs. inversion Hs as [n0 P C s Δ0 Hss|n0 P C k d v t P' HE HkC Hp|n0 P C k d v t P' HI Hp
                  |n0 P C k E' qs t HI|n0 P C k qs t HI|n0 P C k M qs t HI]; subst.
  - eexists (ICh s), _. split; [by constructor|done].
  - eexists (ICh (cpair t k)), _. split; [by econstructor|done].
  - destruct HI as [-> <-]. destruct o as [|k0 d0| | |]; simpl in Hal; try done. subst d0.
    eexists (IOff k0 t), _. split; [apply cs_in; [by split|exact Hp]|]. simpl. by intros ->.
  - destruct HI as [-> <-]. destruct o as [| |k0 E0 qs0| |]; simpl in Hal; try done.
    eexists (IOff k0 t), _. split; [apply cs_op; by split|]. simpl. by intros ->.
  - destruct HI as [-> <-]. destruct o as [| | | |k0 qs0]; simpl in Hal; try done.
    eexists (IOff k0 t), _. split; [apply cs_init; by split|]. simpl. by intros ->.
  - destruct HI as [-> <-]. destruct o as [| | |k0 M0 qs0|]; simpl in Hal; try done.
    eexists (IOff k0 t), _. split; [apply cs_meas; by split|]. simpl. by intros ->.
Qed.

Section Trunc.
  Context `{QM : QuantumModel} (p q : proc * St) (T : proc) (Ch : channel → Prop) (K : tag → okind).
  Context (O : node → list msg) (r : nat → dist comp) (w : nat → item) (F : list tag) (Mo : option meas).

  Notation Sx := (S_T T).
  Notation U := (cells (M := lq_menu O) (S_T T) r w).
  Notation Js := (Jstar (M := lq_menu O) (real_off p q Ch K) (cells (M := lq_menu O) (S_T T) r w) (S_T T) r w).
  Notation Ss := (Sstar (M := lq_menu O) (real_off p q Ch K) (cells (M := lq_menu O) (S_T T) r w) (S_T T) r w).

  Definition retag (k : tag) (o : offer) : offer :=
    match o with
    | OffOut _ c v => OffOut k c v
    | OffIn _ c => OffIn k c
    | OffOp _ _ _ => OffOp k 0 []
    | OffMeas _ M _ => OffMeas k (default M Mo) []
    | OffInit _ _ => OffInit k []
    end.

  Definition canon (o : offer) : Prop :=
    match o with
    | OffOut _ _ _ => False
    | OffIn _ _ => True
    | OffOp _ E qs => E = 0 ∧ qs = []
    | OffMeas _ M qs => Mo = Some M ∧ qs = []
    | OffInit _ qs => qs = []
    end.

  Definition J0 (n : node) (o : offer) : Prop := menu T n o ∨ (Js n o ∧ off_tag o ∈ F ∧ canon o).

  Lemma retag_tag k o : off_tag (retag k o) = k.
  Proof. by destruct o. Qed.

  Lemma alike_retag_l k o : alike o o → alike (retag k o) o.
  Proof. by destruct o. Qed.

  Lemma alike_retag_r k o : alike o o → alike o (retag k o).
  Proof. by destruct o. Qed.

  Hypothesis HMo : ∀ M : meas, ∃ M0, Mo = Some M0.

  Lemma canon_retag k o : alike o o → canon (retag k o).
  Proof. destruct o as [| | |k' M qs|]; simpl; try done. intros _. destruct (HMo M) as (M0 & ->). done. Qed.

  Hypothesis HT : obs_for p q T.
  Hypothesis Hrun : run_word (M := lq_menu O) (menu T) Sx (dinit q) r w.
  Hypothesis HF : ∀ k, k ∈ tags T → k ∈ F.
  Hypothesis Hrep : ∀ k, k ∉ F → k ∉ tags p.1 → k ∉ tags q.1 →
    ∃ k', k' ∈ F ∧ k' ∉ tags T ∧ k' ∉ tags p.1 ∧ k' ∉ tags q.1 ∧ K k' = K k.
  Hypothesis Hnz : ∀ i x, x ∈ r i → x.2 ≠ weight_zero.
  Hypothesis HokT : ∀ n o, menu T n o → real_off p q Ch K o.

  Lemma menu_star n o : menu T n o → Js n o.
  Proof.
    assert (Hr : run_word (M := lq_menu O) (menu T) Sx (r 0) r w) by (split; [done|apply Hrun]).
    assert (Hi : ∀ x, x ∈ r 0 → visited_ok (M := lq_menu O) (menu T) (mnode (MenuSts := lq_menu O) x.1)).
    { rewrite (proj1 Hrun). apply init_visited. intros x ->%list_elem_of_singleton. done. }
    exact (I_sub_star (M := lq_menu O) (real_off p q Ch K) (menu T) Sx r w Hr Hi Hnz HokT n o).
  Qed.

  Lemma U_menu n o : U n o → menu T n o.
  Proof.
    assert (Hr : run_word (M := lq_menu O) (menu T) Sx (r 0) r w) by (split; [done|apply Hrun]).
    assert (Hi : ∀ x, x ∈ r 0 → visited_ok (M := lq_menu O) (menu T) (mnode (MenuSts := lq_menu O) x.1)).
    { rewrite (proj1 Hrun). apply init_visited. intros x ->%list_elem_of_singleton. done. }
    exact (cells_sub (M := lq_menu O) (menu T) Sx r w Hr Hi n o).
  Qed.

  Lemma U_tag n o : U n o → off_tag o ∈ tags T.
  Proof.
    intros HU. unfold tags. apply list_elem_of_fmap. exists (off_tag o, off_kind o). split; [done|].
    exact (menu_kind T (proj1 HT) n o (U_menu n o HU)).
  Qed.

  Lemma refused_swap n o o' :
    alike o o' → off_tag o' ∉ tags T ∨ off_tag o = off_tag o' →
    refused (M := lq_menu O) U Sx r w n o' → refused (M := lq_menu O) U Sx r w n o.
  Proof.
    intros Hal Ht (i & c & ρ & Hin & HS & [(Hd & Hno & Δ & Hs)|(Hst & σ & Δ & Hs)]).
    - destruct (single_swap O n o o' ρ c (w i) Δ Hal Hs) as (σ' & Δ' & Hs' & Heq). destruct Ht as [Hfr|Et].
      + exfalso. pose proof (Hs : cstep (single n o') O ρ c (w i) Δ) as Hc.
        destruct Hd as [(c1 & ρ1 & Δ1 & _ & _ & Hs1) _].
        pose proof (Hs1 : cstep U O ρ1 c1 (w i) Δ1) as Hc1.
        destruct (w i) as [s|k t].
        * apply (Hno Δ). exact (proj1 (cstep_ich _ _ _ _ _ _ Hc) U).
        * destruct (cstep_off_cell _ _ _ _ _ _ _ Hc) as (o1 & [_ ->] & Ek & _).
          destruct (cstep_off_cell _ _ _ _ _ _ _ Hc1) as (o2 & HU2 & Ek2 & _).
          apply Hfr. rewrite Ek, <- Ek2. exact (U_tag _ _ HU2).
      + exists i, c, ρ. split; [done|]. split; [done|]. left. split; [done|]. split; [done|].
        exists Δ'. rewrite <- (Heq Et). exact Hs'.
    - destruct (single_swap O n o o' ρ c σ Δ Hal Hs) as (σ' & Δ' & Hs' & _).
      exists i, c, ρ. split; [done|]. split; [done|]. right. split; [done|]. by exists σ', Δ'.
  Qed.

  Lemma star_rep n o o' :
    Js n o → ¬ U n o → alike o o' → K (off_tag o') = K (off_tag o) →
    off_tag o' ∉ tags p.1 → off_tag o' ∉ tags q.1 →
    off_tag o' ∉ tags T ∨ off_tag o = off_tag o' → Js n o'.
  Proof.
    intros [HU|[Hok Hnr]] HnU Hal HK Hp Hq Ht; [done|]. right. split.
    - destruct Hok as (Hty & _ & _ & Hch). split; [|split; [done|split; [done|]]].
      + unfold typed in *. rewrite HK, <- Hty. symmetry. exact (alike_kind o o' Hal).
      + intros k c ->. destruct o as [|k0 c0| | |]; simpl in Hal; try done. subst c0. exact (Hch k0 c eq_refl).
    - intros Hr. apply Hnr. exact (refused_swap n o o' Hal Ht Hr).
  Qed.

  Lemma cell_rep n o : Js n o → alike o o →
    ∃ o', J0 n o' ∧ alike o' o ∧ (off_tag o ∈ F → off_tag o' = off_tag o).
  Proof.
    intros HJ Hal. destruct (classic (menu T n o)) as [HM|HnM]; [exists o; split; [by left|by split]|].
    assert (HnU : ¬ U n o) by (intros HU; apply HnM; by apply U_menu).
    assert (Hok : real_off p q Ch K o) by (destruct HJ as [HU|[Hok _]]; [by destruct HnU|exact Hok]).
    destruct Hok as (_ & Hp & Hq & _).
    assert (Hk : ∃ k', k' ∈ F ∧ k' ∉ tags p.1 ∧ k' ∉ tags q.1 ∧ K k' = K (off_tag o)
                 ∧ (k' ∉ tags T ∨ off_tag o = k') ∧ (off_tag o ∈ F → k' = off_tag o)).
    { destruct (classic (off_tag o ∈ F)) as [HkF|HkF].
      - exists (off_tag o). split; [done|]. split; [done|]. split; [done|]. split; [done|]. split; [by right|done].
      - destruct (Hrep _ HkF Hp Hq) as (k' & Ha & Hb & Hc & Hd & He).
        exists k'. split; [done|]. split; [done|]. split; [done|]. split; [done|]. split; [by left|].
        intros Hin. by destruct HkF. }
    destruct Hk as (k' & HkF & Hkp & Hkq & HkK & Hkt & Hksame).
    exists (retag k' o). split; [|split; [by apply alike_retag_l|by rewrite retag_tag]].
    right. split; [|split; [by rewrite retag_tag|by apply canon_retag]].
    apply (star_rep n o); rewrite ?retag_tag; try done. by apply alike_retag_r.
  Qed.

  Lemma J0_move ρ c σ Δ : cstep Js O ρ c σ Δ →
    ∃ σ' Δ', cstep J0 O ρ c σ' Δ' ∧ ((∀ k t, σ = IOff k t → k ∈ F) → σ' = σ).
  Proof.
    intros Hs. destruct σ as [s|k t].
    - exists (ICh s), Δ. split; [exact (proj1 (cstep_ich _ _ _ _ _ _ Hs) J0)|done].
    - destruct (cstep_off_cell _ _ _ _ _ _ _ Hs) as (o & Ho & Ek & Hal & Hs1).
      destruct (cell_rep c.1 o Ho Hal) as (o' & Ho' & Hal' & Htag).
      destruct (single_swap O c.1 o' o ρ c (IOff k t) Δ Hal' Hs1) as (σ' & Δ' & Hs' & Heq).
      exists σ', Δ'. split.
      + assert (Hsub : ∀ n1 o1, single c.1 o' n1 o1 → J0 n1 o1) by (intros n1 o1 [-> ->]; exact Ho').
        exact (mstep_mono (M := lq_menu O) _ _ ρ c σ' Δ' Hsub Hs').
      + intros HkF. apply Heq, Htag. rewrite Ek. exact (HkF k t eq_refl).
  Qed.

  Lemma J0_sub n o : J0 n o → Js n o.
  Proof. intros [HM|[HJ _]]; [by apply menu_star|done]. Qed.

  Lemma J0_tag n o : J0 n o → off_tag o ∈ F.
  Proof.
    intros [HM|(_ & Hin & _)]; [|done]. apply HF. unfold tags. apply list_elem_of_fmap.
    exists (off_tag o, off_kind o). split; [done|]. exact (menu_kind T (proj1 HT) n o HM).
  Qed.

  Theorem J0_run Dp r' :
    is_run (SchedSts0 := mdlts (M := lq_menu O) J0 Ss) Stay Dp r' →
    is_run (SchedSts0 := mdlts (M := lq_menu O) Js Ss) Stay Dp r'.
  Proof.
    apply (sub_run (mdlts (M := lq_menu O) J0 Ss) (mdlts (M := lq_menu O) Js Ss)).
    - intros c. done.
    - intros ρ c σ Δ Hs. exact (mstep_mono (M := lq_menu O) J0 Js ρ c σ Δ J0_sub Hs).
    - intros ρ c σ Δ Hs (ρ' & c' & Δ' & Hs'). destruct (J0_move ρ c σ Δ Hs) as (σ1 & Δ1 & Hs1 & Heq).
      exists Δ1. rewrite <- Heq; [exact Hs1|]. intros k t ->.
      destruct (cstep_off_cell _ _ _ _ _ _ _ Hs') as (o & Ho & <- & _). exact (J0_tag _ _ Ho).
    - intros ρ c σ Δ Hs. destruct (J0_move ρ c σ Δ Hs) as (σ1 & Δ1 & Hs1 & _). by exists σ1, Δ1.
  Qed.

  Lemma J0_fin_cells n : fin (λ o, J0 n o ∧ ∀ k c, o ≠ OffIn k c).
  Proof.
    apply (fin_mono _ (λ o, menu T n o
      ∨ ∃ k, k ∈ F ∧ (o = OffOp k 0 [] ∨ o = OffInit k [] ∨ ∃ M, Mo = Some M ∧ o = OffMeas k M []))).
    - intros o [[HM|(_ & HkF & Hc)] Hni]; [by left|right]. exists (off_tag o). split; [done|].
      destruct o as [k c v|k c|k E qs|k M qs|k qs]; simpl in *.
      + done.
      + by destruct (Hni k c).
      + destruct Hc as [-> ->]. by left.
      + destruct Hc as [HM ->]. right. right. by exists M.
      + subst. right. by left.
    - apply fin_or; [apply menu_fin|]. apply (fin_bind _ _ (fin_elem F)). intros k _.
      apply fin_or; [apply fin_eq|]. apply fin_or; [apply fin_eq|].
      apply (fin_img (λ M, OffMeas k M []) (λ M, Mo = Some M)). apply fin_uniq. intros x y Hx Hy. congruence.
  Qed.

  Lemma J0_fin_in n c : fin (λ k, J0 n (OffIn k c)).
  Proof. apply (fin_mono _ (λ k, k ∈ F)); [|apply fin_elem]. intros k HJ. exact (J0_tag n _ HJ). Qed.

  Theorem J0_branching D : fin (rstep (mdlts (M := lq_menu O) J0 Ss) D).
  Proof. exact (lq_rstep_fin O J0 Ss J0_fin_cells J0_fin_in D). Qed.
End Trunc.

Lemma meas_default `{QM : QuantumModel} : ∃ Mo : option meas, ∀ M : meas, ∃ M0, Mo = Some M0.
Proof.
  destruct (classic (∃ M : meas, True)) as [(M & _)|Hn].
  - exists (Some M). intros _. by exists M.
  - exists None. intros M. exfalso. apply Hn. by exists M.
Qed.

Lemma reps_exist `{QM : QuantumModel} (p q : proc * St) (T : proc) (K : tag → okind) :
  ∃ F : list tag, (∀ k, k ∈ tags T → k ∈ F)
     ∧ ∀ k, k ∉ F → k ∉ tags p.1 → k ∉ tags q.1 →
         ∃ k', k' ∈ F ∧ k' ∉ tags T ∧ k' ∉ tags p.1 ∧ k' ∉ tags q.1 ∧ K k' = K k.
Proof.
  assert (Hks : ∀ ks : list okind, ∃ fr : list tag, ∀ k, K k ∈ ks → k ∉ tags T → k ∉ tags p.1 → k ∉ tags q.1 →
    ∃ k', k' ∈ fr ∧ k' ∉ tags T ∧ k' ∉ tags p.1 ∧ k' ∉ tags q.1 ∧ K k' = K k).
  { induction ks as [|κ ks (fr & IH)].
    - exists []. intros k Hk. by apply elem_of_nil in Hk.
    - destruct (classic (∃ k0, K k0 = κ ∧ k0 ∉ tags T ∧ k0 ∉ tags p.1 ∧ k0 ∉ tags q.1)) as [(k0 & Ek & Ha & Hb & Hc)|Hn].
      + exists (k0 :: fr). intros k Hk HkT Hkp Hkq. apply elem_of_cons in Hk as [Hk|Hk].
        * exists k0. split; [by left|]. split; [done|]. split; [done|]. split; [done|]. congruence.
        * destruct (IH k Hk HkT Hkp Hkq) as (k' & Hin & Hrest). exists k'. split; [by right|done].
      + exists fr. intros k Hk HkT Hkp Hkq. apply elem_of_cons in Hk as [Hk|Hk]; [|exact (IH k Hk HkT Hkp Hkq)].
        exfalso. apply Hn. by exists k. }
  destruct (Hks [KOut; KIn; KOp; KMeas; KInit; KTau; KRec]) as (fr & Hfr). exists (tags T ++ fr). split.
  - intros k Hk. apply elem_of_app. by left.
  - intros k HkF Hkp Hkq.
    assert (HkT : k ∉ tags T) by (intros Hc; apply HkF, elem_of_app; by left).
    destruct (Hfr k) as (k' & Hin & Hrest); try done.
    + rewrite !elem_of_cons. destruct (K k); auto 10.
    + exists k'. split; [apply elem_of_app; by right|done].
Qed.
(* end hide *)
