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
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Branching lqCCS.Testing.Truncation lqCCS.Testing.Pull lqCCS.Testing.Head lqCCS.Testing.Modes lqCCS.Testing.Syn lqCCS.Testing.Assembly.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Final.
  Context `{lqP : lqCCS_Parameters}.

#[global] Instance coact_eq_dec : EqDecision coact.
Proof. solve_decision. Defined.

#[global] Instance offer_eq_dec : EqDecision offer.
Proof. solve_decision. Defined.

Lemma fin_exact {A} (P : A → Prop) : fin P → ∃ l : list A, NoDup l ∧ ∀ x, x ∈ l ↔ P x.
Proof.
  intros (l0 & Hl0).
  assert (Hall : ∀ l1 : list A, ∃ l : list A, NoDup l ∧ ∀ x, x ∈ l ↔ (x ∈ l1 ∧ P x)).
  { induction l1 as [|a l1 (l & Hnd & Hl)].
    - exists []. split; [constructor|]. intros x. split; [intros Hx; by apply elem_of_nil in Hx|].
      intros [Hx _]. by apply elem_of_nil in Hx.
    - destruct (classic (P a ∧ a ∉ l)) as [[Ha Hni]|Hn].
      + exists (a :: l). split; [by apply NoDup_cons|]. intros x. rewrite !elem_of_cons, Hl. split.
        * intros [->|[Hx HP]]; [split; [by left|done]|split; [by right|done]].
        * intros [[->|Hx] HP]; [by left|right; by split].
      + exists l. split; [done|]. intros x. rewrite elem_of_cons, Hl. split.
        * intros [Hx HP]. split; [by right|done].
        * intros [[->|Hx] HP]; [|by split]. apply Hl. apply NNPP. intros Hni. apply Hn. split; [done|].
          intros Hin. apply Hni. by apply Hl. }
  destruct (Hall l0) as (l & Hnd & Hl). exists l. split; [done|]. intros x. rewrite Hl. split; [by intros [_ ?]|].
  intros HP. split; [by apply Hl0|done].
Qed.

Lemma fin_choice {A B} (R : A → B → Prop) (l : list A) : (∀ a, ∃ b, R a b) →
  ∃ g : list (A * B), (∀ a, a ∈ l → ∃ b, (a, b) ∈ g) ∧ ∀ a b, (a, b) ∈ g → R a b.
Proof.
  intros HR. induction l as [|a l (g & Hg1 & Hg2)].
  - exists []. split; [intros a Ha; by apply elem_of_nil in Ha|intros a b Hin; by apply elem_of_nil in Hin].
  - destruct (HR a) as (b & Hb). exists ((a, b) :: g). split.
    + intros a' Ha'. apply elem_of_cons in Ha' as [->|Ha']; [exists b; by left|].
      destruct (Hg1 a' Ha') as (b' & Hb'). exists b'. by right.
    + intros a' b' Hin. apply elem_of_cons in Hin as [[= -> ->]|Hin]; [done|by apply Hg2].
Qed.

Definition lk {A B} `{EqDecision A} (d : B) (g : list (A * B)) (a : A) : B :=
  match find (λ ab, bool_decide (ab.1 = a)) g with Some ab => ab.2 | None => d end.

Lemma lk_spec {A B} `{EqDecision A} (R : A → B → Prop) (d : B) (g : list (A * B)) (a : A) :
  (∀ a b, (a, b) ∈ g → R a b) → (lk d g a = d ∧ ∀ b, (a, b) ∉ g) ∨ R a (lk d g a).
Proof.
  intros Hg. unfold lk. destruct (find (λ ab, bool_decide (ab.1 = a)) g) as [[a' b']|] eqn:E.
  - right. apply find_some in E as [Hin Hb]. apply bool_decide_eq_true in Hb. simpl in *. subst a'.
    apply Hg. by apply list_elem_of_In.
  - left. split; [done|]. intros b Hin. apply list_elem_of_In in Hin.
    pose proof (find_none _ _ E (a, b) Hin) as Hf. simpl in Hf. by rewrite bool_decide_eq_false in Hf.
Qed.

Definition valsof (z : node) : list val :=
  omap (λ a, match a with CoIn _ _ v => Some v | CoMeas _ _ _ n => Some (VNat n) | _ => None end) z.

Lemma len_le_sum (L : list node) z : z ∈ L → length z ≤ foldr (λ z' acc, length z' + acc) 0 L.
Proof.
  induction L as [|z' L IH]; intros Hin; [by apply elem_of_nil in Hin|]. simpl.
  apply elem_of_cons in Hin as [->|Hin]; [lia|]. specialize (IH Hin). lia.
Qed.

Section Data.
  Context `{QM : QuantumModel} (p q : prog * St) (T : prog) (Ch : channel → Prop) (K : tag → okind).
  Context (O : node → list msg) (r : nat → dist comp) (w : nat → item) (F : list tag) (Mo : option meas) (N : nat).

  Notation U := (cells (M := lq_menu O) (S_T T) r w).
  Notation J0 := (Truncation.J0 p q T Ch K O r w F Mo).
  Notation reach := (reach p q T Ch K O r w F Mo).

  Hypothesis HT : obs_for p q T.
  Hypothesis HF : ∀ t, t ∈ tags T → t ∈ F.

  Definition LVp (z : node) : Prop := ∃ n D x l, n ≤ N ∧ reach n D ∧ x ∈ D ∧ x.1.1 = z ++ l.

  Definition CLp (ch : channel) : Prop :=
    ∃ n D x t v P', n ≤ N ∧ reach n D ∧ x ∈ D ∧ x.1.2.1 ⟶ₚ{ch ! v}[{[+ t +]}] P'.

  Lemma reach_fin n : fin (reach n).
  Proof.
    induction n as [|n IH]; simpl; [apply fin_eq|]. apply fin_bind; [exact IH|]. intros D0 _.
    exact (J0_branching p q T Ch K O r w F Mo HT HF D0).
  Qed.

  Lemma comps_fin : fin (λ x : comp * weight, ∃ n D, n ≤ N ∧ reach n D ∧ x ∈ D).
  Proof.
    apply (fin_mono _ (λ x, ∃ n, n ∈ seq 0 (S N) ∧ ∃ D, reach n D ∧ x ∈ D)).
    - intros x (n & D & Hk & Hr & Hx). exists n. split; [apply elem_of_seq; lia|by exists D].
    - apply (fin_bind _ _ (fin_elem _)). intros n _. apply (fin_bind _ _ (reach_fin n)). intros D _. apply fin_elem.
  Qed.

  Lemma LVp_fin : fin LVp.
  Proof.
    apply (fin_mono _ (λ z, ∃ x : comp * weight, (∃ n D, n ≤ N ∧ reach n D ∧ x ∈ D) ∧ ∃ l, x.1.1 = z ++ l)).
    - intros z (n & D & x & l & Hk & Hr & Hx & E). exists x. split; [by exists n, D|by exists l].
    - apply (fin_bind _ _ comps_fin). intros x _.
      apply (fin_mono _ (λ z, z ∈ (λ i, take i x.1.1) <$> seq 0 (S (length x.1.1)))); [|apply fin_elem].
      intros z (l & E). apply list_elem_of_fmap. exists (length z). split.
      + rewrite E. by rewrite take_app_length.
      + apply elem_of_seq. rewrite E, length_app. lia.
  Qed.

  Lemma CLp_fin : fin CLp.
  Proof.
    apply (fin_mono _ (λ ch, ∃ x : comp * weight, (∃ n D, n ≤ N ∧ reach n D ∧ x ∈ D)
                         ∧ ∃ t v P', x.1.2.1 ⟶ₚ{ch ! v}[{[+ t +]}] P')).
    - intros ch (n & D & x & t & v & P' & Hk & Hr & Hx & Hp). exists x. split; [by exists n, D|by exists t, v, P'].
    - apply (fin_bind _ _ comps_fin). intros x _.
      apply (fin_mono _ (λ ch, ∃ a, psteps x.1.2.1 [] [] a ∧ ∃ v, a.1 = ch ! v)).
      + intros ch (t & v & P' & Hp). exists (ch ! v, P'). split; [exists ({[+ t +]}); by split|by exists v].
      + apply (fin_bind _ _ (psteps_fin _ [] [])). intros a _. apply fin_uniq.
        intros c1 c2 (v1 & E1) (v2 & E2). congruence.
  Qed.

  Lemma LVp_pre z z' : LVp (z ++ z') → LVp z.
  Proof. intros (n & D & x & l & Hk & Hr & Hx & E). exists n, D, x, (z' ++ l). by rewrite app_assoc. Qed.

  Lemma LVp_reach n D x : n ≤ N → reach n D → x ∈ D → LVp x.1.1.
  Proof. intros Hk Hr Hx. exists n, D, x, []. by rewrite app_nil_r. Qed.

  Lemma CLp_reach n D x t ch v P' : n ≤ N → reach n D → x ∈ D →
    x.1.2.1 ⟶ₚ{ch ! v}[{[+ t +]}] P' → CLp ch.
  Proof. intros Hk Hr Hx Hp. by exists n, D, x, t, v, P'. Qed.

  Lemma data_exist :
    ∃ (VL : list val) (reps : node → list offer) (wrapb : node → offer → bool) (f0 : nat),
      (∀ z', NoDup (reps z'))
      ∧ (∀ z' o, o ∈ reps z' → J0 z' o ∧ ¬ menu T z' o)
      ∧ (∀ z' o, LVp z' → J0 z' o → ¬ menu T z' o → (∀ t c, o = OffIn t c → CLp c) → o ∈ reps z')
      ∧ (∀ z' o, wrapb z' o = true → ¬ U z' o)
      ∧ (∀ z' o, LVp z' → menu T z' o → ¬ U z' o → wrapb z' o = true)
      ∧ (∀ z a, LVp z → a ∈ z → ¬ unlisted VL a)
      ∧ (∀ z, LVp z → length z < f0).
  Proof.
    destruct LVp_fin as (L & HL). exists (concat (map valsof L)).
    assert (Hrp : ∀ z', ∃ l : list offer, NoDup l
               ∧ ∀ o, o ∈ l ↔ (J0 z' o ∧ ¬ menu T z' o ∧ ∀ t c, o = OffIn t c → CLp c)).
    { intros z'. apply fin_exact. destruct CLp_fin as (LC & HLC).
      apply (fin_mono _ (λ o, (J0 z' o ∧ ∀ t c, o ≠ OffIn t c)
                             ∨ ∃ c, c ∈ LC ∧ ∃ t, J0 z' (OffIn t c) ∧ o = OffIn t c)).
      - intros o (HJ & _ & Hc). destruct (classic (∃ t c, o = OffIn t c)) as [(t & c & ->)|Hn].
        + right. exists c. split; [apply HLC; by apply (Hc t c)|by exists t].
        + left. split; [done|]. intros t c E. apply Hn. by exists t, c.
      - apply fin_or; [exact (J0_fin_cells p q T Ch K O r w F Mo z')|].
        apply (fin_bind _ _ (fin_elem LC)). intros c _.
        exact (fin_img (λ t, OffIn t c) _ (J0_fin_in p q T Ch K O r w F Mo HT HF z' c)). }
    destruct (fin_choice _ L Hrp) as (g & Hg1 & Hg2). exists (lk [] g).
    assert (HW : ∃ WL : list (node * offer), ∀ x, x ∈ WL ↔ (x.1 ∈ L ∧ menu T x.1 x.2 ∧ ¬ U x.1 x.2)).
    { destruct (fin_exact (λ x : node * offer, x.1 ∈ L ∧ menu T x.1 x.2 ∧ ¬ U x.1 x.2)) as (WL & _ & HWL);
        [|by exists WL].
      apply (fin_mono _ (λ x : node * offer, ∃ z', z' ∈ L ∧ ∃ o, menu T z' o ∧ x = (z', o))).
      - intros [z' o] (Hm & HM & _). exists z'. split; [done|]. by exists o.
      - apply (fin_bind _ _ (fin_elem L)). intros z' _. exact (fin_img (pair z') _ (menu_fin T z')). }
    destruct HW as (WL & HWL). exists (λ z' o, bool_decide ((z', o) ∈ WL)).
    exists (S (foldr (λ z' acc, length z' + acc) 0 L)).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - intros z'. destruct (lk_spec _ [] g z' Hg2) as [[-> _]|[Hn _]]; [constructor|done].
    - intros z' o Hin. destruct (lk_spec _ [] g z' Hg2) as [[E _]|[_ Hx]].
      + rewrite E in Hin. by apply elem_of_nil in Hin.
      + apply Hx in Hin as (Ha & Hb & _). done.
    - intros z' o Hm HJ HnM Hc. destruct (lk_spec _ [] g z' Hg2) as [[_ Hno]|[_ Hx]].
      + exfalso. destruct (Hg1 z' (HL z' Hm)) as (b & Hb). exact (Hno b Hb).
      + apply Hx. done.
    - intros z' o Hw. apply bool_decide_eq_true in Hw. apply HWL in Hw as (_ & _ & Hn). exact Hn.
    - intros z' o Hm HM HnU. apply bool_decide_eq_true. apply HWL. simpl. split; [exact (HL z' Hm)|done].
    - intros z a Hn Ha Hu.
      assert (Hv : ∀ v, v ∈ valsof z → v ∈ concat (map valsof L)).
      { intros v Hv. apply list_elem_of_In, in_concat. exists (valsof z).
        split; [apply in_map, list_elem_of_In, HL, Hn|by apply list_elem_of_In]. }
      destruct a as [t c v|t c v|t E qs|t M qs n|t q0|t]; simpl in Hu; try done.
      + apply Hu, Hv. apply list_elem_of_omap. by exists (CoIn t c v).
      + apply Hu, Hv. apply list_elem_of_omap. by exists (CoMeas t M qs n).
    - intros z Hn. pose proof (len_le_sum L z (HL z Hn)). lia.
  Qed.
End Data.

Theorem lq_MenuTrunc `{QM : QuantumModel} (p q : prog * St) O Ch K : q.2 ≠ szero → (∀ t, K t ≠ KRec) →
  MenuTrunc (M := lq_menu O) (real_off p q Ch K) (RealT p q O Ch K) (dinit p) (dinit q).
Proof.
  intros Hq HKr I S r w ((T & HT & HO & -> & -> & HCh & HK) & HokT) Hrun.
  destruct (reps_exist p q T K) as (F & HF & Hrep). destruct meas_default as (Mo & HMo).
  assert (Hnz : ∀ n x, x ∈ r n → x.2 ≠ weight_zero).
  { intros n. apply (run_weights (SchedSts0 := mdlts (M := lq_menu O) (menu T) (S_T T)) Stay (λ ρ, ρ ≠ weight_zero)
      (λ ρ c σ Δ Hg Hs, mstep_nonzero (MenuSts := lq_menu O) (menu T) ρ c σ Δ Hg Hs) (dinit q) r
      (run_word_is_run (M := lq_menu O) _ _ _ _ _ Hrun)).
    intros x ->%list_elem_of_singleton. exact Hq. }
  exists (Truncation.J0 p q T Ch K O r w F Mo). split; [|split].
  - exact (J0_run p q T Ch K O r w F Mo HMo HT Hrun HF Hrep Hnz HokT (dinit p)).
  - exact (J0_branching p q T Ch K O r w F Mo HT HF).
  - intros N.
    destruct (data_exist p q T Ch K O r w F Mo N HT HF)
      as (VL & reps & wrapb & f0 & Hnd & HR2 & HR3 & HW1 & HW2 & HVL & Hf0).
    exists (menu (tn VL reps wrapb f0 [] T)), (S_T (tn VL reps wrapb f0 [] T)).
    split; [apply (TN_real p q T Ch K O r w F Mo VL reps wrapb f0); assumption|].
    split; [apply (q_run p q T Ch K O r w F Mo VL reps wrapb f0); assumption|].
    split; [intros n c ρ Hin; apply (q_Sstar p q T Ch K O r w F Mo VL reps wrapb f0) with (n := n) (ρ := ρ); assumption|].
    intros r0 Hr0 n Hi.
    apply (p_good p q T Ch K O r w F Mo VL reps wrapb f0 (LVp p q T Ch K O r w F Mo N) (CLp p q T Ch K O r w F Mo N) N);
      try assumption.
    + exact (LVp_pre p q T Ch K O r w F Mo N).
    + exact (LVp_reach p q T Ch K O r w F Mo N).
    + exact (CLp_reach p q T Ch K O r w F Mo N).
Qed.

Theorem alt_free_obs_iff `{QM : QuantumModel} (DC : dep_choice) (p q : prog * St) :
  q.2 ≠ szero →
  (ctx_pre_sm_on Stay (obs_for p q) p q ↔ alt_free_obs p q).
Proof.
  intros Hz. split; [|exact (alt_free_obs_sound DC p q Hz)].
  intros Hc O Ch K HKr. apply (malt_free_on_trunc (M := lq_menu O) _ _ DC); [by apply lq_MenuTrunc|].
  apply (proj1 (alt_pre_obs_menu p q)); [exact (proj2 (alt_pre_obs_iff Stay DC p q) Hc)|exact HKr].
Qed.

End Final.

(* end hide *)
