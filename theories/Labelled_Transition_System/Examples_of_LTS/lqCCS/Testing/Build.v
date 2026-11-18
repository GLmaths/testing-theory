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
From Stdlib Require Import Lia.
Import ListNotations.
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Pull lqCCS.Testing.Head lqCCS.Testing.Modes lqCCS.Testing.Syn lqCCS.Testing.Assembly lqCCS.Testing.Final.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Build.
  Context `{lqP : lqCCS_Parameters}.

Inductive bag : list msg → prog → Prop :=
| bag_nil : bag [] 𝟘
| bag_one t c v : bag [(t, c, v)] (t ∶ c ! v)
| bag_par E1 E2 B1 B2 : bag E1 B1 → bag E2 B2 → bag (E1 ++ E2) (B1 ∥ B2).

Lemma bag_succ E B : bag E B → successb B = false.
Proof. induction 1 as [|t c v|E1 E2 B1 B2 _ IH1 _ IH2]; simpl; [done|done|by rewrite IH1, IH2]. Qed.

Lemma bag_nout E B a : bag E B → (∀ t c v, a ≠ CoOut t c v) → co_succ B a = [].
Proof.
  intros Hb Ha. induction Hb as [|t c v|E1 E2 B1 B2 _ IH1 _ IH2]; simpl.
  - done.
  - destruct a; try done. by destruct (Ha t0 c0 v0).
  - by rewrite IH1, IH2.
Qed.

Lemma bag_out E B t c v B' : bag E B → B' ∈ co_succ B (CoOut t c v) →
  ∃ E1 E2, E = E1 ++ (t, c, v) :: E2 ∧ bag (E1 ++ E2) B'.
Proof.
  intros Hb. revert B'. induction Hb as [|t0 c0 v0|E1 E2 B1 B2 Hb1 IH1 Hb2 IH2]; intros B' Hin; simpl in Hin.
  - by apply elem_of_nil in Hin.
  - case_decide as Hd; [|by apply elem_of_nil in Hin]. apply list_elem_of_singleton in Hin. subst B'.
    destruct Hd as (-> & -> & Hv). simpl in Hv. injection Hv as ->. exists [], []. split; [done|apply bag_nil].
  - apply elem_of_app in Hin as [(B0 & -> & Hin)%list_elem_of_fmap|(B0 & -> & Hin)%list_elem_of_fmap].
    + destruct (IH1 _ Hin) as (F1 & F2 & -> & Hb'). exists F1, (F2 ++ E2). split; [by rewrite <- app_assoc|].
      rewrite app_assoc. by apply bag_par.
    + destruct (IH2 _ Hin) as (F1 & F2 & -> & Hb'). exists (E1 ++ F1), F2. split; [by rewrite <- app_assoc|].
      rewrite <- app_assoc. by apply bag_par.
Qed.

Lemma bag_msgs E B : bag E B → out_msgs B = E.
Proof. induction 1 as [|t c v|E1 E2 B1 B2 _ IH1 _ IH2]; simpl; [done|done|by rewrite IH1, IH2]. Qed.

Lemma bag_len E B t c v : bag E B → NoDup E → length (co_succ B (CoOut t c v)) ≤ 1.
Proof.
  induction 1 as [|t0 c0 v0|E1 E2 B1 B2 Hb1 IH1 Hb2 IH2]; intros Hnd; simpl.
  - lia.
  - case_decide; simpl; lia.
  - apply NoDup_app in Hnd as (Hn1 & H12 & Hn2). specialize (IH1 Hn1). specialize (IH2 Hn2).
    rewrite length_app, !length_fmap.
    destruct (co_succ B1 (CoOut t c v)) as [|x1 l1] eqn:Ea; [simpl; lia|].
    destruct (co_succ B2 (CoOut t c v)) as [|x2 l2] eqn:Eb; [simpl in *; lia|]. exfalso.
    apply (H12 (t, c, v)).
    + rewrite <- (bag_msgs _ _ Hb1). apply out_msgs_spec. by rewrite Ea.
    + rewrite <- (bag_msgs _ _ Hb2). apply out_msgs_spec. by rewrite Eb.
Qed.

Inductive wr (W : prog) : list msg → prog → Prop :=
| wr_refl : wr W [] W
| wr_T e X A E : 〚 e 〛 = true → wr W E X → wr W E (If e Then X Else A)
| wr_F e X A E : 〚 e 〛 = false → wr W E X → wr W E (If e Then A Else X)
| wr_bag E1 E2 B X : bag E1 B → wr W E2 X → wr W (E1 ++ E2) (B ∥ X).

Lemma wr_succ W E X : wr W E X → successb X = successb W.
Proof.
  induction 1 as [|e X A E He _ IH|e X A E He _ IH|E1 E2 B X Hb _ IH]; simpl.
  - done.
  - by rewrite He.
  - by rewrite He.
  - by rewrite (bag_succ _ _ Hb).
Qed.

Lemma wr_nout W E X a : (∀ t c v, a ≠ CoOut t c v) → wr W E X →
  length (co_succ X a) = length (co_succ W a)
  ∧ ∀ X', X' ∈ co_succ X a → ∃ W', W' ∈ co_succ W a ∧ wr W' E X'.
Proof.
  intros Ha. induction 1 as [|e X A E He _ IH|e X A E He _ IH|E1 E2 B X Hb _ IH]; simpl.
  - split; [done|]. intros X' HX. exists X'. split; [done|apply wr_refl].
  - rewrite He. destruct IH as [IHl IHe]. split; [done|]. exact IHe.
  - rewrite He. destruct IH as [IHl IHe]. split; [done|]. exact IHe.
  - rewrite (bag_nout _ _ a Hb Ha). simpl. destruct IH as [IHl IHe]. split; [by rewrite length_fmap|].
    intros X' (X0 & -> & HX0)%list_elem_of_fmap. destruct (IHe _ HX0) as (W' & HW' & Hw).
    exists W'. split; [done|]. by apply wr_bag.
Qed.

Lemma wr_out W E X t c v X' : nosend W → wr W E X → X' ∈ co_succ X (CoOut t c v) →
  ∃ E1 E2, E = E1 ++ (t, c, v) :: E2 ∧ wr W (E1 ++ E2) X'.
Proof.
  intros Hns Hw. revert X'. induction Hw as [|e X A E He _ IH|e X A E He _ IH|E1 E2 B X Hb Hw0 IH]; intros X' Hin.
  - rewrite Hns in Hin. by apply elem_of_nil in Hin.
  - simpl in Hin. rewrite He in Hin. exact (IH _ Hin).
  - simpl in Hin. rewrite He in Hin. exact (IH _ Hin).
  - simpl in Hin. apply elem_of_app in Hin as [(B0 & -> & Hin)%list_elem_of_fmap|(X0 & -> & Hin)%list_elem_of_fmap].
    + destruct (bag_out _ _ _ _ _ _ Hb Hin) as (F1 & F2 & -> & Hb'). exists F1, (F2 ++ E2).
      split; [by rewrite <- app_assoc|]. rewrite app_assoc. by apply wr_bag.
    + destruct (IH _ Hin) as (F1 & F2 & -> & Hw'). exists (E1 ++ F1), F2. split; [by rewrite <- app_assoc|].
      rewrite <- app_assoc. by apply wr_bag.
Qed.

Lemma wr_msgs W E X t c v : nosend W → wr W E X → (co_succ X (CoOut t c v) ≠ [] ↔ (t, c, v) ∈ E).
Proof.
  intros Hns Hw. split.
  - intros Hne. destruct (co_succ X (CoOut t c v)) as [|X' l] eqn:Ex; [done|].
    destruct (wr_out W E X t c v X' Hns Hw) as (E1 & E2 & -> & _); [rewrite Ex; by left|].
    apply elem_of_app. right. by left.
  - induction Hw as [|e X A E He _ IH|e X A E He _ IH|E1 E2 B X Hb _ IH]; intros Hin.
    + by apply elem_of_nil in Hin.
    + simpl. rewrite He. by apply IH.
    + simpl. rewrite He. by apply IH.
    + simpl. intros Hnil. apply app_eq_nil in Hnil as [Hn1 Hn2]. apply fmap_nil_inv in Hn1, Hn2.
      apply elem_of_app in Hin as [Hin|Hin].
      * rewrite <- (bag_msgs _ _ Hb) in Hin. by apply out_msgs_spec in Hin.
      * by apply IH.
Qed.

Lemma wr_len_out W E X t c v : nosend W → NoDup E → wr W E X → length (co_succ X (CoOut t c v)) ≤ 1.
Proof.
  intros Hns Hnd Hw. induction Hw as [|e X A E He _ IH|e X A E He _ IH|E1 E2 B X Hb Hw IH]; simpl.
  - rewrite Hns. simpl. lia.
  - rewrite He. by apply IH.
  - rewrite He. by apply IH.
  - apply NoDup_app in Hnd as (Hn1 & H12 & Hn2). specialize (IH Hn2).
    pose proof (bag_len _ _ t c v Hb Hn1) as Hl. rewrite length_app, !length_fmap.
    destruct (co_succ B (CoOut t c v)) as [|x1 l1] eqn:Ea; [simpl; lia|].
    destruct (co_succ X (CoOut t c v)) as [|x2 l2] eqn:Eb; [simpl in *; lia|]. exfalso.
    apply (H12 (t, c, v)).
    + rewrite <- (bag_msgs _ _ Hb). apply out_msgs_spec. by rewrite Ea.
    + apply (wr_msgs W E2 X t c v Hns Hw). by rewrite Eb.
Qed.

Lemma wr_trans W W' E E' X : wr W E X → wr W' E' W → wr W' (E ++ E') X.
Proof.
  induction 1 as [|e X A E He _ IH|e X A E He _ IH|E1 E2 B X Hb _ IH]; intros Hw'.
  - done.
  - apply wr_T; auto.
  - apply wr_F; auto.
  - rewrite <- app_assoc. apply wr_bag; auto.
Qed.

Lemma tite_wr W Y : tite W Y → wr W [] Y.
Proof. induction 1 as [|e Y A He _ IH|e Y A He _ IH]; [apply wr_refl|by apply wr_T|by apply wr_F]. Qed.

Definition mtag (m : msg) : tag := m.1.1.

Definition cm (z' : node) : list msg :=
  omap (λ a, match a with CoOut t c v => Some (t, c, v) | _ => None end) z'.

Lemma out_dec (a : coact) : (∃ t c v, a = CoOut t c v) ∨ (∀ t c v, a ≠ CoOut t c v).
Proof. destruct a; [left; by eauto|right; done..]. Qed.

Lemma cm_nout z' a : (∀ t c v, a ≠ CoOut t c v) → cm (z' ++ [a]) = cm z'.
Proof.
  intros Ha. unfold cm. rewrite omap_app. destruct a; simpl; try by rewrite app_nil_r. by destruct (Ha t c v).
Qed.

Lemma cm_out z' t c v : cm (z' ++ [CoOut t c v]) = cm z' ++ [(t, c, v)].
Proof. unfold cm. by rewrite omap_app. Qed.

Section Observer_Build.
  Context (S : node → bool) (O : node → list msg) (cl : node → list offer) (VL : list val) (f0 : nat).

  Definition sends (l : list msg) : prog := foldr (λ (m : msg) acc, (m.1.1 ∶ m.1.2 ! m.2) ∥ acc) 𝟘 l.

  Lemma sends_bag l : bag l (sends l).
  Proof.
    induction l as [|[[t c] v] l IH]; [apply bag_nil|]. exact (bag_par [(t, c, v)] l _ _ (bag_one t c v) IH).
  Qed.

  Definition fresh (prev cur : list msg) : list msg := remove_dups (list_difference cur prev).

  Lemma fresh_spec prev cur x : x ∈ fresh prev cur ↔ x ∈ cur ∧ x ∉ prev.
  Proof. unfold fresh. by rewrite elem_of_remove_dups, list_elem_of_difference. Qed.

  Definition bguard (rec : node → prog) (z : node) (o : offer) : option guard :=
    match o with
    | OffOut _ _ _ => None
    | OffIn t c => Some ((t ∶ c ?) ∙ chain VL (λ v, rec (z ++ [CoIn t c v])) (PG 𝟙))
    | OffOp t U qs => Some ((t ∶ U ⦅quote qs⦆) ∙ rec (z ++ [CoOp t U qs]))
    | OffMeas t M qs =>
        Some ((t ∶ M ⦅quote qs ▷⦆) ∙
                chain VL (λ v, match v with VNat n => rec (z ++ [CoMeas t M qs n]) | _ => PG 𝟙 end) (PG 𝟙))
    | OffInit t q => Some ((t ∶ $q := |0⟩) ∙ rec (z ++ [CoInit t q]))
    | OffUnfold _ => None
    end.

  Definition core (rec : node → prog) (z : node) : prog := PG (gsum (omap (bguard rec z) (cl z))).

  Fixpoint bt (f : nat) (prev : list msg) (z : node) : prog :=
    if S z then PG 𝟙 else
    match f with
    | 0 => 𝟘
    | Datatypes.S f' => sends (fresh prev (O z)) ∥ core (bt f' (O z)) z
    end.

  Lemma bguard_none rec z o a : (∀ t c v, a ≠ CoOut t c v) → (∀ t, o ≠ OffUnfold t) → bguard rec z o = None →
    offer_of a ≠ o.
  Proof.
    intros Ha Hu. destruct o; try done; intros _; [|by destruct (Hu t)]. destruct a; try done. by destruct (Ha t0 c0 v0).
  Qed.

  Lemma bguard_spec rec z o a g : bguard rec z o = Some g →
    (offer_of a ≠ o ∧ gco_succ g a = [])
    ∨ (offer_of a = o ∧ ∃ Y W, gco_succ g a = [Y] ∧ tite W Y
         ∧ (W = rec (z ++ [a]) ∨ (W = PG 𝟙 ∧ unlisted VL a))).
  Proof.
    destruct o as [t c v|t c|t U qs|t M qs|t q|t]; simpl; intros Hg; try done; injection Hg as <-.
    - destruct a as [t0 c0 v0|t0 c0 v0|t0 E0 qs0|t0 M0 qs0 n|t0 q0|t0]; simpl; try (left; by split).
      destruct (decide (t0 = t ∧ c0 = c)) as [[-> ->]|Hd]; [|left; split; [intros [= -> ->]; by apply Hd|done]].
      right. split; [done|].
      destruct (chain_tite VL (λ v, rec (z ++ [CoIn t c v])) (PG 𝟙) v0) as [[_ Ht]|[Hu Ht]].
      + eexists _, _. split; [done|]. split; [exact Ht|by left].
      + eexists _, _. split; [done|]. split; [exact Ht|right; by split].
    - destruct a as [t0 c0 v0|t0 c0 v0|t0 E0 qs0|t0 M0 qs0 n|t0 q0|t0]; simpl; try (left; by split).
      rewrite eval_quote.
      destruct (decide (t0 = t ∧ E0 = U ∧ Some qs = Some qs0)) as [(-> & -> & [= ->])|Hd];
        [|left; split; [intros [= -> -> ->]; by apply Hd|done]].
      right. split; [done|]. eexists _, _. split; [done|]. split; [apply ti_refl|by left].
    - destruct a as [t0 c0 v0|t0 c0 v0|t0 E0 qs0|t0 M0 qs0 n|t0 q0|t0]; simpl; try (left; by split).
      rewrite eval_quote.
      destruct (decide (t0 = t ∧ M0 = M ∧ Some qs = Some qs0)) as [(-> & -> & [= ->])|Hd];
        [|left; split; [intros [= -> -> ->]; by apply Hd|done]].
      right. split; [done|].
      destruct (chain_tite VL (λ v, match v with VNat n0 => rec (z ++ [CoMeas t M qs0 n0]) | _ => PG 𝟙 end)
                  (PG 𝟙) (VNat n)) as [[_ Ht]|[Hu Ht]].
      + eexists _, _. split; [done|]. split; [exact Ht|by left].
      + eexists _, _. split; [done|]. split; [exact Ht|right; by split].
    - destruct a as [t0 c0 v0|t0 c0 v0|t0 E0 qs0|t0 M0 qs0 n|t0 q0|t0]; simpl; try (left; by split).
      change (eval_qubit $q) with (Some q).
      destruct (decide (t0 = t ∧ Some q = Some q0)) as [(-> & [= ->])|Hd];
        [|left; split; [intros [= -> ->]; by apply Hd|done]].
      right. split; [done|]. eexists _, _. split; [done|]. split; [apply ti_refl|by left].
  Qed.

  Lemma gs_step rec z a (l : list offer) : (∀ t c v, a ≠ CoOut t c v) → (∀ t, OffUnfold t ∉ l) → NoDup l →
    (offer_of a ∉ l ∧ gco_succ (gsum (omap (bguard rec z) l)) a = [])
    ∨ (offer_of a ∈ l ∧ ∃ Y W, gco_succ (gsum (omap (bguard rec z) l)) a = [Y] ∧ tite W Y
         ∧ (W = rec (z ++ [a]) ∨ (W = PG 𝟙 ∧ unlisted VL a))).
  Proof.
    intros Ha. induction l as [|o l IH]; intros Hu Hnd.
    - left. split; [by intros ?%elem_of_nil|done].
    - apply NoDup_cons in Hnd as [Ho Hnd].
      specialize (IH (λ t Hk, Hu t (proj2 (elem_of_cons _ _ _) (or_intror Hk))) Hnd). rewrite omap_cons'.
      destruct (bguard rec z o) as [g|] eqn:Eg.
      + simpl. destruct (bguard_spec rec z o a g Eg) as [[Hne ->]|(<- & Y & W & -> & Ht & HW)].
        * simpl. destruct IH as [[Hn Hnil]|(Hin & Hex)].
          -- left. split; [|done]. intros [E|Hin]%elem_of_cons; [by apply Hne|by apply Hn].
          -- right. split; [by right|done].
        * destruct IH as [[Hn ->]|(Hin & _)]; [|by destruct Ho].
          right. split; [by left|]. exists Y, W. by split.
      + pose proof (bguard_none rec z o a Ha (λ t E, Hu t (proj2 (elem_of_cons _ _ _) (or_introl (eq_sym E)))) Eg) as Hne. destruct IH as [[Hn Hnil]|(Hin & Hex)].
        * left. split; [|done]. intros [E|Hin]%elem_of_cons; [by apply Hne|by apply Hn].
        * right. split; [by right|done].
  Qed.

  Hypothesis HS : ext_closed S.
  Hypothesis Hfuel : ∀ z, S z = false → length z < f0.
  Hypothesis Hun : ∀ z a, unlisted VL a → S (z ++ [a]) = true.
  Hypothesis Hcl : ∀ z, NoDup (cl z).
  Hypothesis Hclu : ∀ z t, OffUnfold t ∉ cl z.
  Hypothesis HOf : ∀ z x y, S z = false → x ∈ O z → y ∈ O z → mtag x = mtag y → x = y.
  Hypothesis HOm : ∀ z a x, S (z ++ [a]) = false → x ∈ O z → x ∈ O (z ++ [a]).

  Definition Wn (z : node) : prog :=
    if S z then PG 𝟙 else core (bt (f0 - Datatypes.S (length z)) (O z)) z.

  Definition En (prev : list msg) (z : node) : list msg := if S z then [] else fresh prev (O z).

  Lemma Wn_nosend z : nosend (Wn z).
  Proof. intros t c v. unfold Wn, core. destruct (S z); simpl; [done|apply gco_out]. Qed.

  Lemma bt_wr prev z : wr (Wn z) (En prev z) (bt (f0 - length z) prev z).
  Proof.
    unfold Wn, En. destruct (S z) eqn:Es.
    - destruct (f0 - length z); simpl; rewrite Es; apply wr_refl.
    - pose proof (Hfuel z Es) as Hl.
      replace (f0 - length z) with (Datatypes.S (f0 - Datatypes.S (length z))) by lia. simpl. rewrite Es.
      pose proof (wr_bag (core (bt (f0 - Datatypes.S (length z)) (O z)) z) (fresh prev (O z)) [] _ _
                    (sends_bag (fresh prev (O z))) (wr_refl _)) as Hw.
      rewrite app_nil_r in Hw. exact Hw.
  Qed.

  Lemma Wn_step z a : (∀ t c v, a ≠ CoOut t c v) →
    (co_succ (Wn z) a = [] ∧ (S z = true ∨ offer_of a ∉ cl z))
    ∨ (S z = false ∧ offer_of a ∈ cl z ∧ ∃ Y W, co_succ (Wn z) a = [Y] ∧ tite W Y
         ∧ (W = bt (f0 - Datatypes.S (length z)) (O z) (z ++ [a]) ∨ (W = PG 𝟙 ∧ unlisted VL a))).
  Proof.
    intros Ha. unfold Wn. destruct (S z) eqn:Es; [left; split; [done|by left]|]. unfold core. simpl.
    destruct (gs_step (bt (f0 - Datatypes.S (length z)) (O z)) z a (cl z) Ha (Hclu z) (Hcl z)) as [[Hn Hnil]|(Hin & Hex)].
    - left. split; [done|by right].
    - right. by split.
  Qed.

  Lemma fresh_tags prev z : S z = false → NoDup (mtag <$> fresh prev (O z)).
  Proof.
    intros Es. apply NoDup_fmap_2_strong; [|apply NoDup_remove_dups].
    intros x y Hx Hy E. apply fresh_spec in Hx as [Hx _], Hy as [Hy _]. exact (HOf z x y Es Hx Hy E).
  Qed.

  Definition inv (z' : node) (X : prog) : Prop :=
    ∃ E, wr (Wn (nout z')) E X ∧ NoDup (mtag <$> E) ∧ (∀ x, x ∈ cm z' → mtag x ∉ mtag <$> E)
      ∧ (S (nout z') = false →
           (∀ x, x ∈ E → x ∈ O (nout z')) ∧ (∀ x, x ∈ cm z' → x ∈ O (nout z'))
           ∧ ∀ x, x ∈ O (nout z') → x ∈ E ∨ x ∈ cm z').

  Lemma inv_init : inv [] (bt f0 [] []).
  Proof.
    exists (En [] []). pose proof (bt_wr [] []) as Hw. simpl in Hw. rewrite Nat.sub_0_r in Hw.
    split; [exact Hw|]. unfold En. change (nout []) with (@nil coact). destruct (S []) eqn:Es.
    - split; [apply NoDup_nil_2|]. split; [by intros x ?%elem_of_nil|done].
    - split; [by apply fresh_tags|]. split; [by intros x ?%elem_of_nil|]. intros _.
      split; [intros x Hx; by apply fresh_spec in Hx as [Hx _]|]. split; [by intros x ?%elem_of_nil|].
      intros x Hx. left. apply fresh_spec. split; [done|by intros ?%elem_of_nil].
  Qed.

  Lemma inv_nout z' a X X' : (∀ t c v, a ≠ CoOut t c v) → inv z' X → X' ∈ co_succ X a → inv (z' ++ [a]) X'.
  Proof.
    intros Ha (E & Hw & Hnd & Hcm & H3) HX'.
    destruct (wr_nout _ _ _ a Ha Hw) as [_ He]. destruct (He X' HX') as (W' & HW' & Hw').
    destruct (Wn_step (nout z') a Ha) as [[Hnil _]|(Es & Hin & Y & W0 & Eq & Ht & HW0)].
    { rewrite Hnil in HW'. by apply elem_of_nil in HW'. }
    rewrite Eq in HW'. apply list_elem_of_singleton in HW'. subst W'.
    unfold inv. rewrite (cm_nout z' a Ha), (nout_nout z' a Ha). set (z := nout z') in *. set (z1 := z ++ [a]).
    assert (Hc : wr (Wn z1) (En (O z) z1) W0).
    { destruct HW0 as [->|[-> Hu]].
      - pose proof (bt_wr (O z) (z ++ [a])) as Hb. rewrite length_app in Hb. simpl in Hb.
        replace (f0 - (length z + 1)) with (f0 - Datatypes.S (length z)) in Hb by lia. exact Hb.
      - unfold Wn, En, z1. rewrite (Hun z a Hu). apply wr_refl. }
    pose proof (wr_trans _ _ _ _ _ Hw' (wr_trans _ _ _ _ _ (tite_wr _ _ Ht) Hc)) as Hfin. simpl in Hfin.
    exists (E ++ En (O z) z1). split; [exact Hfin|]. unfold En. destruct (S z1) eqn:Es'.
    - rewrite app_nil_r. split; [done|]. split; [done|]. intros Hf. congruence.
    - destruct (H3 Es) as (Ha1 & Ha2 & Ha3). split; [|split].
      + rewrite fmap_app. apply NoDup_app. split; [done|]. split; [|by apply fresh_tags].
        intros t' (x & -> & Hx)%list_elem_of_fmap (y & Hxy & Hy)%list_elem_of_fmap.
        apply fresh_spec in Hy as [Hy Hny]. apply Hny.
        rewrite <- (HOf z1 x y Es' (HOm z a x Es' (Ha1 x Hx)) Hy Hxy). by apply Ha1.
      + intros x Hx. rewrite fmap_app. intros [Hin'|(y & Hxy & Hy)%list_elem_of_fmap]%elem_of_app.
        * by apply (Hcm x Hx).
        * apply fresh_spec in Hy as [Hy Hny]. apply Hny.
          rewrite <- (HOf z1 x y Es' (HOm z a x Es' (Ha2 x Hx)) Hy Hxy). by apply Ha2.
      + intros _. split; [|split].
        * intros x [Hx|Hx]%elem_of_app; [apply HOm; auto|by apply fresh_spec in Hx as [Hx _]].
        * intros x Hx. apply HOm; auto.
        * intros x Hx. destruct (decide (x ∈ O z)) as [Hd|Hd].
          -- destruct (Ha3 x Hd) as [He'|He']; [left; apply elem_of_app; by left|by right].
          -- left. apply elem_of_app. right. by apply fresh_spec.
  Qed.

  Lemma inv_out z' t c v X X' : inv z' X → X' ∈ co_succ X (CoOut t c v) → inv (z' ++ [CoOut t c v]) X'.
  Proof.
    intros (E & Hw & Hnd & Hcm & H3) HX'.
    destruct (wr_out _ _ _ t c v X' (Wn_nosend _) Hw HX') as (E1 & E2 & -> & Hw').
    unfold inv. rewrite cm_out, nout_out. exists (E1 ++ E2). split; [exact Hw'|].
    rewrite fmap_app, fmap_cons in Hnd. apply NoDup_app in Hnd as (N1 & N12 & N2).
    apply NoDup_cons in N2 as [Nk N2].
    assert (Hsub : ∀ x, x ∈ E1 ++ E2 → x ∈ E1 ++ (t, c, v) :: E2).
    { intros x [Hx|Hx]%elem_of_app; apply elem_of_app; [by left|right; by right]. }
    split; [|split].
    - rewrite fmap_app. apply NoDup_app. split; [done|]. split; [|done]. intros t' Ht Ht2.
      apply (N12 t' Ht). by right.
    - intros x [Hx|Hx]%elem_of_app.
      + intros (y & Hxy & Hy)%list_elem_of_fmap. apply (Hcm x Hx). apply list_elem_of_fmap. exists y. auto.
      + apply list_elem_of_singleton in Hx. subst x. rewrite fmap_app.
        intros [Hin|Hin]%elem_of_app; [|by apply Nk]. apply (N12 _ Hin). by left.
    - intros Es. destruct (H3 Es) as (Ha1 & Ha2 & Ha3). split; [|split].
      + intros x Hx. apply Ha1. by apply Hsub.
      + intros x [Hx|Hx]%elem_of_app; [by apply Ha2|]. apply list_elem_of_singleton in Hx. subst x.
        apply Ha1. apply elem_of_app. right. by left.
      + intros x Hx. destruct (Ha3 x Hx) as [He|He]; [|right; apply elem_of_app; by left].
        apply elem_of_app in He as [He|He]; [left; apply elem_of_app; by left|].
        apply elem_of_cons in He as [->|He]; [right; apply elem_of_app; right; by left|].
        left. apply elem_of_app. by right.
  Qed.

  Lemma inv_len z' X a : inv z' X → length (co_succ X a) ≤ 1.
  Proof.
    intros (E & Hw & Hnd & _). destruct (out_dec a) as [(t & c & v & ->)|Ha].
    - apply (wr_len_out (Wn (nout z')) E X t c v); [apply Wn_nosend| |done]. by apply NoDup_fmap_1 in Hnd.
    - destruct (wr_nout _ _ _ a Ha Hw) as [-> _].
      destruct (Wn_step (nout z') a Ha) as [[-> _]|(_ & _ & Y & W0 & -> & _)]; simpl; lia.
  Qed.

  Definition BT : prog := bt f0 [] [].

  Lemma bt_inv z' : (∀ X, X ∈ tnodes BT z' → inv z' X) ∧ length (tnodes BT z') ≤ 1.
  Proof.
    induction z' as [|a z' [IHi IHl]] using rev_ind.
    - rewrite tnodes_nil. split; [|simpl; lia]. intros X ->%list_elem_of_singleton. apply inv_init.
    - split.
      + intros X' (X & HX & HX')%tnodes_app_elem. destruct (out_dec a) as [(t & c & v & ->)|Ha].
        * exact (inv_out z' t c v X X' (IHi X HX) HX').
        * exact (inv_nout z' a X X' Ha (IHi X HX) HX').
      + rewrite tnodes_app. destruct (tnodes BT z') as [|X [|X2 l]] eqn:Et; simpl in *; [lia| |lia].
        rewrite app_nil_r. apply (inv_len z'). apply IHi. by left.
  Qed.

  Hypothesis Hclo : ∀ z t c v, OffOut t c v ∉ cl z.

  Definition clpath (z : node) : Prop := ∀ z' a z2, z = z' ++ a :: z2 → S z' = false ∧ offer_of a ∈ cl z'.

  Lemma clpath_plain z : clpath z → plain z.
  Proof.
    intros Hc t c v Hin. apply list_elem_of_split in Hin as (z' & z2 & ->).
    destruct (Hc z' _ z2 eq_refl) as [_ Hin]. exact (Hclo z' t c v Hin).
  Qed.

  Lemma clpath_snoc z a : clpath (z ++ [a]) ↔ clpath z ∧ S z = false ∧ offer_of a ∈ cl z.
  Proof.
    split.
    - intros Hc. split.
      + intros z' a0 z2 ->. apply (Hc z' a0 (z2 ++ [a])). by rewrite <- app_assoc.
      + apply (Hc z a []). done.
    - intros (Hc & Hs & Hin) z' a0 z2 E. destruct (split_snoc z z' z2 a a0 E) as [(-> & -> & _)|(z2' & _ & ->)].
      + done.
      + by apply (Hc z' a0 z2').
  Qed.

  Lemma plain_snoc z a : plain (z ++ [a]) → plain z ∧ ∀ t c v, a ≠ CoOut t c v.
  Proof.
    intros Hp. split.
    - intros t c v Hin. apply (Hp t c v). apply elem_of_app. by left.
    - intros t c v ->. apply (Hp t c v). apply elem_of_app. right. by left.
  Qed.

  Lemma bt_state z : clpath z → ∃ X, tnodes BT z = [X] ∧ inv z X.
  Proof.
    induction z as [|a z IH] using rev_ind; intros Hc.
    - exists BT. split; [done|apply inv_init].
    - apply clpath_snoc in Hc as (Hc & Hs & Hin). destruct (IH Hc) as (X & Et & Hinv).
      assert (Ha : ∀ t c v, a ≠ CoOut t c v).
      { intros t c v ->. exact (Hclo z t c v Hin). }
      pose proof (clpath_plain z Hc) as Hpl.
      destruct Hinv as (E & Hw & Hrest). pose proof Hw as Hw0. rewrite (nout_plain z Hpl) in Hw0.
      destruct (wr_nout _ _ _ a Ha Hw0) as [Hl _].
      destruct (Wn_step z a Ha) as [[_ [Hf|Hf]]|(_ & _ & Y & W0 & Eq & _)]; [congruence|done|].
      rewrite Eq in Hl. simpl in Hl.
      rewrite tnodes_app, Et. simpl. rewrite app_nil_r.
      destruct (co_succ X a) as [|X' [|X2 l]] eqn:Ex; simpl in Hl; try lia.
      exists X'. split; [done|]. apply (inv_nout z a X X' Ha); [by exists E|]. rewrite Ex. by left.
  Qed.

  Lemma bt_clpath z : plain z → tnodes BT z ≠ [] → clpath z.
  Proof.
    induction z as [|a z IH] using rev_ind; intros Hp Hne.
    - intros z' a z2 E. by destruct z'.
    - apply plain_snoc in Hp as [Hp Ha]. pose proof (tnodes_app_nonempty BT z [a] Hne) as Hne'.
      pose proof (IH Hp Hne') as Hc. apply clpath_snoc. split; [done|].
      destruct (tnodes BT (z ++ [a])) as [|X' l] eqn:Et; [done|].
      assert (HX' : X' ∈ tnodes BT (z ++ [a])) by (rewrite Et; by left).
      apply tnodes_app_elem in HX' as (X & HX & HX').
      destruct (proj1 (bt_inv z) X HX) as (E & Hw & _). rewrite (nout_plain z Hp) in Hw.
      destruct (wr_nout _ _ _ a Ha Hw) as [_ He]. destruct (He X' HX') as (W' & HW' & _).
      destruct (Wn_step z a Ha) as [[Hnil _]|(Hs & Hin & _)]; [|done].
      rewrite Hnil in HW'. by apply elem_of_nil in HW'.
  Qed.

  Lemma bt_menu z o : plain z → (∀ t c v, o ≠ OffOut t c v) →
    (menu BT z o ↔ clpath z ∧ S z = false ∧ o ∈ cl z).
  Proof.
    intros Hp Ho. split.
    - intros (X & a & HX & <- & Hne).
      assert (Hc : clpath z).
      { apply (bt_clpath z Hp). intros E. rewrite E in HX. by apply elem_of_nil in HX. }
      split; [done|].
      assert (Ha : ∀ t c v, a ≠ CoOut t c v). { intros t c v ->. by apply (Ho t c v). }
      destruct (proj1 (bt_inv z) X HX) as (E & Hw & _). rewrite (nout_plain z Hp) in Hw.
      destruct (wr_nout _ _ _ a Ha Hw) as [Hl _].
      destruct (Wn_step z a Ha) as [[Hnil _]|(Hs & Hin & _)]; [|done].
      rewrite Hnil in Hl. destruct (co_succ X a); simpl in *; done.
    - intros (Hc & Hs & Hin). destruct (bt_state z Hc) as (X & Et & E & Hw & _).
      rewrite (nout_plain z Hp) in Hw. exists X, (co_of o). split; [rewrite Et; by left|].
      split; [apply offer_co_of|].
      assert (Ha : ∀ t c v, co_of o ≠ CoOut t c v).
      { intros t c v Eo. apply (Ho t c v). rewrite <- (offer_co_of o), Eo. done. }
      destruct (wr_nout _ _ _ (co_of o) Ha Hw) as [Hl _].
      destruct (Wn_step z (co_of o) Ha) as [[_ [Hf|Hf]]|(_ & _ & Y & W0 & Eq & _)].
      + congruence.
      + rewrite offer_co_of in Hf. done.
      + rewrite Eq in Hl. intros Enil. rewrite Enil in Hl. done.
  Qed.

  Lemma Wn_succ z : successb (Wn z) = S z.
  Proof.
    unfold Wn. destruct (S z); [done|]. unfold core. simpl. apply gsum_nosucc.
    intros g (o & _ & Hg)%list_elem_of_omap. destruct o; simpl in Hg; try done; by injection Hg as <-.
  Qed.

  Lemma bt_succ_at z : clpath z → succ_at BT z = S z.
  Proof.
    intros Hc. destruct (bt_state z Hc) as (X & Et & E & Hw & _). unfold succ_at. rewrite Et. simpl.
    rewrite orb_false_r, (wr_succ _ _ _ Hw), Wn_succ. by rewrite (nout_plain z (clpath_plain z Hc)).
  Qed.

  Lemma S_app z z' : S z = true → S (z ++ z') = true.
  Proof.
    intros Hs. induction z' as [|a z' IH] using rev_ind; [by rewrite app_nil_r|]. rewrite app_assoc. by apply HS.
  Qed.

  Lemma clpath_take z i : clpath z → clpath (take i z).
  Proof.
    intros Hc z' a z2 E. apply (Hc z' a (z2 ++ drop i z)). rewrite <- (take_drop i z) at 1. rewrite E.
    by rewrite <- app_assoc.
  Qed.

  Lemma bt_S z : clpath z → S_T BT z = S z.
  Proof.
    intros Hc. apply eq_true_iff_eq. rewrite S_T_spec. split.
    - intros (i & Hi & Hs). rewrite (bt_succ_at _ (clpath_take z i Hc)) in Hs.
      rewrite <- (take_drop i z). by apply S_app.
    - intros Hs. exists (length z). split; [done|]. rewrite firstn_all. by rewrite (bt_succ_at z Hc).
  Qed.

  Lemma bt_S_up z : plain z → S_T BT z = true → S z = true.
  Proof.
    intros Hp (i & Hi & Hs)%S_T_spec.
    assert (Hc : clpath (take i z)).
    { apply bt_clpath.
      - intros t c v Hin. apply (Hp t c v). rewrite <- (take_drop i z). apply elem_of_app. by left.
      - intros E. unfold succ_at in Hs. by rewrite E in Hs. }
    rewrite (bt_succ_at _ Hc) in Hs. rewrite <- (take_drop i z). by apply S_app.
  Qed.

  Lemma plain_cm z : plain z → cm z = [].
  Proof.
    induction z as [|a z IH]; intros Hp; [done|]. unfold cm. rewrite omap_cons'.
    destruct a; try (apply IH; intros t' c' v' Hin; apply (Hp t' c' v'); by right).
    exfalso. apply (Hp t c v). by left.
  Qed.

  Lemma bt_O z x : clpath z → S z = false → (x ∈ O_T BT z ↔ x ∈ O z).
  Proof.
    intros Hc Hs. destruct (bt_state z Hc) as (X & Et & E & Hw & _ & _ & H3).
    pose proof (clpath_plain z Hc) as Hp. rewrite (nout_plain z Hp) in Hw, H3.
    destruct (H3 Hs) as (Ha1 & _ & Ha3). rewrite (plain_cm z Hp) in Ha3. destruct x as [[t c] v].
    setoid_rewrite O_T_spec. split.
    - intros (X0 & HX0 & Hne). rewrite Et in HX0. apply list_elem_of_singleton in HX0. subst X0.
      apply Ha1. by apply (wr_msgs _ _ _ t c v (Wn_nosend z) Hw).
    - intros Hin. exists X. split; [rewrite Et; by left|]. apply (wr_msgs _ _ _ t c v (Wn_nosend z) Hw).
      destruct (Ha3 _ Hin) as [He|He]; [done|by apply elem_of_nil in He].
  Qed.

  Lemma bt_nostate z : plain z → ¬ clpath z → tnodes BT z = [].
  Proof.
    intros Hp Hn. destruct (tnodes BT z) eqn:E; [done|]. exfalso. apply Hn, (bt_clpath z Hp). by rewrite E.
  Qed.

  Lemma bt_gone z z' t c v c' v' Y : Y ∈ tnodes BT (z ++ [CoOut t c v] ++ z') → co_succ Y (CoOut t c' v') = [].
  Proof.
    intros HY. destruct (proj1 (bt_inv _) Y HY) as (E & Hw & _ & Hcm & _).
    destruct (co_succ Y (CoOut t c' v')) eqn:Ey; [done|]. exfalso.
    apply (Hcm (t, c, v)).
    - unfold cm. rewrite !omap_app. apply elem_of_app. right. apply elem_of_app. left. by left.
    - apply list_elem_of_fmap. exists (t, c', v'). split; [done|].
      apply (wr_msgs _ _ _ t c' v' (Wn_nosend _) Hw). by rewrite Ey.
  Qed.

  Context (TG : tag * okind → Prop) (OC IC : channel → Prop).
  Hypothesis Hcl_ok : ∀ z o, o ∈ cl z → TG (off_tag o, off_kind o) ∧ ∀ t c, o = OffIn t c → IC c.
  Hypothesis HO_ok : ∀ z t c v, S z = false → (t, c, v) ∈ O z → TG (t, KOut) ∧ OC c.

  Lemma sends_syn l : (∀ t c v, (t, c, v) ∈ l → TG (t, KOut) ∧ OC c) → syn TG OC IC (sends l).
  Proof.
    induction l as [|[[t c] v] l IH]; intros Hl; [apply syn_nil|]. simpl. apply syn_par.
    - destruct (Hl t c v ltac:(by left)) as [Ht Hc]. split; [done|].
      split; [intros x ->%list_elem_of_singleton; done|]. split; [intros x ->%list_elem_of_singleton; done|].
      intros x Hx. by apply elem_of_nil in Hx.
    - apply IH. intros t' c' v' Hin. apply (Hl t' c' v'). by right.
  Qed.

  Lemma bguard_syn rec z o g :
    (∀ z1, syn TG OC IC (rec z1)) → o ∈ cl z → bguard rec z o = Some g → gsyn TG OC IC g.
  Proof.
    intros Hrec Hin Hg. destruct (Hcl_ok z o Hin) as [Ht Hc].
    destruct o as [t c v|t c|t U qs|t M qs|t q|t]; simpl in Hg; try done; injection Hg as <-.
    - apply gsyn_pre; [done|exact Ht|intros t' c' [= -> ->]; by eapply Hc|].
      apply syn_chain; [intros v; apply Hrec|apply syn_succ].
    - apply gsyn_pre; [done|exact Ht|done|apply Hrec].
    - apply gsyn_pre; [done|exact Ht|done|].
      apply syn_chain; [intros v; destruct v; try apply syn_succ; apply Hrec|apply syn_succ].
    - apply gsyn_pre; [done|exact Ht|done|apply Hrec].
  Qed.

  Lemma bt_syn f : ∀ prev z, syn TG OC IC (bt f prev z).
  Proof.
    induction f as [|f IH]; intros prev z; simpl; destruct (S z) eqn:Es.
    - apply syn_succ.
    - apply syn_nil.
    - apply syn_succ.
    - apply syn_par.
      + apply sends_syn. intros t c v Hin. apply fresh_spec in Hin as [Hin _]. exact (HO_ok z t c v Es Hin).
      + apply syn_PG, gsum_syn. intros g (o & Hin & Hg)%list_elem_of_omap.
        exact (bguard_syn (bt f (O z)) z o g (IH (O z)) Hin Hg).
  Qed.
End Observer_Build.

End Build.

(* end hide *)
