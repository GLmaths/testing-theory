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
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Pull lqCCS.Testing.Head lqCCS.Testing.Modes lqCCS.Testing.Syn lqCCS.Testing.Assembly lqCCS.Testing.Final.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Inductive bag : list msg → proc → Prop :=
| bag_nil : bag [] 𝟘
| bag_one k c v : bag [(k, c, v)] (PSend k c (EVal v))
| bag_par E1 E2 B1 B2 : bag E1 B1 → bag E2 B2 → bag (E1 ++ E2) (B1 ∥ B2).

Lemma bag_succ E B : bag E B → successb B = false.
Proof. induction 1 as [|k c v|E1 E2 B1 B2 _ IH1 _ IH2]; simpl; [done|done|by rewrite IH1, IH2]. Qed.

Lemma bag_nout E B a : bag E B → (∀ k c v, a ≠ CoOut k c v) → co_succ B a = [].
Proof.
  intros Hb Ha. induction Hb as [|k c v|E1 E2 B1 B2 _ IH1 _ IH2]; simpl.
  - done.
  - destruct a; try done. by destruct (Ha k0 c0 v0).
  - by rewrite IH1, IH2.
Qed.

Lemma bag_out E B k c v B' : bag E B → B' ∈ co_succ B (CoOut k c v) →
  ∃ E1 E2, E = E1 ++ (k, c, v) :: E2 ∧ bag (E1 ++ E2) B'.
Proof.
  intros Hb. revert B'. induction Hb as [|k0 c0 v0|E1 E2 B1 B2 Hb1 IH1 Hb2 IH2]; intros B' Hin; simpl in Hin.
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
Proof. induction 1 as [|k c v|E1 E2 B1 B2 _ IH1 _ IH2]; simpl; [done|done|by rewrite IH1, IH2]. Qed.

Lemma bag_len E B k c v : bag E B → NoDup E → length (co_succ B (CoOut k c v)) ≤ 1.
Proof.
  induction 1 as [|k0 c0 v0|E1 E2 B1 B2 Hb1 IH1 Hb2 IH2]; intros Hnd; simpl.
  - lia.
  - case_decide; simpl; lia.
  - apply NoDup_app in Hnd as (Hn1 & H12 & Hn2). specialize (IH1 Hn1). specialize (IH2 Hn2).
    rewrite length_app, !length_fmap.
    destruct (co_succ B1 (CoOut k c v)) as [|x1 l1] eqn:Ea; [simpl; lia|].
    destruct (co_succ B2 (CoOut k c v)) as [|x2 l2] eqn:Eb; [simpl in *; lia|]. exfalso.
    apply (H12 (k, c, v)).
    + rewrite <- (bag_msgs _ _ Hb1). apply out_msgs_spec. by rewrite Ea.
    + rewrite <- (bag_msgs _ _ Hb2). apply out_msgs_spec. by rewrite Eb.
Qed.

Inductive wr (W : proc) : list msg → proc → Prop :=
| wr_refl : wr W [] W
| wr_T e X A E : eval e = Some (VBool true) → wr W E X → wr W E (PIte e X A)
| wr_F e X A E : eval e = Some (VBool false) → wr W E X → wr W E (PIte e A X)
| wr_bag E1 E2 B X : bag E1 B → wr W E2 X → wr W (E1 ++ E2) (B ∥ X).

Lemma wr_succ W E X : wr W E X → successb X = successb W.
Proof.
  induction 1 as [|e X A E He _ IH|e X A E He _ IH|E1 E2 B X Hb _ IH]; simpl.
  - done.
  - by rewrite He.
  - by rewrite He.
  - by rewrite (bag_succ _ _ Hb).
Qed.

Lemma wr_nout W E X a : (∀ k c v, a ≠ CoOut k c v) → wr W E X →
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

Lemma wr_out W E X k c v X' : nosend W → wr W E X → X' ∈ co_succ X (CoOut k c v) →
  ∃ E1 E2, E = E1 ++ (k, c, v) :: E2 ∧ wr W (E1 ++ E2) X'.
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

Lemma wr_msgs W E X k c v : nosend W → wr W E X → (co_succ X (CoOut k c v) ≠ [] ↔ (k, c, v) ∈ E).
Proof.
  intros Hns Hw. split.
  - intros Hne. destruct (co_succ X (CoOut k c v)) as [|X' l] eqn:Ex; [done|].
    destruct (wr_out W E X k c v X' Hns Hw) as (E1 & E2 & -> & _); [rewrite Ex; by left|].
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

Lemma wr_len_out W E X k c v : nosend W → NoDup E → wr W E X → length (co_succ X (CoOut k c v)) ≤ 1.
Proof.
  intros Hns Hnd Hw. induction Hw as [|e X A E He _ IH|e X A E He _ IH|E1 E2 B X Hb Hw IH]; simpl.
  - rewrite Hns. simpl. lia.
  - rewrite He. by apply IH.
  - rewrite He. by apply IH.
  - apply NoDup_app in Hnd as (Hn1 & H12 & Hn2). specialize (IH Hn2).
    pose proof (bag_len _ _ k c v Hb Hn1) as Hl. rewrite length_app, !length_fmap.
    destruct (co_succ B (CoOut k c v)) as [|x1 l1] eqn:Ea; [simpl; lia|].
    destruct (co_succ X (CoOut k c v)) as [|x2 l2] eqn:Eb; [simpl in *; lia|]. exfalso.
    apply (H12 (k, c, v)).
    + rewrite <- (bag_msgs _ _ Hb). apply out_msgs_spec. by rewrite Ea.
    + apply (wr_msgs W E2 X k c v Hns Hw). by rewrite Eb.
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

Definition cm (m : node) : list msg :=
  omap (λ a, match a with CoOut k c v => Some (k, c, v) | _ => None end) m.

Lemma out_dec (a : coact) : (∃ k c v, a = CoOut k c v) ∨ (∀ k c v, a ≠ CoOut k c v).
Proof. destruct a; [left; by eauto|right; done..]. Qed.

Lemma cm_nout m a : (∀ k c v, a ≠ CoOut k c v) → cm (m ++ [a]) = cm m.
Proof.
  intros Ha. unfold cm. rewrite omap_app. destruct a; simpl; try by rewrite app_nil_r. by destruct (Ha k c v).
Qed.

Lemma cm_out m k c v : cm (m ++ [CoOut k c v]) = cm m ++ [(k, c, v)].
Proof. unfold cm. by rewrite omap_app. Qed.

Section Build.
  Context (S : node → bool) (O : node → list msg) (cl : node → list offer) (VL : list val) (f0 : nat).

  Definition sends (l : list msg) : proc := foldr (λ m acc, PSend m.1.1 m.1.2 (EVal m.2) ∥ acc) 𝟘 l.

  Lemma sends_bag l : bag l (sends l).
  Proof.
    induction l as [|[[k c] v] l IH]; [apply bag_nil|]. exact (bag_par [(k, c, v)] l _ _ (bag_one k c v) IH).
  Qed.

  Definition fresh (prev cur : list msg) : list msg := remove_dups (list_difference cur prev).

  Lemma fresh_spec prev cur x : x ∈ fresh prev cur ↔ x ∈ cur ∧ x ∉ prev.
  Proof. unfold fresh. by rewrite elem_of_remove_dups, list_elem_of_difference. Qed.

  Definition bguard (rec : node → proc) (n : node) (o : offer) : option guard :=
    match o with
    | OffOut _ _ _ => None
    | OffIn k c => Some (PRecv k c ∙ chain VL (λ v, rec (n ++ [CoIn k c v])) (PG ①))
    | OffOp k E qs => Some (POp k E (quote qs) ∙ rec (n ++ [CoOp k E qs]))
    | OffMeas k M qs =>
        Some (PMeas k M (quote qs) ∙
                chain VL (λ v, match v with VNat i => rec (n ++ [CoMeas k M qs i]) | _ => PG ① end) (PG ①))
    | OffInit k qs => Some (PInit k (quote qs) ∙ rec (n ++ [CoInit k qs]))
    end.

  Definition core (rec : node → proc) (n : node) : proc := PG (gsum (omap (bguard rec n) (cl n))).

  Fixpoint bt (f : nat) (prev : list msg) (n : node) : proc :=
    if S n then PG ① else
    match f with
    | 0 => 𝟘
    | Datatypes.S f' => sends (fresh prev (O n)) ∥ core (bt f' (O n)) n
    end.

  Lemma bguard_none rec n o a : (∀ k c v, a ≠ CoOut k c v) → bguard rec n o = None → offer_of a ≠ o.
  Proof. intros Ha. destruct o; try done. intros _. destruct a; try done. by destruct (Ha k0 c0 v0). Qed.

  Lemma bguard_spec rec n o a g : bguard rec n o = Some g →
    (offer_of a ≠ o ∧ gco_succ g a = [])
    ∨ (offer_of a = o ∧ ∃ Y W, gco_succ g a = [Y] ∧ tite W Y
         ∧ (W = rec (n ++ [a]) ∨ (W = PG ① ∧ unlisted VL a))).
  Proof.
    destruct o as [k c v|k c|k E qs|k M qs|k qs]; simpl; intros Hg; try done; injection Hg as <-.
    - destruct a as [k0 c0 v0|k0 c0 v0|k0 E0 qs0|k0 M0 qs0 i|k0 qs0]; simpl; try (left; by split).
      destruct (decide (k0 = k ∧ c0 = c)) as [[-> ->]|Hd]; [|left; split; [intros [= -> ->]; by apply Hd|done]].
      right. split; [done|].
      destruct (chain_tite VL (λ v, rec (n ++ [CoIn k c v])) (PG ①) v0) as [[_ Ht]|[Hu Ht]].
      + eexists _, _. split; [done|]. split; [exact Ht|by left].
      + eexists _, _. split; [done|]. split; [exact Ht|right; by split].
    - destruct a as [k0 c0 v0|k0 c0 v0|k0 E0 qs0|k0 M0 qs0 i|k0 qs0]; simpl; try (left; by split).
      rewrite eval_quote.
      destruct (decide (k0 = k ∧ E0 = E ∧ Some qs = Some qs0)) as [(-> & -> & [= ->])|Hd];
        [|left; split; [intros [= -> -> ->]; by apply Hd|done]].
      right. split; [done|]. eexists _, _. split; [done|]. split; [apply ti_refl|by left].
    - destruct a as [k0 c0 v0|k0 c0 v0|k0 E0 qs0|k0 M0 qs0 i|k0 qs0]; simpl; try (left; by split).
      rewrite eval_quote.
      destruct (decide (k0 = k ∧ M0 = M ∧ Some qs = Some qs0)) as [(-> & -> & [= ->])|Hd];
        [|left; split; [intros [= -> -> ->]; by apply Hd|done]].
      right. split; [done|].
      destruct (chain_tite VL (λ v, match v with VNat i0 => rec (n ++ [CoMeas k M qs0 i0]) | _ => PG ① end)
                  (PG ①) (VNat i)) as [[_ Ht]|[Hu Ht]].
      + eexists _, _. split; [done|]. split; [exact Ht|by left].
      + eexists _, _. split; [done|]. split; [exact Ht|right; by split].
    - destruct a as [k0 c0 v0|k0 c0 v0|k0 E0 qs0|k0 M0 qs0 i|k0 qs0]; simpl; try (left; by split).
      rewrite eval_quote.
      destruct (decide (k0 = k ∧ Some qs = Some qs0)) as [(-> & [= ->])|Hd];
        [|left; split; [intros [= -> ->]; by apply Hd|done]].
      right. split; [done|]. eexists _, _. split; [done|]. split; [apply ti_refl|by left].
  Qed.

  Lemma gs_step rec n a (l : list offer) : (∀ k c v, a ≠ CoOut k c v) → NoDup l →
    (offer_of a ∉ l ∧ gco_succ (gsum (omap (bguard rec n) l)) a = [])
    ∨ (offer_of a ∈ l ∧ ∃ Y W, gco_succ (gsum (omap (bguard rec n) l)) a = [Y] ∧ tite W Y
         ∧ (W = rec (n ++ [a]) ∨ (W = PG ① ∧ unlisted VL a))).
  Proof.
    intros Ha. induction l as [|o l IH]; intros Hnd.
    - left. split; [by intros ?%elem_of_nil|done].
    - apply NoDup_cons in Hnd as [Ho Hnd]. specialize (IH Hnd). rewrite omap_cons'.
      destruct (bguard rec n o) as [g|] eqn:Eg.
      + simpl. destruct (bguard_spec rec n o a g Eg) as [[Hne ->]|(<- & Y & W & -> & Ht & HW)].
        * simpl. destruct IH as [[Hn Hnil]|(Hin & Hex)].
          -- left. split; [|done]. intros [E|Hin]%elem_of_cons; [by apply Hne|by apply Hn].
          -- right. split; [by right|done].
        * destruct IH as [[Hn ->]|(Hin & _)]; [|by destruct Ho].
          right. split; [by left|]. exists Y, W. by split.
      + pose proof (bguard_none rec n o a Ha Eg) as Hne. destruct IH as [[Hn Hnil]|(Hin & Hex)].
        * left. split; [|done]. intros [E|Hin]%elem_of_cons; [by apply Hne|by apply Hn].
        * right. split; [by right|done].
  Qed.

  Hypothesis HS : ext_closed S.
  Hypothesis Hfuel : ∀ n, S n = false → length n < f0.
  Hypothesis Hun : ∀ n a, unlisted VL a → S (n ++ [a]) = true.
  Hypothesis Hcl : ∀ n, NoDup (cl n).
  Hypothesis HOf : ∀ n x y, S n = false → x ∈ O n → y ∈ O n → mtag x = mtag y → x = y.
  Hypothesis HOm : ∀ n a x, S (n ++ [a]) = false → x ∈ O n → x ∈ O (n ++ [a]).

  Definition Wn (n : node) : proc :=
    if S n then PG ① else core (bt (f0 - Datatypes.S (length n)) (O n)) n.

  Definition En (prev : list msg) (n : node) : list msg := if S n then [] else fresh prev (O n).

  Lemma Wn_nosend n : nosend (Wn n).
  Proof. intros k c v. unfold Wn, core. destruct (S n); simpl; [done|apply gco_out]. Qed.

  Lemma bt_wr prev n : wr (Wn n) (En prev n) (bt (f0 - length n) prev n).
  Proof.
    unfold Wn, En. destruct (S n) eqn:Es.
    - destruct (f0 - length n); simpl; rewrite Es; apply wr_refl.
    - pose proof (Hfuel n Es) as Hl.
      replace (f0 - length n) with (Datatypes.S (f0 - Datatypes.S (length n))) by lia. simpl. rewrite Es.
      pose proof (wr_bag (core (bt (f0 - Datatypes.S (length n)) (O n)) n) (fresh prev (O n)) [] _ _
                    (sends_bag (fresh prev (O n))) (wr_refl _)) as Hw.
      rewrite app_nil_r in Hw. exact Hw.
  Qed.

  Lemma Wn_step n a : (∀ k c v, a ≠ CoOut k c v) →
    (co_succ (Wn n) a = [] ∧ (S n = true ∨ offer_of a ∉ cl n))
    ∨ (S n = false ∧ offer_of a ∈ cl n ∧ ∃ Y W, co_succ (Wn n) a = [Y] ∧ tite W Y
         ∧ (W = bt (f0 - Datatypes.S (length n)) (O n) (n ++ [a]) ∨ (W = PG ① ∧ unlisted VL a))).
  Proof.
    intros Ha. unfold Wn. destruct (S n) eqn:Es; [left; split; [done|by left]|]. unfold core. simpl.
    destruct (gs_step (bt (f0 - Datatypes.S (length n)) (O n)) n a (cl n) Ha (Hcl n)) as [[Hn Hnil]|(Hin & Hex)].
    - left. split; [done|by right].
    - right. by split.
  Qed.

  Lemma fresh_tags prev n : S n = false → NoDup (mtag <$> fresh prev (O n)).
  Proof.
    intros Es. apply NoDup_fmap_2_strong; [|apply NoDup_remove_dups].
    intros x y Hx Hy E. apply fresh_spec in Hx as [Hx _], Hy as [Hy _]. exact (HOf n x y Es Hx Hy E).
  Qed.

  Definition inv (m : node) (X : proc) : Prop :=
    ∃ E, wr (Wn (nout m)) E X ∧ NoDup (mtag <$> E) ∧ (∀ x, x ∈ cm m → mtag x ∉ mtag <$> E)
      ∧ (S (nout m) = false →
           (∀ x, x ∈ E → x ∈ O (nout m)) ∧ (∀ x, x ∈ cm m → x ∈ O (nout m))
           ∧ ∀ x, x ∈ O (nout m) → x ∈ E ∨ x ∈ cm m).

  Lemma inv_init : inv [] (bt f0 [] []).
  Proof.
    exists (En [] []). pose proof (bt_wr [] []) as Hw. simpl in Hw. rewrite Nat.sub_0_r in Hw.
    split; [exact Hw|]. unfold En. change (nout []) with (@nil coact). destruct (S []) eqn:Es.
    - split; [apply NoDup_nil_2|]. split; [by intros x ?%elem_of_nil|done].
    - split; [by apply fresh_tags|]. split; [by intros x ?%elem_of_nil|]. intros _.
      split; [intros x Hx; by apply fresh_spec in Hx as [Hx _]|]. split; [by intros x ?%elem_of_nil|].
      intros x Hx. left. apply fresh_spec. split; [done|by intros ?%elem_of_nil].
  Qed.

  Lemma inv_nout m a X X' : (∀ k c v, a ≠ CoOut k c v) → inv m X → X' ∈ co_succ X a → inv (m ++ [a]) X'.
  Proof.
    intros Ha (E & Hw & Hnd & Hcm & H3) HX'.
    destruct (wr_nout _ _ _ a Ha Hw) as [_ He]. destruct (He X' HX') as (W' & HW' & Hw').
    destruct (Wn_step (nout m) a Ha) as [[Hnil _]|(Es & Hin & Y & W0 & Eq & Ht & HW0)].
    { rewrite Hnil in HW'. by apply elem_of_nil in HW'. }
    rewrite Eq in HW'. apply list_elem_of_singleton in HW'. subst W'.
    unfold inv. rewrite (cm_nout m a Ha), (nout_nout m a Ha). set (n := nout m) in *. set (n' := n ++ [a]).
    assert (Hc : wr (Wn n') (En (O n) n') W0).
    { destruct HW0 as [->|[-> Hu]].
      - pose proof (bt_wr (O n) (n ++ [a])) as Hb. rewrite length_app in Hb. simpl in Hb.
        replace (f0 - (length n + 1)) with (f0 - Datatypes.S (length n)) in Hb by lia. exact Hb.
      - unfold Wn, En, n'. rewrite (Hun n a Hu). apply wr_refl. }
    pose proof (wr_trans _ _ _ _ _ Hw' (wr_trans _ _ _ _ _ (tite_wr _ _ Ht) Hc)) as Hfin. simpl in Hfin.
    exists (E ++ En (O n) n'). split; [exact Hfin|]. unfold En. destruct (S n') eqn:Es'.
    - rewrite app_nil_r. split; [done|]. split; [done|]. intros Hf. congruence.
    - destruct (H3 Es) as (Ha1 & Ha2 & Ha3). split; [|split].
      + rewrite fmap_app. apply NoDup_app. split; [done|]. split; [|by apply fresh_tags].
        intros t (x & -> & Hx)%list_elem_of_fmap (y & Hxy & Hy)%list_elem_of_fmap.
        apply fresh_spec in Hy as [Hy Hny]. apply Hny.
        rewrite <- (HOf n' x y Es' (HOm n a x Es' (Ha1 x Hx)) Hy Hxy). by apply Ha1.
      + intros x Hx. rewrite fmap_app. intros [Hin'|(y & Hxy & Hy)%list_elem_of_fmap]%elem_of_app.
        * by apply (Hcm x Hx).
        * apply fresh_spec in Hy as [Hy Hny]. apply Hny.
          rewrite <- (HOf n' x y Es' (HOm n a x Es' (Ha2 x Hx)) Hy Hxy). by apply Ha2.
      + intros _. split; [|split].
        * intros x [Hx|Hx]%elem_of_app; [apply HOm; auto|by apply fresh_spec in Hx as [Hx _]].
        * intros x Hx. apply HOm; auto.
        * intros x Hx. destruct (decide (x ∈ O n)) as [Hd|Hd].
          -- destruct (Ha3 x Hd) as [He'|He']; [left; apply elem_of_app; by left|by right].
          -- left. apply elem_of_app. right. by apply fresh_spec.
  Qed.

  Lemma inv_out m k c v X X' : inv m X → X' ∈ co_succ X (CoOut k c v) → inv (m ++ [CoOut k c v]) X'.
  Proof.
    intros (E & Hw & Hnd & Hcm & H3) HX'.
    destruct (wr_out _ _ _ k c v X' (Wn_nosend _) Hw HX') as (E1 & E2 & -> & Hw').
    unfold inv. rewrite cm_out, nout_out. exists (E1 ++ E2). split; [exact Hw'|].
    rewrite fmap_app, fmap_cons in Hnd. apply NoDup_app in Hnd as (N1 & N12 & N2).
    apply NoDup_cons in N2 as [Nk N2].
    assert (Hsub : ∀ x, x ∈ E1 ++ E2 → x ∈ E1 ++ (k, c, v) :: E2).
    { intros x [Hx|Hx]%elem_of_app; apply elem_of_app; [by left|right; by right]. }
    split; [|split].
    - rewrite fmap_app. apply NoDup_app. split; [done|]. split; [|done]. intros t Ht Ht2.
      apply (N12 t Ht). by right.
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

  Lemma inv_len m X a : inv m X → length (co_succ X a) ≤ 1.
  Proof.
    intros (E & Hw & Hnd & _). destruct (out_dec a) as [(k & c & v & ->)|Ha].
    - apply (wr_len_out (Wn (nout m)) E X k c v); [apply Wn_nosend| |done]. by apply NoDup_fmap_1 in Hnd.
    - destruct (wr_nout _ _ _ a Ha Hw) as [-> _].
      destruct (Wn_step (nout m) a Ha) as [[-> _]|(_ & _ & Y & W0 & -> & _)]; simpl; lia.
  Qed.

  Definition BT : proc := bt f0 [] [].

  Lemma bt_inv m : (∀ X, X ∈ tnodes BT m → inv m X) ∧ length (tnodes BT m) ≤ 1.
  Proof.
    induction m as [|a m [IHi IHl]] using rev_ind.
    - rewrite tnodes_nil. split; [|simpl; lia]. intros X ->%list_elem_of_singleton. apply inv_init.
    - split.
      + intros X' (X & HX & HX')%tnodes_app_elem. destruct (out_dec a) as [(k & c & v & ->)|Ha].
        * exact (inv_out m k c v X X' (IHi X HX) HX').
        * exact (inv_nout m a X X' Ha (IHi X HX) HX').
      + rewrite tnodes_app. destruct (tnodes BT m) as [|X [|X2 l]] eqn:Et; simpl in *; [lia| |lia].
        rewrite app_nil_r. apply (inv_len m). apply IHi. by left.
  Qed.

  Hypothesis Hclo : ∀ n k c v, OffOut k c v ∉ cl n.

  Definition clpath (n : node) : Prop := ∀ m a m2, n = m ++ a :: m2 → S m = false ∧ offer_of a ∈ cl m.

  Lemma clpath_plain n : clpath n → plain n.
  Proof.
    intros Hc k c v Hin. apply list_elem_of_split in Hin as (m & m2 & ->).
    destruct (Hc m _ m2 eq_refl) as [_ Hin]. exact (Hclo m k c v Hin).
  Qed.

  Lemma clpath_snoc n a : clpath (n ++ [a]) ↔ clpath n ∧ S n = false ∧ offer_of a ∈ cl n.
  Proof.
    split.
    - intros Hc. split.
      + intros m a0 m2 ->. apply (Hc m a0 (m2 ++ [a])). by rewrite <- app_assoc.
      + apply (Hc n a []). done.
    - intros (Hc & Hs & Hin) m a0 m2 E. destruct (split_snoc n m m2 a a0 E) as [(-> & -> & _)|(m2' & _ & ->)].
      + done.
      + by apply (Hc m a0 m2').
  Qed.

  Lemma plain_snoc n a : plain (n ++ [a]) → plain n ∧ ∀ k c v, a ≠ CoOut k c v.
  Proof.
    intros Hp. split.
    - intros k c v Hin. apply (Hp k c v). apply elem_of_app. by left.
    - intros k c v ->. apply (Hp k c v). apply elem_of_app. right. by left.
  Qed.

  Lemma bt_state n : clpath n → ∃ X, tnodes BT n = [X] ∧ inv n X.
  Proof.
    induction n as [|a n IH] using rev_ind; intros Hc.
    - exists BT. split; [done|apply inv_init].
    - apply clpath_snoc in Hc as (Hc & Hs & Hin). destruct (IH Hc) as (X & Et & Hinv).
      assert (Ha : ∀ k c v, a ≠ CoOut k c v).
      { intros k c v ->. exact (Hclo n k c v Hin). }
      pose proof (clpath_plain n Hc) as Hpl.
      destruct Hinv as (E & Hw & Hrest). pose proof Hw as Hw0. rewrite (nout_plain n Hpl) in Hw0.
      destruct (wr_nout _ _ _ a Ha Hw0) as [Hl _].
      destruct (Wn_step n a Ha) as [[_ [Hf|Hf]]|(_ & _ & Y & W0 & Eq & _)]; [congruence|done|].
      rewrite Eq in Hl. simpl in Hl.
      rewrite tnodes_app, Et. simpl. rewrite app_nil_r.
      destruct (co_succ X a) as [|X' [|X2 l]] eqn:Ex; simpl in Hl; try lia.
      exists X'. split; [done|]. apply (inv_nout n a X X' Ha); [by exists E|]. rewrite Ex. by left.
  Qed.

  Lemma bt_clpath n : plain n → tnodes BT n ≠ [] → clpath n.
  Proof.
    induction n as [|a n IH] using rev_ind; intros Hp Hne.
    - intros m a m2 E. by destruct m.
    - apply plain_snoc in Hp as [Hp Ha]. pose proof (tnodes_app_nonempty BT n [a] Hne) as Hne'.
      pose proof (IH Hp Hne') as Hc. apply clpath_snoc. split; [done|].
      destruct (tnodes BT (n ++ [a])) as [|X' l] eqn:Et; [done|].
      assert (HX' : X' ∈ tnodes BT (n ++ [a])) by (rewrite Et; by left).
      apply tnodes_app_elem in HX' as (X & HX & HX').
      destruct (proj1 (bt_inv n) X HX) as (E & Hw & _). rewrite (nout_plain n Hp) in Hw.
      destruct (wr_nout _ _ _ a Ha Hw) as [_ He]. destruct (He X' HX') as (W' & HW' & _).
      destruct (Wn_step n a Ha) as [[Hnil _]|(Hs & Hin & _)]; [|done].
      rewrite Hnil in HW'. by apply elem_of_nil in HW'.
  Qed.

  Lemma bt_menu n o : plain n → (∀ k c v, o ≠ OffOut k c v) →
    (menu BT n o ↔ clpath n ∧ S n = false ∧ o ∈ cl n).
  Proof.
    intros Hp Ho. split.
    - intros (X & a & HX & <- & Hne).
      assert (Hc : clpath n).
      { apply (bt_clpath n Hp). intros E. rewrite E in HX. by apply elem_of_nil in HX. }
      split; [done|].
      assert (Ha : ∀ k c v, a ≠ CoOut k c v). { intros k c v ->. by apply (Ho k c v). }
      destruct (proj1 (bt_inv n) X HX) as (E & Hw & _). rewrite (nout_plain n Hp) in Hw.
      destruct (wr_nout _ _ _ a Ha Hw) as [Hl _].
      destruct (Wn_step n a Ha) as [[Hnil _]|(Hs & Hin & _)]; [|done].
      rewrite Hnil in Hl. destruct (co_succ X a); simpl in *; done.
    - intros (Hc & Hs & Hin). destruct (bt_state n Hc) as (X & Et & E & Hw & _).
      rewrite (nout_plain n Hp) in Hw. exists X, (co_of o). split; [rewrite Et; by left|].
      split; [apply offer_co_of|].
      assert (Ha : ∀ k c v, co_of o ≠ CoOut k c v).
      { intros k c v Eo. apply (Ho k c v). rewrite <- (offer_co_of o), Eo. done. }
      destruct (wr_nout _ _ _ (co_of o) Ha Hw) as [Hl _].
      destruct (Wn_step n (co_of o) Ha) as [[_ [Hf|Hf]]|(_ & _ & Y & W0 & Eq & _)].
      + congruence.
      + rewrite offer_co_of in Hf. done.
      + rewrite Eq in Hl. intros Enil. rewrite Enil in Hl. done.
  Qed.

  Lemma Wn_succ n : successb (Wn n) = S n.
  Proof.
    unfold Wn. destruct (S n); [done|]. unfold core. simpl. apply gsum_nosucc.
    intros g (o & _ & Hg)%list_elem_of_omap. destruct o; simpl in Hg; try done; by injection Hg as <-.
  Qed.

  Lemma bt_succ_at n : clpath n → succ_at BT n = S n.
  Proof.
    intros Hc. destruct (bt_state n Hc) as (X & Et & E & Hw & _). unfold succ_at. rewrite Et. simpl.
    rewrite orb_false_r, (wr_succ _ _ _ Hw), Wn_succ. by rewrite (nout_plain n (clpath_plain n Hc)).
  Qed.

  Lemma S_app n m : S n = true → S (n ++ m) = true.
  Proof.
    intros Hs. induction m as [|a m IH] using rev_ind; [by rewrite app_nil_r|]. rewrite app_assoc. by apply HS.
  Qed.

  Lemma clpath_take n i : clpath n → clpath (take i n).
  Proof.
    intros Hc m a m2 E. apply (Hc m a (m2 ++ drop i n)). rewrite <- (take_drop i n) at 1. rewrite E.
    by rewrite <- app_assoc.
  Qed.

  Lemma bt_S n : clpath n → S_T BT n = S n.
  Proof.
    intros Hc. apply eq_true_iff_eq. rewrite S_T_spec. split.
    - intros (i & Hi & Hs). rewrite (bt_succ_at _ (clpath_take n i Hc)) in Hs.
      rewrite <- (take_drop i n). by apply S_app.
    - intros Hs. exists (length n). split; [done|]. rewrite firstn_all. by rewrite (bt_succ_at n Hc).
  Qed.

  Lemma bt_S_up n : plain n → S_T BT n = true → S n = true.
  Proof.
    intros Hp (i & Hi & Hs)%S_T_spec.
    assert (Hc : clpath (take i n)).
    { apply bt_clpath.
      - intros k c v Hin. apply (Hp k c v). rewrite <- (take_drop i n). apply elem_of_app. by left.
      - intros E. unfold succ_at in Hs. by rewrite E in Hs. }
    rewrite (bt_succ_at _ Hc) in Hs. rewrite <- (take_drop i n). by apply S_app.
  Qed.

  Lemma plain_cm n : plain n → cm n = [].
  Proof.
    induction n as [|a n IH]; intros Hp; [done|]. unfold cm. rewrite omap_cons'.
    destruct a; try (apply IH; intros k' c' v' Hin; apply (Hp k' c' v'); by right).
    exfalso. apply (Hp k c v). by left.
  Qed.

  Lemma bt_O n x : clpath n → S n = false → (x ∈ O_T BT n ↔ x ∈ O n).
  Proof.
    intros Hc Hs. destruct (bt_state n Hc) as (X & Et & E & Hw & _ & _ & H3).
    pose proof (clpath_plain n Hc) as Hp. rewrite (nout_plain n Hp) in Hw, H3.
    destruct (H3 Hs) as (Ha1 & _ & Ha3). rewrite (plain_cm n Hp) in Ha3. destruct x as [[k c] v].
    rewrite O_T_spec. split.
    - intros (X0 & HX0 & Hne). rewrite Et in HX0. apply list_elem_of_singleton in HX0. subst X0.
      apply Ha1. by apply (wr_msgs _ _ _ k c v (Wn_nosend n) Hw).
    - intros Hin. exists X. split; [rewrite Et; by left|]. apply (wr_msgs _ _ _ k c v (Wn_nosend n) Hw).
      destruct (Ha3 _ Hin) as [He|He]; [done|by apply elem_of_nil in He].
  Qed.

  Lemma bt_nostate n : plain n → ¬ clpath n → tnodes BT n = [].
  Proof.
    intros Hp Hn. destruct (tnodes BT n) eqn:E; [done|]. exfalso. apply Hn, (bt_clpath n Hp). by rewrite E.
  Qed.

  Lemma bt_gone n m k c v c' v' Y : Y ∈ tnodes BT (n ++ [CoOut k c v] ++ m) → co_succ Y (CoOut k c' v') = [].
  Proof.
    intros HY. destruct (proj1 (bt_inv _) Y HY) as (E & Hw & _ & Hcm & _).
    destruct (co_succ Y (CoOut k c' v')) eqn:Ey; [done|]. exfalso.
    apply (Hcm (k, c, v)).
    - unfold cm. rewrite !omap_app. apply elem_of_app. right. apply elem_of_app. left. by left.
    - apply list_elem_of_fmap. exists (k, c', v'). split; [done|].
      apply (wr_msgs _ _ _ k c' v' (Wn_nosend _) Hw). by rewrite Ey.
  Qed.

  Context (TG : tag * okind → Prop) (OC IC : channel → Prop).
  Hypothesis Hcl_ok : ∀ n o, o ∈ cl n → TG (off_tag o, off_kind o) ∧ ∀ k c, o = OffIn k c → IC c.
  Hypothesis HO_ok : ∀ n k c v, S n = false → (k, c, v) ∈ O n → TG (k, KOut) ∧ OC c.

  Lemma sends_syn l : (∀ k c v, (k, c, v) ∈ l → TG (k, KOut) ∧ OC c) → syn TG OC IC (sends l).
  Proof.
    induction l as [|[[k c] v] l IH]; intros Hl; [apply syn_nil|]. simpl. apply syn_par.
    - destruct (Hl k c v ltac:(by left)) as [Ht Hc]. split; [done|].
      split; [intros x ->%list_elem_of_singleton; done|]. split; [intros x ->%list_elem_of_singleton; done|].
      intros x Hx. by apply elem_of_nil in Hx.
    - apply IH. intros k' c' v' Hin. apply (Hl k' c' v'). by right.
  Qed.

  Lemma bguard_syn rec n o g :
    (∀ n', syn TG OC IC (rec n')) → o ∈ cl n → bguard rec n o = Some g → gsyn TG OC IC g.
  Proof.
    intros Hrec Hin Hg. destruct (Hcl_ok n o Hin) as [Ht Hc].
    destruct o as [k c v|k c|k E qs|k M qs|k qs]; simpl in Hg; try done; injection Hg as <-.
    - apply gsyn_pre; [done|exact Ht|intros k' c' [= -> ->]; by eapply Hc|].
      apply syn_chain; [intros v; apply Hrec|apply syn_succ].
    - apply gsyn_pre; [done|exact Ht|done|apply Hrec].
    - apply gsyn_pre; [done|exact Ht|done|].
      apply syn_chain; [intros v; destruct v; try apply syn_succ; apply Hrec|apply syn_succ].
    - apply gsyn_pre; [done|exact Ht|done|apply Hrec].
  Qed.

  Lemma bt_syn f : ∀ prev n, syn TG OC IC (bt f prev n).
  Proof.
    induction f as [|f IH]; intros prev n; simpl; destruct (S n) eqn:Es.
    - apply syn_succ.
    - apply syn_nil.
    - apply syn_succ.
    - apply syn_par.
      + apply sends_syn. intros k c v Hin. apply fresh_spec in Hin as [Hin _]. exact (HO_ok n k c v Es Hin).
      + apply syn_PG, gsum_syn. intros g (o & Hin & Hg)%list_elem_of_omap.
        exact (bguard_syn (bt f (O n)) n o g (IH (O n)) Hin Hg).
  Qed.
End Build.
(* end hide *)
