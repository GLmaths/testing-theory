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
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Language.Algebra lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Pull lqCCS.Testing.Head.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Lemma omap_cons' {A B} (f : A → option B) x l :
  omap f (x :: l) = match f x with Some y => y :: omap f l | None => omap f l end.
Proof. done. Qed.

Lemma gco_out g k c v : gco_succ g (CoOut k c v) = [].
Proof.
  induction g as [es| |𝜆 P|g1 IH1 g2 IH2]; simpl; [done|done|by destruct 𝜆|by rewrite IH1, IH2].
Qed.

Definition nosend (X : proc) : Prop := ∀ k c v, co_succ X (CoOut k c v) = [].

Lemma ns_nosend X : nosend (ns X).
Proof.
  intros k c v. induction X as [t c0 e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t x P IHP|g]; simpl.
  - done.
  - destruct (eval e) as [[[]| |]|]; done.
  - by rewrite IHP, IHQ.
  - done.
  - done.
  - done.
  - apply gco_out.
Qed.

Lemma zs_bag_silent B X Z a : zs B X Z → (∀ k c v, a ≠ CoOut k c v) → co_succ B a = [].
Proof.
  intros Hz Ha. induction Hz as [k c e|X|B1 B2 P Q P' Q' _ IH1 _ IH2|e B P Q Z He _ IH|e B P Q Z He _ IH|e P Q Ht Hf]; simpl.
  - destruct a; try done. by destruct (Ha k0 c0 v).
  - done.
  - by rewrite IH1, IH2.
  - exact IH.
  - exact IH.
  - done.
Qed.

Lemma zs_bag_nosucc B X Z : zs B X Z → successb B = false.
Proof.
  induction 1 as [k c e|X|B1 B2 P Q P' Q' _ IH1 _ IH2|e B P Q Z He _ IH|e B P Q Z He _ IH|e P Q Ht Hf]; simpl;
    try done. by rewrite IH1, IH2.
Qed.

Inductive pullb (base : proc → proc → Prop) : proc → proc → Prop :=
| pb_base X Y : base X Y → pullb base X Y
| pb_bag B X Z W : zs B X Z → pullb base Z W → pullb base X (B ∥ W)
| pb_iteT e A W X : eval e = Some (VBool true) → pullb base X W → pullb base X (PIte e W A)
| pb_iteF e A W X : eval e = Some (VBool false) → pullb base X W → pullb base X (PIte e A W).

Lemma pullb_tite base X W Y : tite W Y → pullb base X W → pullb base X Y.
Proof. induction 1 as [|e Y A He _ IH|e Y A He _ IH]; intros Hp; [done|apply pb_iteT; auto|apply pb_iteF; auto]. Qed.

Definition bagc (Q : proc → proc → Prop) : Prop := ∀ B X Z W, zs B X Z → Q Z W → Q X (B ∥ W).

Lemma pullb_nout base a (L : nat → nat → Prop) (Q1 Q2 : proc → proc → Prop) :
  (∀ k c v, a ≠ CoOut k c v) → bagc Q1 → bagc Q2 →
  (∀ X Y, base X Y → L (length (co_succ X a)) (length (co_succ Y a))
     ∧ ∀ Y', Y' ∈ co_succ Y a → (∃ X', X' ∈ co_succ X a ∧ Q1 X' Y') ∨ (co_succ X a = [] ∧ Q2 X Y')) →
  ∀ X Y, pullb base X Y → L (length (co_succ X a)) (length (co_succ Y a))
     ∧ ∀ Y', Y' ∈ co_succ Y a → (∃ X', X' ∈ co_succ X a ∧ Q1 X' Y') ∨ (co_succ X a = [] ∧ Q2 X Y').
Proof.
  intros Ha Hb1 Hb2 Hb X Y Hp. induction Hp as [X Y Hbase|B X Z W Hz Hp IH|e A W X He Hp IH|e A W X He Hp IH].
  - by apply Hb.
  - destruct IH as [IHL IHe]. destruct (zs_step B X Z a Hz) as (Hl & _ & HZ).
    pose proof (zs_bag_silent B X Z a Hz Ha) as EB. rewrite EB in Hl. simpl in Hl. simpl. rewrite EB. simpl. split.
    + rewrite length_fmap, Hl. exact IHL.
    + intros Y' (W' & -> & HW')%list_elem_of_fmap. destruct (IHe W' HW') as [(Z' & HZ' & HQ)|[EZ HQ]].
      * destruct (HZ Z' HZ') as (X' & HX' & Hz'). left. exists X'. split; [done|]. exact (Hb1 _ _ _ _ Hz' HQ).
      * right. split; [|exact (Hb2 _ _ _ _ Hz HQ)]. rewrite EZ in Hl. simpl in Hl. by destruct (co_succ X a).
  - simpl. rewrite He. exact IH.
  - simpl. rewrite He. exact IH.
Qed.

Lemma pullb_out base a :
  (∀ X Y, base X Y → length (co_succ Y a) = length (co_succ X a)
     ∧ ∀ Y', Y' ∈ co_succ Y a → ∃ X', X' ∈ co_succ X a ∧ pullb base X' Y') →
  ∀ X Y, pullb base X Y → length (co_succ Y a) = length (co_succ X a)
     ∧ ∀ Y', Y' ∈ co_succ Y a → ∃ X', X' ∈ co_succ X a ∧ pullb base X' Y'.
Proof.
  intros Hb X Y Hp. induction Hp as [X Y Hbase|B X Z W Hz Hp IH|e A W X He Hp IH|e A W X He Hp IH].
  - by apply Hb.
  - destruct IH as [IHL IHe]. destruct (zs_step B X Z a Hz) as (Hl & HB & HZ). simpl. split.
    + rewrite length_app, !length_fmap. lia.
    + intros Y' HY. apply elem_of_app in HY as [(B' & -> & HB')%list_elem_of_fmap|(W' & -> & HW')%list_elem_of_fmap].
      * destruct (HB _ HB') as (X' & HX' & Hz'). exists X'. split; [done|]. by eapply pb_bag.
      * destruct (IHe _ HW') as (Z' & HZ' & Hp'). destruct (HZ _ HZ') as (X' & HX' & Hz').
        exists X'. split; [done|]. by eapply pb_bag.
  - simpl. rewrite He. exact IH.
  - simpl. rewrite He. exact IH.
Qed.

Lemma pullb_succ base (Φ : bool → bool → Prop) :
  (∀ X Y, base X Y → Φ (successb X) (successb Y)) → ∀ X Y, pullb base X Y → Φ (successb X) (successb Y).
Proof.
  intros Hb X Y Hp. induction Hp as [X Y Hbase|B X Z W Hz Hp IH|e A W X He Hp IH|e A W X He Hp IH].
  - by apply Hb.
  - rewrite (zs_success _ _ _ Hz). simpl. by rewrite (zs_bag_nosucc _ _ _ Hz).
  - simpl. by rewrite He.
  - simpl. by rewrite He.
Qed.

Lemma offer_co_of o : offer_of (co_of o) = o.
Proof. by destruct o. Qed.

Lemma resp_offer a a' h : offer_of a = offer_of a' → resp a h = None → resp a' h = None.
Proof.
  destruct h as [𝜆 D]. unfold resp. intros Ho.
  destruct 𝜆, a, a'; simpl in *; try done; inversion Ho; subst; repeat case_decide; try done; naive_solver.
Qed.

Lemma omap_nil_offer a a' (l : list (prefix * proc)) :
  offer_of a = offer_of a' → omap (resp a) l = [] → omap (resp a') l = [].
Proof.
  intros Ho. induction l as [|h l IH]; [done|]. rewrite !omap_cons'.
  destruct (resp a h) eqn:E; [done|]. rewrite (resp_offer a a' h Ho E). exact IH.
Qed.

Lemma rg_resp o a : (∀ k c v, a ≠ CoOut k c v) →
  match rg o with
  | Some g => (offer_of a = o → gco_succ g a = [PG ①]) ∧ (offer_of a ≠ o → gco_succ g a = [])
  | None => offer_of a ≠ o
  end.
Proof.
  intros Ha. destruct o as [k c v|k c|k E qs|k M qs|k qs]; simpl.
  - intros Ho. destruct a; try discriminate Ho. by destruct (Ha k0 c0 v0).
  - destruct a as [k0 c0 v0|k0 c0 v0|k0 E0 qs0|k0 M0 qs0 n0|k0 qs0]; simpl; try (split; [intros [=]|done]).
    case_decide as Hd.
    + split; [done|]. intros Hne. destruct Hne. by destruct Hd as [-> ->].
    + split; [|done]. intros [= -> ->]. by destruct Hd.
  - destruct a as [k0 c0 v0|k0 c0 v0|k0 E0 qs0|k0 M0 qs0 n0|k0 qs0]; simpl; try (split; [intros [=]|done]).
    rewrite eval_quote. case_decide as Hd.
    + split; [done|]. intros Hne. destruct Hne. by destruct Hd as (-> & -> & [= ->]).
    + split; [|done]. intros [= -> -> ->]. by destruct Hd.
  - destruct a as [k0 c0 v0|k0 c0 v0|k0 E0 qs0|k0 M0 qs0 n0|k0 qs0]; simpl; try (split; [intros [=]|done]).
    rewrite eval_quote. case_decide as Hd.
    + split; [done|]. intros Hne. destruct Hne. by destruct Hd as (-> & -> & [= ->]).
    + split; [|done]. intros [= -> -> ->]. by destruct Hd.
  - destruct a as [k0 c0 v0|k0 c0 v0|k0 E0 qs0|k0 M0 qs0 n0|k0 qs0]; simpl; try (split; [intros [=]|done]).
    rewrite eval_quote. case_decide as Hd.
    + split; [done|]. intros Hne. destruct Hne. by destruct Hd as (-> & [= ->]).
    + split; [|done]. intros [= -> ->]. by destruct Hd.
Qed.

Lemma reps_part (l : list offer) a : (∀ k c v, a ≠ CoOut k c v) → NoDup l →
  (offer_of a ∈ l → concat (map (λ g, gco_succ g a) (omap rg l)) = [PG ①])
  ∧ (offer_of a ∉ l → concat (map (λ g, gco_succ g a) (omap rg l)) = []).
Proof.
  intros Ha. induction l as [|o l IH]; intros Hnd.
  - split; [intros Hin; by apply elem_of_nil in Hin|done].
  - apply NoDup_cons in Hnd as [Hni Hnd]. destruct (IH Hnd) as [IH1 IH2]. rewrite omap_cons'.
    pose proof (rg_resp o a Ha) as Hr. destruct (rg o) as [g|].
    + destruct Hr as [Hr1 Hr2]. simpl. split.
      * intros Hin. apply elem_of_cons in Hin as [E|Hin].
        -- rewrite (Hr1 E). rewrite IH2; [done|]. by rewrite E.
        -- rewrite Hr2; [|intros E; apply Hni; by rewrite <- E]. simpl. by apply IH1.
      * intros Hnin. rewrite Hr2; [|intros E; apply Hnin; rewrite E; by left]. simpl.
        apply IH2. intros Hin. apply Hnin. by right.
    + split.
      * intros Hin. apply elem_of_cons in Hin as [E|Hin]; [by destruct Hr|by apply IH1].
      * intros Hnin. apply IH2. intros Hin. apply Hnin. by right.
Qed.

Definition ans (X : proc) (o : offer) : Prop := ∃ a, offer_of a = o ∧ co_succ X a ≠ [].

Inductive mode : Type := MP | MH (f : nat) (m : node) | MC | MR.

Section Modes.
  Context (VL : list val) (reps : node → list offer) (wrapb : node → offer → bool).
  Hypothesis Hnd : ∀ m, NoDup (reps m).

  Definition bP (X Y : proc) : Prop := Y = X.
  Definition bC (X Y : proc) : Prop := ∃ W, pullb bP X W ∧ Y = PG ① ∥ W.
  Definition bH (f : nat) (m : node) (X Y : proc) : Prop :=
    successb X = false ∧ nosend X ∧ Y = PG (hsum VL reps wrapb (tn VL reps wrapb f) m X).
  Definition bR (X Y : proc) : Prop := nosend X ∧ Y = PG ①.

  Definition rel (md : mode) : proc → proc → Prop :=
    pullb (match md with MP => bP | MH f m => bH f m | MC => bC | MR => bR end).

  Lemma rel_bagc md : bagc (rel md).
  Proof. intros B X Z W Hz Hp. by eapply pb_bag. Qed.

  Lemma tn_rel f m X :
    (rel MP X (tn VL reps wrapb f m X) ∧ (f = 0 ∨ successb X = true))
    ∨ ∃ f', f = S f' ∧ rel (MH f' m) X (tn VL reps wrapb f m X).
  Proof.
    destruct f as [|f]; [left; split; [by apply pb_base|by left]|]. simpl.
    destruct (successb X) eqn:Es; [left; split; [by apply pb_base|by right]|].
    right. exists f. split; [done|]. apply (pb_bag _ _ _ _ _ (zs_bagof X)). apply pb_base.
    split; [|split; [apply ns_nosend|done]].
    pose proof (zs_success _ _ _ (zs_bagof X)) as E. rewrite Es in E. by destruct (successb (bagof X)), (successb (ns X)).
  Qed.

  Lemma heads_part rec m a (l : list (prefix * proc)) :
    length (concat (map (λ g, gco_succ g a) (omap (hguard VL wrapb rec m) l))) = length (omap (resp a) l)
    ∧ ∀ Y', Y' ∈ concat (map (λ g, gco_succ g a) (omap (hguard VL wrapb rec m) l)) →
        ∃ Z', Z' ∈ omap (resp a) l ∧ hres VL wrapb rec m a Z' Y'.
  Proof.
    induction l as [|h l [IHl IHe]]; [split; [done|intros Y' HY; by apply elem_of_nil in HY]|].
    rewrite !omap_cons'. pose proof (hguard_spec VL wrapb rec m h a) as Hsp.
    destruct (hguard VL wrapb rec m h) as [g|].
    - destruct Hsp as [[Hr Hg]|(Z' & Y0 & Hr & Hg & Hh)]; rewrite Hr; simpl; rewrite Hg; simpl.
      + split; [exact IHl|exact IHe].
      + split; [by rewrite IHl|]. intros Y' HY. apply elem_of_cons in HY as [->|HY].
        * exists Z'. split; [by left|done].
        * destruct (IHe Y' HY) as (Z2 & HZ2 & Hh2). exists Z2. split; [by right|done].
    - rewrite Hsp. split; [exact IHl|exact IHe].
  Qed.

  Definition LH (m : node) (a : coact) (x y : nat) : Prop :=
    (1 ≤ x → y = x) ∧ (x = 0 → (offer_of a ∈ reps m → y = 1) ∧ (offer_of a ∉ reps m → y = 0)).

  Definition Q1H (f : nat) (m : node) (a : coact) (X' Y' : proc) : Prop :=
    (wrapb m (offer_of a) = true ∧ rel MC X' Y')
    ∨ (wrapb m (offer_of a) = false
       ∧ ((rel MP X' Y' ∧ (unlisted VL a ∨ f = 0 ∨ successb X' = true))
          ∨ ∃ f', f = S f' ∧ rel (MH f' (m ++ [a])) X' Y')).

  Lemma bH_nout f m Z a : (∀ k c v, a ≠ CoOut k c v) → nosend Z →
    LH m a (length (co_succ Z a)) (length (co_succ (PG (hsum VL reps wrapb (tn VL reps wrapb f) m Z)) a))
    ∧ ∀ Y', Y' ∈ co_succ (PG (hsum VL reps wrapb (tn VL reps wrapb f) m Z)) a →
        (∃ Z', Z' ∈ co_succ Z a ∧ Q1H f m a Z' Y') ∨ (co_succ Z a = [] ∧ rel MR Z Y').
  Proof.
    intros Ha Hns. simpl. unfold hsum. rewrite gco_gsum, map_app, concat_app, (co_heads Z a Ha).
    destruct (heads_part (tn VL reps wrapb f) m a (heads Z)) as [Hl1 He1].
    assert (Hndr : NoDup (repl reps m Z)) by (apply NoDup_filter, Hnd).
    destruct (reps_part (repl reps m Z) a Ha Hndr) as [R1 R2].
    assert (Hmem : offer_of a ∈ repl reps m Z ↔ offer_of a ∈ reps m ∧ omap (resp a) (heads Z) = []).
    { unfold repl. rewrite list_elem_of_filter. unfold free_rep. split.
      - intros [Hf Hin]. split; [done|].
        destruct (omap (resp (co_of (offer_of a))) (heads Z)) eqn:E; [|discriminate].
        apply (omap_nil_offer (co_of (offer_of a)) a); [apply offer_co_of|done].
      - intros [Hin E]. split; [|done].
        by rewrite (omap_nil_offer a (co_of (offer_of a)) _ (eq_sym (offer_co_of _)) E). }
    split.
    - rewrite length_app, Hl1. split.
      + intros Hx. rewrite R2; [simpl; lia|]. intros Hin. apply Hmem in Hin as [_ E]. rewrite E in Hx. simpl in Hx. lia.
      + intros Hx. assert (E : omap (resp a) (heads Z) = []).
        { destruct (omap (resp a) (heads Z)); [done|simpl in Hx; lia]. }
        split; intros Hin.
        * rewrite R1; [simpl; lia|]. apply Hmem. by split.
        * rewrite R2; [simpl; lia|]. intros Hin'. apply Hin. exact (proj1 (proj1 Hmem Hin')).
    - intros Y' HY. apply elem_of_app in HY as [HY|HY].
      + left. destruct (He1 Y' HY) as (Z' & HZ' & Hh). exists Z'. split; [done|].
        destruct Hh as (W & Ht & [[Hw ->]|[Hw [->|[-> Hu]]]]).
        * left. split; [done|]. apply (pullb_tite _ _ _ _ Ht). apply pb_base. exists Z'. split; [by apply pb_base|done].
        * right. split; [done|]. destruct (tn_rel f (m ++ [a]) Z') as [[Hp Hc]|(f' & Ef & Hh')].
          -- left. split; [by apply (pullb_tite _ _ _ _ Ht)|by right].
          -- right. exists f'. split; [done|]. by apply (pullb_tite _ _ _ _ Ht).
        * right. split; [done|]. left. split; [|by left]. apply (pullb_tite _ _ _ _ Ht). by apply pb_base.
      + right. destruct (classic (offer_of a ∈ repl reps m Z)) as [Hin|Hnin];
          [|rewrite (R2 Hnin) in HY; by apply elem_of_nil in HY].
        rewrite (R1 Hin) in HY. apply list_elem_of_singleton in HY. subst Y'.
        apply Hmem in Hin as [_ E]. split; [done|]. apply pb_base. by split.
  Qed.

  Lemma rel_nout_H f m X Y a : (∀ k c v, a ≠ CoOut k c v) → rel (MH f m) X Y →
    LH m a (length (co_succ X a)) (length (co_succ Y a))
    ∧ ∀ Y', Y' ∈ co_succ Y a → (∃ X', X' ∈ co_succ X a ∧ Q1H f m a X' Y') ∨ (co_succ X a = [] ∧ rel MR X Y').
  Proof.
    intros Ha. apply (pullb_nout (bH f m) a (LH m a) (Q1H f m a) (rel MR) Ha).
    - intros B X0 Z W Hz [[Hw Hq]|[Hw [[Hq Hc]|(f' & Ef & Hq)]]].
      + left. split; [done|]. by eapply pb_bag.
      + right. split; [done|]. left. split; [by eapply pb_bag|].
        destruct Hc as [Hc|[Hc|Hc]]; [by left|right; by left|right; right].
        rewrite (zs_success _ _ _ Hz), Hc. apply orb_true_r.
      + right. split; [done|]. right. exists f'. split; [done|]. by eapply pb_bag.
    - apply rel_bagc.
    - intros X0 Y0 (Hs & Hn & ->). exact (bH_nout f m X0 a Ha Hn).
  Qed.

  Lemma rel_nout_P X Y a : (∀ k c v, a ≠ CoOut k c v) → rel MP X Y →
    length (co_succ Y a) = length (co_succ X a) ∧ ∀ Y', Y' ∈ co_succ Y a → ∃ X', X' ∈ co_succ X a ∧ rel MP X' Y'.
  Proof.
    intros Ha Hp.
    destruct (pullb_nout bP a (λ x y, y = x) (rel MP) (λ _ _, False) Ha (rel_bagc MP)
                (λ B X0 Z W _ Hf, Hf)) with (X := X) (Y := Y) as [HL He]; [|exact Hp|].
    - intros X0 Y0 ->. split; [done|]. intros Y' HY. left. exists Y'. split; [done|by apply pb_base].
    - split; [done|]. intros Y' HY. destruct (He Y' HY) as [Hq|[_ []]]. exact Hq.
  Qed.

  Lemma rel_nout_C X Y a : (∀ k c v, a ≠ CoOut k c v) → rel MC X Y →
    length (co_succ Y a) = length (co_succ X a) ∧ ∀ Y', Y' ∈ co_succ Y a → ∃ X', X' ∈ co_succ X a ∧ rel MC X' Y'.
  Proof.
    intros Ha Hp.
    destruct (pullb_nout bC a (λ x y, y = x) (rel MC) (λ _ _, False) Ha (rel_bagc MC)
                (λ B X0 Z W _ Hf, Hf)) with (X := X) (Y := Y) as [HL He]; [|exact Hp|].
    - intros X0 Y0 (W & HW & ->). destruct (rel_nout_P X0 W a Ha HW) as [Hl Hel]. simpl. split.
      + by rewrite length_fmap.
      + intros Y' (W' & -> & HW')%list_elem_of_fmap. destruct (Hel W' HW') as (X' & HX' & Hr).
        left. exists X'. split; [done|]. apply pb_base. by exists W'.
    - split; [done|]. intros Y' HY. destruct (He Y' HY) as [Hq|[_ []]]. exact Hq.
  Qed.

  Lemma rel_nout_R X Y a : (∀ k c v, a ≠ CoOut k c v) → rel MR X Y → co_succ Y a = [].
  Proof.
    intros Ha Hp.
    destruct (pullb_nout bR a (λ x y, y = 0) (λ _ _, False) (λ _ _, False) Ha
                (λ B X0 Z W _ Hf, Hf) (λ B X0 Z W _ Hf, Hf)) with (X := X) (Y := Y) as [HL _]; [|exact Hp|].
    - intros X0 Y0 [_ ->]. split; [done|]. intros Y' HY. by apply elem_of_nil in HY.
    - by destruct (co_succ Y a).
  Qed.

  Lemma rel_out_P X Y k c v : rel MP X Y →
    length (co_succ Y (CoOut k c v)) = length (co_succ X (CoOut k c v))
    ∧ ∀ Y', Y' ∈ co_succ Y (CoOut k c v) → ∃ X', X' ∈ co_succ X (CoOut k c v) ∧ rel MP X' Y'.
  Proof.
    apply pullb_out. intros X0 Y0 ->. split; [done|]. intros Y' HY. exists Y'. split; [done|by apply pb_base].
  Qed.

  Lemma rel_out md X Y k c v : rel md X Y →
    length (co_succ Y (CoOut k c v)) = length (co_succ X (CoOut k c v))
    ∧ ∀ Y', Y' ∈ co_succ Y (CoOut k c v) → ∃ X', X' ∈ co_succ X (CoOut k c v) ∧ rel md X' Y'.
  Proof.
    destruct md as [|f m| |]; [apply rel_out_P| | |]; apply pullb_out.
    - intros X0 Y0 (_ & Hn & ->). simpl. rewrite gco_out, (Hn k c v). split; [done|].
      intros Y' HY. by apply elem_of_nil in HY.
    - intros X0 Y0 (W & HW & ->). destruct (rel_out_P X0 W k c v HW) as [Hl Hel]. simpl. split.
      + by rewrite length_fmap.
      + intros Y' (W' & -> & HW')%list_elem_of_fmap. destruct (Hel W' HW') as (X' & HX' & Hr).
        exists X'. split; [done|]. apply pb_base. by exists W'.
    - intros X0 Y0 (Hn & ->). simpl. rewrite (Hn k c v). split; [done|].
      intros Y' HY. by apply elem_of_nil in HY.
  Qed.

  Lemma gsum_nosucc (l : list guard) : (∀ g, g ∈ l → gsuccessb g = false) → gsuccessb (gsum l) = false.
  Proof.
    induction l as [|g l IH]; intros Hl; [done|]. simpl. rewrite (Hl g) by (by left).
    apply IH. intros g' Hg'. apply Hl. by right.
  Qed.

  Lemma hsum_nosucc rec m Z : gsuccessb (hsum VL reps wrapb rec m Z) = false.
  Proof.
    apply gsum_nosucc. intros g Hg. apply elem_of_app in Hg as [Hg|Hg]; apply list_elem_of_omap in Hg as (x & _ & Hx).
    - destruct x as [𝜆 D]. unfold hguard in Hx. destruct 𝜆 as [t|t c|t E es|t M es|t es]; simpl in Hx.
      + discriminate Hx.
      + injection Hx as <-. done.
      + destruct (eval_qubits es); [injection Hx as <-; done|discriminate Hx].
      + destruct (eval_qubits es); [injection Hx as <-; done|discriminate Hx].
      + destruct (eval_qubits es); [injection Hx as <-; done|discriminate Hx].
    - destruct x as [k c v|k c|k E qs|k M qs|k qs]; simpl in Hx;
        [discriminate Hx|injection Hx as <-; done..].
  Qed.

  Lemma rel_success md X Y : rel md X Y →
    match md with
    | MP => successb Y = successb X
    | MH _ _ => successb X = false ∧ successb Y = false
    | MC | MR => successb Y = true
    end.
  Proof.
    destruct md as [|f m| |]; intros Hp.
    - refine (pullb_succ bP (λ x y, y = x) _ X Y Hp). by intros X0 Y0 ->.
    - refine (pullb_succ (bH f m) (λ x y, x = false ∧ y = false) _ X Y Hp). intros X0 Y0 (Hs & _ & ->).
      split; [done|]. apply hsum_nosucc.
    - refine (pullb_succ bC (λ x y, y = true) _ X Y Hp). by intros X0 Y0 (W & _ & ->).
    - refine (pullb_succ bR (λ x y, y = true) _ X Y Hp). by intros X0 Y0 (_ & ->).
  Qed.

  Lemma relP_len X Y a : rel MP X Y → length (co_succ Y a) = length (co_succ X a).
  Proof.
    intros Hr. destruct (classic (∃ k c v, a = CoOut k c v)) as [(k & c & v & ->)|Ha].
    - exact (proj1 (rel_out MP X Y k c v Hr)).
    - apply (rel_nout_P X Y a); [|done]. intros k c v E. apply Ha. by exists k, c, v.
  Qed.

  Lemma relC_len X Y a : rel MC X Y → length (co_succ Y a) = length (co_succ X a).
  Proof.
    intros Hr. destruct (classic (∃ k c v, a = CoOut k c v)) as [(k & c & v & ->)|Ha].
    - exact (proj1 (rel_out MC X Y k c v Hr)).
    - apply (rel_nout_C X Y a); [|done]. intros k c v E. apply Ha. by exists k, c, v.
  Qed.

  Lemma ans_len X Y o : (∀ a, length (co_succ Y a) = length (co_succ X a)) → (ans Y o ↔ ans X o).
  Proof.
    intros Hl. split; intros (a & Eo & Hne); exists a; (split; [done|]); intros E; apply Hne;
      pose proof (Hl a) as Hla; rewrite E in Hla; simpl in Hla.
    - by destruct (co_succ Y a).
    - by destruct (co_succ X a).
  Qed.

  Lemma ans_P X Y o : rel MP X Y → (ans Y o ↔ ans X o).
  Proof. intros Hr. apply ans_len. intros a. by apply relP_len. Qed.

  Lemma ans_C X Y o : rel MC X Y → (ans Y o ↔ ans X o).
  Proof. intros Hr. apply ans_len. intros a. by apply relC_len. Qed.

  Lemma ans_H f m X Y o : rel (MH f m) X Y →
    (ans Y o ↔ ans X o ∨ (o ∈ reps m ∧ ∀ k c v, o ≠ OffOut k c v)).
  Proof.
    intros Hr. split.
    - intros (a & Eo & Hne). destruct (classic (∃ k c v, a = CoOut k c v)) as [(k & c & v & ->)|Ha].
      + left. exists (CoOut k c v). split; [done|]. intros E. apply Hne.
        pose proof (proj1 (rel_out (MH f m) X Y k c v Hr)) as Hl. rewrite E in Hl. simpl in Hl.
        by destruct (co_succ Y (CoOut k c v)).
      + assert (Ha' : ∀ k c v, a ≠ CoOut k c v) by (intros k c v E; apply Ha; by exists k, c, v).
        destruct (rel_nout_H f m X Y a Ha' Hr) as [[L1 L2] _].
        destruct (co_succ X a) as [|X' lx] eqn:EX.
        * right. destruct (L2 eq_refl) as [_ Lb]. split.
          -- rewrite <- Eo. apply NNPP. intros Hnin. pose proof (Lb Hnin) as Ly. by destruct (co_succ Y a).
          -- intros k c v E. rewrite <- Eo in E. destruct a; try discriminate E. by destruct (Ha' k0 c0 v0).
        * left. exists a. split; [done|]. by rewrite EX.
    - intros [(a & Eo & Hne)|[Hin Hno]].
      + exists a. split; [done|]. destruct (classic (∃ k c v, a = CoOut k c v)) as [(k & c & v & ->)|Ha].
        * intros E. apply Hne. pose proof (proj1 (rel_out (MH f m) X Y k c v Hr)) as Hl. rewrite E in Hl.
          simpl in Hl. by destruct (co_succ X (CoOut k c v)).
        * assert (Ha' : ∀ k c v, a ≠ CoOut k c v) by (intros k c v E; apply Ha; by exists k, c, v).
          destruct (rel_nout_H f m X Y a Ha' Hr) as [[L1 _] _]. intros E. rewrite E in L1. simpl in L1.
          destruct (co_succ X a); [done|]. simpl in L1. specialize (L1 ltac:(lia)). lia.
      + assert (Ha' : ∀ k c v, co_of o ≠ CoOut k c v).
        { intros k c v E. destruct o; try discriminate E. by destruct (Hno k0 c0 v0). }
        destruct (rel_nout_H f m X Y (co_of o) Ha' Hr) as [[L1 L2] _]. exists (co_of o).
        split; [apply offer_co_of|]. intros E. rewrite E in L1, L2. simpl in L1, L2.
        destruct (co_succ X (co_of o)) as [|X' lx]; simpl in *.
        * destruct (L2 eq_refl) as [La _]. rewrite offer_co_of in La. specialize (La Hin). lia.
        * specialize (L1 ltac:(lia)). lia.
  Qed.

  Lemma ans_R X Y o : rel MR X Y → ans Y o → ans X o.
  Proof.
    intros Hr (a & Eo & Hne). destruct (classic (∃ k c v, a = CoOut k c v)) as [(k & c & v & ->)|Ha].
    - exists (CoOut k c v). split; [done|]. intros E. apply Hne.
      pose proof (proj1 (rel_out MR X Y k c v Hr)) as Hl. rewrite E in Hl. simpl in Hl.
      by destruct (co_succ Y (CoOut k c v)).
    - exfalso. apply Hne. apply (rel_nout_R X Y a); [|done]. intros k c v E. apply Ha. by exists k, c, v.
  Qed.
End Modes.

Lemma menu_single T n X o : tnodes T n = [X] → (menu T n o ↔ ans X o).
Proof.
  intros E. unfold menu. rewrite E. split.
  - intros (T' & a & HT' & Eo & Hne). apply list_elem_of_singleton in HT'. subst. by exists a.
  - intros (a & Eo & Hne). exists X, a. split; [by left|done].
Qed.

Lemma menu_nil T n o : tnodes T n = [] → ¬ menu T n o.
Proof. intros E (T' & a & HT' & _). rewrite E in HT'. by apply elem_of_nil in HT'. Qed.

Lemma succ_at_S T n : succ_at T n = true → S_T T n = true.
Proof. intros Hs. apply S_T_spec. exists (length n). split; [done|]. by rewrite firstn_all. Qed.

Lemma split_snoc {A} (n m m2 : list A) a a0 :
  n ++ [a] = m ++ a0 :: m2 → (m = n ∧ a0 = a ∧ m2 = []) ∨ ∃ m2', m2 = m2' ++ [a] ∧ n = m ++ a0 :: m2'.
Proof.
  induction m2 as [|b m2 _] using rev_ind; intros E.
  - left. change (n ++ [a] = m ++ [a0]) in E. apply app_inj_tail in E as [-> ->]. done.
  - right. exists m2. rewrite app_comm_cons, app_assoc in E. apply app_inj_tail in E as [-> ->]. done.
Qed.

Lemma single_step (lx ly : list proc) (Q : proc → proc → Prop) :
  length lx ≤ 1 → length ly = length lx → (∀ Y', Y' ∈ ly → ∃ X', X' ∈ lx ∧ Q X' Y') →
  (lx = [] ∧ ly = []) ∨ ∃ X' Y', lx = [X'] ∧ ly = [Y'] ∧ Q X' Y'.
Proof.
  intros Hlx Hl He. destruct lx as [|X' [|X2 lx]]; destruct ly as [|Y' [|Y2 ly]]; simpl in *; try lia.
  - by left.
  - right. exists X', Y'. split; [done|]. split; [done|]. destruct (He Y') as (X'' & HX'' & HQ); [by left|].
    apply list_elem_of_singleton in HX''. by subst.
Qed.

Lemma tri_step (lx ly : list proc) (P : Prop) (Q1 : proc → proc → Prop) (Q2 : proc → Prop) :
  length lx ≤ 1 →
  (1 ≤ length lx → length ly = length lx) ∧ (length lx = 0 → (P → length ly = 1) ∧ (¬ P → length ly = 0)) →
  (∀ Y', Y' ∈ ly → (∃ X', X' ∈ lx ∧ Q1 X' Y') ∨ (lx = [] ∧ Q2 Y')) →
  (lx = [] ∧ ly = [] ∧ ¬ P) ∨ (∃ X' Y', lx = [X'] ∧ ly = [Y'] ∧ Q1 X' Y') ∨ (lx = [] ∧ P ∧ ∃ Y', ly = [Y'] ∧ Q2 Y').
Proof.
  intros Hlx [L1 L2] He. destruct lx as [|X' [|X2 lx]]; simpl in *; [| |lia].
  - destruct (L2 eq_refl) as [La Lb]. destruct (classic P) as [HP|HP].
    + right. right. split; [done|]. split; [done|]. pose proof (La HP) as Ly.
      destruct ly as [|Y' [|Y2 ly]]; simpl in Ly; try lia. exists Y'. split; [done|].
      destruct (He Y') as [(X' & HX' & _)|[_ HQ]]; [by left|by apply elem_of_nil in HX'|done].
    + left. pose proof (Lb HP) as Ly. by destruct ly.
  - right. left. pose proof (L1 ltac:(lia)) as Ly. destruct ly as [|Y' [|Y2 ly]]; simpl in Ly; try lia.
    exists X', Y'. split; [done|]. split; [done|].
    destruct (He Y') as [(X'' & HX'' & HQ)|[E0 _]]; [by left| |discriminate E0].
    apply list_elem_of_singleton in HX''. by subst.
Qed.

Definition isout (a : coact) : bool := match a with CoOut _ _ _ => true | _ => false end.

Definition nout (n : list coact) : list coact := filter (λ a, isout a = false) n.

Lemma nout_out n k c v : nout (n ++ [CoOut k c v]) = nout n.
Proof. unfold nout. rewrite list.filter_app, list.filter_cons_False by done. by rewrite list.filter_nil, app_nil_r. Qed.

Lemma nout_nout n a : (∀ k c v, a ≠ CoOut k c v) → nout (n ++ [a]) = nout n ++ [a].
Proof.
  intros Ha. unfold nout. rewrite list.filter_app. f_equal. rewrite list.filter_cons_True; [done|].
  destruct a; try done. by destruct (Ha k c v).
Qed.

Lemma S_T_ext T n a : S_T T n = true → S_T T (n ++ [a]) = true.
Proof.
  rewrite !S_T_spec. intros (i & Hi & Hs). exists i. split; [rewrite length_app; lia|].
  by rewrite take_app_le by lia.
Qed.

Section Inv.
  Context (VL : list val) (reps : node → list offer) (wrapb : node → offer → bool).
  Hypothesis Hnd : ∀ m, NoDup (reps m).
  Context (T : proc) (f0 : nat).
  Hypothesis HT1 : ∀ n, length (tnodes T n) ≤ 1.

  Notation TN := (tn VL reps wrapb f0 [] T).
  Notation rel := (rel VL reps wrapb).

  Definition pcause (n : node) : Prop :=
    f0 ≤ length (nout n) ∨ S_T T n = true ∨ ∃ a, a ∈ n ∧ unlisted VL a.

  Definition wpath (n : node) : Prop :=
    ∃ m a m2, n = m ++ a :: m2 ∧ (∀ k c v, a ≠ CoOut k c v) ∧ wrapb (nout m) (offer_of a) = true
      ∧ tnodes T (m ++ [a]) ≠ [].

  Definition rpath (n : node) : Prop :=
    ∃ m a m2, n = m ++ a :: m2 ∧ (∀ k c v, a ≠ CoOut k c v) ∧ offer_of a ∈ reps (nout m).

  Definition nowrap (n : node) : Prop :=
    ∀ m a m2, n = m ++ a :: m2 → (∀ k c v, a ≠ CoOut k c v) → wrapb (nout m) (offer_of a) = false.

  Definition track (md : mode) (n : node) : Prop :=
    match md with
    | MP => pcause n
    | MH f m => m = nout n ∧ f + length m + 1 = f0 ∧ nowrap n
    | MC => wpath n
    | MR => False
    end.

  Lemma nowrap_out n k c v : nowrap n → nowrap (n ++ [CoOut k c v]).
  Proof.
    intros Hn m a m2 E Ha. apply split_snoc in E as [(-> & -> & _)|(m2' & -> & ->)].
    - by destruct (Ha k c v).
    - by apply (Hn m a m2').
  Qed.

  Lemma nowrap_step n a : nowrap n → wrapb (nout n) (offer_of a) = false → nowrap (n ++ [a]).
  Proof.
    intros Hn Hw m a0 m2 E Ha. apply split_snoc in E as [(-> & -> & _)|(m2' & -> & ->)].
    - done.
    - by apply (Hn m a0 m2').
  Qed.

  Lemma pcause_ext n a : pcause n → pcause (n ++ [a]).
  Proof.
    intros [Hf|[Hs|(a0 & Hin & Hu)]].
    - left. unfold nout in *. rewrite list.filter_app, length_app. lia.
    - right. left. by apply S_T_ext.
    - right. right. exists a0. split; [apply elem_of_app; by left|done].
  Qed.

  Lemma wpath_ext n a : wpath n → wpath (n ++ [a]).
  Proof.
    intros (m & a0 & m2 & -> & Ha & Hw & Ht). exists m, a0, (m2 ++ [a]). by rewrite <- app_assoc.
  Qed.

  Lemma rpath_ext n a : rpath n → rpath (n ++ [a]).
  Proof.
    intros (m & a0 & m2 & -> & Ha & Hr). exists m, a0, (m2 ++ [a]). by rewrite <- app_assoc.
  Qed.

  Lemma track_out md n k c v : track md n → track md (n ++ [CoOut k c v]).
  Proof.
    destruct md as [|f m| |]; simpl; [apply pcause_ext| |apply wpath_ext|done].
    rewrite nout_out. intros (Em & Ef & Hn). split; [done|]. split; [done|]. by apply nowrap_out.
  Qed.

  Definition inv (n : node) : Prop :=
    (tnodes T n = [] ∧ tnodes TN n = [])
    ∨ (∃ X Y md, tnodes T n = [X] ∧ tnodes TN n = [Y] ∧ rel md X Y ∧ track md n)
    ∨ (tnodes T n = [] ∧ ∃ n0 X Y, tnodes TN n = [Y] ∧ tnodes T n0 = [X] ∧ rel MR X Y
        ∧ (∀ k c v, CoOut k c v ∈ n → CoOut k c v ∈ n0) ∧ rpath n).

  Lemma inv_step n a : inv n → inv (n ++ [a]).
  Proof.
    intros [[EX EY]|[(X & Y & md & EX & EY & Hr & Hm)|(ET & n0 & X & Y & EY & EX0 & Hr & Hp & Hrp)]];
      unfold inv; rewrite !tnodes_app.
    - rewrite EX, EY. by left.
    - rewrite EX, EY. simpl. rewrite !app_nil_r.
      assert (Hlx : length (co_succ X a) ≤ 1).
      { pose proof (HT1 (n ++ [a])) as Hle. rewrite tnodes_app, EX in Hle. simpl in Hle. by rewrite app_nil_r in Hle. }
      destruct (classic (∃ k c v, a = CoOut k c v)) as [(k & c & v & ->)|Ha].
      + destruct (rel_out VL reps wrapb md X Y k c v Hr) as [Hl He].
        destruct (single_step _ _ (rel md) Hlx Hl He) as [[-> ->]|(X' & Y' & -> & -> & Hr')]; [by left|].
        right. left. exists X', Y', md. split; [done|]. split; [done|]. split; [done|]. by apply track_out.
      + assert (Ha' : ∀ k c v, a ≠ CoOut k c v) by (intros k c v E; apply Ha; by exists k, c, v).
        destruct md as [|f m| |]; [| | |done].
        * destruct (rel_nout_P VL reps wrapb X Y a Ha' Hr) as [Hl He].
          destruct (single_step _ _ (rel MP) Hlx Hl He) as [[-> ->]|(X' & Y' & -> & -> & Hr')]; [by left|].
          right. left. exists X', Y', MP. split; [done|]. split; [done|]. split; [done|]. by apply pcause_ext.
        * destruct Hm as (Em & Ef & Hnw). destruct (rel_nout_H VL reps wrapb Hnd f m X Y a Ha' Hr) as [HL He].
          destruct (tri_step _ _ (offer_of a ∈ reps m) (Q1H VL reps wrapb f m a) (rel MR X) Hlx HL He)
            as [(-> & -> & _)|[(X' & Y' & E1 & E2 & HQ)|(E1 & Hin & Y' & -> & HR)]].
          -- by left.
          -- rewrite E1, E2. right. left. destruct HQ as [[Hw HQ]|[Hw [[HQ Hc]|(f' & Ef' & HQ)]]].
             ++ exists X', Y', MC. split; [done|]. split; [done|]. split; [done|].
                exists n, a, []. split; [done|]. split; [done|]. split; [by rewrite <- Em|].
                rewrite tnodes_app, EX. simpl. by rewrite app_nil_r, E1.
             ++ exists X', Y', MP. split; [done|]. split; [done|]. split; [done|].
                destruct Hc as [Hc|[Hc|Hc]].
                ** right. right. exists a. split; [apply elem_of_app; right; by left|done].
                ** left. rewrite (nout_nout n a Ha'), length_app, <- Em. simpl. lia.
                ** right. left. apply S_T_spec. exists (length (n ++ [a])). split; [done|].
                   rewrite firstn_all. unfold succ_at. rewrite tnodes_app, EX. simpl. rewrite app_nil_r, E1. simpl.
                   by rewrite Hc.
             ++ exists X', Y', (MH f' (m ++ [a])). split; [done|]. split; [done|]. split; [done|].
                split; [rewrite Em; symmetry; by apply nout_nout|]. split; [rewrite length_app; simpl; lia|].
                apply nowrap_step; [done|]. by rewrite <- Em.
          -- right. right. rewrite E1. split; [done|]. exists n, X, Y'. split; [done|]. split; [done|]. split; [done|].
             split.
             ++ intros k c v Hin'. apply elem_of_app in Hin' as [Hin'|Hin']; [done|].
                apply list_elem_of_singleton in Hin'. by destruct (Ha' k c v).
             ++ exists n, a, []. split; [done|]. split; [done|]. by rewrite <- Em.
        * destruct (rel_nout_C VL reps wrapb X Y a Ha' Hr) as [Hl He].
          destruct (single_step _ _ (rel MC) Hlx Hl He) as [[-> ->]|(X' & Y' & -> & -> & Hr')]; [by left|].
          right. left. exists X', Y', MC. split; [done|]. split; [done|]. split; [done|]. by apply wpath_ext.
    - rewrite ET, EY. simpl. rewrite app_nil_r.
      destruct (classic (∃ k c v, a = CoOut k c v)) as [(k & c & v & ->)|Ha].
      + assert (Hlx : length (co_succ X (CoOut k c v)) ≤ 1).
        { pose proof (HT1 (n0 ++ [CoOut k c v])) as Hle. rewrite tnodes_app, EX0 in Hle. simpl in Hle.
          by rewrite app_nil_r in Hle. }
        destruct (rel_out VL reps wrapb MR X Y k c v Hr) as [Hl He].
        destruct (single_step _ _ (rel MR) Hlx Hl He) as [[E1 ->]|(X' & Y' & E1 & -> & Hr')]; [by left|].
        right. right. split; [done|]. exists (n0 ++ [CoOut k c v]), X', Y'. split; [done|].
        split; [rewrite tnodes_app, EX0; simpl; by rewrite app_nil_r|]. split; [done|]. split; [|by apply rpath_ext].
        intros k1 c1 v1 Hin. apply elem_of_app in Hin as [Hin|Hin]; apply elem_of_app; [left; by apply Hp|by right].
      + assert (Ha' : ∀ k c v, a ≠ CoOut k c v) by (intros k c v E; apply Ha; by exists k, c, v).
        rewrite (rel_nout_R VL reps wrapb X Y a Ha' Hr). by left.
  Qed.

  Theorem inv_all n : inv n.
  Proof.
    induction n as [|a n IH] using rev_ind; [|by apply inv_step].
    right. left. destruct (tn_rel VL reps wrapb f0 [] T) as [[Hp Hc]|(f' & Ef & Hh)].
    - exists T, TN, MP. split; [done|]. split; [done|]. split; [done|]. destruct Hc as [->|Hc].
      + left. simpl. lia.
      + right. left. apply S_T_spec. exists 0. split; [simpl; lia|]. unfold succ_at. simpl. by rewrite Hc.
    - exists T, TN, (MH f' []). split; [done|]. split; [done|]. split; [done|]. split; [done|].
      split; [simpl; lia|]. intros m a m2 E. by destruct m.
  Qed.

  Lemma pcause_app n m : pcause n → pcause (n ++ m).
  Proof.
    intros Hp. induction m as [|a m IH] using rev_ind; [by rewrite app_nil_r|]. rewrite app_assoc. by apply pcause_ext.
  Qed.

  Lemma wpath_app n m : wpath n → wpath (n ++ m).
  Proof.
    intros Hp. induction m as [|a m IH] using rev_ind; [by rewrite app_nil_r|]. rewrite app_assoc. by apply wpath_ext.
  Qed.

  Lemma rpath_app n m : rpath n → rpath (n ++ m).
  Proof.
    intros Hp. induction m as [|a m IH] using rev_ind; [by rewrite app_nil_r|]. rewrite app_assoc. by apply rpath_ext.
  Qed.

  Lemma tn_len n : length (tnodes TN n) ≤ 1.
  Proof.
    destruct (inv_all n) as [[_ ->]|[(X & Y & md & _ & -> & _)|(_ & n0 & X & Y & -> & _)]]; simpl; lia.
  Qed.

  Lemma tn_gone n m k c v c' v' Y :
    (∀ n m k c v c' v' T', T' ∈ tnodes T (n ++ [CoOut k c v] ++ m) → co_succ T' (CoOut k c' v') = []) →
    Y ∈ tnodes TN (n ++ [CoOut k c v] ++ m) → co_succ Y (CoOut k c' v') = [].
  Proof.
    intros HT4 HY.
    destruct (inv_all (n ++ [CoOut k c v] ++ m))
      as [[_ E]|[(X & Y0 & md & EX & EY & Hr & _)|(_ & n0 & X & Y0 & EY & EX0 & Hr & Hp & _)]].
    - rewrite E in HY. by apply elem_of_nil in HY.
    - rewrite EY in HY. apply list_elem_of_singleton in HY. subst Y0.
      pose proof (HT4 n m k c v c' v' X) as HX. rewrite EX in HX. specialize (HX ltac:(by left)).
      pose proof (proj1 (rel_out VL reps wrapb md X Y k c' v' Hr)) as Hl. rewrite HX in Hl.
      by destruct (co_succ Y (CoOut k c' v')).
    - rewrite EY in HY. apply list_elem_of_singleton in HY. subst Y0.
      assert (Hin : CoOut k c v ∈ n0).
      { apply Hp. apply elem_of_app. right. by left. }
      apply list_elem_of_split in Hin as (n1 & m1 & ->).
      pose proof (HT4 n1 m1 k c v c' v' X) as HX. simpl in HX. rewrite EX0 in HX. specialize (HX ltac:(by left)).
      pose proof (proj1 (rel_out VL reps wrapb MR X Y k c' v' Hr)) as Hl. rewrite HX in Hl.
      by destruct (co_succ Y (CoOut k c' v')).
  Qed.

  Lemma tn_low n : S_T TN n = false →
    (tnodes T n = [] ∧ tnodes TN n = [])
    ∨ ∃ X Y, tnodes T n = [X] ∧ tnodes TN n = [Y] ∧ ((rel MP X Y ∧ pcause n) ∨ ∃ f, rel (MH f (nout n)) X Y).
  Proof.
    intros HS. assert (Hsa : succ_at TN n = false).
    { destruct (succ_at TN n) eqn:E; [by rewrite (succ_at_S _ _ E) in HS|done]. }
    destruct (inv_all n) as [H1|[(X & Y & md & EX & EY & Hr & Ht)|(_ & n0 & X & Y & EY & _ & Hr & _)]].
    - by left.
    - right. exists X, Y. split; [done|]. split; [done|].
      pose proof (rel_success VL reps wrapb md X Y Hr) as Hsu. unfold succ_at in Hsa. rewrite EY in Hsa.
      simpl in Hsa. rewrite orb_false_r in Hsa. destruct md as [|f m| |]; simpl in *.
      + left. by split.
      + right. exists f. destruct Ht as (-> & _). done.
      + congruence.
      + done.
    - exfalso. pose proof (rel_success VL reps wrapb MR X Y Hr) as Hsu. simpl in Hsu. unfold succ_at in Hsa.
      rewrite EY in Hsa. simpl in Hsa. rewrite orb_false_r in Hsa. congruence.
  Qed.

  Lemma tn_O n k c v : S_T TN n = false → ((k, c, v) ∈ O_T TN n ↔ (k, c, v) ∈ O_T T n).
  Proof.
    intros HS. rewrite !O_T_spec. destruct (tn_low n HS) as [[EX EY]|(X & Y & EX & EY & Hm)]; rewrite EX, EY.
    - split; intros (T' & HT' & _); by apply elem_of_nil in HT'.
    - assert (Hl : length (co_succ Y (CoOut k c v)) = length (co_succ X (CoOut k c v))).
      { destruct Hm as [[Hr _]|(f & Hr)]; exact (proj1 (rel_out VL reps wrapb _ X Y k c v Hr)). }
      split; intros (T' & HT' & Hne); apply list_elem_of_singleton in HT'; subst T'.
      + exists X. split; [by left|]. intros E. apply Hne. rewrite E in Hl. simpl in Hl.
        by destruct (co_succ Y (CoOut k c v)).
      + exists Y. split; [by left|]. intros E. apply Hne. rewrite E in Hl. simpl in Hl.
        by destruct (co_succ X (CoOut k c v)).
  Qed.

  Lemma tn_menu_low n o : S_T TN n = false →
    (menu T n o → menu TN n o) ∧ (menu TN n o → menu T n o ∨ o ∈ reps (nout n)).
  Proof.
    intros HS. destruct (tn_low n HS) as [[EX EY]|(X & Y & EX & EY & Hm)].
    - split; intros Hm; [by destruct (menu_nil _ _ _ EX Hm)|by destruct (menu_nil _ _ _ EY Hm)].
    - rewrite (menu_single _ _ _ o EX), (menu_single _ _ _ o EY). destruct Hm as [[Hr _]|(f & Hr)].
      + rewrite (ans_P VL reps wrapb X Y o Hr). split; [done|by left].
      + rewrite (ans_H VL reps wrapb Hnd f (nout n) X Y o Hr). split; [by left|].
        intros [Ha|[Hin _]]; [by left|by right].
  Qed.

  Lemma tn_menu_head n o : S_T TN n = false → ¬ pcause n → tnodes TN n ≠ [] →
    (menu TN n o ↔ menu T n o ∨ (o ∈ reps (nout n) ∧ ∀ k c v, o ≠ OffOut k c v)).
  Proof.
    intros HS Hnp Hne. destruct (tn_low n HS) as [[EX EY]|(X & Y & EX & EY & Hm)]; [done|].
    rewrite (menu_single _ _ _ o EX), (menu_single _ _ _ o EY). destruct Hm as [[_ Hp]|(f & Hr)]; [done|].
    exact (ans_H VL reps wrapb Hnd f (nout n) X Y o Hr).
  Qed.

  Lemma tn_menu_any n o : menu TN n o → menu T n o ∨ o ∈ reps (nout n) ∨ ∃ n0, menu T n0 o.
  Proof.
    intros Hm. destruct (inv_all n) as [[_ EY]|[(X & Y & md & EX & EY & Hr & Ht)|(_ & n0 & X & Y & EY & EX0 & Hr & _)]].
    - by destruct (menu_nil _ _ _ EY Hm).
    - apply (menu_single _ _ _ o EY) in Hm. rewrite (menu_single _ _ _ o EX). destruct md as [|f m| |]; simpl in Ht.
      + left. by apply (ans_P VL reps wrapb X Y o Hr).
      + destruct Ht as (Em & _). subst m. destruct (proj1 (ans_H VL reps wrapb Hnd f (nout n) X Y o Hr) Hm) as [Hx|[Hin _]];
          [by left|right; by left].
      + left. by apply (ans_C VL reps wrapb X Y o Hr).
      + done.
    - apply (menu_single _ _ _ o EY) in Hm. right. right. exists n0. apply (menu_single _ _ _ o EX0).
      exact (ans_R VL reps wrapb X Y o Hr Hm).
  Qed.

  Lemma tn_succ_up n : succ_at T n = true → succ_at TN n = true.
  Proof.
    unfold succ_at. destruct (inv_all n) as [[EX _]|[(X & Y & md & EX & EY & Hr & _)|(EX & _)]]; rewrite EX; [done| |done].
    rewrite EY. simpl. rewrite !orb_false_r. intros Hs. pose proof (rel_success VL reps wrapb md X Y Hr) as Hsu.
    destruct md as [|f m| |]; simpl in Hsu; [congruence|destruct Hsu; congruence|done|done].
  Qed.

  Lemma tn_succ_cases n : succ_at TN n = true → succ_at T n = true ∨ wpath n ∨ rpath n.
  Proof.
    unfold succ_at.
    destruct (inv_all n) as [[_ EY]|[(X & Y & md & EX & EY & Hr & Ht)|(_ & n0 & X & Y & EY & _ & _ & _ & Hrp)]];
      rewrite EY; [done| |by right; right].
    rewrite EX. simpl. rewrite !orb_false_r. intros Hs. pose proof (rel_success VL reps wrapb md X Y Hr) as Hsu.
    destruct md as [|f m| |]; simpl in *; [left; congruence|destruct Hsu; congruence|right; by left|done].
  Qed.

  Lemma tn_S_up n : S_T T n = true → S_T TN n = true.
  Proof. rewrite !S_T_spec. intros (i & Hi & Hs). exists i. split; [done|]. by apply tn_succ_up. Qed.

  Lemma tn_S_cases n : S_T TN n = true → S_T T n = true ∨ wpath n ∨ rpath n.
  Proof.
    rewrite !S_T_spec. intros (i & Hi & Hs). destruct (tn_succ_cases _ Hs) as [Hc|[Hc|Hc]].
    - left. by exists i.
    - right. left. rewrite <- (take_drop i n). by apply wpath_app.
    - right. right. rewrite <- (take_drop i n). by apply rpath_app.
  Qed.

  Lemma tn_wrap_succ m a : (∀ k c v, a ≠ CoOut k c v) → wrapb (nout m) (offer_of a) = true →
    tnodes T (m ++ [a]) ≠ [] → tnodes TN (m ++ [a]) ≠ [] → ¬ pcause (m ++ [a]) → succ_at TN (m ++ [a]) = true.
  Proof.
    intros Ha Hw HT HTN Hnp. unfold succ_at.
    destruct (inv_all (m ++ [a])) as [[_ EY]|[(X & Y & md & EX & EY & Hr & Ht)|(EX & _)]]; [done| |done].
    rewrite EY. simpl. rewrite orb_false_r. pose proof (rel_success VL reps wrapb md X Y Hr) as Hsu.
    destruct md as [|f m0| |]; simpl in *; [done| |done|done].
    destruct Ht as (_ & _ & Hnw). rewrite (Hnw m a [] eq_refl Ha) in Hw. discriminate Hw.
  Qed.

  Lemma tn_rep_succ n : tnodes T n = [] → tnodes TN n ≠ [] → succ_at TN n = true.
  Proof.
    intros HT HTN. unfold succ_at.
    destruct (inv_all n) as [[_ EY]|[(X & Y & md & EX & _)|(_ & n0 & X & Y & EY & _ & Hr & _)]]; [done|congruence|].
    rewrite EY. simpl. rewrite orb_false_r. exact (rel_success VL reps wrapb MR X Y Hr).
  Qed.
End Inv.
(* end hide *)
