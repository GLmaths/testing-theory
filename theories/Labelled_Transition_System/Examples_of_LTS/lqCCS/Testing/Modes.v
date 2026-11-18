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
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical lqCCS.Testing.Pull lqCCS.Testing.Head.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Modes.
  Context `{lqP : lqCCS_Parameters}.

Lemma omap_cons' {A B} (f : A → option B) x l :
  omap f (x :: l) = match f x with Some y => y :: omap f l | None => omap f l end.
Proof. done. Qed.

Lemma gco_out g t c v : gco_succ g (CoOut t c v) = [].
Proof.
  induction g as [es| |π P|g1 IH1 g2 IH2]; simpl; [done|done|by destruct π|by rewrite IH1, IH2].
Qed.

Definition nosend (X : prog) : Prop := ∀ t c v, co_succ X (CoOut t c v) = [].

Lemma ns_nosend X : nosend (ns X).
Proof.
  intros t c v. induction X as [t' c0 e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t' P IHP|g]; simpl.
  - done.
  - destruct (eval e) as [[[]| |]|]; done.
  - by rewrite IHP, IHQ.
  - done.
  - done.
  - done.
  - apply gco_out.
Qed.

Lemma zs_bag_silent B X Z a : zs B X Z → (∀ t c v, a ≠ CoOut t c v) → co_succ B a = [].
Proof.
  intros Hz Ha. induction Hz as [t c e|X|B1 B2 P Q P' Q' _ IH1 _ IH2|e B P Q Z He _ IH|e B P Q Z He _ IH|e P Q Ht Hf]; simpl.
  - destruct a; try done. by destruct (Ha t0 c0 v).
  - done.
  - by rewrite IH1, IH2.
  - exact IH.
  - exact IH.
  - done.
Qed.

Lemma zs_bag_nosucc B X Z : zs B X Z → successb B = false.
Proof.
  induction 1 as [t c e|X|B1 B2 P Q P' Q' _ IH1 _ IH2|e B P Q Z He _ IH|e B P Q Z He _ IH|e P Q Ht Hf]; simpl;
    try done. by rewrite IH1, IH2.
Qed.

Inductive pullb (base : prog → prog → Prop) : prog → prog → Prop :=
| pb_base X Y : base X Y → pullb base X Y
| pb_bag B X Z W : zs B X Z → pullb base Z W → pullb base X (B ∥ W)
| pb_iteT e A W X : 〚 e 〛 = true → pullb base X W → pullb base X (If e Then W Else A)
| pb_iteF e A W X : 〚 e 〛 = false → pullb base X W → pullb base X (If e Then A Else W).

Lemma pullb_tite base X W Y : tite W Y → pullb base X W → pullb base X Y.
Proof. induction 1 as [|e Y A He _ IH|e Y A He _ IH]; intros Hp; [done|apply pb_iteT; auto|apply pb_iteF; auto]. Qed.

Definition bagc (Q : prog → prog → Prop) : Prop := ∀ B X Z W, zs B X Z → Q Z W → Q X (B ∥ W).

Lemma pullb_nout base a (L : nat → nat → Prop) (Q1 Q2 : prog → prog → Prop) :
  (∀ t c v, a ≠ CoOut t c v) → bagc Q1 → bagc Q2 →
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
  destruct h as [π D]. unfold resp. intros Ho.
  destruct π, a, a'; simpl in *; try done; inversion Ho; subst; repeat case_decide; try done; naive_solver.
Qed.

Lemma omap_nil_offer a a' (l : list (prefix * prog)) :
  offer_of a = offer_of a' → omap (resp a) l = [] → omap (resp a') l = [].
Proof.
  intros Ho. induction l as [|h l IH]; [done|]. rewrite !omap_cons'.
  destruct (resp a h) eqn:E; [done|]. rewrite (resp_offer a a' h Ho E). exact IH.
Qed.

Lemma rg_resp o a : (∀ t c v, a ≠ CoOut t c v) → (∀ t, o ≠ OffUnfold t) →
  match rg o with
  | Some g => (offer_of a = o → gco_succ g a = [PG 𝟙]) ∧ (offer_of a ≠ o → gco_succ g a = [])
  | None => offer_of a ≠ o
  end.
Proof.
  intros Ha Hu. destruct o as [t c v|t c|t U qs|t M qs|t q|t]; simpl.
  - intros Ho. destruct a; try discriminate Ho. by destruct (Ha t0 c0 v0).
  - destruct a as [t0 c0 v0|t0 c0 v0|t0 E0 qs0|t0 M0 qs0 n0|t0 q0|t0]; simpl; try (split; [intros [=]|done]).
    case_decide as Hd.
    + split; [done|]. intros Hne. destruct Hne. by destruct Hd as [-> ->].
    + split; [|done]. intros [= -> ->]. by destruct Hd.
  - destruct a as [t0 c0 v0|t0 c0 v0|t0 E0 qs0|t0 M0 qs0 n0|t0 q0|t0]; simpl; try (split; [intros [=]|done]).
    rewrite eval_quote. case_decide as Hd.
    + split; [done|]. intros Hne. destruct Hne. by destruct Hd as (-> & -> & [= ->]).
    + split; [|done]. intros [= -> -> ->]. by destruct Hd.
  - destruct a as [t0 c0 v0|t0 c0 v0|t0 E0 qs0|t0 M0 qs0 n0|t0 q0|t0]; simpl; try (split; [intros [=]|done]).
    rewrite eval_quote. case_decide as Hd.
    + split; [done|]. intros Hne. destruct Hne. by destruct Hd as (-> & -> & [= ->]).
    + split; [|done]. intros [= -> -> ->]. by destruct Hd.
  - destruct a as [t0 c0 v0|t0 c0 v0|t0 E0 qs0|t0 M0 qs0 n0|t0 q0|t0]; simpl; try (split; [intros [=]|done]).
    change (eval_qubit $q) with (Some q). case_decide as Hd.
    + split; [done|]. intros Hne. destruct Hne. by destruct Hd as (-> & [= ->]).
    + split; [|done]. intros [= -> ->]. by destruct Hd.
  - by destruct (Hu t).
Qed.

Lemma reps_part (l : list offer) a : (∀ t c v, a ≠ CoOut t c v) → (∀ t, OffUnfold t ∉ l) → NoDup l →
  (offer_of a ∈ l → concat (map (λ g, gco_succ g a) (omap rg l)) = [PG 𝟙])
  ∧ (offer_of a ∉ l → concat (map (λ g, gco_succ g a) (omap rg l)) = []).
Proof.
  intros Ha. induction l as [|o l IH]; intros Hu Hnd.
  - split; [intros Hin; by apply elem_of_nil in Hin|done].
  - apply NoDup_cons in Hnd as [Hni Hnd].
    destruct (IH (λ t Hk, Hu t (proj2 (elem_of_cons _ _ _) (or_intror Hk))) Hnd) as [IH1 IH2]. rewrite omap_cons'.
    pose proof (rg_resp o a Ha (λ t E, Hu t (proj2 (elem_of_cons _ _ _) (or_introl (eq_sym E))))) as Hr. destruct (rg o) as [g|].
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

Definition ans (X : prog) (o : offer) : Prop := ∃ a, offer_of a = o ∧ co_succ X a ≠ [].

Lemma ns_obsb X : obsb X = true → obsb (ns X) = true.
Proof.
  induction X as [t c e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t P IHP|g]; simpl; intros Hob; try done.
  - apply andb_prop in Hob as [HP HQ]. destruct (eval e) as [[[]| |]|]; auto.
  - apply andb_prop in Hob as [HP HQ]. by rewrite IHP, IHQ.
Qed.

Inductive mode : Type := MP | MH (f : nat) (z' : node) | MC | MR.

Section Mode_Relations.
  Context (VL : list val) (reps : node → list offer) (wrapb : node → offer → bool).
  Hypothesis Hnd : ∀ z', NoDup (reps z').
  Hypothesis Hru : ∀ z' t, OffUnfold t ∉ reps z'.

  Definition bP (X Y : prog) : Prop := Y = X.
  Definition bC (X Y : prog) : Prop := ∃ W, pullb bP X W ∧ Y = PG 𝟙 ∥ W.
  Definition bH (f : nat) (z' : node) (X Y : prog) : Prop :=
    successb X = false ∧ nosend X ∧ obsb X = true ∧ Y = PG (hsum VL reps wrapb (tn VL reps wrapb f) z' X).
  Definition bR (X Y : prog) : Prop := nosend X ∧ Y = PG 𝟙.

  Definition rel (md : mode) : prog → prog → Prop :=
    pullb (match md with MP => bP | MH f z' => bH f z' | MC => bC | MR => bR end).

  Lemma rel_bagc md : bagc (rel md).
  Proof. intros B X Z W Hz Hp. by eapply pb_bag. Qed.

  Lemma tn_rel f z' X : obsb X = true →
    (rel MP X (tn VL reps wrapb f z' X) ∧ (f = 0 ∨ successb X = true))
    ∨ ∃ f', f = S f' ∧ rel (MH f' z') X (tn VL reps wrapb f z' X).
  Proof.
    intros Hob. destruct f as [|f]; [left; split; [by apply pb_base|by left]|]. simpl.
    destruct (successb X) eqn:Es; [left; split; [by apply pb_base|by right]|].
    right. exists f. split; [done|]. apply (pb_bag _ _ _ _ _ (zs_bagof X)). apply pb_base.
    split; [|split; [apply ns_nosend|split; [by apply ns_obsb|done]]].
    pose proof (zs_success _ _ _ (zs_bagof X)) as E. rewrite Es in E. by destruct (successb (bagof X)), (successb (ns X)).
  Qed.

  Lemma heads_part rec z' a (l : list (prefix * prog)) :
    length (concat (map (λ g, gco_succ g a) (omap (hguard VL wrapb rec z') l))) = length (omap (resp a) l)
    ∧ ∀ Y', Y' ∈ concat (map (λ g, gco_succ g a) (omap (hguard VL wrapb rec z') l)) →
        ∃ Z', Z' ∈ omap (resp a) l ∧ hres VL wrapb rec z' a Z' Y'.
  Proof.
    induction l as [|h l [IHl IHe]]; [split; [done|intros Y' HY; by apply elem_of_nil in HY]|].
    rewrite !omap_cons'. pose proof (hguard_spec VL wrapb rec z' h a) as Hsp.
    destruct (hguard VL wrapb rec z' h) as [g|].
    - destruct Hsp as [[Hr Hg]|(Z' & Y0 & Hr & Hg & Hh)]; rewrite Hr; simpl; rewrite Hg; simpl.
      + split; [exact IHl|exact IHe].
      + split; [by rewrite IHl|]. intros Y' HY. apply elem_of_cons in HY as [->|HY].
        * exists Z'. split; [by left|done].
        * destruct (IHe Y' HY) as (Z2 & HZ2 & Hh2). exists Z2. split; [by right|done].
    - rewrite Hsp. split; [exact IHl|exact IHe].
  Qed.

  Definition LH (z' : node) (a : coact) (x y : nat) : Prop :=
    (1 ≤ x → y = x) ∧ (x = 0 → (offer_of a ∈ reps z' → y = 1) ∧ (offer_of a ∉ reps z' → y = 0)).

  Definition Q1H (f : nat) (z' : node) (a : coact) (X' Y' : prog) : Prop :=
    (wrapb z' (offer_of a) = true ∧ rel MC X' Y')
    ∨ (wrapb z' (offer_of a) = false
       ∧ ((rel MP X' Y' ∧ (unlisted VL a ∨ f = 0 ∨ successb X' = true))
          ∨ ∃ f', f = S f' ∧ rel (MH f' (z' ++ [a])) X' Y')).

  Lemma bH_nout f z' Z a : (∀ t c v, a ≠ CoOut t c v) → nosend Z → obsb Z = true →
    LH z' a (length (co_succ Z a)) (length (co_succ (PG (hsum VL reps wrapb (tn VL reps wrapb f) z' Z)) a))
    ∧ ∀ Y', Y' ∈ co_succ (PG (hsum VL reps wrapb (tn VL reps wrapb f) z' Z)) a →
        (∃ Z', Z' ∈ co_succ Z a ∧ Q1H f z' a Z' Y') ∨ (co_succ Z a = [] ∧ rel MR Z Y').
  Proof.
    intros Ha Hns Hob. simpl. unfold hsum. rewrite gco_gsum, map_app, concat_app, (co_heads Z a Ha Hob).
    destruct (heads_part (tn VL reps wrapb f) z' a (heads Z)) as [Hl1 He1].
    assert (Hndr : NoDup (repl reps z' Z)) by (apply NoDup_filter, Hnd).
    destruct (reps_part (repl reps z' Z) a Ha (λ t Hk, Hru z' t (proj2 (proj1 (list_elem_of_filter _ _ _) Hk))) Hndr) as [R1 R2].
    assert (Hmem : offer_of a ∈ repl reps z' Z ↔ offer_of a ∈ reps z' ∧ omap (resp a) (heads Z) = []).
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
        * right. split; [done|]. assert (HZo : obsb Z' = true) by (apply (co_succ_obsb Z a Z' Hob); by rewrite (co_heads Z a Ha Hob)).
          destruct (tn_rel f (z' ++ [a]) Z' HZo) as [[Hp Hc]|(f' & Ef & Hh')].
          -- left. split; [by apply (pullb_tite _ _ _ _ Ht)|by right].
          -- right. exists f'. split; [done|]. by apply (pullb_tite _ _ _ _ Ht).
        * right. split; [done|]. left. split; [|by left]. apply (pullb_tite _ _ _ _ Ht). by apply pb_base.
      + right. destruct (classic (offer_of a ∈ repl reps z' Z)) as [Hin|Hnin];
          [|rewrite (R2 Hnin) in HY; by apply elem_of_nil in HY].
        rewrite (R1 Hin) in HY. apply list_elem_of_singleton in HY. subst Y'.
        apply Hmem in Hin as [_ E]. split; [done|]. apply pb_base. by split.
  Qed.

  Lemma rel_nout_H f z' X Y a : (∀ t c v, a ≠ CoOut t c v) → rel (MH f z') X Y →
    LH z' a (length (co_succ X a)) (length (co_succ Y a))
    ∧ ∀ Y', Y' ∈ co_succ Y a → (∃ X', X' ∈ co_succ X a ∧ Q1H f z' a X' Y') ∨ (co_succ X a = [] ∧ rel MR X Y').
  Proof.
    intros Ha. apply (pullb_nout (bH f z') a (LH z' a) (Q1H f z' a) (rel MR) Ha).
    - intros B X0 Z W Hz [[Hw Hq]|[Hw [[Hq Hc]|(f' & Ef & Hq)]]].
      + left. split; [done|]. by eapply pb_bag.
      + right. split; [done|]. left. split; [by eapply pb_bag|].
        destruct Hc as [Hc|[Hc|Hc]]; [by left|right; by left|right; right].
        rewrite (zs_success _ _ _ Hz), Hc. apply orb_true_r.
      + right. split; [done|]. right. exists f'. split; [done|]. by eapply pb_bag.
    - apply rel_bagc.
    - intros X0 Y0 (Hs & Hn & Hob & ->). exact (bH_nout f z' X0 a Ha Hn Hob).
  Qed.

  Lemma rel_nout_P X Y a : (∀ t c v, a ≠ CoOut t c v) → rel MP X Y →
    length (co_succ Y a) = length (co_succ X a) ∧ ∀ Y', Y' ∈ co_succ Y a → ∃ X', X' ∈ co_succ X a ∧ rel MP X' Y'.
  Proof.
    intros Ha Hp.
    destruct (pullb_nout bP a (λ x y, y = x) (rel MP) (λ _ _, False) Ha (rel_bagc MP)
                (λ B X0 Z W _ Hf, Hf)) with (X := X) (Y := Y) as [HL He]; [|exact Hp|].
    - intros X0 Y0 ->. split; [done|]. intros Y' HY. left. exists Y'. split; [done|by apply pb_base].
    - split; [done|]. intros Y' HY. destruct (He Y' HY) as [Hq|[_ []]]. exact Hq.
  Qed.

  Lemma rel_nout_C X Y a : (∀ t c v, a ≠ CoOut t c v) → rel MC X Y →
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

  Lemma rel_nout_R X Y a : (∀ t c v, a ≠ CoOut t c v) → rel MR X Y → co_succ Y a = [].
  Proof.
    intros Ha Hp.
    destruct (pullb_nout bR a (λ x y, y = 0) (λ _ _, False) (λ _ _, False) Ha
                (λ B X0 Z W _ Hf, Hf) (λ B X0 Z W _ Hf, Hf)) with (X := X) (Y := Y) as [HL _]; [|exact Hp|].
    - intros X0 Y0 [_ ->]. split; [done|]. intros Y' HY. by apply elem_of_nil in HY.
    - by destruct (co_succ Y a).
  Qed.

  Lemma rel_out_P X Y t c v : rel MP X Y →
    length (co_succ Y (CoOut t c v)) = length (co_succ X (CoOut t c v))
    ∧ ∀ Y', Y' ∈ co_succ Y (CoOut t c v) → ∃ X', X' ∈ co_succ X (CoOut t c v) ∧ rel MP X' Y'.
  Proof.
    apply pullb_out. intros X0 Y0 ->. split; [done|]. intros Y' HY. exists Y'. split; [done|by apply pb_base].
  Qed.

  Lemma rel_out md X Y t c v : rel md X Y →
    length (co_succ Y (CoOut t c v)) = length (co_succ X (CoOut t c v))
    ∧ ∀ Y', Y' ∈ co_succ Y (CoOut t c v) → ∃ X', X' ∈ co_succ X (CoOut t c v) ∧ rel md X' Y'.
  Proof.
    destruct md as [|f z'| |]; [apply rel_out_P| | |]; apply pullb_out.
    - intros X0 Y0 (_ & Hn & _ & ->). simpl. rewrite gco_out, (Hn t c v). split; [done|].
      intros Y' HY. by apply elem_of_nil in HY.
    - intros X0 Y0 (W & HW & ->). destruct (rel_out_P X0 W t c v HW) as [Hl Hel]. simpl. split.
      + by rewrite length_fmap.
      + intros Y' (W' & -> & HW')%list_elem_of_fmap. destruct (Hel W' HW') as (X' & HX' & Hr).
        exists X'. split; [done|]. apply pb_base. by exists W'.
    - intros X0 Y0 (Hn & ->). simpl. rewrite (Hn t c v). split; [done|].
      intros Y' HY. by apply elem_of_nil in HY.
  Qed.

  Lemma gsum_nosucc (l : list guard) : (∀ g, g ∈ l → gsuccessb g = false) → gsuccessb (gsum l) = false.
  Proof.
    induction l as [|g l IH]; intros Hl; [done|]. simpl. rewrite (Hl g) by (by left).
    apply IH. intros g' Hg'. apply Hl. by right.
  Qed.

  Lemma hsum_nosucc rec z' Z : gsuccessb (hsum VL reps wrapb rec z' Z) = false.
  Proof.
    apply gsum_nosucc. intros g Hg. apply elem_of_app in Hg as [Hg|Hg]; apply list_elem_of_omap in Hg as (x & _ & Hx).
    - destruct x as [π D]. unfold hguard in Hx. destruct π as [t'|t' c|t' U es|t' M es|t' e]; simpl in Hx.
      + discriminate Hx.
      + injection Hx as <-. done.
      + destruct (eval_qubits es); [injection Hx as <-; done|discriminate Hx].
      + destruct (eval_qubits es); [injection Hx as <-; done|discriminate Hx].
      + destruct (eval_qubit e); [injection Hx as <-; done|discriminate Hx].
    - destruct x as [t c v|t c|t U qs|t M qs|t q|t]; simpl in Hx;
        [discriminate Hx|injection Hx as <-; done..|discriminate Hx].
  Qed.

  Lemma rel_success md X Y : rel md X Y →
    match md with
    | MP => successb Y = successb X
    | MH _ _ => successb X = false ∧ successb Y = false
    | MC | MR => successb Y = true
    end.
  Proof.
    destruct md as [|f z'| |]; intros Hp.
    - refine (pullb_succ bP (λ x y, y = x) _ X Y Hp). by intros X0 Y0 ->.
    - refine (pullb_succ (bH f z') (λ x y, x = false ∧ y = false) _ X Y Hp). intros X0 Y0 (Hs & _ & _ & ->).
      split; [done|]. apply hsum_nosucc.
    - refine (pullb_succ bC (λ x y, y = true) _ X Y Hp). by intros X0 Y0 (W & _ & ->).
    - refine (pullb_succ bR (λ x y, y = true) _ X Y Hp). by intros X0 Y0 (_ & ->).
  Qed.

  Lemma relP_len X Y a : rel MP X Y → length (co_succ Y a) = length (co_succ X a).
  Proof.
    intros Hr. destruct (classic (∃ t c v, a = CoOut t c v)) as [(t & c & v & ->)|Ha].
    - exact (proj1 (rel_out MP X Y t c v Hr)).
    - apply (rel_nout_P X Y a); [|done]. intros t c v E. apply Ha. by exists t, c, v.
  Qed.

  Lemma relC_len X Y a : rel MC X Y → length (co_succ Y a) = length (co_succ X a).
  Proof.
    intros Hr. destruct (classic (∃ t c v, a = CoOut t c v)) as [(t & c & v & ->)|Ha].
    - exact (proj1 (rel_out MC X Y t c v Hr)).
    - apply (rel_nout_C X Y a); [|done]. intros t c v E. apply Ha. by exists t, c, v.
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

  Lemma ans_H f z' X Y o : rel (MH f z') X Y →
    (ans Y o ↔ ans X o ∨ (o ∈ reps z' ∧ ∀ t c v, o ≠ OffOut t c v)).
  Proof.
    intros Hr. split.
    - intros (a & Eo & Hne). destruct (classic (∃ t c v, a = CoOut t c v)) as [(t & c & v & ->)|Ha].
      + left. exists (CoOut t c v). split; [done|]. intros E. apply Hne.
        pose proof (proj1 (rel_out (MH f z') X Y t c v Hr)) as Hl. rewrite E in Hl. simpl in Hl.
        by destruct (co_succ Y (CoOut t c v)).
      + assert (Ha' : ∀ t c v, a ≠ CoOut t c v) by (intros t c v E; apply Ha; by exists t, c, v).
        destruct (rel_nout_H f z' X Y a Ha' Hr) as [[L1 L2] _].
        destruct (co_succ X a) as [|X' lx] eqn:EX.
        * right. destruct (L2 eq_refl) as [_ Lb]. split.
          -- rewrite <- Eo. apply NNPP. intros Hnin. pose proof (Lb Hnin) as Ly. by destruct (co_succ Y a).
          -- intros t c v E. rewrite <- Eo in E. destruct a; try discriminate E. by destruct (Ha' t0 c0 v0).
        * left. exists a. split; [done|]. by rewrite EX.
    - intros [(a & Eo & Hne)|[Hin Hno]].
      + exists a. split; [done|]. destruct (classic (∃ t c v, a = CoOut t c v)) as [(t & c & v & ->)|Ha].
        * intros E. apply Hne. pose proof (proj1 (rel_out (MH f z') X Y t c v Hr)) as Hl. rewrite E in Hl.
          simpl in Hl. by destruct (co_succ X (CoOut t c v)).
        * assert (Ha' : ∀ t c v, a ≠ CoOut t c v) by (intros t c v E; apply Ha; by exists t, c, v).
          destruct (rel_nout_H f z' X Y a Ha' Hr) as [[L1 _] _]. intros E. rewrite E in L1. simpl in L1.
          destruct (co_succ X a); [done|]. simpl in L1. specialize (L1 ltac:(lia)). lia.
      + assert (Ha' : ∀ t c v, co_of o ≠ CoOut t c v).
        { intros t c v E. destruct o; try discriminate E. by destruct (Hno t0 c0 v0). }
        destruct (rel_nout_H f z' X Y (co_of o) Ha' Hr) as [[L1 L2] _]. exists (co_of o).
        split; [apply offer_co_of|]. intros E. rewrite E in L1, L2. simpl in L1, L2.
        destruct (co_succ X (co_of o)) as [|X' lx]; simpl in *.
        * destruct (L2 eq_refl) as [La _]. rewrite offer_co_of in La. specialize (La Hin). lia.
        * specialize (L1 ltac:(lia)). lia.
  Qed.

  Lemma ans_R X Y o : rel MR X Y → ans Y o → ans X o.
  Proof.
    intros Hr (a & Eo & Hne). destruct (classic (∃ t c v, a = CoOut t c v)) as [(t & c & v & ->)|Ha].
    - exists (CoOut t c v). split; [done|]. intros E. apply Hne.
      pose proof (proj1 (rel_out MR X Y t c v Hr)) as Hl. rewrite E in Hl. simpl in Hl.
      by destruct (co_succ Y (CoOut t c v)).
    - exfalso. apply Hne. apply (rel_nout_R X Y a); [|done]. intros t c v E. apply Ha. by exists t, c, v.
  Qed.
End Mode_Relations.

Lemma menu_single T z X o : tnodes T z = [X] → (menu T z o ↔ ans X o).
Proof.
  intros E. unfold menu. rewrite E. split.
  - intros (T' & a & HT' & Eo & Hne). apply list_elem_of_singleton in HT'. subst. by exists a.
  - intros (a & Eo & Hne). exists X, a. split; [by left|done].
Qed.

Lemma menu_nil T z o : tnodes T z = [] → ¬ menu T z o.
Proof. intros E (T' & a & HT' & _). rewrite E in HT'. by apply elem_of_nil in HT'. Qed.

Lemma succ_at_S T z : succ_at T z = true → S_T T z = true.
Proof. intros Hs. apply S_T_spec. exists (length z). split; [done|]. by rewrite firstn_all. Qed.

Lemma split_snoc {A} (z z' z2 : list A) a a0 :
  z ++ [a] = z' ++ a0 :: z2 → (z' = z ∧ a0 = a ∧ z2 = []) ∨ ∃ z2', z2 = z2' ++ [a] ∧ z = z' ++ a0 :: z2'.
Proof.
  induction z2 as [|b z2 _] using rev_ind; intros E.
  - left. change (z ++ [a] = z' ++ [a0]) in E. apply app_inj_tail in E as [-> ->]. done.
  - right. exists z2. rewrite app_comm_cons, app_assoc in E. apply app_inj_tail in E as [-> ->]. done.
Qed.

Lemma single_step (lx ly : list prog) (Q : prog → prog → Prop) :
  length lx ≤ 1 → length ly = length lx → (∀ Y', Y' ∈ ly → ∃ X', X' ∈ lx ∧ Q X' Y') →
  (lx = [] ∧ ly = []) ∨ ∃ X' Y', lx = [X'] ∧ ly = [Y'] ∧ Q X' Y'.
Proof.
  intros Hlx Hl He. destruct lx as [|X' [|X2 lx]]; destruct ly as [|Y' [|Y2 ly]]; simpl in *; try lia.
  - by left.
  - right. exists X', Y'. split; [done|]. split; [done|]. destruct (He Y') as (X'' & HX'' & HQ); [by left|].
    apply list_elem_of_singleton in HX''. by subst.
Qed.

Lemma tri_step (lx ly : list prog) (P : Prop) (Q1 : prog → prog → Prop) (Q2 : prog → Prop) :
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

Definition nout (z : list coact) : list coact := filter (λ a, isout a = false) z.

Lemma nout_out z t c v : nout (z ++ [CoOut t c v]) = nout z.
Proof. unfold nout. rewrite list.filter_app, list.filter_cons_False by done. by rewrite list.filter_nil, app_nil_r. Qed.

Lemma nout_nout z a : (∀ t c v, a ≠ CoOut t c v) → nout (z ++ [a]) = nout z ++ [a].
Proof.
  intros Ha. unfold nout. rewrite list.filter_app. f_equal. rewrite list.filter_cons_True; [done|].
  destruct a; try done. by destruct (Ha t c v).
Qed.

Lemma S_T_ext T z a : S_T T z = true → S_T T (z ++ [a]) = true.
Proof.
  rewrite !S_T_spec. intros (i & Hi & Hs). exists i. split; [rewrite length_app; lia|].
  by rewrite take_app_le by lia.
Qed.

Section Inv.
  Context (VL : list val) (reps : node → list offer) (wrapb : node → offer → bool).
  Hypothesis Hnd : ∀ z', NoDup (reps z').
  Hypothesis Hru : ∀ z' t, OffUnfold t ∉ reps z'.
  Context (T : prog) (f0 : nat).
  Hypothesis HT1 : ∀ z, length (tnodes T z) ≤ 1.
  Hypothesis HTo : obsb T = true.

  Notation TN := (tn VL reps wrapb f0 [] T).
  Notation rel := (rel VL reps wrapb).

  Definition pcause (z : node) : Prop :=
    f0 ≤ length (nout z) ∨ S_T T z = true ∨ ∃ a, a ∈ z ∧ unlisted VL a.

  Definition wpath (z : node) : Prop :=
    ∃ z' a z2, z = z' ++ a :: z2 ∧ (∀ t c v, a ≠ CoOut t c v) ∧ wrapb (nout z') (offer_of a) = true
      ∧ tnodes T (z' ++ [a]) ≠ [].

  Definition rpath (z : node) : Prop :=
    ∃ z' a z2, z = z' ++ a :: z2 ∧ (∀ t c v, a ≠ CoOut t c v) ∧ offer_of a ∈ reps (nout z').

  Definition nowrap (z : node) : Prop :=
    ∀ z' a z2, z = z' ++ a :: z2 → (∀ t c v, a ≠ CoOut t c v) → wrapb (nout z') (offer_of a) = false.

  Definition track (md : mode) (z : node) : Prop :=
    match md with
    | MP => pcause z
    | MH f z' => z' = nout z ∧ f + length z' + 1 = f0 ∧ nowrap z
    | MC => wpath z
    | MR => False
    end.

  Lemma nowrap_out z t c v : nowrap z → nowrap (z ++ [CoOut t c v]).
  Proof.
    intros Hn z' a z2 E Ha. apply split_snoc in E as [(-> & -> & _)|(z2' & -> & ->)].
    - by destruct (Ha t c v).
    - by apply (Hn z' a z2').
  Qed.

  Lemma nowrap_step z a : nowrap z → wrapb (nout z) (offer_of a) = false → nowrap (z ++ [a]).
  Proof.
    intros Hn Hw z' a0 z2 E Ha. apply split_snoc in E as [(-> & -> & _)|(z2' & -> & ->)].
    - done.
    - by apply (Hn z' a0 z2').
  Qed.

  Lemma pcause_ext z a : pcause z → pcause (z ++ [a]).
  Proof.
    intros [Hf|[Hs|(a0 & Hin & Hu)]].
    - left. unfold nout in *. rewrite list.filter_app, length_app. lia.
    - right. left. by apply S_T_ext.
    - right. right. exists a0. split; [apply elem_of_app; by left|done].
  Qed.

  Lemma wpath_ext z a : wpath z → wpath (z ++ [a]).
  Proof.
    intros (z' & a0 & z2 & -> & Ha & Hw & Ht). exists z', a0, (z2 ++ [a]). by rewrite <- app_assoc.
  Qed.

  Lemma rpath_ext z a : rpath z → rpath (z ++ [a]).
  Proof.
    intros (z' & a0 & z2 & -> & Ha & Hr). exists z', a0, (z2 ++ [a]). by rewrite <- app_assoc.
  Qed.

  Lemma track_out md z t c v : track md z → track md (z ++ [CoOut t c v]).
  Proof.
    destruct md as [|f z'| |]; simpl; [apply pcause_ext| |apply wpath_ext|done].
    rewrite nout_out. intros (Em & Ef & Hn). split; [done|]. split; [done|]. by apply nowrap_out.
  Qed.

  Definition inv (z : node) : Prop :=
    (tnodes T z = [] ∧ tnodes TN z = [])
    ∨ (∃ X Y md, tnodes T z = [X] ∧ tnodes TN z = [Y] ∧ rel md X Y ∧ track md z)
    ∨ (tnodes T z = [] ∧ ∃ z0 X Y, tnodes TN z = [Y] ∧ tnodes T z0 = [X] ∧ rel MR X Y
        ∧ (∀ t c v, CoOut t c v ∈ z → CoOut t c v ∈ z0) ∧ rpath z).

  Lemma inv_step z a : inv z → inv (z ++ [a]).
  Proof.
    intros [[EX EY]|[(X & Y & md & EX & EY & Hr & Hm)|(ET & z0 & X & Y & EY & EX0 & Hr & Hp & Hrp)]];
      unfold inv; rewrite !tnodes_app.
    - rewrite EX, EY. by left.
    - rewrite EX, EY. simpl. rewrite !app_nil_r.
      assert (Hlx : length (co_succ X a) ≤ 1).
      { pose proof (HT1 (z ++ [a])) as Hle. rewrite tnodes_app, EX in Hle. simpl in Hle. by rewrite app_nil_r in Hle. }
      destruct (classic (∃ t c v, a = CoOut t c v)) as [(t & c & v & ->)|Ha].
      + destruct (rel_out VL reps wrapb md X Y t c v Hr) as [Hl He].
        destruct (single_step _ _ (rel md) Hlx Hl He) as [[-> ->]|(X' & Y' & -> & -> & Hr')]; [by left|].
        right. left. exists X', Y', md. split; [done|]. split; [done|]. split; [done|]. by apply track_out.
      + assert (Ha' : ∀ t c v, a ≠ CoOut t c v) by (intros t c v E; apply Ha; by exists t, c, v).
        destruct md as [|f z'| |]; [| | |done].
        * destruct (rel_nout_P VL reps wrapb X Y a Ha' Hr) as [Hl He].
          destruct (single_step _ _ (rel MP) Hlx Hl He) as [[-> ->]|(X' & Y' & -> & -> & Hr')]; [by left|].
          right. left. exists X', Y', MP. split; [done|]. split; [done|]. split; [done|]. by apply pcause_ext.
        * destruct Hm as (Em & Ef & Hnw). destruct (rel_nout_H VL reps wrapb Hnd Hru f z' X Y a Ha' Hr) as [HL He].
          destruct (tri_step _ _ (offer_of a ∈ reps z') (Q1H VL reps wrapb f z' a) (rel MR X) Hlx HL He)
            as [(-> & -> & _)|[(X' & Y' & E1 & E2 & HQ)|(E1 & Hin & Y' & -> & HR)]].
          -- by left.
          -- rewrite E1, E2. right. left. destruct HQ as [[Hw HQ]|[Hw [[HQ Hc]|(f' & Ef' & HQ)]]].
             ++ exists X', Y', MC. split; [done|]. split; [done|]. split; [done|].
                exists z, a, []. split; [done|]. split; [done|]. split; [by rewrite <- Em|].
                rewrite tnodes_app, EX. simpl. by rewrite app_nil_r, E1.
             ++ exists X', Y', MP. split; [done|]. split; [done|]. split; [done|].
                destruct Hc as [Hc|[Hc|Hc]].
                ** right. right. exists a. split; [apply elem_of_app; right; by left|done].
                ** left. rewrite (nout_nout z a Ha'), length_app, <- Em. simpl. lia.
                ** right. left. apply S_T_spec. exists (length (z ++ [a])). split; [done|].
                   rewrite firstn_all. unfold succ_at. rewrite tnodes_app, EX. simpl. rewrite app_nil_r, E1. simpl.
                   by rewrite Hc.
             ++ exists X', Y', (MH f' (z' ++ [a])). split; [done|]. split; [done|]. split; [done|].
                split; [rewrite Em; symmetry; by apply nout_nout|]. split; [rewrite length_app; simpl; lia|].
                apply nowrap_step; [done|]. by rewrite <- Em.
          -- right. right. rewrite E1. split; [done|]. exists z, X, Y'. split; [done|]. split; [done|]. split; [done|].
             split.
             ++ intros t c v Hin'. apply elem_of_app in Hin' as [Hin'|Hin']; [done|].
                apply list_elem_of_singleton in Hin'. by destruct (Ha' t c v).
             ++ exists z, a, []. split; [done|]. split; [done|]. by rewrite <- Em.
        * destruct (rel_nout_C VL reps wrapb X Y a Ha' Hr) as [Hl He].
          destruct (single_step _ _ (rel MC) Hlx Hl He) as [[-> ->]|(X' & Y' & -> & -> & Hr')]; [by left|].
          right. left. exists X', Y', MC. split; [done|]. split; [done|]. split; [done|]. by apply wpath_ext.
    - rewrite ET, EY. simpl. rewrite app_nil_r.
      destruct (classic (∃ t c v, a = CoOut t c v)) as [(t & c & v & ->)|Ha].
      + assert (Hlx : length (co_succ X (CoOut t c v)) ≤ 1).
        { pose proof (HT1 (z0 ++ [CoOut t c v])) as Hle. rewrite tnodes_app, EX0 in Hle. simpl in Hle.
          by rewrite app_nil_r in Hle. }
        destruct (rel_out VL reps wrapb MR X Y t c v Hr) as [Hl He].
        destruct (single_step _ _ (rel MR) Hlx Hl He) as [[E1 ->]|(X' & Y' & E1 & -> & Hr')]; [by left|].
        right. right. split; [done|]. exists (z0 ++ [CoOut t c v]), X', Y'. split; [done|].
        split; [rewrite tnodes_app, EX0; simpl; by rewrite app_nil_r|]. split; [done|]. split; [|by apply rpath_ext].
        intros t1 c1 v1 Hin. apply elem_of_app in Hin as [Hin|Hin]; apply elem_of_app; [left; by apply Hp|by right].
      + assert (Ha' : ∀ t c v, a ≠ CoOut t c v) by (intros t c v E; apply Ha; by exists t, c, v).
        rewrite (rel_nout_R VL reps wrapb X Y a Ha' Hr). by left.
  Qed.

  Theorem inv_all z : inv z.
  Proof.
    induction z as [|a z IH] using rev_ind; [|by apply inv_step].
    right. left. destruct (tn_rel VL reps wrapb f0 [] T HTo) as [[Hp Hc]|(f' & Ef & Hh)].
    - exists T, TN, MP. split; [done|]. split; [done|]. split; [done|]. destruct Hc as [->|Hc].
      + left. simpl. lia.
      + right. left. apply S_T_spec. exists 0. split; [simpl; lia|]. unfold succ_at. simpl. by rewrite Hc.
    - exists T, TN, (MH f' []). split; [done|]. split; [done|]. split; [done|]. split; [done|].
      split; [simpl; lia|]. intros z' a z2 E. by destruct z'.
  Qed.

  Lemma pcause_app z z' : pcause z → pcause (z ++ z').
  Proof.
    intros Hp. induction z' as [|a z' IH] using rev_ind; [by rewrite app_nil_r|]. rewrite app_assoc. by apply pcause_ext.
  Qed.

  Lemma wpath_app z z' : wpath z → wpath (z ++ z').
  Proof.
    intros Hp. induction z' as [|a z' IH] using rev_ind; [by rewrite app_nil_r|]. rewrite app_assoc. by apply wpath_ext.
  Qed.

  Lemma rpath_app z z' : rpath z → rpath (z ++ z').
  Proof.
    intros Hp. induction z' as [|a z' IH] using rev_ind; [by rewrite app_nil_r|]. rewrite app_assoc. by apply rpath_ext.
  Qed.

  Lemma tn_len z : length (tnodes TN z) ≤ 1.
  Proof.
    destruct (inv_all z) as [[_ ->]|[(X & Y & md & _ & -> & _)|(_ & z0 & X & Y & -> & _)]]; simpl; lia.
  Qed.

  Lemma tn_gone z z' t c v c' v' Y :
    (∀ z z' t c v c' v' T', T' ∈ tnodes T (z ++ [CoOut t c v] ++ z') → co_succ T' (CoOut t c' v') = []) →
    Y ∈ tnodes TN (z ++ [CoOut t c v] ++ z') → co_succ Y (CoOut t c' v') = [].
  Proof.
    intros HT4 HY.
    destruct (inv_all (z ++ [CoOut t c v] ++ z'))
      as [[_ E]|[(X & Y0 & md & EX & EY & Hr & _)|(_ & z0 & X & Y0 & EY & EX0 & Hr & Hp & _)]].
    - rewrite E in HY. by apply elem_of_nil in HY.
    - rewrite EY in HY. apply list_elem_of_singleton in HY. subst Y0.
      pose proof (HT4 z z' t c v c' v' X) as HX. rewrite EX in HX. specialize (HX ltac:(by left)).
      pose proof (proj1 (rel_out VL reps wrapb md X Y t c' v' Hr)) as Hl. rewrite HX in Hl.
      by destruct (co_succ Y (CoOut t c' v')).
    - rewrite EY in HY. apply list_elem_of_singleton in HY. subst Y0.
      assert (Hin : CoOut t c v ∈ z0).
      { apply Hp. apply elem_of_app. right. by left. }
      apply list_elem_of_split in Hin as (z1 & z1' & ->).
      pose proof (HT4 z1 z1' t c v c' v' X) as HX. simpl in HX. rewrite EX0 in HX. specialize (HX ltac:(by left)).
      pose proof (proj1 (rel_out VL reps wrapb MR X Y t c' v' Hr)) as Hl. rewrite HX in Hl.
      by destruct (co_succ Y (CoOut t c' v')).
  Qed.

  Lemma tn_low z : S_T TN z = false →
    (tnodes T z = [] ∧ tnodes TN z = [])
    ∨ ∃ X Y, tnodes T z = [X] ∧ tnodes TN z = [Y] ∧ ((rel MP X Y ∧ pcause z) ∨ ∃ f, rel (MH f (nout z)) X Y).
  Proof.
    intros HS. assert (Hsa : succ_at TN z = false).
    { destruct (succ_at TN z) eqn:E; [by rewrite (succ_at_S _ _ E) in HS|done]. }
    destruct (inv_all z) as [H1|[(X & Y & md & EX & EY & Hr & Ht)|(_ & z0 & X & Y & EY & _ & Hr & _)]].
    - by left.
    - right. exists X, Y. split; [done|]. split; [done|].
      pose proof (rel_success VL reps wrapb md X Y Hr) as Hsu. unfold succ_at in Hsa. rewrite EY in Hsa.
      simpl in Hsa. rewrite orb_false_r in Hsa. destruct md as [|f z'| |]; simpl in *.
      + left. by split.
      + right. exists f. destruct Ht as (-> & _). done.
      + congruence.
      + done.
    - exfalso. pose proof (rel_success VL reps wrapb MR X Y Hr) as Hsu. simpl in Hsu. unfold succ_at in Hsa.
      rewrite EY in Hsa. simpl in Hsa. rewrite orb_false_r in Hsa. congruence.
  Qed.

  Lemma tn_O z t c v : S_T TN z = false → ((t, c, v) ∈ O_T TN z ↔ (t, c, v) ∈ O_T T z).
  Proof.
    intros HS. rewrite !O_T_spec. destruct (tn_low z HS) as [[EX EY]|(X & Y & EX & EY & Hm)]; rewrite EX, EY.
    - split; intros (T' & HT' & _); by apply elem_of_nil in HT'.
    - assert (Hl : length (co_succ Y (CoOut t c v)) = length (co_succ X (CoOut t c v))).
      { destruct Hm as [[Hr _]|(f & Hr)]; exact (proj1 (rel_out VL reps wrapb _ X Y t c v Hr)). }
      split; intros (T' & HT' & Hne); apply list_elem_of_singleton in HT'; subst T'.
      + exists X. split; [by left|]. intros E. apply Hne. rewrite E in Hl. simpl in Hl.
        by destruct (co_succ Y (CoOut t c v)).
      + exists Y. split; [by left|]. intros E. apply Hne. rewrite E in Hl. simpl in Hl.
        by destruct (co_succ X (CoOut t c v)).
  Qed.

  Lemma tn_menu_low z o : S_T TN z = false →
    (menu T z o → menu TN z o) ∧ (menu TN z o → menu T z o ∨ o ∈ reps (nout z)).
  Proof.
    intros HS. destruct (tn_low z HS) as [[EX EY]|(X & Y & EX & EY & Hm)].
    - split; intros Hm; [by destruct (menu_nil _ _ _ EX Hm)|by destruct (menu_nil _ _ _ EY Hm)].
    - rewrite (menu_single _ _ _ o EX), (menu_single _ _ _ o EY). destruct Hm as [[Hr _]|(f & Hr)].
      + rewrite (ans_P VL reps wrapb X Y o Hr). split; [done|by left].
      + rewrite (ans_H VL reps wrapb Hnd Hru f (nout z) X Y o Hr). split; [by left|].
        intros [Ha|[Hin _]]; [by left|by right].
  Qed.

  Lemma tn_menu_head z o : S_T TN z = false → ¬ pcause z → tnodes TN z ≠ [] →
    (menu TN z o ↔ menu T z o ∨ (o ∈ reps (nout z) ∧ ∀ t c v, o ≠ OffOut t c v)).
  Proof.
    intros HS Hnp Hne. destruct (tn_low z HS) as [[EX EY]|(X & Y & EX & EY & Hm)]; [done|].
    rewrite (menu_single _ _ _ o EX), (menu_single _ _ _ o EY). destruct Hm as [[_ Hp]|(f & Hr)]; [done|].
    exact (ans_H VL reps wrapb Hnd Hru f (nout z) X Y o Hr).
  Qed.

  Lemma tn_menu_any z o : menu TN z o → menu T z o ∨ o ∈ reps (nout z) ∨ ∃ z0, menu T z0 o.
  Proof.
    intros Hm. destruct (inv_all z) as [[_ EY]|[(X & Y & md & EX & EY & Hr & Ht)|(_ & z0 & X & Y & EY & EX0 & Hr & _)]].
    - by destruct (menu_nil _ _ _ EY Hm).
    - apply (menu_single _ _ _ o EY) in Hm. rewrite (menu_single _ _ _ o EX). destruct md as [|f z'| |]; simpl in Ht.
      + left. by apply (ans_P VL reps wrapb X Y o Hr).
      + destruct Ht as (Em & _). subst z'. destruct (proj1 (ans_H VL reps wrapb Hnd Hru f (nout z) X Y o Hr) Hm) as [Hx|[Hin _]];
          [by left|right; by left].
      + left. by apply (ans_C VL reps wrapb X Y o Hr).
      + done.
    - apply (menu_single _ _ _ o EY) in Hm. right. right. exists z0. apply (menu_single _ _ _ o EX0).
      exact (ans_R VL reps wrapb X Y o Hr Hm).
  Qed.

  Lemma tn_succ_up z : succ_at T z = true → succ_at TN z = true.
  Proof.
    unfold succ_at. destruct (inv_all z) as [[EX _]|[(X & Y & md & EX & EY & Hr & _)|(EX & _)]]; rewrite EX; [done| |done].
    rewrite EY. simpl. rewrite !orb_false_r. intros Hs. pose proof (rel_success VL reps wrapb md X Y Hr) as Hsu.
    destruct md as [|f z'| |]; simpl in Hsu; [congruence|destruct Hsu; congruence|done|done].
  Qed.

  Lemma tn_succ_cases z : succ_at TN z = true → succ_at T z = true ∨ wpath z ∨ rpath z.
  Proof.
    unfold succ_at.
    destruct (inv_all z) as [[_ EY]|[(X & Y & md & EX & EY & Hr & Ht)|(_ & z0 & X & Y & EY & _ & _ & _ & Hrp)]];
      rewrite EY; [done| |by right; right].
    rewrite EX. simpl. rewrite !orb_false_r. intros Hs. pose proof (rel_success VL reps wrapb md X Y Hr) as Hsu.
    destruct md as [|f z'| |]; simpl in *; [left; congruence|destruct Hsu; congruence|right; by left|done].
  Qed.

  Lemma tn_S_up z : S_T T z = true → S_T TN z = true.
  Proof. rewrite !S_T_spec. intros (i & Hi & Hs). exists i. split; [done|]. by apply tn_succ_up. Qed.

  Lemma tn_S_cases z : S_T TN z = true → S_T T z = true ∨ wpath z ∨ rpath z.
  Proof.
    rewrite !S_T_spec. intros (i & Hi & Hs). destruct (tn_succ_cases _ Hs) as [Hc|[Hc|Hc]].
    - left. by exists i.
    - right. left. rewrite <- (take_drop i z). by apply wpath_app.
    - right. right. rewrite <- (take_drop i z). by apply rpath_app.
  Qed.

  Lemma tn_wrap_succ z' a : (∀ t c v, a ≠ CoOut t c v) → wrapb (nout z') (offer_of a) = true →
    tnodes T (z' ++ [a]) ≠ [] → tnodes TN (z' ++ [a]) ≠ [] → ¬ pcause (z' ++ [a]) → succ_at TN (z' ++ [a]) = true.
  Proof.
    intros Ha Hw HT HTN Hnp. unfold succ_at.
    destruct (inv_all (z' ++ [a])) as [[_ EY]|[(X & Y & md & EX & EY & Hr & Ht)|(EX & _)]]; [done| |done].
    rewrite EY. simpl. rewrite orb_false_r. pose proof (rel_success VL reps wrapb md X Y Hr) as Hsu.
    destruct md as [|f z0'| |]; simpl in *; [done| |done|done].
    destruct Ht as (_ & _ & Hnw). rewrite (Hnw z' a [] eq_refl Ha) in Hw. discriminate Hw.
  Qed.

  Lemma tn_rep_succ z : tnodes T z = [] → tnodes TN z ≠ [] → succ_at TN z = true.
  Proof.
    intros HT HTN. unfold succ_at.
    destruct (inv_all z) as [[_ EY]|[(X & Y & md & EX & _)|(_ & z0 & X & Y & EY & _ & Hr & _)]]; [done|congruence|].
    rewrite EY. simpl. rewrite orb_false_r. exact (rel_success VL reps wrapb MR X Y Hr).
  Qed.
End Inv.

End Modes.

(* end hide *)
