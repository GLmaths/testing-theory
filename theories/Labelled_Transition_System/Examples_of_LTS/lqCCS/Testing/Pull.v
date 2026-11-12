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
From Stdlib Require Import Lia.
Import ListNotations.
From stdpp Require Import base countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum lqCCS.Language.Quantum_Weights.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.LTS lqCCS.Testing.Scheduled lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical.

#[local] Open Scope lqccs_scope.

Definition osim (R : proc → proc → Prop) : Prop :=
  ∀ X Y, R X Y → successb X = successb Y
    ∧ ∀ a, length (co_succ Y a) = length (co_succ X a)
         ∧ ∀ Y', Y' ∈ co_succ Y a → ∃ X', X' ∈ co_succ X a ∧ R X' Y'.

Section Osim.
  Context (R : proc → proc → Prop) (X Y : proc).
  Hypothesis HR : osim R.
  Hypothesis HXY : R X Y.
  Hypothesis HX : ∀ n, length (tnodes X n) ≤ 1.

  Lemma osim_tnodes n :
    (tnodes X n = [] ∧ tnodes Y n = []) ∨ ∃ X' Y', tnodes X n = [X'] ∧ tnodes Y n = [Y'] ∧ R X' Y'.
  Proof.
    induction n as [|a n IH] using rev_ind.
    - right. exists X, Y. by rewrite !tnodes_nil.
    - rewrite !tnodes_app. destruct IH as [[EX EY]|(X1 & Y1 & EX & EY & H1)]; rewrite EX, EY; simpl.
      + by left.
      + rewrite !app_nil_r. destruct (HR X1 Y1 H1) as [_ Ha]. destruct (Ha a) as [Hl Hel].
        pose proof (HX (n ++ [a])) as Hle. rewrite tnodes_app, EX in Hle. simpl in Hle. rewrite app_nil_r in Hle.
        revert Hl Hel Hle.
        destruct (co_succ X1 a) as [|X2 [|X3 l]]; destruct (co_succ Y1 a) as [|Y2 [|Y3 l']];
          intros Hl Hel Hle; simpl in *; try lia.
        * by left.
        * right. exists X2, Y2. split; [done|]. split; [done|].
          destruct (Hel Y2) as (X' & HX' & HR'); [by left|]. apply list_elem_of_singleton in HX'. by subst.
  Qed.

  Lemma osim_len n : length (tnodes Y n) ≤ 1.
  Proof. destruct (osim_tnodes n) as [[_ ->]|(X' & Y' & _ & -> & _)]; simpl; lia. Qed.

  Lemma osim_menu n o : menu Y n o ↔ menu X n o.
  Proof.
    destruct (osim_tnodes n) as [[EX EY]|(X' & Y' & EX & EY & H1)]; unfold menu; rewrite EX, EY.
    - split; intros (T' & a & HT' & _); by apply elem_of_nil in HT'.
    - destruct (HR X' Y' H1) as [_ Ha]. split; intros (T' & a & HT' & Eo & Hne);
        apply list_elem_of_singleton in HT'; subst T'; destruct (Ha a) as [Hl _].
      + exists X', a. split; [by left|]. split; [done|]. intros E. rewrite E in Hl. by destruct (co_succ Y' a).
      + exists Y', a. split; [by left|]. split; [done|]. intros E. rewrite E in Hl. by destruct (co_succ X' a).
  Qed.

  Lemma osim_succ_at n : succ_at Y n = succ_at X n.
  Proof.
    unfold succ_at. destruct (osim_tnodes n) as [[-> ->]|(X' & Y' & -> & -> & H1)]; [done|].
    simpl. by rewrite (proj1 (HR X' Y' H1)).
  Qed.

  Lemma osim_S n : S_T Y n = S_T X n.
  Proof.
    apply eq_true_iff_eq. rewrite !S_T_spec.
    split; intros (i & Hi & Hs); exists i; (split; [done|]); [by rewrite <- osim_succ_at|by rewrite osim_succ_at].
  Qed.

  Lemma osim_O n m : m ∈ O_T Y n ↔ m ∈ O_T X n.
  Proof.
    destruct m as [[k c] v]. rewrite !O_T_spec.
    destruct (osim_tnodes n) as [[EX EY]|(X' & Y' & EX & EY & H1)]; rewrite EX, EY.
    - split; intros (T' & HT' & _); by apply elem_of_nil in HT'.
    - destruct (HR X' Y' H1) as [_ Ha]. destruct (Ha (CoOut k c v)) as [Hl _].
      split; intros (T' & HT' & Hne); apply list_elem_of_singleton in HT'; subst T'.
      + exists X'. split; [by left|]. intros E. rewrite E in Hl. by destruct (co_succ Y' (CoOut k c v)).
      + exists Y'. split; [by left|]. intros E. rewrite E in Hl. by destruct (co_succ X' (CoOut k c v)).
  Qed.

  Lemma osim_gone n k c v :
    (∀ T', T' ∈ tnodes X n → co_succ T' (CoOut k c v) = []) →
    ∀ T', T' ∈ tnodes Y n → co_succ T' (CoOut k c v) = [].
  Proof.
    intros Hg T' HT'. destruct (osim_tnodes n) as [[EX EY]|(X' & Y' & EX & EY & H1)]; rewrite EY in HT'.
    - by apply elem_of_nil in HT'.
    - apply list_elem_of_singleton in HT'. subst T'. destruct (HR X' Y' H1) as [_ Ha].
      destruct (Ha (CoOut k c v)) as [Hl _]. rewrite (Hg X') in Hl; [|rewrite EX; by left].
      by destruct (co_succ Y' (CoOut k c v)).
  Qed.
End Osim.

Fixpoint bagof (X : proc) : proc :=
  match X with
  | PSend k c e => PSend k c e
  | P ∥ Q => bagof P ∥ bagof Q
  | PIte e P Q =>
      match eval e with
      | Some (VBool true) => bagof P
      | Some (VBool false) => bagof Q
      | _ => 𝟘
      end
  | _ => 𝟘
  end.

Fixpoint ns (X : proc) : proc :=
  match X with
  | PSend _ _ _ => 𝟘
  | P ∥ Q => ns P ∥ ns Q
  | PIte e P Q =>
      match eval e with
      | Some (VBool true) => ns P
      | Some (VBool false) => ns Q
      | _ => 𝟘
      end
  | _ => X
  end.

Inductive zs : proc → proc → proc → Prop :=
| zs_send k c e : zs (PSend k c e) (PSend k c e) 𝟘
| zs_refl X : zs 𝟘 X X
| zs_par B1 B2 P Q P' Q' : zs B1 P P' → zs B2 Q Q' → zs (B1 ∥ B2) (P ∥ Q) (P' ∥ Q')
| zs_iteT e B P Q Z : eval e = Some (VBool true) → zs B P Z → zs B (PIte e P Q) Z
| zs_iteF e B P Q Z : eval e = Some (VBool false) → zs B Q Z → zs B (PIte e P Q) Z
| zs_dead e P Q : eval e ≠ Some (VBool true) → eval e ≠ Some (VBool false) → zs 𝟘 (PIte e P Q) 𝟘.

Lemma zs_bagof X : zs (bagof X) X (ns X).
Proof.
  induction X as [t c e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t x P IHP|g]; simpl; try apply zs_refl.
  - apply zs_send.
  - destruct (eval e) as [[[]| |]|] eqn:He.
    + by apply zs_iteT.
    + by apply zs_iteF.
    + apply zs_dead; by rewrite He.
    + apply zs_dead; by rewrite He.
    + apply zs_dead; by rewrite He.
  - by apply zs_par.
Qed.

Lemma zs_success B X Z : zs B X Z → successb X = successb B || successb Z.
Proof.
  induction 1 as [k c e|X|B1 B2 P Q P' Q' _ IH1 _ IH2|e B P Q Z He _ IH|e B P Q Z He _ IH|e P Q Ht Hf]; simpl.
  - done.
  - done.
  - rewrite IH1, IH2. destruct (successb B1), (successb B2), (successb P'), (successb Q'); done.
  - by rewrite He.
  - by rewrite He.
  - destruct (eval e) as [[[]| |]|]; done.
Qed.

Lemma zs_step B X Z a : zs B X Z →
  length (co_succ X a) = length (co_succ B a) + length (co_succ Z a)
  ∧ (∀ B', B' ∈ co_succ B a → ∃ X', X' ∈ co_succ X a ∧ zs B' X' Z)
  ∧ (∀ Z', Z' ∈ co_succ Z a → ∃ X', X' ∈ co_succ X a ∧ zs B X' Z').
Proof.
  induction 1 as [k c e|X|B1 B2 P Q P' Q' Hz1 IH1 Hz2 IH2|e B P Q Z He _ IH|e B P Q Z He _ IH|e P Q Ht Hf].
  - split; [simpl; lia|]. split; [|intros Z' HZ; simpl in HZ; by apply elem_of_nil in HZ].
    intros B' HB. exists B'. split; [done|]. simpl in HB. destruct a; try (by apply elem_of_nil in HB).
    case_decide; [|by apply elem_of_nil in HB]. apply list_elem_of_singleton in HB. subst. apply zs_refl.
  - split; [done|]. split; [intros B' HB; simpl in HB; by apply elem_of_nil in HB|].
    intros Z' HZ. exists Z'. split; [done|apply zs_refl].
  - destruct IH1 as (L1 & HB1 & HZ1). destruct IH2 as (L2 & HB2 & HZ2). simpl.
    split; [rewrite !length_app, !length_fmap; lia|]. split.
    + intros B' HB. apply elem_of_app in HB as [(B0 & -> & HB)%list_elem_of_fmap|(B0 & -> & HB)%list_elem_of_fmap].
      * destruct (HB1 _ HB) as (X' & HX' & Hz). exists (X' ∥ Q).
        split; [apply elem_of_app; left; apply list_elem_of_fmap; by exists X'|by apply zs_par].
      * destruct (HB2 _ HB) as (X' & HX' & Hz). exists (P ∥ X').
        split; [apply elem_of_app; right; apply list_elem_of_fmap; by exists X'|by apply zs_par].
    + intros Z' HZ. apply elem_of_app in HZ as [(Z0 & -> & HZ)%list_elem_of_fmap|(Z0 & -> & HZ)%list_elem_of_fmap].
      * destruct (HZ1 _ HZ) as (X' & HX' & Hz). exists (X' ∥ Q).
        split; [apply elem_of_app; left; apply list_elem_of_fmap; by exists X'|by apply zs_par].
      * destruct (HZ2 _ HZ) as (X' & HX' & Hz). exists (P ∥ X').
        split; [apply elem_of_app; right; apply list_elem_of_fmap; by exists X'|by apply zs_par].
  - simpl. rewrite He. exact IH.
  - simpl. rewrite He. exact IH.
  - simpl. destruct (eval e) as [[[]| |]|]; try (by destruct Ht); try (by destruct Hf);
      (split; [done|split; intros x Hx; by apply elem_of_nil in Hx]).
Qed.

Inductive pull : proc → proc → Prop :=
| pl_refl X : pull X X
| pl_bag B X Z W : zs B X Z → pull Z W → pull X (B ∥ W)
| pl_iteT e A W X : eval e = Some (VBool true) → pull X W → pull X (PIte e W A)
| pl_iteF e A W X : eval e = Some (VBool false) → pull X W → pull X (PIte e A W).

Lemma pull_osim : osim pull.
Proof.
  intros X Y Hp. induction Hp as [X|B X Z W Hz Hp IH|e A W X He Hp IH|e A W X He Hp IH].
  - split; [done|]. intros a. split; [done|]. intros Y' HY. exists Y'. split; [done|apply pl_refl].
  - destruct IH as [IHs IHa]. split; [rewrite (zs_success _ _ _ Hz); simpl; by rewrite IHs|].
    intros a. destruct (zs_step B X Z a Hz) as (L & HB & HZ). destruct (IHa a) as [Lw Hw]. split.
    + simpl. rewrite length_app, !length_fmap. lia.
    + intros Y' HY. simpl in HY.
      apply elem_of_app in HY as [(B' & -> & HB')%list_elem_of_fmap|(W' & -> & HW')%list_elem_of_fmap].
      * destruct (HB _ HB') as (X' & HX' & Hz'). exists X'. split; [done|]. by eapply pl_bag.
      * destruct (Hw _ HW') as (Z' & HZ' & Hp'). destruct (HZ _ HZ') as (X' & HX' & Hz').
        exists X'. split; [done|]. by eapply pl_bag.
  - destruct IH as [IHs IHa]. split; [simpl; by rewrite He|]. intros a. simpl. rewrite He. exact (IHa a).
  - destruct IH as [IHs IHa]. split; [simpl; by rewrite He|]. intros a. simpl. rewrite He. exact (IHa a).
Qed.

Lemma exp_subst_shift k v e : exp_subst k v (exp_shift k e) = e.
Proof.
  induction e as [i|w|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2]; simpl; try congruence.
  case_decide as Hk; simpl.
  - case_decide as Ha; [lia|]. case_decide as Hb; [lia|done].
  - case_decide as Ha; [lia|]. case_decide as Hb; [done|lia].
Qed.

Lemma exps_subst_shift k v (es : list exp) : map (exp_subst k v) (map (exp_shift k) es) = es.
Proof. induction es as [|e es IH]; [done|]. simpl. by rewrite exp_subst_shift, IH. Qed.

Lemma prefix_subst_shift k v 𝜆 : prefix_subst k v (prefix_shift k 𝜆) = 𝜆.
Proof. destruct 𝜆; simpl; by rewrite ?exps_subst_shift. Qed.

Lemma prefix_binds_shift k 𝜆 : prefix_binds (prefix_shift k 𝜆) = prefix_binds 𝜆.
Proof. by destruct 𝜆. Qed.

Lemma subst_shiftv k v P : subst k v (shiftv k P) = P
with gsubst_gshiftv k v g : gsubst k v (gshiftv k g) = g.
Proof.
  - destruct P; simpl; rewrite ?exp_subst_shift, ?subst_shiftv, ?gsubst_gshiftv; done.
  - destruct g; simpl; rewrite ?exps_subst_shift, ?prefix_subst_shift, ?prefix_binds_shift,
      ?subst_shiftv, ?gsubst_gshiftv; done.
Qed.

Fixpoint gosucc (sel : prefix → bool) (g : guard) : list proc :=
  match g with
  | GNil _ | ① => []
  | 𝜆 ∙ P => if sel 𝜆 then [P] else []
  | g1 ⊕ g2 => gosucc sel g1 ++ gosucc sel g2
  end.

Fixpoint osucc (sel : prefix → bool) (Z : proc) : list proc :=
  match Z with
  | PIte e P Q =>
      match eval e with
      | Some (VBool true) => osucc sel P
      | Some (VBool false) => osucc sel Q
      | _ => []
      end
  | P ∥ Q => ((λ D, D ∥ shiftv 0 Q) <$> osucc sel P) ++ ((λ D, shiftv 0 P ∥ D) <$> osucc sel Q)
  | PG g => gosucc sel g
  | _ => []
  end.

Definition sel_in (k : tag) (c : channel) (𝜆 : prefix) : bool :=
  match 𝜆 with PRecv k' c' => bool_decide (k = k' ∧ c = c') | _ => false end.

Definition sel_meas (k : tag) (M : meas) (qs : list qubit) (𝜆 : prefix) : bool :=
  match 𝜆 with PMeas k' M' es => bool_decide (k = k' ∧ M = M' ∧ eval_qubits es = Some qs) | _ => false end.

Lemma gco_succ_in g k c v : gco_succ g (CoIn k c v) = (λ D, D ⟦ v ⟧) <$> gosucc (sel_in k c) g.
Proof.
  induction g as [es| |𝜆 P|g1 IH1 g2 IH2]; simpl.
  - done.
  - done.
  - destruct 𝜆 as [t|t c0|t E es|t M es|t es]; simpl; [done| |done|done|done].
    case_decide as Hd; [rewrite bool_decide_eq_true_2 by done|rewrite bool_decide_eq_false_2 by done]; done.
  - by rewrite fmap_app, IH1, IH2.
Qed.

Lemma co_succ_in Z k c v : co_succ Z (CoIn k c v) = (λ D, D ⟦ v ⟧) <$> osucc (sel_in k c) Z.
Proof.
  induction Z as [t c0 e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t x P IHP|g]; simpl.
  - done.
  - destruct (eval e) as [[[]| |]|]; done.
  - rewrite fmap_app, <- !list_fmap_compose, IHP, IHQ, <- !list_fmap_compose.
    f_equal; apply list_fmap_ext; intros i D _; simpl; by rewrite subst_shiftv.
  - done.
  - done.
  - done.
  - apply gco_succ_in.
Qed.

Lemma gco_succ_meas g k M qs n :
  gco_succ g (CoMeas k M qs n) = (λ D, D ⟦ VNat n ⟧) <$> gosucc (sel_meas k M qs) g.
Proof.
  induction g as [es| |𝜆 P|g1 IH1 g2 IH2]; simpl.
  - done.
  - done.
  - destruct 𝜆 as [t|t c0|t E es|t M0 es|t es]; simpl; [done|done|done| |done].
    case_decide as Hd; [rewrite bool_decide_eq_true_2 by done|rewrite bool_decide_eq_false_2 by done]; done.
  - by rewrite fmap_app, IH1, IH2.
Qed.

Lemma co_succ_meas Z k M qs n :
  co_succ Z (CoMeas k M qs n) = (λ D, D ⟦ VNat n ⟧) <$> osucc (sel_meas k M qs) Z.
Proof.
  induction Z as [t c0 e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t x P IHP|g]; simpl.
  - done.
  - destruct (eval e) as [[[]| |]|]; done.
  - rewrite fmap_app, <- !list_fmap_compose, IHP, IHQ, <- !list_fmap_compose.
    f_equal; apply list_fmap_ext; intros i D _; simpl; by rewrite subst_shiftv.
  - done.
  - done.
  - done.
  - apply gco_succ_meas.
Qed.

Definition quote (qs : list qubit) : list exp := map (λ x, EVal (VQubit x)) qs.

Lemma eval_quote qs : eval_qubits (quote qs) = Some qs.
Proof.
  unfold eval_qubits, quote. induction qs as [|x qs IH]; [done|]. simpl. rewrite IH. done.
Qed.
(* end hide *)
