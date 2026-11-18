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
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau pMust_almost_sure pMust_smyth pMust_transfer pMust_canonical.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.quantum_mem.Quantum_Weights.
From TestingTheory Require Import lqCCS.lqCCS_prog.Syntax lqCCS.Helper.De_Brujin_lemmas lqCCS.General_definition.Parallel_choice_LTS lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS lqCCS.lqCCS_process.LTS.LTS lqCCS.Helper.Conf_labels lqCCS.Helper.Label_lemmas lqCCS.Testing.Scheduled lqCCS.Testing.Observer_predicates lqCCS.Helper.Tag_lemmas lqCCS.Testing.DistLTS lqCCS.Testing.Programs lqCCS.Testing.Observers lqCCS.Testing.Smyth_Soundness lqCCS.Testing.Canonical.

#[local] Open Scope lqccs_scope.
#[local] Open Scope nat_scope.

Section Pull.
  Context `{lqP : lqCCS_Parameters}.

Definition osim (R : prog → prog → Prop) : Prop :=
  ∀ X Y, R X Y → successb X = successb Y
    ∧ ∀ a, length (co_succ Y a) = length (co_succ X a)
         ∧ ∀ Y', Y' ∈ co_succ Y a → ∃ X', X' ∈ co_succ X a ∧ R X' Y'.

Section Osim.
  Context (R : prog → prog → Prop) (X Y : prog).
  Hypothesis HR : osim R.
  Hypothesis HXY : R X Y.
  Hypothesis HX : ∀ z, length (tnodes X z) ≤ 1.

  Lemma osim_tnodes z :
    (tnodes X z = [] ∧ tnodes Y z = []) ∨ ∃ X' Y', tnodes X z = [X'] ∧ tnodes Y z = [Y'] ∧ R X' Y'.
  Proof.
    induction z as [|a z IH] using rev_ind.
    - right. exists X, Y. by rewrite !tnodes_nil.
    - rewrite !tnodes_app. destruct IH as [[EX EY]|(X1 & Y1 & EX & EY & H1)]; rewrite EX, EY; simpl.
      + by left.
      + rewrite !app_nil_r. destruct (HR X1 Y1 H1) as [_ Ha]. destruct (Ha a) as [Hl Hel].
        pose proof (HX (z ++ [a])) as Hle. rewrite tnodes_app, EX in Hle. simpl in Hle. rewrite app_nil_r in Hle.
        revert Hl Hel Hle.
        destruct (co_succ X1 a) as [|X2 [|X3 l]]; destruct (co_succ Y1 a) as [|Y2 [|Y3 l']];
          intros Hl Hel Hle; simpl in *; try lia.
        * by left.
        * right. exists X2, Y2. split; [done|]. split; [done|].
          destruct (Hel Y2) as (X' & HX' & HR'); [by left|]. apply list_elem_of_singleton in HX'. by subst.
  Qed.

  Lemma osim_len z : length (tnodes Y z) ≤ 1.
  Proof. destruct (osim_tnodes z) as [[_ ->]|(X' & Y' & _ & -> & _)]; simpl; lia. Qed.

  Lemma osim_menu z o : menu Y z o ↔ menu X z o.
  Proof.
    destruct (osim_tnodes z) as [[EX EY]|(X' & Y' & EX & EY & H1)]; unfold menu; rewrite EX, EY.
    - split; intros (T' & a & HT' & _); by apply elem_of_nil in HT'.
    - destruct (HR X' Y' H1) as [_ Ha]. split; intros (T' & a & HT' & Eo & Hne);
        apply list_elem_of_singleton in HT'; subst T'; destruct (Ha a) as [Hl _].
      + exists X', a. split; [by left|]. split; [done|]. intros E. rewrite E in Hl. by destruct (co_succ Y' a).
      + exists Y', a. split; [by left|]. split; [done|]. intros E. rewrite E in Hl. by destruct (co_succ X' a).
  Qed.

  Lemma osim_succ_at z : succ_at Y z = succ_at X z.
  Proof.
    unfold succ_at. destruct (osim_tnodes z) as [[-> ->]|(X' & Y' & -> & -> & H1)]; [done|].
    simpl. by rewrite (proj1 (HR X' Y' H1)).
  Qed.

  Lemma osim_S z : S_T Y z = S_T X z.
  Proof.
    apply eq_true_iff_eq. rewrite !S_T_spec.
    split; intros (i & Hi & Hs); exists i; (split; [done|]); [by rewrite <- osim_succ_at|by rewrite osim_succ_at].
  Qed.

  Lemma osim_O z m : m ∈ O_T Y z ↔ m ∈ O_T X z.
  Proof.
    destruct m as [[t c] v]. setoid_rewrite O_T_spec.
    destruct (osim_tnodes z) as [[EX EY]|(X' & Y' & EX & EY & H1)]; rewrite EX, EY.
    - split; intros (T' & HT' & _); by apply elem_of_nil in HT'.
    - destruct (HR X' Y' H1) as [_ Ha]. destruct (Ha (CoOut t c v)) as [Hl _].
      split; intros (T' & HT' & Hne); apply list_elem_of_singleton in HT'; subst T'.
      + exists X'. split; [by left|]. intros E. rewrite E in Hl. by destruct (co_succ Y' (CoOut t c v)).
      + exists Y'. split; [by left|]. intros E. rewrite E in Hl. by destruct (co_succ X' (CoOut t c v)).
  Qed.

  Lemma osim_gone z t c v :
    (∀ T', T' ∈ tnodes X z → co_succ T' (CoOut t c v) = []) →
    ∀ T', T' ∈ tnodes Y z → co_succ T' (CoOut t c v) = [].
  Proof.
    intros Hg T' HT'. destruct (osim_tnodes z) as [[EX EY]|(X' & Y' & EX & EY & H1)]; rewrite EY in HT'.
    - by apply elem_of_nil in HT'.
    - apply list_elem_of_singleton in HT'. subst T'. destruct (HR X' Y' H1) as [_ Ha].
      destruct (Ha (CoOut t c v)) as [Hl _]. rewrite (Hg X') in Hl; [|rewrite EX; by left].
      by destruct (co_succ Y' (CoOut t c v)).
  Qed.
End Osim.

Fixpoint bagof (X : prog) : prog :=
  match X with
  | t ∶ c ! e => t ∶ c ! e
  | P ∥ Q => bagof P ∥ bagof Q
  | If e Then P Else Q =>
      match eval e with
      | Some (VBool true) => bagof P
      | Some (VBool false) => bagof Q
      | _ => 𝟘
      end
  | _ => 𝟘
  end.

Fixpoint ns (X : prog) : prog :=
  match X with
  | PSend _ _ _ => 𝟘
  | P ∥ Q => ns P ∥ ns Q
  | If e Then P Else Q =>
      match eval e with
      | Some (VBool true) => ns P
      | Some (VBool false) => ns Q
      | _ => 𝟘
      end
  | _ => X
  end.

Inductive zs : prog → prog → prog → Prop :=
| zs_send t c e : zs (t ∶ c ! e) (t ∶ c ! e) 𝟘
| zs_refl X : zs 𝟘 X X
| zs_par B1 B2 P Q P' Q' : zs B1 P P' → zs B2 Q Q' → zs (B1 ∥ B2) (P ∥ Q) (P' ∥ Q')
| zs_iteT e B P Q Z : 〚 e 〛 = true → zs B P Z → zs B (If e Then P Else Q) Z
| zs_iteF e B P Q Z : 〚 e 〛 = false → zs B Q Z → zs B (If e Then P Else Q) Z
| zs_dead e P Q : ¬ 〚 e 〛 = true → ¬ 〚 e 〛 = false → zs 𝟘 (If e Then P Else Q) 𝟘.

Lemma zs_bagof X : zs (bagof X) X (ns X).
Proof.
  induction X as [t c e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t P IHP|g]; simpl; try apply zs_refl.
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
  induction 1 as [t c e|X|B1 B2 P Q P' Q' _ IH1 _ IH2|e B P Q Z He _ IH|e B P Q Z He _ IH|e P Q Ht Hf]; simpl.
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
  induction 1 as [t c e|X|B1 B2 P Q P' Q' Hz1 IH1 Hz2 IH2|e B P Q Z He _ IH|e B P Q Z He _ IH|e P Q Ht Hf].
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

Inductive pull : prog → prog → Prop :=
| pl_refl X : pull X X
| pl_bag B X Z W : zs B X Z → pull Z W → pull X (B ∥ W)
| pl_iteT e A W X : 〚 e 〛 = true → pull X W → pull X (If e Then W Else A)
| pl_iteF e A W X : 〚 e 〛 = false → pull X W → pull X (If e Then A Else W).

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

Fixpoint gosucc (sel : prefix → bool) (g : guard) : list prog :=
  match g with
  | 𝟘{_} | 𝟙 => []
  | π ∙ P => if sel π then [P] else []
  | (g1 + g2)%lq => gosucc sel g1 ++ gosucc sel g2
  end.

Fixpoint osucc (sel : prefix → bool) (Z : prog) : list prog :=
  match Z with
  | If e Then P Else Q =>
      match eval e with
      | Some (VBool true) => osucc sel P
      | Some (VBool false) => osucc sel Q
      | _ => []
      end
  | P ∥ Q => ((λ D, D ∥ ⇧ᵥ Q) <$> osucc sel P) ++ ((λ D, ⇧ᵥ P ∥ D) <$> osucc sel Q)
  | PG g => gosucc sel g
  | _ => []
  end.

Definition sel_in (t : tag) (c : channel) (π : prefix) : bool :=
  match π with (t' ∶ c' ?) => bool_decide (t = t' ∧ c = c') | _ => false end.

Definition sel_meas (t : tag) (M : meas) (qs : list qubit) (π : prefix) : bool :=
  match π with (t' ∶ M' ⦅es ▷⦆) => bool_decide (t = t' ∧ M = M' ∧ eval_qubits es = Some qs) | _ => false end.

Lemma gco_succ_in g t c v : gco_succ g (CoIn t c v) = (λ D, D ⁅ v ⁆ᵥ) <$> gosucc (sel_in t c) g.
Proof.
  induction g as [es| |π P|g1 IH1 g2 IH2]; simpl.
  - done.
  - done.
  - destruct π as [t'|t' c0|t' U es|t' M es|t' es]; simpl; [done| |done|done|done].
    case_decide as Hd; [rewrite bool_decide_eq_true_2 by done|rewrite bool_decide_eq_false_2 by done]; done.
  - by rewrite fmap_app, IH1, IH2.
Qed.

Lemma co_succ_in Z t c v : co_succ Z (CoIn t c v) = (λ D, D ⁅ v ⁆ᵥ) <$> osucc (sel_in t c) Z.
Proof.
  induction Z as [t' c0 e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t' P IHP|g]; simpl.
  - done.
  - destruct (eval e) as [[[]| |]|]; done.
  - rewrite fmap_app, <- !list_fmap_compose, IHP, IHQ, <- !list_fmap_compose.
    f_equal; apply list_fmap_ext; intros i D _; simpl; by rewrite subst_shiftv.
  - done.
  - done.
  - done.
  - apply gco_succ_in.
Qed.

Lemma gco_succ_meas g t M qs n :
  gco_succ g (CoMeas t M qs n) = (λ D, D ⁅ VNat n ⁆ᵥ) <$> gosucc (sel_meas t M qs) g.
Proof.
  induction g as [es| |π P|g1 IH1 g2 IH2]; simpl.
  - done.
  - done.
  - destruct π as [t'|t' c0|t' U es|t' M0 es|t' es]; simpl; [done|done|done| |done].
    case_decide as Hd; [rewrite bool_decide_eq_true_2 by done|rewrite bool_decide_eq_false_2 by done]; done.
  - by rewrite fmap_app, IH1, IH2.
Qed.

Lemma co_succ_meas Z t M qs n :
  co_succ Z (CoMeas t M qs n) = (λ D, D ⁅ VNat n ⁆ᵥ) <$> osucc (sel_meas t M qs) Z.
Proof.
  induction Z as [t' c0 e|e P IHP Q IHQ|P IHP Q IHQ|P IHP|x|t' P IHP|g]; simpl.
  - done.
  - destruct (eval e) as [[[]| |]|]; done.
  - rewrite fmap_app, <- !list_fmap_compose, IHP, IHQ, <- !list_fmap_compose.
    f_equal; apply list_fmap_ext; intros i D _; simpl; by rewrite subst_shiftv.
  - done.
  - done.
  - done.
  - apply gco_succ_meas.
Qed.

Definition quote (qs : list qubit) : list exp := map (λ x, EVal $x) qs.

Lemma eval_quote qs : eval_qubits (quote qs) = Some qs.
Proof.
  unfold eval_qubits, quote. induction qs as [|x qs IH]; [done|]. simpl. rewrite IH. done.
Qed.

End Pull.

(* end hide *)
