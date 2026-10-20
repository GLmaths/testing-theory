(* begin hide *)
(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>
   Copyright (c) 2025 Gaëtan Lopez <glopez@irif.fr>

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

From Stdlib.Program Require Import Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.
From stdpp Require Import decidable countable.
From TestingTheory Require Import ActTau gLts InputOutputActions Must 
Testing_Predicate VCCS.Language.gLts_Instance.


Section VCCS_Testing.

Context `{VP : VCCS_Parameters}.

(** ** Testing Predicate for VCCS *)
Inductive good_VCCS : proc -> Prop :=
| good_success : good_VCCS ①
| good_par : forall p q, good_VCCS p \/ good_VCCS q -> good_VCCS (p ‖ q)
| good_choice : forall p q, good_VCCS (g p) \/ good_VCCS (g q) -> good_VCCS (p + q)
| good_if_true : forall E p q, good_VCCS p -> Eval_Eq 0 E = Some true -> good_VCCS (If E Then p Else q)
| good_if_false : forall E p q, good_VCCS q -> Eval_Eq 0 E = Some false -> good_VCCS (If E Then p Else q)
| good_res : forall p, good_VCCS p -> good_VCCS (ν p).

Hint Constructors good_VCCS:ccs.

#[global] Instance good_decidable e : Decision $ good_VCCS e.
Proof.
  induction e; try (now right; inversion 1).
  - destruct IHe1; destruct IHe2; try (now left; eauto with ccs).
    right. inversion 1; naive_solver.
  - case_eq (Eval_Eq 0 e1); intros.
    + destruct b.
      * destruct IHe1; destruct IHe2; try (now left; eauto with ccs).
        right. inversion 1; naive_solver.
        right. inversion 1; naive_solver.
      * destruct IHe1; destruct IHe2; try (now left; eauto with ccs).
        right. inversion 1; naive_solver.
        right. inversion 1; naive_solver.
    + right. inversion 1; naive_solver.
  - destruct IHe. left. eapply good_res. eauto. right. intro. inversion H. subst. eauto.
  - induction g; try (now right; inversion 1); try (now left; eauto with ccs).
    destruct IHg1; destruct IHg2; try (now left; eauto with ccs).
    right. inversion 1; naive_solver.
Qed.

Lemma VarSwap_respects_good k p : good_VCCS p <-> good_VCCS (VarSwap_in_proc k p).
Proof.
  split.
  + revert k. induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
    destruct p; intros; simpl in *; eauto.
    ++ inversion H; subst. destruct H1.
       +++ eapply good_par. left. eapply Hp. simpl; lia. eauto.
       +++ eapply good_par. right. eapply Hp. simpl; lia. eauto.
    ++ inversion H.
    ++ inversion H; subst.
       +++ eapply good_if_true; eauto. eapply Hp. simpl; lia. eauto.
       +++ eapply good_if_false; eauto. eapply Hp. simpl; lia. eauto.
    ++ inversion H; subst. eapply good_res. eapply Hp. simpl; lia. eauto.
    ++ destruct g; intros; simpl in *; eauto; try now inversion H.
       inversion H; subst. destruct H1.
       +++ eapply good_choice. left.
           assert (good_VCCS (VarSwap_in_proc k (g g1))) as eq1.
           { eapply Hp. simpl; lia. eauto. }
           simpl in *; eauto.
       +++ eapply good_choice. right.
           assert (good_VCCS (VarSwap_in_proc k (g g2))) as eq2.
           { eapply Hp. simpl; lia. eauto. }
           simpl in *; eauto.
  + revert k. induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
    destruct p; intros; simpl in *; eauto.
    ++ inversion H; subst. destruct H1.
       +++ eapply good_par. left. eapply Hp. simpl; lia. eauto.
       +++ eapply good_par. right. eapply Hp. simpl; lia. eauto.
    ++ inversion H.
    ++ inversion H; subst.
       +++ eapply good_if_true; eauto. eapply Hp. simpl; lia. eauto.
       +++ eapply good_if_false; eauto. eapply Hp. simpl; lia. eauto.
    ++ inversion H; subst. eapply good_res. eapply Hp. simpl; lia. eauto.
    ++ destruct g; intros; simpl in *; eauto; try now inversion H.
       inversion H; subst. destruct H1.
       +++ eapply good_choice. left. eapply Hp. simpl; lia. eauto.
       +++ eapply good_choice. right. eapply Hp. simpl; lia. eauto.
Qed.

Lemma NewVarC_respects_good k p : good_VCCS p <-> good_VCCS (NewVarC k p).
Proof.
  split.
  + revert k. induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
    destruct p; intros; simpl in *; eauto.
    ++ inversion H; subst. destruct H1.
       +++ eapply good_par. left. eapply Hp. simpl; lia. eauto.
       +++ eapply good_par. right. eapply Hp. simpl; lia. eauto.
    ++ inversion H.
    ++ inversion H; subst.
       +++ eapply good_if_true; eauto. eapply Hp. simpl; lia. eauto.
       +++ eapply good_if_false; eauto. eapply Hp. simpl; lia. eauto.
    ++ inversion H; subst. eapply good_res. eapply Hp. simpl; lia. eauto.
    ++ destruct g; intros; simpl in *; eauto; try now inversion H.
       inversion H; subst. destruct H1.
       +++ eapply good_choice. left.
           assert (good_VCCS (NewVarC k (g g1))) as eq1.
           { eapply Hp. simpl; lia. eauto. }
           simpl in *; eauto.
       +++ eapply good_choice. right.
           assert (good_VCCS (NewVarC k (g g2))) as eq2.
           { eapply Hp. simpl; lia. eauto. }
           simpl in *; eauto.
  + revert k. induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
    destruct p; intros; simpl in *; eauto.
    ++ inversion H; subst. destruct H1.
       +++ eapply good_par. left. eapply Hp. simpl; lia. eauto.
       +++ eapply good_par. right. eapply Hp. simpl; lia. eauto.
    ++ inversion H.
    ++ inversion H; subst.
       +++ eapply good_if_true; eauto. eapply Hp. simpl; lia. eauto.
       +++ eapply good_if_false; eauto. eapply Hp. simpl; lia. eauto.
    ++ inversion H; subst. eapply good_res. eapply Hp. simpl; lia. eauto.
    ++ destruct g; intros; simpl in *; eauto; try now inversion H.
       inversion H; subst. destruct H1.
       +++ eapply good_choice. left. eapply Hp. simpl; lia. eauto.
       +++ eapply good_choice. right. eapply Hp. simpl; lia. eauto.
Qed.

Lemma good_preserved_by_cgr_step p q : good_VCCS p -> p ≡ q -> good_VCCS q.
Proof.
  intros happy cong. remember 0%nat as n0 eqn:hn0 in cong. revert happy.
  induction cong; intros happy; subst; try (now (inversion happy; subst; eauto)).
  + inversion happy; subst; eauto. rewrite H in H4. inversion H4; subst.
  + eapply good_if_true; eauto.
  + inversion happy; subst; eauto. rewrite H in H4. inversion H4; subst.
  + eapply good_if_false; eauto.
  + inversion happy; subst; eauto. destruct H0; eauto. inversion H; subst.
  + eapply good_par. left; eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end. eapply good_par.  destruct H; eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end. inversion H; subst; clear H; match goal with h : _ |- _ => rename h into H end.
    inversion H; subst; clear H; match goal with h : _ |- _ => rename h into H end. eapply good_par. destruct H; eauto. right. eapply good_par; eauto.
    eapply good_par. right. eapply good_par; eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end. inversion H; subst; clear H; match goal with h : _ |- _ => rename h into H end.
    eapply good_par; eauto. left. eapply good_par; eauto.
    inversion H; subst; clear H; match goal with h : _ |- _ => rename h into H end. eapply good_par. destruct H; eauto. left. eapply good_par; eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end ;eauto. inversion H; subst; clear H; match goal with h : _ |- _ => rename h into H end ;eauto.
    eapply good_res. eapply good_res. eapply VarSwap_respects_good in H. eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end ;eauto. inversion H; subst; clear H; match goal with h : _ |- _ => rename h into H end ;eauto.
    eapply good_res. eapply good_res. eapply VarSwap_respects_good in H. eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end ;eauto. inversion H; subst; clear H; match goal with h : _ |- _ => rename h into H end ;eauto.
    destruct H.
    ++ eapply good_par. left. eapply good_res. eauto.
    ++ eapply good_par. right. eapply NewVarC_respects_good. eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end ;eauto. destruct H.
    ++ inversion H; subst; clear H; match goal with h : _ |- _ => rename h into H end ;eauto. eapply good_res. eapply good_par. left. eauto.
    ++ eapply good_res. eapply good_par. right. eapply NewVarC_respects_good in H. eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end ;eauto. destruct H. eauto. inversion H.
  + eapply good_choice. left; eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end ;eauto. eapply good_choice. destruct H; eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end ;eauto. inversion H; subst; clear H; match goal with h : _ |- _ => rename h into H end ;eauto.
    inversion H; subst; clear H; match goal with h : _ |- _ => rename h into H end ;eauto. eapply good_choice; eauto. destruct H;eauto.
    right. eapply good_choice; eauto. eapply good_choice; eauto. right. eapply good_choice; eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end ;eauto. inversion H; subst; clear H; match goal with h : _ |- _ => rename h into H end ;eauto.
    eapply good_choice; eauto. left. eapply good_choice; eauto.
    inversion H; subst; clear H; match goal with h : _ |- _ => rename h into H end ;eauto. eapply good_choice; eauto. destruct H;eauto.
    left. eapply good_choice; eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end. destruct H. eapply good_par. left. eauto.
    eapply good_par. right. eauto.
  + eapply good_res. eapply IHcong; [reflexivity |]. inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end. eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end. eapply good_if_true; eauto.
    eapply good_if_false; eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end. eapply good_if_true; eauto.
    eapply good_if_false; eauto.
  + inversion happy; subst; clear happy; match goal with h : _ |- _ => rename h into H end. destruct H. eapply good_choice. left; eauto.
    eapply good_choice. right. eauto.
Qed.

Lemma good_preserved_by_cgr p q : good_VCCS p -> p ≡* q -> good_VCCS q.
Proof.
  intros hg hcgr. revert hg.
  induction hcgr; intros hg; [eapply good_preserved_by_cgr_step|]; eauto.
Qed.

#[global] Program Instance VCCS_Good : Testing_Predicate good_VCCS _.
Next Obligation. 
 intros. eapply good_preserved_by_cgr; eassumption.
Qed.
Next Obligation.
 intros. unfold non_blocking in H.  simpl in *. inversion H.
Qed.
Next Obligation.
 intros. unfold non_blocking in H.  simpl in *. inversion H.
Qed.
(* end hide *)

End VCCS_Testing.

#[global] Hint Constructors good_VCCS:ccs.
