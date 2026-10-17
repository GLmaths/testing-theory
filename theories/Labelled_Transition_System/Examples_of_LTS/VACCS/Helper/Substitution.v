(* begin hide *)
(*
   Copyright (c) 2024 Gaëtan Lopez <gaetanlopez.maths@gmail.com>

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

From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Lia Program.Equality Relations Wellfounded.Inverse_Image.
From stdpp Require Import base countable list.
From TestingTheory Require Import ActTau InputOutputActions VACCS.Language.LTS.

Section VACCS_Substitution.

Context `{VP : VACCS_Parameters}.
Existing Instance VP.

Notation "⇑ g" := (gNewVarC 0 g) (at level 40).

Lemma VarC_TypeOfActions_add_add (k : nat) (i : nat) (a : TypeOfActions) :
        VarC_TypeOfActions_add k (VarC_TypeOfActions_add i a) = VarC_TypeOfActions_add (k + i) a.
Proof.
  revert i a.
  induction k; destruct a;destruct c; simpl ;eauto.
  f_equal. replace (k + (i + n))%nat with (k + i + n)%nat by lia. eauto.
Qed.

Lemma VarC_action_add_add (k : nat) (i : nat) (μ : ExtAct TypeOfActions) :
        VarC_action_add k (VarC_action_add i μ) = VarC_action_add (k + i) μ.
Proof.
  revert k μ.
  induction k; destruct μ ; destruct a; destruct c; intros; simpl; eauto.
  + f_equal. f_equal. f_equal. lia.
  + f_equal. f_equal. f_equal. lia.
Qed.

Lemma subst_and_VarSwap k k0 v p : subst_in_proc k v (VarSwap_in_proc k0 p) =
  (VarSwap_in_proc k0 (subst_in_proc k v p)).
Proof. 
  revert k k0 v.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *; repeat rewrite Hp by lia; eauto.
  destruct g; simpl in *; auto.
  - rewrite Hp by lia. eauto.
  - rewrite Hp by lia. eauto.
  - assert (subst_in_proc k v (VarSwap_in_proc k0 (g g1)) =
    VarSwap_in_proc k0 (subst_in_proc k v (g g1))) as eq1.
   { eapply Hp. simpl. lia. }
   assert (subst_in_proc k v (VarSwap_in_proc k0 (g g2)) =
      VarSwap_in_proc k0 (subst_in_proc k v (g g2))) as eq2.
   { eapply Hp. simpl. lia. } simpl in *. inversion eq1. inversion eq2.
   rewrite H0 , H1. eauto.
Qed.

Lemma subst_and_NewVarC k j v q : subst_in_proc k v (NewVarC j q) = NewVarC j (subst_in_proc k v q).
Proof.
  revert k j v.
  induction q as (q & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct q; intros; simpl in *; repeat rewrite Hp by lia; eauto.
  destruct g; simpl in *; auto.
  - assert ((subst_in_proc (S k) (Succ_bvar v) (NewVarC j p))
      = (NewVarC j (subst_in_proc (S k) (Succ_bvar v) p))) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  - assert (subst_in_proc k v (NewVarC j p) = NewVarC j (subst_in_proc k v p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  - assert (subst_in_proc k v (NewVarC j (g g1)) =
      NewVarC j (subst_in_proc k v (g g1))) as eq1.
    { eapply Hp. simpl. lia. }
    assert (subst_in_proc k v (NewVarC j (g g2)) =
        NewVarC j (subst_in_proc k v (g g2))) as eq2.
    { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

Lemma NewVar_and_VarSwap j k0 p :
  (NewVar j (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVar j p)).
Proof.
  revert j k0.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *; repeat rewrite Hp by lia; eauto.
  destruct g; simpl in *; auto.
  - now rewrite Hp by lia.
  - now rewrite Hp by lia.
  - assert (NewVar j (VarSwap_in_proc k0 (g g1)) =
      VarSwap_in_proc k0 (NewVar j (g g1))) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVar j (VarSwap_in_proc k0 (g g2)) =
      VarSwap_in_proc k0 (NewVar j (g g2))) as eq2.
    { eapply Hp. simpl. lia. } simpl in *. inversion eq1. inversion eq2.
    rewrite H0 , H1. eauto.
Qed.

Lemma NewVar_and_NewVarC j k p : (NewVar k (NewVarC j p) = (NewVarC j (NewVar k p))).
Proof.
  revert j k.
  (** ******* Induction on the size of p*)
  induction p as (p & Hp) using
      (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros; destruct p ; simpl in *; repeat rewrite Hp by lia; eauto.
  destruct g; simpl in *.
  - eauto.
  - eauto.
  - assert (NewVar (S k) (NewVarC j p) = NewVarC j (NewVar (S k) p)) as eq.
    { eapply Hp; simpl ; lia. }
    rewrite eq. eauto.
  - assert (NewVar k (NewVarC j p) = NewVarC j (NewVar k p)) as eq.
    { eapply Hp; simpl ; lia. }
    rewrite eq. eauto.
  - assert (NewVar k (NewVarC j (g g1)) = NewVarC j (NewVar k (g g1))) as eq1.
    { eapply Hp; simpl ; lia. }
    assert (NewVar k (NewVarC j (g g2)) = NewVarC j (NewVar k (g g2))) as eq2.
    { eapply Hp; simpl ; lia. } inversion eq1. inversion eq2.
    rewrite H0, H1. eauto.
Qed.

Lemma NewVar_in_ChannelData_and_VarSwap_in_ChannelData j k0 c :
(NewVar_in_ChannelData (S (S (j + k0))) (VarSwap_in_ChannelData k0 c)
        = VarSwap_in_ChannelData k0 (NewVar_in_ChannelData (S (S (j + k0))) c)).
Proof.
  destruct c.
  + simpl. reflexivity.
  + simpl. destruct (decide (n = k0)).
    - subst. simpl. destruct (decide (j + k0 < k0)).
      * rewrite decide_True; try lia.
      * rewrite decide_False; try lia.
        rewrite decide_False; try lia. simpl.
        rewrite decide_True; try lia. eauto.
    - simpl. destruct (decide ((n = S k0)%nat)); subst. 
      * simpl. destruct (decide ((S (S (j + k0)) < S k0)%nat)); subst.
        ++ rewrite decide_False; try lia.
        ++ rewrite decide_False; try lia. simpl.
           rewrite decide_False; try lia.
           rewrite decide_True; try lia. eauto.
      * destruct (decide (S (S (j + k0)) < S n)).
        ++ simpl. rewrite decide_True; try lia.
           destruct (decide ((S n = k0))).
           ** subst. lia.
           ** rewrite decide_False; try lia. eauto.
        ++ simpl. rewrite decide_False; try lia.
           rewrite decide_False; eauto.
           rewrite decide_False; try lia. eauto.
Qed.

Lemma NewVarC_and_VarSwap j k0 p : (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p)).
Proof.
  revert j k0.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *; repeat rewrite Hp by lia; eauto.
  - rewrite NewVar_in_ChannelData_and_VarSwap_in_ChannelData. eauto.
  - assert (S (S (S (j + k0))) = S (S (j + (S k0)))) as eq' by lia. rewrite eq'.
    assert (NewVarC (S (S (j + (S k0)))) (VarSwap_in_proc (S k0) p)
        = VarSwap_in_proc (S k0) (NewVarC (S (S (j + (S k0)))) p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  - destruct g; simpl in *.
    + reflexivity.
    + reflexivity.
    + assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p)) as eq1.
      { eapply Hp. simpl. lia. } rewrite eq1.
      rewrite NewVar_in_ChannelData_and_VarSwap_in_ChannelData. eauto.
    + assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) p)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    + assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 (g g1)) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) (g g1))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (NewVarC (S (S (j + k0))) (VarSwap_in_proc k0 (g g2)) = VarSwap_in_proc k0 (NewVarC (S (S (j + k0))) (g g2))) as eq2.
      { eapply Hp. simpl. lia. } simpl in *. inversion eq1. inversion eq2.
      rewrite H0 , H1. eauto.
Qed.

Lemma NewVar_in_ChannelData_and_NewVar_in_ChannelData i j c :
    NewVar_in_ChannelData (i + (S j)) (NewVar_in_ChannelData i c) 
      = NewVar_in_ChannelData i (NewVar_in_ChannelData ( i + j ) c).
Proof.
  destruct c. simpl.
  + eauto.
  + simpl. destruct (decide ((i < S n))).
    - simpl. destruct (decide (i + j < S n)).
      * rewrite decide_True; try lia. simpl.
        rewrite decide_True; try lia. eauto.
      * rewrite decide_False; try lia. simpl.
        rewrite decide_True; try lia. eauto.
    - simpl. rewrite decide_False; try lia.
      rewrite decide_False; try lia. simpl.
      rewrite decide_False; try lia. eauto.
Qed.

Lemma NewVarC_and_NewVarC i j p : NewVarC (i + (S j)) (NewVarC i p) = NewVarC i (NewVarC ( i + j ) p).
Proof.
  revert i j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *; repeat rewrite Hp by lia; eauto.
  + rewrite NewVar_in_ChannelData_and_NewVar_in_ChannelData. eauto.
  + assert (NewVarC (S (i + S j)) (NewVarC (S i) p) = NewVarC (S i) (NewVarC (S (i + j)) p)) as eq.
    { replace ((S (i + S j))) with ((S i) + S j)%nat; try lia.
      replace (S (i + j)) with ((S i) + j)%nat; try lia. eapply Hp.
      simpl. lia. } rewrite eq. eauto.
  + destruct g; simpl.
    * eauto.
    * eauto.
    * rewrite NewVar_in_ChannelData_and_NewVar_in_ChannelData.
      assert ((NewVarC (i + S j) (NewVarC i p)) = (NewVarC i (NewVarC (i + j) p))) as eq.
      { eapply Hp. simpl. eauto. } rewrite eq. eauto.
    * assert ((NewVarC (i + S j) (NewVarC i p)) = (NewVarC i (NewVarC (i + j) p))) as eq.
      { eapply Hp. simpl. eauto. } rewrite eq. eauto.
    * assert ((NewVarC (i + S j) (NewVarC i (g g1))) = (NewVarC i (NewVarC (i + j) (g g1)))) as eq1.
      { eapply Hp. simpl. lia. } inversion eq1.
      assert ((NewVarC (i + S j) (NewVarC i (g g2))) = (NewVarC i (NewVarC (i + j) (g g2)))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq2. eauto.
Qed.

Lemma VarSwap_NewVarC_in_ChannelData k c : NewVar_in_ChannelData k (NewVar_in_ChannelData k c) 
  = VarSwap_in_ChannelData k (NewVar_in_ChannelData k (NewVar_in_ChannelData k c)).
Proof.
  destruct c; simpl.
  + eauto.
  + destruct (decide (k < S n)).
    * simpl. rewrite decide_True; try lia.
      simpl. rewrite decide_False; try lia.
      rewrite decide_False; try lia. eauto.
    * simpl. rewrite decide_False; try lia.
      simpl. rewrite decide_False; try lia.
      rewrite decide_False; try lia. eauto.
Qed.

Lemma VarSwap_NewVarC k q : NewVarC k (NewVarC k q) = VarSwap_in_proc k (NewVarC k (NewVarC k q)).
Proof.
  revert k.
  induction q as (q & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct q ; intros; simpl in *.
  + assert (NewVarC k (NewVarC k q1) = VarSwap_in_proc k (NewVarC k (NewVarC k q1))) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarC k (NewVarC k q2) = VarSwap_in_proc k (NewVarC k (NewVarC k q2))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1 at 1. rewrite eq2 at 1. eauto.
  + eauto.
  + assert (NewVarC k (NewVarC k q) = VarSwap_in_proc k (NewVarC k (NewVarC k q))) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq at 1. eauto.
  + assert (NewVarC k (NewVarC k q1) = VarSwap_in_proc k (NewVarC k (NewVarC k q1))) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarC k (NewVarC k q2) = VarSwap_in_proc k (NewVarC k (NewVarC k q2))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1 at 1. rewrite eq2 at 1. eauto.
  + rewrite VarSwap_NewVarC_in_ChannelData at 1. eauto.
  + assert (NewVarC (S k) (NewVarC (S k) q) = VarSwap_in_proc (S k) (NewVarC (S k) (NewVarC (S k) q))) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq at 1. eauto.
  + destruct g; simpl in *.
    * eauto.
    * eauto.
    * assert (NewVarC k (NewVarC k p) = VarSwap_in_proc k (NewVarC k (NewVarC k p))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq at 1. eauto. rewrite VarSwap_NewVarC_in_ChannelData at 1.
      eauto.
    * assert (NewVarC k (NewVarC k p) = VarSwap_in_proc k (NewVarC k (NewVarC k p))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq at 1. eauto.
    * assert (NewVarC k (NewVarC k (g g1)) = VarSwap_in_proc k (NewVarC k (NewVarC k (g g1)))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (NewVarC k (NewVarC k (g g2)) = VarSwap_in_proc k (NewVarC k (NewVarC k (g g2)))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

Lemma pr_subst_and_VarSwap n p0 k q : pr_subst n (VarSwap_in_proc k p0) (NewVarC k (NewVarC k q)) 
      = VarSwap_in_proc k (pr_subst n p0 (NewVarC k (NewVarC k q))).
Proof.
  revert n k q.
  induction p0 as (p0 & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros; destruct p0; simpl in *.
  + assert (pr_subst n (VarSwap_in_proc k p0_1) (NewVarC k (NewVarC k q))
       = VarSwap_in_proc k (pr_subst n p0_1 (NewVarC k (NewVarC k q)))) as eq1.
    { eapply Hp. simpl. lia. }
    assert (pr_subst n (VarSwap_in_proc k p0_2) (NewVarC k (NewVarC k q))
       = VarSwap_in_proc k (pr_subst n p0_2 (NewVarC k (NewVarC k q)))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + destruct (decide (n = n0)); subst.
    ++ simpl. rewrite VarSwap_NewVarC at 1. eauto.
    ++ simpl. eauto.
  + destruct (decide (n = n0)); subst.
    ++ eauto.
    ++ simpl. assert (pr_subst n (VarSwap_in_proc k p0) (NewVarC k (NewVarC k q)) 
          = VarSwap_in_proc k (pr_subst n p0 (NewVarC k (NewVarC k q)))) as eq.
       { eapply Hp. simpl. lia. }
       rewrite eq. eauto.
  + assert (pr_subst n (VarSwap_in_proc k p0_1) (NewVarC k (NewVarC k q))
      = VarSwap_in_proc k (pr_subst n p0_1 (NewVarC k (NewVarC k q)))) as eq1.
    { eapply Hp. simpl. lia. }
    assert (pr_subst n (VarSwap_in_proc k p0_2) (NewVarC k (NewVarC k q))
      = VarSwap_in_proc k (pr_subst n p0_2 (NewVarC k (NewVarC k q)))) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + eauto.
  + assert (NewVarC (0 + (S k)) (NewVarC 0 q) = NewVarC 0 (NewVarC ( 0 + k ) q)) as eq.
    { rewrite NewVarC_and_NewVarC. eauto. }
    assert (NewVarC (0 + (S k)) (NewVarC 0 (NewVarC k q)) = NewVarC 0 (NewVarC ( 0 + k ) (NewVarC k q))) as eq2.
    { rewrite NewVarC_and_NewVarC. eauto. } simpl in *. rewrite<- eq2. rewrite<- eq.
    assert (pr_subst n (VarSwap_in_proc (S k) p0) (NewVarC (S k) (NewVarC (S k) (NewVarC 0 q)))
      = VarSwap_in_proc (S k) (pr_subst n p0 (NewVarC (S k) (NewVarC (S k) (NewVarC 0 q))))) as eq1.
    { eapply Hp. simpl. lia. } rewrite eq1. eauto.
  + destruct g; simpl.
    * eauto.
    * eauto.
    * rewrite NewVar_and_NewVarC. rewrite NewVar_and_NewVarC. 
      assert ((pr_subst n (VarSwap_in_proc k p) (NewVarC k (NewVarC k (NewVar 0 q))))
        = (VarSwap_in_proc k (pr_subst n p (NewVarC k (NewVarC k (NewVar 0 q)))))) as eq1.
      { eapply Hp. simpl. lia. } rewrite eq1. eauto.
    * assert (pr_subst n (VarSwap_in_proc k p) (NewVarC k (NewVarC k q))
        = VarSwap_in_proc k (pr_subst n p (NewVarC k (NewVarC k q)))) as eq1.
      { eapply Hp. simpl. lia. } rewrite eq1. eauto.
    * assert (pr_subst n (VarSwap_in_proc k (g g1)) (NewVarC k (NewVarC k q))
        = VarSwap_in_proc k (pr_subst n (g g1) (NewVarC k (NewVarC k q)))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (pr_subst n (VarSwap_in_proc k (g g2)) (NewVarC k (NewVarC k q))
        = VarSwap_in_proc k (pr_subst n (g g2) (NewVarC k (NewVarC k q)))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

Lemma pr_subst_and_NewVarC q0 q n k : (pr_subst n (NewVarC k q0) (NewVarC k q) = NewVarC k (pr_subst n q0 q)).
Proof.
  revert n k q.
  induction q0 as (q0 & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct q0; intros; simpl in *; repeat rewrite Hp by lia; eauto.
  + destruct (decide(n0 = n)); auto.
  + destruct (decide(n0 = n)); eauto.
  + assert (NewVarC (0 + (S k)) (NewVarC 0 q) = NewVarC 0 (NewVarC ( 0 + k ) q)) as eq1.
    { rewrite NewVarC_and_NewVarC. eauto. }
    simpl in *. rewrite<- eq1.
    now rewrite Hp by lia.
  + destruct g; simpl in *; auto.
    * simpl. rewrite NewVar_and_NewVarC, Hp; auto.
    * now rewrite Hp by lia.
    * assert (pr_subst n (NewVarC k (g g1)) (NewVarC k q) = NewVarC k (pr_subst n (g g1) q)) as eq1.
      { eapply Hp. simpl. lia. }
      assert (pr_subst n (NewVarC k (g g2)) (NewVarC k q) = NewVarC k (pr_subst n (g g2) q)) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

Lemma NewVar_in_ChannelData_inj k c1 c2 :
  NewVar_in_ChannelData k c1 = NewVar_in_ChannelData k c2 -> c1 = c2.
Proof.
  destruct c1, c2; simpl; intros H.
  - exact H.
  - destruct (decide (k < S n)); discriminate.
  - destruct (decide (k < S n)); discriminate.
  - destruct (decide (k < S n)); destruct (decide (k < S n0)); injection H as H; f_equal; lia.
Qed.

Lemma NewVarC_inj p1 p2 k : NewVarC k p1 = NewVarC k p2 -> p1 = p2.
Proof.
  revert k p2.
  induction p1 as (p1 & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p1; intros k p2 Heq; destruct p2; simpl in *; try discriminate.
  + injection Heq as Heq1 Heq2.
    f_equal.
    * eapply Hp; [simpl; lia | exact Heq1].
    * eapply Hp; [simpl; lia | exact Heq2].
  + injection Heq as Heq.
    subst.
    reflexivity.
  + injection Heq as Heq.
    f_equal.
    exact Heq.
    eapply Hp; [simpl; lia | exact H].
  + injection Heq as Heq1 Heq2.
    subst.
    f_equal.
    * eapply Hp; [simpl; lia | exact Heq2].
    * eapply Hp; [simpl; lia | exact H].
  + injection Heq as Heq1 Heq2.
    assert (c = c0) as Hc by (eapply NewVar_in_ChannelData_inj; exact Heq1).
    subst. reflexivity.
  + injection Heq as Heq.
    f_equal.
    eapply Hp; [simpl; lia | exact Heq].
  + destruct g, g0; simpl in *; try discriminate.
    * reflexivity.
    * reflexivity.
    * injection Heq as Heq1 Heq2.
      assert (c = c0) as Hc by (eapply NewVar_in_ChannelData_inj; exact Heq1).
      assert (p = p0) as Hpp by (eapply Hp; [simpl; lia | exact Heq2]).
      subst.
      reflexivity.
    * injection Heq as Heq.
      f_equal.
      assert (p = p0) as Hpp by (eapply Hp; [simpl; lia | exact Heq]).
      subst.
      reflexivity.
    * injection Heq as Heq1 Heq2.
      assert (g g1 = g g0_1) as E1 by (eapply Hp; [simpl; lia | simpl; f_equal; exact Heq1]).
      assert (g g2 = g g0_2) as E2 by (eapply Hp; [simpl; lia | simpl; f_equal; exact Heq2]).
      injection E1 as E1.
      injection E2 as E2.
      subst.
      reflexivity.
Qed.

Corollary gNewVarC_inj g1 g2 k : gNewVarC k g1 = gNewVarC k g2 -> g1 = g2.
Proof.
  intro H.
  assert (g g1 = g g2) as E by (apply (NewVarC_inj (g g1) (g g2) k); simpl; f_equal; exact H).
  injection E as E.
  exact E.
Qed.

Lemma gNewVarC_swap_0_S k g0 : gNewVarC (S k) (gNewVarC 0 g0) = gNewVarC 0 (gNewVarC k g0).
Proof.
  pose proof (NewVarC_and_NewVarC 0 k (g g0)) as Heq.
  simpl in Heq. injection Heq as Heq. exact Heq.
Qed.

Definition NewVar_in_ChannelData_down (k : nat) (Y : ChannelData) : ChannelData :=
match Y with
| cst v => cst v
| bvar i => if (decide (k < i)) then bvar (Nat.pred i) else bvar i
end.

Fixpoint NewVarCdown (k : nat) (p : proc) {struct p} : proc :=
match p with
| P ‖ Q => (NewVarCdown k P) ‖ (NewVarCdown k Q)
| pr_var i => pr_var i
| rec x • P =>  rec x • (NewVarCdown k P)
| If C Then P Else Q => If C Then (NewVarCdown k P) Else (NewVarCdown k Q)
| c ! v • 𝟘 => (NewVar_in_ChannelData_down k c) ! v • 𝟘
| ν P => ν (NewVarCdown (S k) P)
| g M => gNewVarCdown k M
end

with gNewVarCdown k M {struct M} : gproc :=
match M with
| ① => ①
| 𝟘 => 𝟘
| c ? • p => (NewVar_in_ChannelData_down k c) ? • (NewVarCdown k p)
| 𝛕 • p => 𝛕 • (NewVarCdown k p)
| p1 + p2 => (gNewVarCdown k p1) + (gNewVarCdown k p2)
end.

Lemma NewVar_in_ChannelData_retract k c : NewVar_in_ChannelData_down k (NewVar_in_ChannelData k c) = c.
Proof.
  destruct c; simpl; auto.
  destruct (decide (k < S n)).
  - simpl. destruct (decide (k < S n)); [f_equal; lia | lia].
  - simpl. destruct (decide (k < n)); [lia | reflexivity].
Qed.

Lemma NewVarC_retract p : forall k, NewVarCdown k (NewVarC k p) = p.
Proof.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros k; simpl.
  + assert (NewVarCdown k (NewVarC k p1) = p1) as H1 by (apply Hp; simpl; lia).
    assert (NewVarCdown k (NewVarC k p2) = p2) as H2 by (apply Hp; simpl; lia).
    rewrite H1, H2. reflexivity.
  + reflexivity.
  + assert (NewVarCdown k (NewVarC k p) = p) as H1 by (apply Hp; simpl; lia).
    rewrite H1. reflexivity.
  + assert (NewVarCdown k (NewVarC k p1) = p1) as H1 by (apply Hp; simpl; lia).
    assert (NewVarCdown k (NewVarC k p2) = p2) as H2 by (apply Hp; simpl; lia).
    rewrite H1, H2. reflexivity.
  + assert (NewVar_in_ChannelData_down k (NewVar_in_ChannelData k c) = c) as Hc by (apply NewVar_in_ChannelData_retract).
    rewrite Hc. reflexivity.
  + assert (NewVarCdown (S k) (NewVarC (S k) p) = p) as H1 by (apply Hp; simpl; lia).
    rewrite H1. reflexivity.
  + destruct g; simpl; try reflexivity.
    * assert (NewVar_in_ChannelData_down k (NewVar_in_ChannelData k c) = c) as Hc by (apply NewVar_in_ChannelData_retract).
      assert (NewVarCdown k (NewVarC k p) = p) as Hpp by (apply Hp; simpl; lia).
      rewrite Hc, Hpp. reflexivity.
    * assert (NewVarCdown k (NewVarC k p) = p) as Hpp by (apply Hp; simpl; lia).
      rewrite Hpp. reflexivity.
    * assert (NewVarCdown k (NewVarC k (g g1)) = g g1) as H1 by (apply Hp; simpl; lia).
      assert (NewVarCdown k (NewVarC k (g g2)) = g g2) as H2 by (apply Hp; simpl; lia).
      simpl in H1, H2. injection H1 as H1. injection H2 as H2.
      rewrite H1, H2. reflexivity.
Qed.

Corollary gNewVarC_retract k g0 : gNewVarCdown k (gNewVarC k g0) = g0.
Proof.
  assert (NewVarCdown k (NewVarC k (g g0)) = g g0) as H by (apply NewVarC_retract).
  simpl in H. injection H as H. exact H.
Qed.

Lemma NewVar_in_ChannelData_and_VarSwap_in_ChannelData_le i k0 c : i <= k0 ->
  VarSwap_in_ChannelData (S k0) (NewVar_in_ChannelData i c) = NewVar_in_ChannelData i (VarSwap_in_ChannelData k0 c).
Proof.
  intro Hle.
  destruct c; simpl; auto.
  destruct (decide (i < S n)).
  - simpl.
    destruct (decide (n = k0)).
    + subst.
      destruct (decide (S k0 = S k0)); try lia.
      simpl.
      destruct (decide (i < S (S k0))); [f_equal; lia | lia].
    + destruct (decide (n = S k0)).
      * subst.
        destruct (decide (S (S k0) = S k0)); try lia.
        destruct (decide (S (S k0) = S (S k0))); try lia.
        simpl.
        destruct (decide (i < S k0)); [f_equal; lia | lia].
      * destruct (decide (S n = S k0)); try lia.
        destruct (decide (S n = S (S k0))); try lia.
        simpl.
        destruct (decide (i < S n)); [f_equal; lia | lia].
  - simpl.
    destruct (decide (n = S k0)); try lia.
    destruct (decide (n = S (S k0))); try lia.
    destruct (decide (n = k0)); try lia.
    simpl.
    destruct (decide (i < S n)); [lia | reflexivity].
Qed.

Lemma NewVarC_and_VarSwap_le p : forall i k0, i <= k0 ->
  VarSwap_in_proc (S k0) (NewVarC i p) = NewVarC i (VarSwap_in_proc k0 p).
Proof.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros i k0 Hle; simpl.
  + assert (VarSwap_in_proc (S k0) (NewVarC i p1) = NewVarC i (VarSwap_in_proc k0 p1)) as eq1.
    { apply Hp; [simpl; lia | lia]. }
    assert (VarSwap_in_proc (S k0) (NewVarC i p2) = NewVarC i (VarSwap_in_proc k0 p2)) as eq2.
    { apply Hp; [simpl; lia | lia]. }
    rewrite eq1, eq2. reflexivity.
  + reflexivity.
  + assert (VarSwap_in_proc (S k0) (NewVarC i p) = NewVarC i (VarSwap_in_proc k0 p)) as eq.
    { apply Hp; [simpl; lia | lia]. }
    rewrite eq. reflexivity.
  + assert (VarSwap_in_proc (S k0) (NewVarC i p1) = NewVarC i (VarSwap_in_proc k0 p1)) as eq1.
    { apply Hp; [simpl; lia | lia]. }
    assert (VarSwap_in_proc (S k0) (NewVarC i p2) = NewVarC i (VarSwap_in_proc k0 p2)) as eq2.
    { apply Hp; [simpl; lia | lia]. }
    rewrite eq1, eq2. reflexivity.
  + rewrite NewVar_in_ChannelData_and_VarSwap_in_ChannelData_le; auto.
  + assert (VarSwap_in_proc (S (S k0)) (NewVarC (S i) p) = NewVarC (S i) (VarSwap_in_proc (S k0) p)) as eq.
    { apply Hp; [simpl; lia | lia]. }
    rewrite eq. reflexivity.
  + destruct g; simpl.
    * reflexivity.
    * reflexivity.
    * rewrite NewVar_in_ChannelData_and_VarSwap_in_ChannelData_le; auto.
      assert (VarSwap_in_proc (S k0) (NewVarC i p) = NewVarC i (VarSwap_in_proc k0 p)) as eq.
      { apply Hp; [simpl; lia | lia]. }
      rewrite eq. reflexivity.
    * assert (VarSwap_in_proc (S k0) (NewVarC i p) = NewVarC i (VarSwap_in_proc k0 p)) as eq.
      { apply Hp; [simpl; lia | lia]. }
      rewrite eq. reflexivity.
    * assert (VarSwap_in_proc (S k0) (NewVarC i (g g1)) = NewVarC i (VarSwap_in_proc k0 (g g1))) as eq1.
      { apply Hp; [simpl; lia | lia]. } inversion eq1.
      assert (VarSwap_in_proc (S k0) (NewVarC i (g g2)) = NewVarC i (VarSwap_in_proc k0 (g g2))) as eq2.
      { apply Hp; [simpl; lia | lia]. } inversion eq2.
      rewrite H0, H1. reflexivity.
Qed.

Corollary gVarSwap_and_gNewVarC0 k0 g1 :
  gVarSwap_in_proc (S k0) (gNewVarC 0 g1) = gNewVarC 0 (gVarSwap_in_proc k0 g1).
Proof.
  assert (VarSwap_in_proc (S k0) (NewVarC 0 (g g1)) = NewVarC 0 (VarSwap_in_proc k0 (g g1))) as H.
  { apply NewVarC_and_VarSwap_le. lia. }
  simpl in H. injection H as H. exact H.
Qed.

Lemma VarSwap_in_ChannelData_disjoint j k0 c :
  VarSwap_in_ChannelData j (VarSwap_in_ChannelData (S (S (j+k0))) c) = VarSwap_in_ChannelData (S (S (j+k0))) (VarSwap_in_ChannelData j c).
Proof.
destruct c; simpl; auto.
repeat match goal with
| |- context[decide (?a = ?b)] => destruct (decide (a = b))
end; try lia; try reflexivity.
all: simpl; repeat match goal with
| |- context[decide (?a = ?b)] => destruct (decide (a = b))
end; try lia; try reflexivity.
Qed.

Lemma VarSwap_and_VarSwap_disjoint p : forall j k0,
  VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p).
Proof.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros j k0; simpl.
  + assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p1) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p1)) as eq1.
    { apply Hp. simpl. lia. }
    assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p2) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p2)) as eq2.
    { apply Hp. simpl. lia. }
    rewrite eq1, eq2. reflexivity.
  + reflexivity.
  + assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p)) as eq.
    { apply Hp. simpl. lia. }
    rewrite eq. reflexivity.
  + assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p1) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p1)) as eq1.
    { apply Hp. simpl. lia. }
    assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p2) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p2)) as eq2.
    { apply Hp. simpl. lia. }
    rewrite eq1, eq2. reflexivity.
  + rewrite VarSwap_in_ChannelData_disjoint. reflexivity.
  + assert (S (S (S (j + k0))) = S (S (S j + k0))) as eq' by lia. rewrite eq'.
    assert (VarSwap_in_proc (S j) (VarSwap_in_proc (S (S (S j+k0))) p) = VarSwap_in_proc (S (S (S j+k0))) (VarSwap_in_proc (S j) p)) as eq.
    { apply Hp. simpl. lia. }
    rewrite eq. reflexivity.
  + destruct g; simpl.
    * reflexivity.
    * reflexivity.
    * rewrite VarSwap_in_ChannelData_disjoint.
      assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p)) as eq.
      { apply Hp. simpl. lia. }
      rewrite eq. reflexivity.
    * assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) p) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j p)) as eq.
      { apply Hp. simpl. lia. }
      rewrite eq. reflexivity.
    * assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) (g g1)) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j (g g1))) as eq1.
      { apply Hp. simpl. lia. } inversion eq1.
      assert (VarSwap_in_proc j (VarSwap_in_proc (S (S (j+k0))) (g g2)) = VarSwap_in_proc (S (S (j+k0))) (VarSwap_in_proc j (g g2))) as eq2.
      { apply Hp. simpl. lia. } inversion eq2.
      rewrite H0, H1. reflexivity.
Qed.

Lemma VarSwap_in_ChannelData_invol k0 c : VarSwap_in_ChannelData k0 (VarSwap_in_ChannelData k0 c) = c.
Proof.
destruct c; simpl; auto.
destruct (decide (n = k0)).
- subst. simpl. destruct (decide (S k0 = k0)); try lia.
  destruct (decide (S k0 = S k0)); try lia. reflexivity.
- destruct (decide (n = S k0)).
  + subst. simpl. destruct (decide (k0 = k0)); try lia. reflexivity.
  + simpl. destruct (decide (n = k0)); try lia. destruct (decide (n = S k0)); try lia. reflexivity.
Qed.

Lemma VarSwap_in_proc_invol k0 p : VarSwap_in_proc k0 (VarSwap_in_proc k0 p) = p.
Proof.
revert k0.
induction p as (p & Hp) using
  (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros k0; simpl.
+ assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p1) = p1) as H1 by (apply Hp; simpl; lia).
  assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p2) = p2) as H2 by (apply Hp; simpl; lia).
  rewrite H1, H2. reflexivity.
+ reflexivity.
+ assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p) = p) as H1 by (apply Hp; simpl; lia).
  rewrite H1. reflexivity.
+ assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p1) = p1) as H1 by (apply Hp; simpl; lia).
  assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p2) = p2) as H2 by (apply Hp; simpl; lia).
  rewrite H1, H2. reflexivity.
+ rewrite VarSwap_in_ChannelData_invol. reflexivity.
+ assert (VarSwap_in_proc (S k0) (VarSwap_in_proc (S k0) p) = p) as H1 by (apply Hp; simpl; lia).
  rewrite H1. reflexivity.
+ destruct g; simpl; try reflexivity.
  * rewrite VarSwap_in_ChannelData_invol.
    assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p) = p) as Hpp by (apply Hp; simpl; lia).
    rewrite Hpp. reflexivity.
  * assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 p) = p) as Hpp by (apply Hp; simpl; lia).
    rewrite Hpp. reflexivity.
  * assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 (g g1)) = g g1) as H1 by (apply Hp; simpl; lia).
    assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 (g g2)) = g g2) as H2 by (apply Hp; simpl; lia).
    simpl in H1, H2. injection H1 as H1. injection H2 as H2.
    rewrite H1, H2. reflexivity.
Qed.

Corollary gVarSwap_in_proc_invol k0 g1 : gVarSwap_in_proc k0 (gVarSwap_in_proc k0 g1) = g1.
Proof.
assert (VarSwap_in_proc k0 (VarSwap_in_proc k0 (g g1)) = g g1) as H by (apply VarSwap_in_proc_invol).
simpl in H. injection H as H. exact H.
Qed.

Lemma NewVar_in_ChannelData_down_and_VarSwap_in_ChannelData j k0 c :
NewVar_in_ChannelData_down (S (S (j + k0))) (VarSwap_in_ChannelData k0 c)
        = VarSwap_in_ChannelData k0 (NewVar_in_ChannelData_down (S (S (j + k0))) c).
Proof.
  destruct c.
  + simpl. reflexivity.
  + simpl. destruct (decide (n = k0)).
    - subst. simpl. destruct (decide (S (S (j+k0)) < k0)); try lia.
      rewrite decide_False; try lia. simpl.
      destruct (decide (k0 = k0)); try lia. reflexivity.
    - simpl. destruct (decide (n = S k0)); subst.
      * simpl. destruct (decide (S (S (j+k0)) < S k0)); try lia.
        rewrite decide_False; try lia. simpl.
        destruct (decide (S k0 = k0)); try lia.
        destruct (decide (S k0 = S k0)); try lia. reflexivity.
      * destruct (decide (S (S (j+k0)) < n)).
        ++ simpl. rewrite decide_True; try lia.
           destruct (decide (Nat.pred n = k0)); try lia.
           destruct (decide (Nat.pred n = S k0)); try lia.
           reflexivity.
        ++ simpl. destruct (decide (n = k0)); try lia.
           destruct (decide (n = S k0)); try lia.
           rewrite decide_False; try lia. reflexivity.
Qed.

Lemma NewVarCdown_and_VarSwap j k0 p : (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p)).
Proof.
  revert j k0.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + reflexivity.
  + assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p1) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p2) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + rewrite NewVar_in_ChannelData_down_and_VarSwap_in_ChannelData. eauto.
  + assert (S (S (S (j + k0))) = S (S (j + (S k0)))) as eq' by lia. rewrite eq'.
    assert (NewVarCdown (S (S (j + (S k0)))) (VarSwap_in_proc (S k0) p)
        = VarSwap_in_proc (S k0) (NewVarCdown (S (S (j + (S k0)))) p)) as eq.
    { eapply Hp. simpl. lia. }
    rewrite eq. eauto.
  + destruct g; simpl in *.
    * reflexivity.
    * reflexivity.
    * assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p)) as eq1.
      { eapply Hp. simpl. lia. } rewrite eq1.
      rewrite NewVar_in_ChannelData_down_and_VarSwap_in_ChannelData. eauto.
    * assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 p) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) p)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 (g g1)) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) (g g1))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (NewVarCdown (S (S (j + k0))) (VarSwap_in_proc k0 (g g2)) = VarSwap_in_proc k0 (NewVarCdown (S (S (j + k0))) (g g2))) as eq2.
      { eapply Hp. simpl. lia. } simpl in *. inversion eq1. inversion eq2.
      rewrite H0, H1. eauto.
Qed.

Lemma NewVar_in_ChannelData_up_down i j c :
  NewVar_in_ChannelData_down (i + S j) (NewVar_in_ChannelData i c) = NewVar_in_ChannelData i (NewVar_in_ChannelData_down (i+j) c).
Proof.
  destruct c.
  simpl.
  + eauto.
  + simpl.
    destruct (decide (i < S n)).
    - simpl.
      destruct (decide (i + j < n)).
      * rewrite decide_True; try lia.
        simpl.
        rewrite decide_True; try lia.
        f_equal; lia.
      * rewrite decide_False; try lia.
        simpl.
        rewrite decide_True; try lia.
        eauto.
    - simpl.
      rewrite decide_False; try lia.
      destruct (decide (i + j < n)); try lia.
      simpl.
      destruct (decide (i < S n)); [lia | reflexivity].
Qed.

Lemma NewVarC_up_down i j p : NewVarCdown (i + S j) (NewVarC i p) = NewVarC i (NewVarCdown (i+j) p).
Proof.
  revert i j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (NewVarCdown (i + S j) (NewVarC i p1) = NewVarC i (NewVarCdown (i+j) p1)) as eq1.
    { eapply Hp. simpl. lia. } rewrite eq1.
    assert (NewVarCdown (i + S j) (NewVarC i p2) = NewVarC i (NewVarCdown (i+j) p2)) as eq2.
    { eapply Hp. simpl. lia. } rewrite eq2. eauto.
  + eauto.
  + assert (NewVarCdown (i + S j) (NewVarC i p) = NewVarC i (NewVarCdown (i+j) p)) as eq.
    { eapply Hp. simpl. eauto. } rewrite eq. eauto.
  + assert (NewVarCdown (i + S j) (NewVarC i p1) = NewVarC i (NewVarCdown (i+j) p1)) as eq1.
    { eapply Hp. simpl. lia. } rewrite eq1.
    assert (NewVarCdown (i + S j) (NewVarC i p2) = NewVarC i (NewVarCdown (i+j) p2)) as eq2.
    { eapply Hp. simpl. lia. } rewrite eq2. eauto.
  + rewrite NewVar_in_ChannelData_up_down. eauto.
  + assert (NewVarCdown (S (i + S j)) (NewVarC (S i) p) = NewVarC (S i) (NewVarCdown (S (i+j)) p)) as eq.
    { replace ((S (i + S j))) with ((S i) + S j)%nat; try lia.
      replace (S (i + j)) with ((S i) + j)%nat; try lia. eapply Hp.
      simpl. lia. } rewrite eq. eauto.
  + destruct g; simpl.
    * eauto.
    * eauto.
    * rewrite NewVar_in_ChannelData_up_down.
      assert (NewVarCdown (i + S j) (NewVarC i p) = NewVarC i (NewVarCdown (i+j) p)) as eq.
      { eapply Hp. simpl. eauto. } rewrite eq. eauto.
    * assert (NewVarCdown (i + S j) (NewVarC i p) = NewVarC i (NewVarCdown (i+j) p)) as eq.
      { eapply Hp. simpl. eauto. } rewrite eq. eauto.
    * assert (NewVarCdown (i + S j) (NewVarC i (g g1)) = NewVarC i (NewVarCdown (i+j) (g g1))) as eq1.
      { eapply Hp. simpl. lia. } inversion eq1.
      assert (NewVarCdown (i + S j) (NewVarC i (g g2)) = NewVarC i (NewVarCdown (i+j) (g g2))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq2. eauto.
Qed.

Lemma NewVar_in_ChannelData_double_fixed k c :
  VarSwap_in_ChannelData k (NewVar_in_ChannelData k (NewVar_in_ChannelData k c)) = NewVar_in_ChannelData k (NewVar_in_ChannelData k c).
Proof.
destruct c; simpl; auto.
destruct (decide (k < S n)).
- simpl. destruct (decide (k < S (S n))).
  + simpl. destruct (decide (S (S n) = k)); try lia.
    destruct (decide (S (S n) = S k)); try lia. reflexivity.
  + lia.
- simpl. destruct (decide (k < S n)); try lia.
  destruct (decide (n = k)); try lia.
  destruct (decide (n = S k)); try lia.
  simpl. destruct (decide (n = k)); try lia.
  destruct (decide (n = S k)); try lia. reflexivity.
Qed.

Lemma VarSwap_fixes_NewVarC_double p : forall k,
  VarSwap_in_proc k (NewVarC k (NewVarC k p)) = NewVarC k (NewVarC k p).
Proof.
induction p as (p & Hp) using
  (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros k; simpl.
+ assert (VarSwap_in_proc k (NewVarC k (NewVarC k p1)) = NewVarC k (NewVarC k p1)) as H1 by (apply Hp; simpl; lia).
  assert (VarSwap_in_proc k (NewVarC k (NewVarC k p2)) = NewVarC k (NewVarC k p2)) as H2 by (apply Hp; simpl; lia).
  rewrite H1, H2. reflexivity.
+ reflexivity.
+ assert (VarSwap_in_proc k (NewVarC k (NewVarC k p)) = NewVarC k (NewVarC k p)) as H1 by (apply Hp; simpl; lia).
  rewrite H1. reflexivity.
+ assert (VarSwap_in_proc k (NewVarC k (NewVarC k p1)) = NewVarC k (NewVarC k p1)) as H1 by (apply Hp; simpl; lia).
  assert (VarSwap_in_proc k (NewVarC k (NewVarC k p2)) = NewVarC k (NewVarC k p2)) as H2 by (apply Hp; simpl; lia).
  rewrite H1, H2. reflexivity.
+ rewrite NewVar_in_ChannelData_double_fixed. reflexivity.
+ assert (VarSwap_in_proc (S k) (NewVarC (S k) (NewVarC (S k) p)) = NewVarC (S k) (NewVarC (S k) p)) as H1 by (apply Hp; simpl; lia).
  rewrite H1. reflexivity.
+ destruct g; simpl; try reflexivity.
  * rewrite NewVar_in_ChannelData_double_fixed.
    assert (VarSwap_in_proc k (NewVarC k (NewVarC k p)) = NewVarC k (NewVarC k p)) as Hpp by (apply Hp; simpl; lia).
    rewrite Hpp. reflexivity.
  * assert (VarSwap_in_proc k (NewVarC k (NewVarC k p)) = NewVarC k (NewVarC k p)) as Hpp by (apply Hp; simpl; lia).
    rewrite Hpp. reflexivity.
  * assert (VarSwap_in_proc k (NewVarC k (NewVarC k (g g1))) = NewVarC k (NewVarC k (g g1))) as H1 by (apply Hp; simpl; lia).
    assert (VarSwap_in_proc k (NewVarC k (NewVarC k (g g2))) = NewVarC k (NewVarC k (g g2))) as H2 by (apply Hp; simpl; lia).
    simpl in H1, H2. injection H1 as H1. injection H2 as H2.
    rewrite H1, H2. reflexivity.
Qed.

Lemma gVarSwap_NewVar_NewVar g0 :
  gVarSwap_in_proc 0 (⇑ (⇑ g0)) = ⇑ (⇑ g0).
Proof.
assert (VarSwap_in_proc 0 (NewVarC 0 (NewVarC 0 (g g0))) = NewVarC 0 (NewVarC 0 (g g0))) as H by (apply VarSwap_fixes_NewVarC_double).
simpl in H. injection H as H. exact H.
Qed.

Lemma subst_equation d E v x : Eval_Eq (S d) E = Some x -> Eval_Eq d (subst_in_Equation d v E) = Some x.
Proof.
  intros H. destruct E as [v0 v1]. destruct v0 as [t|n]; destruct v1 as [t'|n0];
    simpl in *; eauto; try discriminate.
  - destruct (decide (S d <= n0)) as [Hn|Hn]; [| discriminate].
    injection H as Hx. subst x.
    rewrite decide_False by lia.
    rewrite decide_False by lia.
    simpl.
    rewrite decide_True by lia.
    reflexivity.
  - destruct (decide (S d <= n)) as [Hn|Hn]; [| discriminate].
    injection H as Hx. subst x.
    rewrite decide_False by lia.
    rewrite decide_False by lia.
    simpl.
    rewrite decide_True by lia.
    reflexivity.
  - destruct (decide (n = n0)) as [->|Hneq].
    + injection H as Hx. subst x.
      destruct (decide (n0 = d)) as [->|Hnd].
      * destruct v as [c|i]; simpl; rewrite decide_True; reflexivity.
      * destruct (decide (n0 < d)) as [Hlt|Hlt]; simpl; rewrite decide_True; reflexivity.
    + destruct (decide (S d <= n)) as [Hn|Hn]; [| discriminate].
      destruct (decide (S d <= n0)) as [Hn0|Hn0]; [| discriminate].
      injection H as Hx. subst x.
      rewrite decide_False by lia.
      rewrite decide_False by lia.
      simpl.
      rewrite decide_False by lia.
      rewrite decide_False by lia.
      simpl.
      destruct (decide (Nat.pred n = Nat.pred n0)); [lia|].
      rewrite decide_True by lia.
      rewrite decide_True by lia.
      reflexivity.
Qed.

Lemma NewVar_equation n E k x : k <= n -> Eval_Eq n E = Some x -> Eval_Eq (S n) (NewVar_in_Equation k E) = Some x.
Proof.
  intros Hkn H. destruct E as [v0 v1]. destruct v0 as [t|i]; destruct v1 as [t'|i'];
    simpl in *; eauto; try discriminate.
  - destruct (decide (n <= i')) as [Hi|Hi]; [| discriminate].
    injection H as Hx. subst x.
    rewrite decide_True by lia.
    simpl.
    rewrite decide_True by lia.
    reflexivity.
  - destruct (decide (n <= i)) as [Hi|Hi]; [| discriminate].
    injection H as Hx. subst x.
    rewrite decide_True by lia.
    simpl.
    rewrite decide_True by lia.
    reflexivity.
  - destruct (decide (i = i')) as [->|Hneq].
    + injection H as Hx. subst x.
      destruct (decide (k < S i')) as [Hlt|Hlt]; simpl; rewrite decide_True by reflexivity; reflexivity.
    + destruct (decide (n <= i)) as [Hi|Hi]; [| discriminate].
      destruct (decide (n <= i')) as [Hi'|Hi']; [| discriminate].
      injection H as Hx. subst x.
      rewrite decide_True by lia.
      rewrite decide_True by lia.
      simpl.
      destruct (decide (S i = S i')); [lia|].
      rewrite decide_True by lia.
      rewrite decide_True by lia.
      reflexivity.
Qed.

Fixpoint Ѵ (n : nat) (P : proc) : proc :=
match n with 
| 0 => P
| S n => ν (Ѵ  n P)
end.

Fixpoint NewVarCn (k : nat) (n : nat) (P : proc) : proc :=
match n with 
| 0 => P
| S n => NewVarC k (NewVarCn k n P)
end.

Fixpoint gNewVarCn (k : nat) (n : nat) (P : gproc) : gproc :=
match n with 
| 0 => P
| S n => gNewVarC k (gNewVarCn k n P)
end.

Lemma NewVarCn_revert_def n P k: NewVarCn k n (NewVarC k P) = NewVarC k (NewVarCn k n P).
Proof.
  revert P. induction n.
  - reflexivity.
  - intros; simpl in *. f_equal. eauto.
Qed.

Lemma VarC_add_zero c : VarC_add 0 c = c.
Proof.
  destruct c ; simpl ; eauto.
Qed.

Lemma VarC_add_revert_def k n c : VarC_add (k + n) c = (VarC_add k (VarC_add n c)).
Proof.
  revert n c. induction k; intros; simpl.
  + destruct c; simpl; eauto.
  + destruct c; simpl; eauto. f_equal. lia.
Qed.

Lemma VarC_add_zero_ext μ : VarC_action_add 0 μ = μ.
Proof.
  destruct μ; destruct a; destruct c; simpl; eauto.
Qed.

Lemma NewVarCzero_and_add_Channel c : VarC_add 1 c = NewVar_in_ChannelData 0 c.
Proof.
  destruct c; simpl ;eauto.
Qed.

Definition NewVarC_in_ext (k : nat) (μ : ExtAct TypeOfActions) : ExtAct TypeOfActions :=
match μ with
| ActIn (c , v) => ActIn (NewVar_in_ChannelData k c , v)
| ActOut (c , v) => ActOut (NewVar_in_ChannelData k c , v)
end.

Lemma NewVarCzero_and_add μ : VarC_action_add 1 μ = NewVarC_in_ext 0 μ.
Proof.
  destruct μ; destruct a; simpl; rewrite NewVarCzero_and_add_Channel; eauto.
Qed.

Lemma NewVarC_and_NewVarC_in_ChannelData k j μ :
      NewVarC_in_ext j (NewVarC_in_ext (j + k) μ) = NewVarC_in_ext (j + (S k)) (NewVarC_in_ext j μ).
Proof.
  destruct μ; destruct a; simpl; rewrite NewVar_in_ChannelData_and_NewVar_in_ChannelData; eauto.
Qed.

Lemma VarCadd_and_NewVarCn n c v : VarC_add n c ! v • 𝟘 = NewVarCn 0 n (c ! v • 𝟘).
Proof.
  revert c v.
  induction n.
  + destruct c; simpl;  eauto.
  + intros. replace (S n)%nat with (n + 1)%nat by lia.
    rewrite VarC_add_revert_def.
    rewrite (IHn (VarC_add 1 c) v). symmetry. etrans.
    replace (n + 1)%nat with (S n)%nat by lia. simpl in *.
    rewrite<- NewVarCn_revert_def. simpl. reflexivity.
    destruct c; eauto.
Qed.

Lemma VarC_action_add_Swap k μ : 
      (VarC_action_add 1 (VarSwap_in_ext k μ) = VarSwap_in_ext (S k) (VarC_action_add 1 μ)).
Proof.
  destruct μ; destruct a; destruct c; simpl in *.
  + eauto.
  + destruct (decide (n = k)).
    - subst. rewrite decide_True; eauto.
    - destruct (decide (n = S k)); subst.
      ++ rewrite decide_False; eauto.
         rewrite decide_True; eauto.
      ++ rewrite decide_False; eauto.
         rewrite decide_False; eauto.
  + eauto.
  + destruct (decide (n = k)).
    - subst. rewrite decide_True; eauto.
    - destruct (decide (n = S k)); subst.
      ++ rewrite decide_False; eauto.
         rewrite decide_True; eauto.
      ++ rewrite decide_False; eauto.
         rewrite decide_False; eauto.
Qed.

Lemma VarSwap_com_VarC_in_ChannelData k j c : (NewVar_in_ChannelData j (VarSwap_in_ChannelData (j + k) c) 
          = VarSwap_in_ChannelData (j + S k) (NewVar_in_ChannelData j c)).
Proof.
  destruct c; simpl.
  + eauto.
  + destruct (decide (n = (j + k)%nat)); subst.
    - rewrite decide_True; try lia. simpl.
      rewrite decide_True; try lia.
      rewrite decide_True; try lia. eauto.
    - destruct (decide (n = S (j + k))); subst.
      * simpl. rewrite decide_True; try lia.
        rewrite decide_True; try lia. simpl.
        rewrite decide_False; try lia.
        rewrite decide_True; try lia. eauto.
      * simpl. destruct (decide (j < S n)); subst.
        ++ simpl. rewrite decide_False; try lia.
           rewrite decide_False; try lia. eauto.
        ++ simpl. rewrite decide_False; try lia.
           rewrite decide_False; try lia. eauto.
Qed.

Lemma VarSwap_com_VarC k j p : (NewVarC j (VarSwap_in_proc (j + k) p) = VarSwap_in_proc (j + S k) (NewVarC j p)).
Proof.
  revert k j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (NewVarC j (VarSwap_in_proc (j + k) p1) = VarSwap_in_proc (j + S k) (NewVarC j p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarC j (VarSwap_in_proc (j + k) p2) = VarSwap_in_proc (j + S k) (NewVarC j p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + eauto.
  + f_equal. eapply Hp. lia.
  + assert (NewVarC j (VarSwap_in_proc (j + k) p1) = VarSwap_in_proc (j + S k) (NewVarC j p1)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (NewVarC j (VarSwap_in_proc (j + k) p2) = VarSwap_in_proc (j + S k) (NewVarC j p2)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + rewrite VarSwap_com_VarC_in_ChannelData. eauto.
  + f_equal. replace (S (j + k))%nat with ((S j) + k)%nat by lia.
    replace (S (j + S k))%nat with ((S j) + S k)%nat by lia.
    eapply Hp. lia.
  + destruct g; simpl in *.
    - eauto.
    - eauto.
    - rewrite VarSwap_com_VarC_in_ChannelData.
      assert (NewVarC j (VarSwap_in_proc (j + k) p) = VarSwap_in_proc (j + S k) (NewVarC j p)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    - assert (NewVarC j (VarSwap_in_proc (j + k) p) = VarSwap_in_proc (j + S k) (NewVarC j p)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    - assert (NewVarC j (VarSwap_in_proc (j + k) (g g1)) = VarSwap_in_proc (j + S k) (NewVarC j (g g1))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (NewVarC j (VarSwap_in_proc (j + k) (g g2)) = VarSwap_in_proc (j + S k) (NewVarC j (g g2))) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

Lemma pr_subst_and_VarSwap2  (n : nat) (p : proc) (k : nat) (q : proc) : 
    pr_subst n (VarSwap_in_proc k p) (VarSwap_in_proc k q) =
    VarSwap_in_proc k (pr_subst n p q).
Proof.
  revert n k q.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (pr_subst n (VarSwap_in_proc k p1) (VarSwap_in_proc k q) = VarSwap_in_proc k (pr_subst n p1 q)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (pr_subst n (VarSwap_in_proc k p2) (VarSwap_in_proc k q) = VarSwap_in_proc k (pr_subst n p2 q)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + destruct (decide (n0 = n)); simpl ; eauto.
  + destruct (decide (n0 = n)); simpl.
    - eauto.
    - assert (pr_subst n0 (VarSwap_in_proc k p) (VarSwap_in_proc k q) = VarSwap_in_proc k (pr_subst n0 p q)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
  + assert (pr_subst n (VarSwap_in_proc k p1) (VarSwap_in_proc k q) = VarSwap_in_proc k (pr_subst n p1 q)) as eq1.
    { eapply Hp. simpl. lia. }
    assert (pr_subst n (VarSwap_in_proc k p2) (VarSwap_in_proc k q) = VarSwap_in_proc k (pr_subst n p2 q)) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + eauto.
  + f_equal. replace k with (0 + k)%nat by lia. rewrite VarSwap_com_VarC.
    simpl in *. eapply Hp. eauto.
  + destruct g; simpl in *.
    * eauto.
    * eauto.
    * rewrite NewVar_and_VarSwap.
      assert (pr_subst n (VarSwap_in_proc k p) (VarSwap_in_proc k (NewVar 0 q))
          = VarSwap_in_proc k (pr_subst n p (NewVar 0 q))) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (pr_subst n (VarSwap_in_proc k p) (VarSwap_in_proc k q)
          = VarSwap_in_proc k (pr_subst n p q)) as eq.
      { eapply Hp. simpl. lia. }
      rewrite eq. eauto.
    * assert (pr_subst n (VarSwap_in_proc k (g g1)) (VarSwap_in_proc k q) 
                  = VarSwap_in_proc k (pr_subst n (g g1) q)) as eq1.
      { eapply Hp. simpl. lia. }
      assert (pr_subst n (VarSwap_in_proc k (g g2)) (VarSwap_in_proc k q) 
                  = VarSwap_in_proc k (pr_subst n (g g2) q)) as eq2.
      { eapply Hp. simpl. lia. } inversion eq1. inversion eq2. eauto.
Qed.

Lemma NewVarC_in_ext_inv μ μ' k : NewVarC_in_ext k μ = NewVarC_in_ext k μ' -> μ = μ'.
Proof.
  destruct μ; destruct μ'; destruct a; destruct a0; simpl in *; intro Hyp; inversion Hyp; subst;
  eapply NewVar_in_ChannelData_inj in H0 ; subst; eauto.
Qed.

Lemma NewVarC_res i k p : NewVarC i (Ѵ k p) = Ѵ k (NewVarC (i + k) p).
Proof.
  revert i p. induction k.
  + intros; simpl; eauto. replace (i + 0)%nat with i by lia. eauto.
  + intros; simpl. f_equal. rewrite IHk. f_equal. replace (S i + k)%nat with (i + S k)%nat by lia. eauto.
Qed.

Lemma NewVarCn_res i j k p : NewVarCn i j (Ѵ k p) = Ѵ k (NewVarCn (i + k) j p).
Proof.
  revert i k p. induction j.
  + intros; simpl; eauto.
  + intros; simpl. rewrite<- NewVarCn_revert_def. rewrite<- NewVarCn_revert_def.
    rewrite<- (IHj i k (NewVarC (i + k) p)). f_equal. rewrite NewVarC_res. eauto.
Qed.

Lemma NewVarCn_par i j p q: NewVarCn i j (p ‖ q) = (NewVarCn i j p) ‖ (NewVarCn i j q).
Proof.
  revert i p q. induction j.
  + intros; simpl; eauto.
  + intros; simpl. rewrite<- NewVarCn_revert_def. simpl. rewrite<- NewVarCn_revert_def.
    rewrite<- NewVarCn_revert_def. rewrite IHj. eauto. 
Qed.

Lemma NewVarCn_input k j c p : gNewVarCn 0 j ((VarC_add k c) ? • p) = (VarC_add (j + k) c) ? • (NewVarCn 0 j p).
Proof.
  revert k c p. induction j.
  + intros; simpl; eauto.
  + intros; simpl. rewrite<- NewVarCn_revert_def. rewrite IHj. simpl. rewrite<- NewVarCn_revert_def.
    rewrite<- NewVarCzero_and_add_Channel. rewrite<- VarC_add_revert_def. simpl. eauto.
Qed.

Lemma subst_and_NewVarCn k i j v q :
    subst_in_proc k v (NewVarCn i j q) = NewVarCn i j (subst_in_proc k v q).
Proof.
  revert v q k i. induction j.
  + intros; simpl; eauto.
  + intros; simpl. rewrite subst_and_NewVarC. f_equal.
    eapply IHj.
Qed.

Lemma simpl_NewVar_auto k j c : (NewVar_in_ChannelData k (VarC_add (k + j) c)) = (VarC_add (k + S j) c).
Proof.
  destruct c.
  + simpl. eauto.
  + simpl. rewrite decide_True; try lia. replace (k + S j)%nat with (S (k + j))%nat by lia.
    replace (S (k + j) + n)%nat with (S (k + j + n))%nat by lia. eauto.
Qed.

Lemma NewVarCn_output k j c d : (NewVarCn k j (VarC_add k c ! d • 𝟘) = (VarC_add (j + k) c) ! d • 𝟘).
Proof.
  revert k c d. induction j.
  + intros; simpl; eauto.
  + intros; simpl. rewrite IHj. simpl. 
    assert (j+k = k + j)%nat as eq by lia. rewrite eq at 1. rewrite simpl_NewVar_auto.
    replace (k + S j)%nat with (S (j + k))%nat by lia. f_equal.
Qed.

Lemma NewVarCn_choice i j g1 g2: NewVarCn i j (g (g1 + g2)) = (gNewVarCn i j g1) + (gNewVarCn i j g2).
Proof.
  revert i g1 g2. induction j.
  + intros; simpl; eauto.
  + intros; simpl. rewrite IHj. simpl. eauto.
Qed.

Lemma simpl_NewVarCn_plus_par k j c p g1 q : (NewVarCn k j ((gpr_input (VarC_add k c) p + g1) ‖ q)
        = ((gpr_input (VarC_add (k + j) c) (NewVarCn k j p)) + (gNewVarCn k j g1)) ‖ (NewVarCn k j q)).
Proof.
  revert k c p g1 q. induction j.
  + intros ; simpl; eauto. replace (k + 0)%nat with k by lia. eauto.
  + intros; simpl. rewrite IHj. simpl. f_equal. rewrite simpl_NewVar_auto. eauto.
Qed.

Lemma simpl_NewVarCn_par_plus k j c v q : NewVarCn 0 k ((VarC_add j c ! v • 𝟘) ‖ q)
        = ((VarC_add (k + j) c ! v • 𝟘 ) ‖ (NewVarCn 0 k q)).
Proof.
  revert j c v q. induction k.
  + intros ; simpl; eauto.
  + intros; simpl. rewrite IHk. simpl. f_equal.
    rewrite<- NewVarCzero_and_add_Channel. rewrite<- VarC_add_revert_def.
    simpl. eauto.
Qed.

Lemma NewVarCn_nil j k : NewVarCn j k 𝟘 = 𝟘.
Proof.
  revert j. induction k; simpl ; eauto. intros; rewrite IHk. simpl;eauto.
Qed.

Lemma simpl_bvar_in_NewVar_ChannelData j c : NewVar_in_ChannelData j (NewVar_in_ChannelData j c) 
        = NewVar_in_ChannelData (S j) (NewVar_in_ChannelData j c).
Proof.
  destruct c.
  + simpl. eauto.
  + simpl. destruct (decide (j < S n)).
    ++ simpl. rewrite decide_True; try lia.
       rewrite decide_True; try lia. eauto.
    ++ simpl. rewrite decide_False; try lia.
       rewrite decide_False; try lia. eauto.
Qed.

Lemma simpl_bvar_in_NewVarC j p : NewVarC j (NewVarC j p) = NewVarC (S j) (NewVarC j p).
Proof.
  revert j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *; repeat rewrite Hp by lia; trivial.
  + rewrite simpl_bvar_in_NewVar_ChannelData. eauto.
  + destruct g; simpl in *.
    - eauto.
    - eauto.
    - rewrite simpl_bvar_in_NewVar_ChannelData.
      assert ((NewVarC j (NewVarC j p)) = (NewVarC (S j) (NewVarC j p))) as eq.
      { eapply Hp. simpl. eauto. }
      rewrite eq. eauto.
    - assert ((NewVarC j (NewVarC j p)) = (NewVarC (S j) (NewVarC j p))) as eq.
      { eapply Hp. simpl. eauto. }
      rewrite eq. eauto.
    - assert (NewVarC j (NewVarC j (g g1)) = NewVarC (S j) (NewVarC j (g g1))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (NewVarC j (NewVarC j (g g2)) = NewVarC (S j) (NewVarC j (g g2))) as eq2.
      { eapply Hp. simpl. lia. }
      inversion eq1. inversion eq2. eauto.
Qed.

Lemma simpl_bvar_in_NewVarCn j k p :(NewVarCn j k (NewVarC j p) = NewVarCn (S j) k (NewVarC j p)).
Proof.
  revert p j.
  induction k.
  - simpl; eauto.
  - intros; simpl. rewrite<- (NewVarCn_revert_def k _ j). rewrite IHk.
    rewrite<- (NewVarCn_revert_def k _ (S j)). f_equal.
    replace (NewVarC j (NewVarCn j k (NewVarC j p))) with (NewVarCn j 1 (NewVarCn j k (NewVarC j p))).
    2 : { eauto. } rewrite simpl_bvar_in_NewVarC. eauto.
Qed.

Definition NewVar_in_label k (μ : ExtAct TypeOfActions) :=
match μ with 
| ActIn (c , d) => ActIn (c , (NewVar_in_Data k d))
| ActOut (c , d) => ActOut (c , (NewVar_in_Data k d))
end.

Fixpoint NewVar_in_trace k s :=
match s with
| [] => []
| a :: l => (NewVar_in_label k a) :: NewVar_in_trace k l
end.

Definition Succ_bvar_for k (X : ValueData) : ValueData :=
match X with
| cst v => cst v
| bvar i => bvar (i + k)
end.

Lemma NewVar_in_Data_zero : forall v, NewVar_in_Data 0 v = Succ_bvar v.
Proof.
intros. induction v; simpl; reflexivity.
Qed.

Lemma subst_NewVar_Data_cancel : forall k X Y,
  subst_Data k X (NewVar_in_Data k Y) = Y.
Proof.
  intros k X [a|i]; simpl; [ reflexivity | ].
  destruct (decide (k < S i)) as [H|H]; simpl.
  - destruct (decide (S i = k)) as [E|E]; [ exfalso; lia | ].
    destruct (decide (S i < k)) as [E2|E2]; [ exfalso; lia | reflexivity ].
  - destruct (decide (i = k)) as [E|E]; [ exfalso; lia | ].
    destruct (decide (i < k)) as [E2|E2]; [ reflexivity | exfalso; lia ].
Qed.

Lemma subst_NewVar_Equation_cancel : forall k X E,
  subst_in_Equation k X (NewVar_in_Equation k E) = E.
Proof. intros k X [D1 D2]; simpl; rewrite !subst_NewVar_Data_cancel; reflexivity. Qed.

Lemma NewVar_subst_cancel : forall p k X, subst_in_proc k X (NewVar k p) = p
with gNewVar_subst_cancel : forall M k X, subst_in_gproc k X (gNewVar k M) = M.
Proof.
  - destruct p; intros k X; simpl.
    + f_equal; apply NewVar_subst_cancel.
    + reflexivity.
    + f_equal; apply NewVar_subst_cancel.
    + f_equal; [ apply subst_NewVar_Equation_cancel | apply NewVar_subst_cancel
               | apply NewVar_subst_cancel ].
    + f_equal; apply subst_NewVar_Data_cancel.
    + f_equal; apply NewVar_subst_cancel.
    + f_equal; apply gNewVar_subst_cancel.
  - destruct M; intros k X; simpl.
    + reflexivity.
    + reflexivity.
    + f_equal; apply NewVar_subst_cancel.
    + f_equal; apply NewVar_subst_cancel.
    + f_equal; apply gNewVar_subst_cancel.
Qed.

Lemma gproc_NewVar_cancel : forall N v, subst_in_gproc 0 v (gNewVar 0 N) = N.
Proof. intros N v. apply gNewVar_subst_cancel. Qed.

Lemma Eval_simpl_true n v : Eval_Eq n (v == v) = Some true <-> v = v.
Proof.
  split.
  - intro e. inversion e. destruct v; rewrite decide_True in H0; eauto.
  - intro e. subst. simpl. destruct v; rewrite decide_True; eauto.
Qed.

Lemma Eval_simpl_false n v1 v2 : v1 ≠ v2 ->  Eval_Eq n (cst v1 == cst v2) = Some false.
Proof.
  - intro e. simpl. rewrite decide_False; eauto.
Qed.

Lemma Eval_simpl_false_gen (v1 v2 : ValueData) : v1 ≠ v2 -> Eval_Eq 0 (v1 == v2) = Some false.
Proof.
  intros neq. destruct v1 as [t1|i1], v2 as [t2|i2]; simpl.
  - destruct (decide (t1 = t2)) as [->|]. contradiction (neq eq_refl). reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (decide (i1 = i2)) as [->|].
    + contradiction (neq eq_refl).
    + reflexivity.
Qed.

Lemma New_Var_And_NewVar_in_Data : forall j i e, NewVar_in_Data (i + S j) (NewVar_in_Data i e) = NewVar_in_Data i (NewVar_in_Data (i + j) e).
Proof.
  intros. revert j. induction e.
  * intros. simpl. reflexivity.
  * intros. simpl. destruct (decide (i < S n)); destruct (decide (i + j < S n)); simpl; auto.
    - destruct (decide (i + S j < S (S n))); destruct ((decide (i < S (S n)))); simpl; auto with arith. exfalso. apply n0. auto with arith.
      exfalso. apply n0. simpl. assert ((i + S j)%nat = S (i + j)%nat). auto with arith. rewrite H. auto with arith.
    - destruct (decide (i + S j < S (S n))); destruct (decide (i < S n)); simpl; auto with arith. exfalso. apply n0. 
      assert ((i + S j)%nat = S (i + j)%nat). auto with arith. rewrite H in l0. auto with arith. exfalso. apply n1. assumption. exfalso. apply n2.
      assumption.
    - exfalso. apply n0. assert (i <= i + j). auto with arith. destruct H. assumption. apply transitivity with (S m). auto with arith. assumption.
    - destruct (decide (i + S j < S n)); destruct (decide (i < S n)); simpl; auto with arith. exfalso. apply n2. eauto with arith.
      exfalso. apply n0. assumption.
Qed.

Lemma New_Var_And_NewVar_in_Trace : forall j i e, NewVar_in_trace (i + S j) (NewVar_in_trace i e) = NewVar_in_trace i (NewVar_in_trace (i + j) e).
Proof.
  intros. revert j. induction e.
  - intros. simpl. reflexivity.
  - intros. simpl. destruct a;destruct a; simpl.
    + rewrite New_Var_And_NewVar_in_Data.
      assert (NewVar_in_trace (i + S j) (NewVar_in_trace i e) 
        = NewVar_in_trace i (NewVar_in_trace (i + j) e)) as eq1.
      { eapply IHe. }
      rewrite eq1. eauto.
    + rewrite New_Var_And_NewVar_in_Data.
      assert (NewVar_in_trace (i + S j) (NewVar_in_trace i e) 
        = NewVar_in_trace i (NewVar_in_trace (i + j) e)) as eq1.
      { eapply IHe. }
      rewrite eq1. eauto.
Qed.

Lemma New_Var_And_NewVar_in_eq : forall j i e, NewVar_in_Equation (i + S j) (NewVar_in_Equation i e) 
                                  = NewVar_in_Equation i (NewVar_in_Equation (i + j) e).
Proof.
intros. induction e.
* simpl. assert (NewVar_in_Data (i + S j) (NewVar_in_Data i a) = NewVar_in_Data i (NewVar_in_Data (i + j) a)). apply New_Var_And_NewVar_in_Data.
  assert (NewVar_in_Data (i + S j) (NewVar_in_Data i a0) = NewVar_in_Data i (NewVar_in_Data (i + j) a0)). apply New_Var_And_NewVar_in_Data.
  rewrite H , H0. auto.
Qed.

Lemma New_Var_And_NewVar : forall j i p, NewVar (i + S j) (NewVar i p) = NewVar i (NewVar (i + j) p).
Proof.
intros. revert j i. induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; simpl; intros.
* assert (NewVar (i + S j) (NewVar i p1) = NewVar i (NewVar (i + j) p1)) as eq1.
  { apply Hp. simpl. auto with arith. }
  assert (NewVar (i + S j) (NewVar i p2) = NewVar i (NewVar (i + j) p2)) as eq2.
  { apply Hp. simpl. auto with arith. }
  rewrite eq1, eq2. auto.
* reflexivity.
* assert (NewVar (i + S j) (NewVar i p) = NewVar i (NewVar (i + j) p)) as eq.
  { apply Hp. simpl. auto with arith. }
  rewrite eq. auto.
* rewrite New_Var_And_NewVar_in_eq.
  assert (NewVar (i + S j) (NewVar i p1) = NewVar i (NewVar (i + j) p1)) as eq2.
  { apply Hp. simpl. auto with arith. }
  assert (NewVar (i + S j) (NewVar i p2) = NewVar i (NewVar (i + j) p2)) as eq3.
  { apply Hp. simpl. auto with arith. }
  rewrite eq2, eq3. auto.
* rewrite New_Var_And_NewVar_in_Data. eauto.
* assert (NewVar (i + S j) (NewVar i p) = NewVar i (NewVar (i + j) p)) as eq.
  { apply Hp. simpl. auto with arith. }
  rewrite eq. auto.
* destruct g; simpl.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. assert (S (i + S j%nat) = ((S i) + (S j))%nat) as eq1 by auto with arith.
    rewrite eq1. assert (S (i + j) = (S i + j)%nat) as eq2 by auto with arith. rewrite eq2.
    assert (NewVar (S i + S j) (NewVar (S i) p) = NewVar (S i) (NewVar (S i + j) p)) as eq.
    { apply Hp. simpl. auto with arith. }
    rewrite eq. auto.
  - simpl. assert (NewVar (i + S j) (NewVar i p) = NewVar i (NewVar (i + j) p)) as eq.
    { apply Hp. simpl. auto with arith. } 
    rewrite eq. eauto.
  - simpl. assert (NewVar (i + S j) (NewVar i (g g1)) = NewVar i (NewVar (i + j) (g g1))) as eq1.
    { apply Hp. simpl. auto with arith. } 
    assert (NewVar (i + S j) (NewVar i (g g2)) = NewVar i (NewVar (i + j) (g g2))) as eq2.
    { apply Hp. simpl. auto with arith. }
    simpl in eq1 , eq2. inversion eq1. inversion eq2. eauto.
Qed.

Lemma size_subst : forall p k X, size (subst_in_proc k X p) = size p.
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros k X.
  destruct p; simpl in *.
  - rewrite (IH p1); [rewrite (IH p2) | ]; simpl; lia.
  - reflexivity.
  - rewrite (IH p); simpl; lia.
  - rewrite (IH p1); [rewrite (IH p2) | ]; simpl; lia.
  - reflexivity.
  - rewrite (IH p); simpl; lia.
  - destruct g as [ | | c p | p | ga gb ]; simpl in *; try reflexivity.
    + rewrite (IH p); simpl; lia.
    + rewrite (IH p); simpl; lia.
    + assert (Heq1: gsize (subst_in_gproc k X ga) = gsize ga) by (apply (IH (g ga)); simpl; lia).
      assert (Heq2: gsize (subst_in_gproc k X gb) = gsize gb) by (apply (IH (g gb)); simpl; lia).
      rewrite Heq1, Heq2. reflexivity.
Qed.

Definition NewVarC_TOA (k : nat) (a : TypeOfActions) : TypeOfActions :=
  match a with (c,v) => (NewVar_in_ChannelData k c, v) end.

Definition NewVar_in_action (k : nat) (μ : ExtAct TypeOfActions) : ExtAct TypeOfActions :=
  match μ with
  | ActIn x  => ActIn (NewVarC_TOA k x)
  | ActOut x => ActOut (NewVarC_TOA k x)
  end.

Definition NewVarC_act (k : nat) (a : ActIO TypeOfActions) : ActIO TypeOfActions :=
  match a with
  | ActExt (ActIn x)  => ActExt (ActIn (NewVarC_TOA k x))
  | ActExt (ActOut x) => ActExt (ActOut (NewVarC_TOA k x))
  | τ => τ
  end.

Lemma NewVarC_act_ext : forall k μ,
  NewVarC_act k (ActExt μ) = ActExt (NewVar_in_action k μ).
Proof. intros k [x|x]; reflexivity. Qed.

(** ****** The two shifts of the development coincide at level [0]. *)
Lemma NewVarC_at_zero : forall c, NewVar_in_ChannelData 0 c = VarC_add 1 c.
Proof.
  intros [a|i]; simpl; [ reflexivity | ].
  destruct (decide (0 < S i)) as [H|H]; [ reflexivity | exfalso; lia ].
Qed.

Lemma NewVarC_shift_comm : forall k c,
  NewVar_in_ChannelData (S k) (VarC_add 1 c) = VarC_add 1 (NewVar_in_ChannelData k c).
Proof.
  intros k [a|i]; simpl; [ reflexivity | ].
  destruct (decide (S k < S (S i))) as [H1|H1]; destruct (decide (k < S i)) as [H2|H2];
    simpl; try reflexivity; exfalso; lia.
Qed.

Lemma NewVar_in_action_at_zero : forall μ, NewVar_in_action 0 μ = VarC_action_add 1 μ.
Proof. intros [[c v]|[c v]]; simpl; f_equal; f_equal; apply NewVarC_at_zero. Qed.

Lemma NewVarC_act_at_zero : forall μ, NewVarC_act 0 (ActExt μ) = ActExt (VarC_action_add 1 μ).
Proof. intros μ. rewrite NewVarC_act_ext. f_equal. apply NewVar_in_action_at_zero. Qed.

Lemma Eval_Eq_0_not_none : forall E, Eval_Eq 0 E <> None.
Proof.
  intros [d1 d2]. destruct d1 as [t|i]; destruct d2 as [t'|i']; simpl.
  - destruct (decide (t=t')); discriminate.
  - destruct (decide (0<=i')); discriminate.
  - destruct (decide (0<=i)); discriminate.
  - destruct (decide (i=i')); [discriminate|].
    destruct (decide (0<=i)); [destruct (decide (0<=i')); discriminate|].
    discriminate.
Qed.

Lemma NewVarCn_g : forall k n M, NewVarCn k n (g M) = g (gNewVarCn k n M).
Proof. intros k n. induction n; intro M; simpl; [ reflexivity | rewrite IHn; reflexivity ]. Qed.

Lemma NewVarCn_msg : forall k n c v,
  NewVarCn k n (c ! v • 𝟘) = (Nat.iter n (NewVar_in_ChannelData k) c) ! v • 𝟘.
Proof. intros k n c v. induction n; simpl; [ reflexivity | rewrite IHn; reflexivity ]. Qed.

Lemma subst_gNewVarC M j k X :
  subst_in_gproc j X (gNewVarC k M) = gNewVarC k (subst_in_gproc j X M).
Proof. pose proof (subst_and_NewVarC j k X (g M)) as h. simpl in h. by injection h. Qed.

Lemma NewVar_in_Data_Succ : forall j X,
  NewVar_in_Data (S j) (Succ_bvar X) = Succ_bvar (NewVar_in_Data j X).
Proof.
  intros j [a|i]; simpl; [ reflexivity | ].
  destruct (decide (S j < S (S i))); destruct (decide (j < S i));
    simpl; try reflexivity; exfalso; lia.
Qed.

Lemma subst_NewVar_Data : forall j k X Y, (j <= k)%nat ->
  subst_Data (S k) (NewVar_in_Data j X) (NewVar_in_Data j Y)
  = NewVar_in_Data j (subst_Data k X Y).
Proof.
  intros j k X [a|i] Hjk; simpl; [ reflexivity | ].
  destruct (decide (j < S i)) as [Hji|Hji]; simpl.
  - destruct (decide (S i = S k)) as [E1|E1]; destruct (decide (i = k)) as [E2|E2];
      simpl; try (exfalso; lia); [ reflexivity | ].
    destruct (decide (S i < S k)) as [E3|E3]; destruct (decide (i < k)) as [E4|E4];
      simpl; try (exfalso; lia).
    + destruct (decide (j < S i)); simpl; [ reflexivity | exfalso; lia ].
    + destruct (decide (j < S (Nat.pred i))); simpl; [ | exfalso; lia ].
      destruct i; [ exfalso; lia | simpl; reflexivity ].
  - destruct (decide (i = S k)) as [E1|E1]; [ exfalso; lia | ].
    destruct (decide (i < S k)) as [E2|E2]; [ | exfalso; lia ]. simpl.
    destruct (decide (i = k)) as [E3|E3]; [ exfalso; lia | ].
    destruct (decide (i < k)) as [E4|E4]; [ | exfalso; lia ]. simpl.
    destruct (decide (j < S i)); [ exfalso; lia | reflexivity ].
Qed.

Lemma subst_NewVar : forall p j k X, (j <= k)%nat ->
  subst_in_proc (S k) (NewVar_in_Data j X) (NewVar j p) = NewVar j (subst_in_proc k X p)
with subst_gNewVar : forall M j k X, (j <= k)%nat ->
  subst_in_gproc (S k) (NewVar_in_Data j X) (gNewVar j M) = gNewVar j (subst_in_gproc k X M).
Proof.
  - destruct p as [p1 p2|x|x p0|E p1 p2|c w|p0|M]; intros j k X Hjk; simpl.
    + f_equal; apply subst_NewVar; exact Hjk.
    + reflexivity.
    + f_equal; apply subst_NewVar; exact Hjk.
    + destruct E as [D1 D2]. simpl. f_equal;
        [ f_equal; apply subst_NewVar_Data; exact Hjk
        | apply subst_NewVar; exact Hjk | apply subst_NewVar; exact Hjk ].
    + f_equal. apply subst_NewVar_Data. exact Hjk.
    + f_equal. apply subst_NewVar. exact Hjk.
    + f_equal. apply subst_gNewVar. exact Hjk.
  - destruct M as [ | |c p0|p0|M1 M2]; intros j k X Hjk; simpl.
    + reflexivity.
    + reflexivity.
    + f_equal. rewrite <- NewVar_in_Data_Succ. apply subst_NewVar. lia.
    + f_equal. apply subst_NewVar. exact Hjk.
    + f_equal; apply subst_gNewVar; exact Hjk.
Qed.

(** ****** The instance the expansion law's [gNewVar 0] needs. *)
Corollary subst_NewVar_0 : forall p k X,
  subst_in_proc (S k) (Succ_bvar X) (NewVar 0 p) = NewVar 0 (subst_in_proc k X p).
Proof. intros p k X. rewrite <- NewVar_in_Data_zero. apply subst_NewVar. lia. Qed.

Lemma subst_res_n : forall n j X p,
  subst_in_proc j X (Ѵ n p) = Ѵ n (subst_in_proc j X p).
Proof. induction n; intros j X p; simpl; [ reflexivity | f_equal; apply IHn ]. Qed.

Corollary subst_gNewVar_0 : forall M k X,
  subst_in_gproc (S k) (Succ_bvar X) (gNewVar 0 M) = gNewVar 0 (subst_in_gproc k X M).
Proof. intros M k X. rewrite <- NewVar_in_Data_zero. apply subst_gNewVar. lia. Qed.

Lemma subst_gNewVarCn : forall n i j X M,
  subst_in_gproc j X (gNewVarCn i n M) = gNewVarCn i n (subst_in_gproc j X M).
Proof.
  induction n; intros i j X M; simpl; [ reflexivity | ].
  rewrite subst_gNewVarC. f_equal. apply IHn.
Qed.

Lemma subst_NewVar_in_Data_cancel : forall (X Y : ValueData),
  subst_Data 0 X (NewVar_in_Data 0 Y) = Y.
Proof.
  intros X Y. destruct Y as [v|i]; simpl; [ reflexivity | ].
  destruct (decide (0 < S i)) as [_|Hn]; [ | lia ].
  simpl. destruct (decide (S i = 0)) as [E|_]; [ discriminate | ].
  destruct (decide (S i < 0)) as [E|_]; [ lia | ]. reflexivity.
Qed.

Lemma eval_eq_refl : forall (Y : ValueData), Eval_Eq 0 (Y == Y) = Some true.
Proof.
  intros [v|i]; simpl.
  - destruct (decide (v = v)); [ reflexivity | contradiction ].
  - destruct (decide (i = i)); [ reflexivity | contradiction ].
Qed.

Lemma eval_eq_true : forall (w u : ValueData),
  Eval_Eq 0 (w == u) = Some true -> w = u.
Proof.
  intros [v|i] [v'|j] H; simpl in H.
  - destruct (decide (v = v')); [ subst; reflexivity | discriminate ].
  - discriminate.
  - discriminate.
  - destruct (decide (i = j)); [ subst; reflexivity | ].
    destruct (decide (0 <= i)); [ | lia ].
    destruct (decide (0 <= j)); [ discriminate | lia ].
Qed.

Lemma iter_shift_bvar : forall n j,
  Nat.iter n (NewVar_in_ChannelData 0) (bvar j) = bvar (n + j).
Proof.
  induction n as [|n IH]; intro j; simpl; [ reflexivity | ].
  rewrite IH. simpl. reflexivity.
Qed.

Lemma iter_shift_cst : forall n a,
  Nat.iter n (NewVar_in_ChannelData 0) (cst a) = cst a.
Proof.
  induction n as [|n IH]; intro a; simpl; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma VarC_action_add_revert : forall k n μ,
  VarC_action_add (k + n) μ = VarC_action_add k (VarC_action_add n μ).
Proof.
  intros k n μ. destruct μ as [(c,v)|(c,v)]; simpl; f_equal; f_equal;
    apply VarC_add_revert_def.
Qed.

Lemma varc_add_cst_inv : forall n (c : ChannelData) (a : Channel),
  VarC_add n c = cst a -> c = cst a.
Proof. intros n c a H. destruct c; simpl in H; [ exact H | discriminate ]. Qed.

Lemma BigNew_reverse_def_one j p : (Ѵ j (ν p)) = ν (Ѵ j p).
Proof.
  revert p.
  induction j.
  - intros. simpl. eauto.
  - intros. simpl. rewrite IHj. eauto.
Qed.

Lemma BigNew_reverse_def k j p : Ѵ k (Ѵ j p) = Ѵ j (Ѵ k p).
Proof.
  revert j p.
  induction k.
  - intros; simpl; eauto.
  - intros; simpl in *. replace ((ν Ѵ k p)) with (Ѵ 1 (Ѵ k p)); eauto.
    rewrite<- (IHk 1) at 1. simpl. rewrite<- IHk. replace ((ν Ѵ k (Ѵ j p))) with (Ѵ 1 (Ѵ k (Ѵ j p))); eauto.
    rewrite<- (IHk 1). f_equal. simpl. rewrite BigNew_reverse_def_one. eauto.
Qed.

Lemma NewVarC_in_ext_rev_Input c v μ' k : ActIn (c , v) = NewVarC_in_ext k μ' 
    -> exists c' v', μ' = ActIn (c' , v') /\ v = v' /\ NewVar_in_ChannelData k c' = c.
Proof.
  destruct μ'; destruct c; destruct a; simpl in * ; intro Hyp; try (inversion Hyp); subst.
  + exists c0. exists v0. split ;eauto.
  + exists c. exists v0. split ;eauto.
Qed.

Lemma NewVarC_in_ext_rev_Output c v μ' k : ActOut (c , v) = NewVarC_in_ext k μ' 
    -> exists c' v', μ' = ActOut (c' , v') /\ v = v' /\ NewVar_in_ChannelData k c' = c.
Proof.
  destruct μ'; destruct c; destruct a; simpl in * ; intro Hyp; try (inversion Hyp); subst.
  + exists c0. exists v0. split ;eauto.
  + exists c. exists v0. split ;eauto.
Qed.

Lemma inversion_k_NewVarC k μ μ' : NewVarC_in_ext 0 μ = NewVarC_in_ext (S k) μ' 
  -> NewVarC_in_ext 0 μ = μ' \/ (exists μ'0, μ = NewVarC_in_ext k μ'0).
Proof.
  intro Hyp.
  destruct μ; destruct a; destruct μ'; destruct a; destruct c; destruct c0; simpl in *; subst; try (inversion Hyp).
    + subst. right. exists (ActIn (cst c0 , v0)). simpl; eauto.
    + destruct (decide ((S k < S n))); inversion H0.
    + destruct (decide ((S k < S n0))).
      - subst. inversion H0. subst. right. inversion l.
        ++ subst. exists (ActIn (bvar k , v0)). simpl; eauto. rewrite decide_True; try lia. eauto.
        ++ subst. assert (0 < n0); try lia. assert (0 < n0); try lia. eapply Nat.succ_pred_pos in H. exists (ActIn (bvar (Nat.pred n0) , v0)).
           simpl. rewrite decide_True; try lia. f_equal. f_equal. eapply Nat.succ_pred_pos in H2. eauto.
      - subst. inversion H0. subst. left; eauto.
    + subst. left. eauto.
    + destruct (decide ((S k < S n))); inversion H0.
    + destruct (decide ((S k < S n0))).
      - subst. inversion H0. subst. right. inversion l.
        ++ subst. exists (ActOut (bvar k , v0)). simpl; eauto. rewrite decide_True; try lia. eauto.
        ++ subst. assert (0 < n0); try lia. assert (0 < n0); try lia. eapply Nat.succ_pred_pos in H. exists (ActOut (bvar (Nat.pred n0) , v0)).
           simpl. rewrite decide_True; try lia. f_equal. f_equal. eapply Nat.succ_pred_pos in H2. eauto.
      - subst. inversion H0. subst. left; eauto.
Qed.

Lemma inversion_NewVarC_par p1 p2 p3 k : p1 ‖ NewVarC k p2 = NewVarC k p3 -> exists p', p1 = NewVarC k p'.
Proof.
  destruct p3; intro Hyp ; simpl in *; try (inversion Hyp).
  exists p3_1; eauto.
Qed.

Lemma inversion_NewVarC_par2 p1 p2 p3 k : NewVarC k p2 ‖ p1  = NewVarC k p3 -> exists p', p1 = NewVarC k p'.
Proof.
  destruct p3; intro Hyp ; simpl in *; try (inversion Hyp).
  exists p3_2; eauto.
Qed.

Lemma NewVarC_shift_inv : forall k c c0, VarC_add 1 c = NewVar_in_ChannelData (S k) c0 ->
  exists c1, c = NewVar_in_ChannelData k c1 /\ c0 = VarC_add 1 c1.
Proof.
  intros k c [a|j] Heq.
  - destruct c as [b|m]; simpl in Heq; try discriminate Heq.
    inversion Heq; subst. exists (cst a). split; reflexivity.
  - destruct c as [b|m]; simpl in Heq;
      [ destruct (decide (S k < S j)); discriminate Heq | ].
    destruct (decide (S k < S j)) as [Hlt|Hge].
    + destruct j as [|j']; [ exfalso; lia | ].
      exists (bvar j'). inversion Heq; subst. simpl.
      split; [ destruct (decide (k < S j')) as [H1|H1];
               [ reflexivity | exfalso; lia ] | reflexivity ].
    + exists (bvar m). inversion Heq; subst. simpl.
      split; [ destruct (decide (k < S m)) as [H1|H1];
               [ exfalso; lia | reflexivity ] | reflexivity ].
Qed.

Lemma NewVar_in_action_inv : forall k μ μ0,
  VarC_action_add 1 μ = NewVar_in_action (S k) μ0 ->
  exists μ1, μ = NewVar_in_action k μ1 /\ μ0 = VarC_action_add 1 μ1.
Proof.
  intros k [[c v]|[c v]] [[c0 v0]|[c0 v0]] Heq; simpl in Heq; inversion Heq; subst;
    match goal with H : VarC_add 1 c = _ |- _ =>
      destruct (NewVarC_shift_inv k c c0 H) as (c1 & Hc1 & Hc2) end; subst;
    [ exists (ActIn (c1, v0)) | exists (ActOut (c1, v0)) ]; split; reflexivity.
Qed.

Lemma BigNew_add : forall n m p, Ѵ (n + m) p = Ѵ n (Ѵ m p).
Proof. induction n; intros m p; simpl; [ reflexivity | rewrite IHn; reflexivity ]. Qed.

Lemma subst_par_inv : forall (R : proc) (v : ValueData) (r1 r2 : proc),
  subst_in_proc 0 v R = r1 ‖ r2 ->
  exists R1 R2, R = R1 ‖ R2
             /\ r1 = subst_in_proc 0 v R1 /\ r2 = subst_in_proc 0 v R2.
Proof.
  intros R v r1 r2 H. destruct R; simpl in H; try discriminate H.
  inversion H; subst. exists R1, R2. split; [ reflexivity | split; reflexivity ].
Qed.

Lemma subst_res_inv : forall (R : proc) (v : ValueData) (r : proc),
  subst_in_proc 0 v R = ν r ->
  exists R0, R = ν R0 /\ r = subst_in_proc 0 v R0.
Proof.
  intros R v r H. destruct R; simpl in H; try discriminate H.
  inversion H; subst. exists R. split; [ reflexivity | reflexivity ].
Qed.

Lemma subst_NewVarC_inv : forall R j v k s,
  subst_in_proc j v R = NewVarC k s ->
  exists S, R = NewVarC k S /\ s = subst_in_proc j v S
with subst_gNewVarC_inv : forall M j v k N,
  subst_in_gproc j v M = gNewVarC k N ->
  exists S, M = gNewVarC k S /\ N = subst_in_gproc j v S.
Proof.
  - destruct R as [Ra Rb|xa|xa Ra|Ea Ra Rb|ca wa|Ra|Ma];
    destruct s as [sa sb|xb|xb sa|Eb sa sb|cb wb|sa|Mb];
    intros H; simpl in H; try discriminate H.
    + inversion H; subst.
      destruct (subst_NewVarC_inv Ra j v k sa H1) as (S1 & EA & EB).
      destruct (subst_NewVarC_inv Rb j v k sb H2) as (S2 & EC & ED).
      exists (S1 ‖ S2). subst. split; reflexivity.
    + inversion H; subst. exists (pr_var xb). split; reflexivity.
    + inversion H; subst.
      destruct (subst_NewVarC_inv Ra j v k sa H2) as (S1 & EA & EB).
      exists (rec xb • S1). subst. split; reflexivity.
    + inversion H; subst.
      destruct (subst_NewVarC_inv Ra j v k sa H2) as (S1 & EA & EB).
      destruct (subst_NewVarC_inv Rb j v k sb H3) as (S2 & EC & ED).
      exists (If Ea Then S1 Else S2). subst. split; reflexivity.
    + inversion H; subst. exists (cb ! wa • 𝟘). split; reflexivity.
    + inversion H; subst.
      destruct (subst_NewVarC_inv Ra j v (S k) sa H1) as (S1 & EA & EB).
      exists (ν S1). subst. split; reflexivity.
    + inversion H; subst.
      destruct (subst_gNewVarC_inv Ma j v k Mb H1) as (S1 & EA & EB).
      exists (LTS.g S1). subst. split; reflexivity.
  - destruct M as [ | | ca Ma | Ma | Ma Mb ];
    destruct N as [ | | cb Na | Na | Na Nb ];
    intros H; simpl in H; try discriminate H.
    + exists ①. split; reflexivity.
    + exists 𝟘. split; reflexivity.
    + inversion H; subst.
      destruct (subst_NewVarC_inv Ma (S j) (Succ_bvar v) k Na H2) as (S1 & EA & EB).
      exists (cb ? • S1). subst. split; reflexivity.
    + inversion H; subst.
      destruct (subst_NewVarC_inv Ma j v k Na H1) as (S1 & EA & EB).
      exists (𝛕 • S1). subst. split; reflexivity.
    + inversion H; subst.
      destruct (subst_gNewVarC_inv Ma j v k Na H1) as (S1 & EA & EB).
      destruct (subst_gNewVarC_inv Mb j v k Nb H2) as (S2 & EC & ED).
      exists (S1 + S2). subst. split; reflexivity.
Qed.

End VACCS_Substitution.

Global Notation "⇑ g" := (gNewVarC 0 g) (at level 40).
