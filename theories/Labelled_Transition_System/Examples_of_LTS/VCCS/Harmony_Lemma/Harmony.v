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

From stdpp Require Import base countable finite list gmap gmultiset.
From Stdlib.Program Require Import Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.
From TestingTheory Require Import ActTau InputOutputActions Clos_n gLts.
From TestingTheory Require Import VCCS.Language.LTS VCCS.Helper.Substitution VCCS.Language.Congruence.

Section VCCS_Harmony.

Context `{VP : VCCS_Parameters}.
Existing Instance VP.

(** ******* State Transition System (STS-reduction) *)
Inductive sts : proc -> proc -> Prop :=
(** ******* Communication of channels output and input that have the same name *)
| sts_com : forall {c v p1 g1 p2 g2},
    sts (((c ! v • p1) + g1) ‖ ((c ? • p2) + g2)) (p1 ‖ (p2 ^ v))
(** ******* Nothing more , something less *)
| sts_tau : forall {p g},
    sts ((𝛕 • p) + g) p
(** ******* Resursion *)
| sts_recursion : forall {x p},
    sts (rec x • p) (pr_subst x p (rec x • p))

(** ******* The left parallele respect the Reduction *)
| sts_par : forall {p1 p2 q},
    sts p1 p2 ->
    sts (p1 ‖ q) (p2 ‖ q)

(** ******* Restriction on Channel *)
| sts_res : forall {p1 p2}, 
    sts p1 p2 ->
    sts (ν p1) (ν p2)

(** ******* The Congruence respects the Reduction *)
| sts_cong : forall {p1 p2 q2 q1},
    p1 ≡* p2 -> sts p2 q2 -> q2 ≡* q1 -> sts p1 q1
.

Hint Constructors sts:ccs.

Lemma cgr_res_n n P Q : P ≡* Q -> Ѵ  n P ≡* Ѵ  n Q.
Proof.
  revert P Q. induction n.
  - intros; eauto.
  - intros; simpl. eapply cgr_res. eauto.
Qed.


Lemma cgr_res_scope_n n P Q : (Ѵ  n P) ‖ Q ≡* (Ѵ n (P ‖ NewVarCn 0 n Q)).
Proof.
  revert P Q.
  dependent induction n.
  - simpl. reflexivity.
  - intros. simpl. etrans. eapply cgr_res_scope_rev. eapply cgr_res.
    etrans. eapply IHn. eapply cgr_res_n. eapply cgr_fullpar. reflexivity.
    rewrite NewVarCn_revert_def. reflexivity.
Qed.

(** ******* For the (STS-reduction), the reductible terms and reducted terms are pretty all the same, up to ≡* *)
Lemma ReductionShape : forall P Q, sts P Q ->
((exists c v P1 P2 G1 G2 S n , ((P ≡* Ѵ  n (((c ! v • P1) + G1) ‖ ((c ? • P2) + G2) ‖ S))) /\ (Q ≡* Ѵ  n ((P1 ‖ (P2^v)) ‖ S)))
\/ (exists P1 G1 S n, (P ≡* Ѵ  n (((𝛕 • P1) + G1) ‖ S)) /\ (Q ≡* Ѵ  n (P1 ‖ S)))
\/ (exists n P1 S n', (P ≡* Ѵ  n' ((rec n • P1) ‖ S)) /\ (Q ≡* Ѵ  n' (pr_subst n P1 (rec n • P1) ‖ S)))
).
Proof.
  intros P Q Transition. induction Transition.
  - left. exists c. exists v. exists p1. exists p2.
    exists g1. exists g2. exists 𝟘. exists 0. split.
    * simpl. etrans. eapply cgr_par_nil_rev. eapply cgr_fullpar; reflexivity.
    * simpl. etrans. eapply cgr_par_nil_rev. eapply cgr_fullpar; reflexivity.
  - right. left. exists p. exists g. exists 𝟘. exists 0. split.
    * simpl. eapply cgr_par_nil_rev.
    * simpl. eapply cgr_par_nil_rev.
  - right. right. exists x. exists p. exists 𝟘. exists 0. split.
    * simpl. eapply cgr_par_nil_rev.
    * simpl. eapply cgr_par_nil_rev.
  - destruct IHTransition as [IH|[IH|IH]];  decompose record IH. 
    * left. exists x. exists x0. exists x1. exists x2. exists x3. exists x4.
      exists (x5 ‖ NewVarCn 0 x6 q). exists x6. split; simpl.
      + apply transitivity with (Ѵ x6 ((((x ! x0 • x1 + x3) ‖ (gpr_input x x2 + x4)) ‖ x5)) ‖ q).
        apply cgr_par. eauto. etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
      + apply transitivity with (Ѵ x6 ((x1 ‖ x2 ^ x0) ‖ x5) ‖ q).
        apply cgr_par. eauto. etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
    * right. left. exists x. exists x0. exists (x1 ‖ NewVarCn 0 x2 q). exists x2. split.
      + apply transitivity with (Ѵ x2 ((𝛕 • x + x0) ‖ x1) ‖ q). apply cgr_par. auto. etrans.
           eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
      + apply transitivity with (Ѵ x2 (x ‖ x1) ‖ q). apply cgr_par. auto. etrans.
           eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
    * right. right. exists x. exists x0. exists (x1 ‖ NewVarCn 0 x2 q). exists x2. split. 
      + apply transitivity with (Ѵ  x2 ((rec x • x0) ‖ x1) ‖ q). apply cgr_par. assumption.
           etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
      + apply transitivity with (Ѵ  x2 (pr_subst x x0 (rec x • x0) ‖ x1) ‖ q). apply cgr_par. assumption. 
           etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  - destruct IHTransition as [IH|[IH|IH]]; decompose record IH. 
    * left. exists x. exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. exists (S x6). split.
      + simpl. eapply cgr_res. eauto.
      + simpl. eapply cgr_res. eauto.
    * right. left. exists x. exists x0. exists x1. exists (S x2). split.
      + simpl. eapply cgr_res. eauto.
      + simpl. eapply cgr_res. eauto.
    * right. right. exists x. exists x0. exists x1. exists (S x2). split.
      + simpl. eapply cgr_res. eauto.
      + simpl. eapply cgr_res. eauto.
  - destruct IHTransition as [IH|[IH|IH]]; decompose record IH. 
    * left. exists x. exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. exists x6. split.
      + apply cgr_trans with p2. exact H. exact H1.
      + apply cgr_trans with q2. apply cgr_symm. exact H0. exact H3.
    * right. left. exists x. exists x0. exists x1. exists x2. split.
      + apply cgr_trans with p2. exact H. exact H1.
      + apply cgr_trans with q2. apply cgr_symm. apply H0. apply H3.
    * right. right. exists x. exists x0. exists x1. exists x2. split.
      + apply cgr_trans with p2. exact H. exact H1.
      + apply cgr_trans with q2. apply cgr_symm. apply H0. apply H3.
Qed.

(** ******* For the (LTS-transition), the transitable terms and transitted terms, that performs a INPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForInput : forall P Q c v, (lts P ((c , v) ?) Q) -> 
(exists P1 G R n, ((P ≡* Ѵ  n (((VarC_add n c) ? • P1 + G) ‖ R)) /\ (Q ≡* Ѵ  n (P1^v ‖ R))
  /\ ((exists L,P = (g L)) -> R = 𝟘 /\ n = 0))).
Proof.
intros P Q c v Transition.
 dependent induction Transition.
- exists P. exists 𝟘. exists 𝟘. exists 0. repeat split.
  * simpl. destruct c.
    + simpl. apply cgr_trans with ((c ? • P) + 𝟘). apply cgr_trans with (c ? • P).
      apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
    + simpl. apply cgr_trans with ((n ? • P) + 𝟘). apply cgr_trans with (n ? • P).
      apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
- destruct (IHTransition c v). reflexivity. decompose record H0.
  exists x. exists x0. exists x1. exists x2. split; try split.
  * apply cgr_trans with p. apply cgr_if_true. assumption. simpl. assumption.
  * assumption.
  * intros. inversion H3. inversion H5.
- destruct (IHTransition c v). reflexivity. decompose record H0.
  exists x. exists x0. exists x1. exists x2. split; try split.
  * apply cgr_trans with q. apply cgr_if_false. assumption. assumption.
  * assumption.
  * intros. inversion H3. inversion H5.
- destruct (IHTransition (VarC_add 1 c) v). reflexivity. decompose record H. exists x. exists x0.
  exists x1. exists (S x2). repeat split.
  * simpl. eapply cgr_res. rewrite<- VarC_add_revert_def in H1.
    replace (S x2)%nat with (x2 + 1)%nat by lia. exact H1.
  * simpl. eapply cgr_res. exact H0.
  * intros. inversion H2. inversion H4.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0.
  exists (x1 ‖ NewVarCn 0 x2 q). exists x2. repeat split.
  * apply cgr_trans with (Ѵ x2 ((((VarC_add x2 c) ? • x) + x0) ‖ x1) ‖ q). apply cgr_par. assumption.
    etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  * apply cgr_trans with (Ѵ x2 (x^v ‖ x1) ‖ q). apply cgr_par. assumption. etrans.
    eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ NewVarCn 0 x2 p). exists x2. repeat split.
  * apply cgr_trans with (Ѵ x2 ((((VarC_add x2 c) ? • x) + x0) ‖ x1) ‖ p). apply cgr_trans with (q1 ‖ p).
    apply cgr_par_com. apply cgr_par. assumption. etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  * apply cgr_trans with (Ѵ x2 (x^v ‖ x1) ‖ p). apply cgr_trans with (q2 ‖ p). apply cgr_par_com. apply cgr_par. assumption.
    etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p2). exists 𝟘. exists 0. repeat split.
  * simpl. apply cgr_trans with ((c ? • x) + (x0 + p2)). apply cgr_trans with (((c ? • x) + x0) + p2).
    apply cgr_choice. assert (x1 = 𝟘 ∧ x2 = 0) as (eq1 & eq2). apply H3. exists p1. reflexivity. subst.
    apply transitivity with (((c ? • x) + x0) ‖ 𝟘). simpl in *. rewrite VarC_add_zero in H1. eauto.
    apply cgr_par_nil. apply cgr_choice_assoc. rewrite VarC_add_zero. apply cgr_par_nil_rev.
  * simpl. assert (x1 = 𝟘 ∧ x2 = 0) as (eq1 & eq2). apply H3. exists p1. reflexivity. subst. simpl in *. assumption.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p1). exists 𝟘. exists 0. repeat split.
  * simpl. apply cgr_trans with ((c ? • x) + (x0 + p1)). apply cgr_trans with (((c ? • x) + x0) + p1).
    etrans. eapply cgr_choice_com. apply cgr_choice. assert (x1 = 𝟘 ∧ x2 = 0) as (eq1 & eq2).
    apply H3. exists p2. reflexivity. subst.
    apply transitivity with (((c ? • x) + x0) ‖ 𝟘). simpl in *. rewrite VarC_add_zero in H1. eauto.
    apply cgr_par_nil. apply cgr_choice_assoc. rewrite VarC_add_zero. apply cgr_par_nil_rev.
  * simpl. assert (x1 = 𝟘 ∧ x2 = 0) as (eq1 & eq2). apply H3. exists p2. reflexivity. subst. simpl in *. assumption.
Qed.

(** ******* For the (LTS-transition), the transitable terms and transitted terms, that performs a OUPUT,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForOutput : forall P Q c v, (lts P (((c , v))!) Q) -> 
(exists P1 G R n, ((P ≡* Ѵ  n (((VarC_add n c) ! v • P1 + G) ‖ R)) /\ (Q ≡* Ѵ  n (P1 ‖ R)) /\
((exists L,P = (g L)) -> R = 𝟘 /\ n = 0))).
Proof.
intros P Q c v Transition.
dependent induction Transition.
- exists P. exists 𝟘. exists 𝟘. exists 0. repeat split.
  * simpl. destruct c; simpl.
    + apply cgr_trans with ((c ! v • P) + 𝟘). apply cgr_trans with (c ! v • P).
      apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
    + apply cgr_trans with ((n ! v • P) + 𝟘). apply cgr_trans with (n ! v • P).
      apply cgr_refl. apply cgr_choice_nil_rev. apply cgr_par_nil_rev.
  * apply cgr_par_nil_rev.
- destruct (IHTransition c v). reflexivity. decompose record H0. exists x. exists x0. exists x1. exists x2. repeat split.
  * apply cgr_trans with p. apply cgr_if_true. assumption. assumption.
  * assumption.
  * intros. inversion H3. inversion H5.
  * intros. inversion H3. inversion H5.
- destruct (IHTransition c v). reflexivity. decompose record H0. exists x. exists x0. exists x1. exists x2. repeat split.
  * apply cgr_trans with q. apply cgr_if_false. assumption. assumption.
  * assumption.
  * intros. inversion H3. inversion H5.
  * intros. inversion H3. inversion H5.
- destruct (IHTransition (VarC_add 1 c) v). reflexivity. decompose record H. exists x. exists x0.
  exists x1. exists (S x2). repeat split.
  * simpl. eapply cgr_res. rewrite<- VarC_add_revert_def in H1.
    replace (S x2)%nat with (x2 + 1)%nat by lia. exact H1.
  * simpl. eapply cgr_res. exact H0.
  * intros. inversion H2. inversion H4.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ NewVarCn 0 x2 q). exists x2. repeat split.
  * etrans. apply cgr_par. eassumption. etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  * apply cgr_trans with (Ѵ x2 (x ‖ x1) ‖ q). apply cgr_par. assumption. etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists x0. exists (x1 ‖ NewVarCn 0 x2 p). exists x2. repeat split.
  * apply cgr_trans with (Ѵ x2  (((VarC_add x2 c ! v • x) + x0) ‖ x1) ‖ p). apply cgr_trans with (q1 ‖ p).
    apply cgr_par_com. apply cgr_par. assumption. etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  * apply cgr_trans with (Ѵ x2 (x ‖ x1) ‖ p). apply cgr_trans with (q2 ‖ p). apply cgr_par_com. apply cgr_par. assumption.
    etrans. eapply cgr_res_scope_n. eapply cgr_res_n. apply cgr_par_assoc.
  * intros. inversion H2. inversion H4.
  * intros. inversion H2. inversion H4.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p2). exists 𝟘. exists 0. repeat split.
  * simpl. apply cgr_trans with ((c ! v • x) + (x0 + p2)). apply cgr_trans with (((c ! v • x) + x0) + p2).
    apply cgr_choice. assert (x1 = 𝟘 ∧ x2 = 0) as (eq1 & eq2). apply H3. exists p1. reflexivity. subst.
    apply transitivity with (((c ! v • x) + x0) ‖ 𝟘). simpl in *. rewrite VarC_add_zero in H1. eauto.
    apply cgr_par_nil. apply cgr_choice_assoc. rewrite VarC_add_zero. apply cgr_par_nil_rev.
  * simpl. assert (x1 = 𝟘 ∧ x2 = 0) as (eq1 & eq2). apply H3. exists p1. reflexivity. subst. simpl in *. assumption.
- destruct (IHTransition c v). reflexivity. decompose record H. exists x. exists (x0 + p1). exists 𝟘. exists 0. repeat split.
  * simpl. apply cgr_trans with ((c ! v • x) + (x0 + p1)). apply cgr_trans with (((c ! v • x) + x0) + p1).
    etrans. eapply cgr_choice_com. apply cgr_choice. assert (x1 = 𝟘 ∧ x2 = 0) as (eq1 & eq2).
    apply H3. exists p2. reflexivity. subst.
    apply transitivity with (((c ! v • x) + x0) ‖ 𝟘). simpl in *. rewrite VarC_add_zero in H1. eauto.
    apply cgr_par_nil. apply cgr_choice_assoc. rewrite VarC_add_zero. apply cgr_par_nil_rev.
  * simpl. assert (x1 = 𝟘 ∧ x2 = 0) as (eq1 & eq2). apply H3. exists p2. reflexivity. subst. simpl in *. assumption.
Qed.

(** ******* For the (LTS-transition), the transitable Guards and transitted terms, that performs a Tau ,
are pretty all the same, up to ≡* *)
Lemma TransitionShapeForTauAndGuard : forall P V, ((lts P τ V) /\ (exists L, P = (g L))) -> 
(exists Q M, ((P ≡* ((𝛕 • Q) + M))) /\ (V ≡* Q)).
Proof.
intros P V Hyp. 
destruct Hyp. rename H into Transition. dependent induction Transition.
- exists P. exists 𝟘. split. 
  * apply cgr_choice_nil_rev.
  * apply cgr_refl.
- inversion H0. inversion H.
- inversion H0. inversion H1.
- inversion H0. inversion H1.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- inversion H0. inversion H.
- edestruct IHTransition. reflexivity. exists p1. reflexivity. destruct H. destruct H.  exists x. 
  exists (x0 + p2). split. apply cgr_trans with (((𝛕 • x) + x0) + p2).
  apply cgr_choice. assumption.
  apply cgr_choice_assoc. assumption.
- edestruct IHTransition. reflexivity. exists p2. reflexivity. destruct H. destruct H.  exists x. 
  exists (x0 + p1). split. apply cgr_trans with (((𝛕 • x) + x0) + p1). apply cgr_trans with (p2 + p1). 
  apply cgr_choice_com. apply cgr_choice. assumption. apply cgr_choice_assoc. assumption.
Qed.

(** ******* p 'is equivalent some r 'and r performs α to q *)
Definition sc_then_lts p α q := exists r, p ≡* r /\ (lts r α q).

(** ******* p performs α to some r and this is equivalent to q*)
Definition lts_then_sc p α q := exists r, ((lts p α r) /\ r ≡* q).

Lemma VarSwap_swap_proc p p' μ k : lts (VarSwap_in_proc k p) (ActExt (VarC_action_add (S (S k)) μ)) p' -> 
lts p (ActExt (VarC_action_add (S (S k)) μ)) (VarSwap_in_proc k p').
Proof.
  revert p' μ k.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + dependent destruction H.
    * simpl. rewrite VarSwap_in_proc_invol. eapply lts_parL. eapply Hp. simpl. lia. eauto.
    * simpl. rewrite VarSwap_in_proc_invol. eapply lts_parR. eapply Hp. simpl. lia. eauto.
  + inversion H.
  + inversion H.
  + dependent destruction H.
    * simpl. eapply lts_ifOne; eauto. eapply Hp. simpl. lia. eauto.
    * simpl. eapply lts_ifZero; eauto. eapply Hp. simpl. lia. eauto.
  + dependent destruction H. rewrite VarC_action_add_add in H. simpl in H.
    eapply Hp in H; simpl ; try lia. replace (S (S (S k)))%nat with (1 + (S (S k)))%nat in H by lia.
    rewrite<- VarC_action_add_add in H. eapply lts_res_ext in H. eauto. 
  + destruct g.
    * inversion H.
    * inversion H.
    * simpl in *. destruct c.
      - simpl in *. inversion H; subst. rewrite<- subst_and_VarSwap. rewrite VarSwap_in_proc_invol. eapply lts_input.
      - simpl in *. destruct (decide (n = k)).
        ++ subst. inversion H; subst. destruct μ. 
           ++++ destruct a. simpl in *. inversion H3. subst. destruct c.
                +++++ simpl in *. inversion H1.
                +++++ simpl in *. destruct n. 
                      ++++++ inversion H3. lia.
                      ++++++ inversion H1. lia.
           ++++ destruct a. simpl in *. inversion H3.
        ++ destruct (decide (n = S k)).
           ++++ subst. inversion H; subst. destruct μ. 
                +++++ destruct a. simpl in *. inversion H3. subst. destruct c.
                      ++++++ inversion H3.
                      ++++++ inversion H1. lia.
                +++++ destruct a. simpl in *. inversion H3.
           ++++ inversion H; subst. rewrite<- subst_and_VarSwap. rewrite VarSwap_in_proc_invol. eapply lts_input.
    * simpl in *. destruct c.
      - simpl in *. inversion H; subst. rewrite VarSwap_in_proc_invol. eapply lts_output.
      - simpl in *. destruct (decide (n = k)).
        ++ subst. inversion H; subst. destruct μ. 
           ++++ destruct a. simpl in *. inversion H4.
           ++++ destruct a. simpl in *. inversion H4. subst. destruct c.
                +++++ simpl in *. inversion H1.
                +++++ simpl in *. destruct n. 
                      ++++++ inversion H1. lia.
                      ++++++ inversion H1. lia.
        ++ destruct (decide (n = S k)).
           ++++ subst. inversion H; subst. destruct μ.
                +++++ destruct a. simpl in *. inversion H4.
                +++++ destruct a. simpl in *. inversion H4. subst. destruct c.
                      ++++++ inversion H1.
                      ++++++ inversion H1. lia.
           ++++ inversion H; subst. rewrite VarSwap_in_proc_invol. eapply lts_output.
    * inversion H.
    * dependent destruction H.
      - simpl. eapply lts_choiceL. eapply Hp. simpl. lia. eauto.
      - simpl. eapply lts_choiceR. eapply Hp. simpl. lia. eauto.
Qed.

Lemma VarSwap_swap2_proc p p' μ k : lts (VarSwap_in_proc k p) (ActExt μ) p' -> 
lts p (ActExt (VarSwap_in_ext k μ)) (VarSwap_in_proc k p').
Proof.
  revert p' μ k.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + dependent destruction H.
    * simpl. rewrite VarSwap_in_proc_invol. eapply lts_parL. eapply Hp. simpl. lia. eauto.
    * simpl. rewrite VarSwap_in_proc_invol. eapply lts_parR. eapply Hp. simpl. lia. eauto.
  + inversion H.
  + inversion H.
  + dependent destruction H.
    * simpl. eapply lts_ifOne; eauto. eapply Hp. simpl. lia. eauto.
    * simpl. eapply lts_ifZero; eauto. eapply Hp. simpl. lia. eauto.
  + dependent destruction H. simpl in *. eapply Hp in H; try lia.
    eapply lts_res_ext. rewrite VarC_action_add_Swap. eauto.
  + destruct g.
    * inversion H.
    * inversion H.
    * simpl in *. destruct c.
      - simpl in *. inversion H; subst. rewrite<- subst_and_VarSwap. rewrite VarSwap_in_proc_invol. eapply lts_input.
      - simpl in *. destruct (decide (n = k)).
        ++ subst. inversion H; subst. rewrite<- subst_and_VarSwap. rewrite VarSwap_in_proc_invol.
           simpl in *. rewrite decide_False; try lia. rewrite decide_True; try lia. eapply lts_input.
        ++ destruct (decide (n = S k)).
           ++++ subst. inversion H; subst. simpl in *. rewrite decide_True; try lia.
                rewrite<- subst_and_VarSwap. rewrite VarSwap_in_proc_invol. eapply lts_input.
           ++++ inversion H; subst. rewrite<- subst_and_VarSwap. rewrite VarSwap_in_proc_invol. simpl in *.
                rewrite decide_False; try lia. rewrite decide_False; try lia. eapply lts_input.
    * simpl in *. destruct c.
      - simpl in *. inversion H; subst. rewrite VarSwap_in_proc_invol. eapply lts_output.
      - simpl in *. destruct (decide (n = k)).
        ++ subst. inversion H; subst. rewrite VarSwap_in_proc_invol.
           simpl in *. rewrite decide_False; try lia. rewrite decide_True; try lia. eapply lts_output.
        ++ destruct (decide (n = S k)).
           ++++ subst. inversion H; subst. simpl in *. rewrite decide_True; try lia.
                rewrite VarSwap_in_proc_invol. eapply lts_output.
           ++++ inversion H; subst. rewrite VarSwap_in_proc_invol. simpl in *.
                rewrite decide_False; try lia. rewrite decide_False; try lia. eapply lts_output.
    * inversion H.
    * dependent destruction H.
      - simpl. eapply lts_choiceL. eapply Hp. simpl. lia. eauto.
      - simpl. eapply lts_choiceR. eapply Hp. simpl. lia. eauto.
Qed.

Lemma NewVarC_preserves_transition k p μ q :
  lts p (ActExt μ) q -> lts (NewVarC k p) (ActExt (NewVarC_in_ext k μ)) (NewVarC k q).
Proof.
  revert k μ q. induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; simpl in *; intros.
  + inversion H; subst; simpl in *.
    - eapply lts_parL. eapply Hp; eauto. simpl. lia.
    - eapply lts_parR. eapply Hp; eauto. simpl. lia.
  + inversion H.
  + inversion H.
  + inversion H; subst; simpl in *.
    * eapply lts_ifOne; eauto. eapply Hp; eauto. simpl. lia.
    * eapply lts_ifZero; eauto. eapply Hp; eauto. simpl. lia.
  + inversion H; subst; simpl in *.
    eapply lts_res_ext. rewrite NewVarCzero_and_add.
    assert (k = (0 + k))%nat as eq by lia. rewrite eq at 2.
    rewrite NewVarC_and_NewVarC_in_ChannelData. simpl. eapply Hp. lia. eauto.
  + destruct g; simpl in *.
    * inversion H.
    * inversion H.
    * inversion H; subst. simpl. rewrite<- subst_and_NewVarC. eapply lts_input.
    * inversion H; subst. simpl. eapply lts_output.
    * inversion H.
    * inversion H; subst; simpl in *.
      - eapply lts_choiceL. eapply Hp in H4; simpl; try lia. eauto.
      - eapply lts_choiceR. eapply Hp in H4; simpl; try lia. eauto.
Qed.

Lemma NewVarCn_preserves_transition k q μ q2 :
  lts q (ActExt μ) q2 -> lts (NewVarCn 0 k q) (ActExt (VarC_action_add k μ)) (NewVarCn 0 k q2).
Proof.
  revert μ q2 q. induction k.
  + intros. simpl; rewrite VarC_add_zero_ext. eauto.
  + intros; simpl in *. replace (S k)%nat with (1 + k)%nat; try lia.
    rewrite<- VarC_action_add_add. rewrite NewVarCzero_and_add. eapply NewVarC_preserves_transition.
    eapply IHk. eauto.
Qed.

Lemma NewVarC_preserves_reduction k p q :
  lts p τ q -> lts (NewVarC k p) τ (NewVarC k q).
Proof.
  revert k q. induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; simpl in *; intros.
  + inversion H; subst; simpl in *.
    - eapply NewVarC_preserves_transition in H2.
      eapply NewVarC_preserves_transition in H3.
      eapply lts_comL; eauto.
    - eapply NewVarC_preserves_transition in H2.
      eapply NewVarC_preserves_transition in H3.
      eapply lts_comR; eauto.
    - eapply lts_parL. eapply Hp; eauto. simpl. lia.
    - eapply lts_parR. eapply Hp; eauto. simpl. lia.
  + inversion H.
  + inversion H; subst. rewrite<- pr_subst_and_NewVarC. constructor.
  + inversion H; subst; simpl in *.
    * eapply lts_ifOne; eauto. eapply Hp; eauto. simpl. lia.
    * eapply lts_ifZero; eauto. eapply Hp; eauto. simpl. lia.
  + inversion H; subst; simpl in *.
    eapply lts_res_tau. eapply Hp. lia. eauto.
  + destruct g; simpl in *.
    * inversion H.
    * inversion H.
    * inversion H.
    * inversion H.
    * inversion H; subst. constructor.
    * inversion H; subst; simpl in *.
      - eapply lts_choiceL. eapply Hp in H4; simpl; try lia. eauto.
      - eapply lts_choiceR. eapply Hp in H4; simpl; try lia. eauto.
Qed.

Lemma NewVarCn_preserves_reduction q q2 k :
  lts q τ q2 -> lts (NewVarCn 0 k q) τ (NewVarCn 0 k q2).
Proof.
  revert q q2. induction k.
  + intros. simpl;eauto.
  + intros; simpl in *. eapply NewVarC_preserves_reduction.
    eapply IHk. eauto.
Qed.

Lemma VarSwap_swap_tau_proc p p' k : lts (VarSwap_in_proc k p) τ p' -> 
lts p τ (VarSwap_in_proc k p').
Proof.
  revert k p'.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  * dependent destruction H; simpl in *.
    - eapply VarSwap_swap2_proc in H, H0. simpl in *. eapply lts_comL; eauto.
    - eapply VarSwap_swap2_proc in H, H0. simpl in *. eapply lts_comR; eauto.
    - rewrite VarSwap_in_proc_invol. eapply lts_parL. eapply Hp; simpl; eauto. lia.
    - rewrite VarSwap_in_proc_invol. eapply lts_parR. eapply Hp; simpl; eauto. lia.
  * inversion H.
  * dependent destruction H; simpl in *. rewrite<- pr_subst_and_VarSwap2.
    simpl in *. rewrite VarSwap_in_proc_invol. constructor.
  * dependent destruction H; simpl in *.
    - eapply lts_ifOne; eauto. eapply Hp; simpl; eauto. lia.
    - eapply lts_ifZero; eauto. eapply Hp; simpl; eauto. lia.
  * dependent destruction H; simpl in *.
    eapply lts_res_tau. eapply Hp; simpl; eauto.
  * destruct g; simpl in *.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
    - dependent destruction H; simpl in *. rewrite VarSwap_in_proc_invol. eapply lts_tau.
    - dependent destruction H; simpl in *.
      + eapply lts_choiceL. eapply Hp; simpl; eauto. lia.
      + eapply lts_choiceR. eapply Hp; simpl; eauto. lia.
Qed.

Lemma NewVarC_ext_proc p μ p' k : lts (NewVarC k p) (ActExt μ)  p' -> 
exists μ' p'', μ = NewVarC_in_ext k μ' /\ p' = (NewVarC k p'').
Proof.
  revert μ p' k.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  * dependent destruction H; simpl in *.
    - eapply Hp in H as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
      exists μ'. exists (p'' ‖  p2). split; eauto.
    - eapply Hp in H as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
      exists μ'. exists (p1 ‖  p''). split; eauto.
  * inversion H.
  * inversion H.
  * dependent destruction H; simpl in *.
    - eapply Hp in H0 as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
      exists μ'. exists p''. split; eauto.
    - eapply Hp in H0 as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
      exists μ'. exists p''. split; eauto.
  * dependent destruction H; simpl in *.
    eapply Hp in H as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
    rewrite NewVarCzero_and_add in eq'.
    assert (NewVarC_in_ext 0 μ = NewVarC_in_ext (S k) μ'); eauto.
    eapply inversion_k_NewVarC in eq'. destruct eq' as [case1 | (μ'0 & case2)]; subst.
    + replace (S k) with (0 + S k)%nat in H by lia.
      rewrite<- NewVarC_and_NewVarC_in_ChannelData in H. simpl in *.
      exists μ. exists (ν p''). split. eapply NewVarC_in_ext_inv in H. eauto.
      simpl. eauto.
    + exists μ'0. exists (ν p''). split; eauto.
  * destruct g; simpl in *.
    - inversion H.
    - inversion H.
    - inversion H; subst. exists (ActIn ((c , v))). exists (p ^ v).
      split ;eauto. rewrite subst_and_NewVarC. eauto.
    - inversion H; subst. exists (ActOut (c , v)). exists p.
      split ;eauto.
    - inversion H.
    - dependent destruction H; simpl in *.
      + assert (lts (NewVarC k (g g1)) (ActExt μ) q) as Hyp; eauto.
        eapply Hp in Hyp as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
        exists μ'. exists p''. split; eauto.
      + assert (lts (NewVarC k (g g2)) (ActExt μ) q) as Hyp; eauto.
        eapply Hp in Hyp as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
        exists μ'. exists p''. split; eauto.
Qed.

Lemma NewVarC_tau_proc p p' k : lts (NewVarC k p) τ p' ->
 exists p'', p' = NewVarC k p''.
Proof.
  revert k p'.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  * dependent destruction H; simpl in *.
    - assert (lts (NewVarC k p1) (((c , v)) !) p3); eauto. assert (lts (NewVarC k p2) (((c , v)) ?) q2); eauto.
      eapply NewVarC_ext_proc in H as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
      eapply NewVarC_ext_proc in H0 as (μ'' & p''' & eq'' & eq''') ; simpl; subst ; try lia.
      exists (p'' ‖  p'''). split; eauto.
    - assert (lts (NewVarC k p2) (((c , v)) !) p3); eauto. assert (lts (NewVarC k p1) (((c , v)) ?) q2); eauto.
      eapply NewVarC_ext_proc in H as (μ' & p'' & eq' & eq'') ; simpl; subst ; try lia.
      eapply NewVarC_ext_proc in H0 as (μ'' & p''' & eq'' & eq''') ; simpl; subst ; try lia.
      exists (p''' ‖  p''). split; eauto.
    - eapply Hp in H as (p'' & eq'') ; simpl; subst ; try lia.
      exists (p'' ‖  p2). split; eauto.
    - eapply Hp in H as (p'' & eq'') ; simpl; subst ; try lia.
      exists (p1 ‖  p''). split; eauto.
  * inversion H.
  * inversion H ; subst. exists (pr_subst n p (rec n • p)).
    rewrite<- pr_subst_and_NewVarC. simpl; eauto.
  * dependent destruction H; simpl in *.
    - eapply Hp in H0 as (p'' & eq'') ; simpl; subst ; try lia.
      exists p''. split; eauto.
    - eapply Hp in H0 as (p'' & eq'') ; simpl; subst ; try lia.
      exists p''. split; eauto.
  * dependent destruction H; simpl in *.
    eapply Hp in H as (p'' & eq'') ; simpl; subst ; try lia.
    exists (ν p''). simpl ; eauto.
  * destruct g; simpl in *.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H; subst. exists p. auto.
    - dependent destruction H; simpl in *.
      + assert (lts (NewVarC k (g g1)) τ q) as Hyp; eauto.
        eapply Hp in Hyp as (p'' & eq'') ; simpl; subst ; try lia.
        exists p''. split; eauto.
      + assert (lts (NewVarC k (g g2)) τ q) as Hyp; eauto.
        eapply Hp in Hyp as (p'' & eq'') ; simpl; subst ; try lia.
        exists p''. split; eauto.
Qed.

Lemma NewVarC_ext_proc_rev p μ' p' k : lts (NewVarC k p) (ActExt (NewVarC_in_ext k μ')) (NewVarC k p') -> 
lts p (ActExt μ') p'.
Proof.
  revert μ' k p'.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  * dependent destruction H; simpl in *; subst.
    - assert (lts (NewVarC k p1) (ActExt (NewVarC_in_ext k μ')) p3) ; eauto.
      eapply NewVarC_ext_proc in H as (μ'' & p'' & eq' & eq''); subst.
      eapply Hp in H0; try lia. assert (NewVarC k (p'' ‖ p2) = NewVarC k p') as Hyp'; eauto.
      eapply NewVarC_inj in Hyp'. subst. eapply lts_parL. eauto.
    - assert (lts (NewVarC k p2) (ActExt (NewVarC_in_ext k μ')) q2) ; eauto.
      eapply NewVarC_ext_proc in H as (μ'' & p'' & eq' & eq''); subst. eapply Hp in H0; try lia.
      assert (NewVarC k (p1 ‖ p'') = NewVarC k p') as Hyp'; eauto.
      eapply NewVarC_inj in Hyp'. subst. eapply lts_parR. eauto.
  * inversion H.
  * inversion H.
  * dependent destruction H; simpl in *.
    - eapply lts_ifOne; eauto. eapply Hp; simpl; eauto. lia.
    - eapply lts_ifZero; eauto. eapply Hp; simpl; eauto. lia.
  * dependent destruction H; simpl in *. rewrite NewVarCzero_and_add in H. assert (0 + k = k)%nat as eq by lia.
    rewrite<- eq in H at 2. rewrite NewVarC_and_NewVarC_in_ChannelData in H. simpl in *.
    assert (lts (NewVarC (S k) p) (ActExt (NewVarC_in_ext (S k) (NewVarC_in_ext 0 μ'))) p'0) ;eauto.
    eapply NewVarC_ext_proc in H as (μ'' & p'' & eq1 & eq2). subst.
    eapply NewVarC_in_ext_inv in eq1. subst. assert (NewVarC k (ν p'') = NewVarC k p'); eauto.
    eapply NewVarC_inj in H. subst. eapply lts_res_ext. eapply Hp in H0; try lia. rewrite NewVarCzero_and_add. eauto.
  * destruct g; simpl in *.
    - inversion H.
    - inversion H.
    - inversion H; subst. assert (NewVarC_in_ext k (ActIn ((c , v))) = NewVarC_in_ext k μ') as Hyp; eauto.
      eapply NewVarC_in_ext_inv in Hyp. subst. rewrite subst_and_NewVarC in H4.
      eapply NewVarC_inj in H4. subst. eapply lts_input.
    - inversion H; subst. assert (NewVarC_in_ext k (ActOut (c , v)) = NewVarC_in_ext k μ') as Hyp; eauto.
      eapply NewVarC_in_ext_inv in Hyp. subst.
      eapply NewVarC_inj in H5. subst. eapply lts_output.
    - inversion H.
    - dependent destruction H; simpl in *.
      + assert (lts (NewVarC k (g g1)) (ActExt (NewVarC_in_ext k μ')) (NewVarC k p')); eauto.
        eapply Hp in H0; simpl; try lia. eapply lts_choiceL. eauto.
      + assert (lts (NewVarC k (g g2)) (ActExt (NewVarC_in_ext k μ')) (NewVarC k p')); eauto.
        eapply Hp in H0; simpl; try lia. eapply lts_choiceR. eauto.
Qed.

Lemma NewVarC_tau_proc_rev p p' k : lts (NewVarC k p) τ (NewVarC k p') -> 
lts p τ p'.
Proof.
  revert k p'.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  * dependent destruction H; simpl in *; subst.
    - assert (lts (NewVarC k p1) (((c , v)) !) p3); eauto. assert (lts (NewVarC k p2) (((c , v)) ?) q2); eauto.
      eapply NewVarC_ext_proc in H as (μ' & p'' & eq1 & eq2); subst.
      eapply NewVarC_ext_proc in H0 as (μ'' & p''' & eq'1 & eq'2); subst.
      rewrite eq1 in H1. rewrite eq'1 in H2.
      eapply NewVarC_ext_proc_rev in H1.
      eapply NewVarC_ext_proc_rev in H2.
      assert (NewVarC k (p'' ‖ p''') = NewVarC k p'); eauto.
      eapply NewVarC_inj in H. subst. eapply NewVarC_in_ext_rev_Output in eq1 as (c' & v' & eq'' & eq''' & eq'''').
      subst. eapply NewVarC_in_ext_rev_Input in eq'1 as (c'' & v'' & eq'' & eq''' & eq'''').
      subst. eapply NewVar_in_ChannelData_inj in eq''''. subst. eapply lts_comL; eauto.
    - assert (lts (NewVarC k p2) (((c , v)) !) p3); eauto. assert (lts (NewVarC k p1) (((c , v)) ?) q2); eauto.
      eapply NewVarC_ext_proc in H as (μ' & p'' & eq1 & eq2); subst.
      eapply NewVarC_ext_proc in H0 as (μ'' & p''' & eq'1 & eq'2); subst.
      rewrite eq1 in H1. rewrite eq'1 in H2.
      eapply NewVarC_ext_proc_rev in H1.
      eapply NewVarC_ext_proc_rev in H2.
      assert (NewVarC k (p''' ‖ p'') = NewVarC k p'); eauto.
      eapply NewVarC_inj in H. subst. eapply NewVarC_in_ext_rev_Output in eq1 as (c' & v' & eq'' & eq''' & eq'''').
      subst. eapply NewVarC_in_ext_rev_Input in eq'1 as (c'' & v'' & eq'' & eq''' & eq'''').
      subst. eapply NewVar_in_ChannelData_inj in eq''''. subst. eapply lts_comR; eauto.
    - assert (lts (NewVarC k p1) τ p3); eauto. assert (exists p', p3 = NewVarC k p') as (p'1 & eq); subst.
      { eapply inversion_NewVarC_par. eauto. } assert (NewVarC k (p'1 ‖ p2) = NewVarC k p'); eauto.
      eapply NewVarC_inj in H1; subst. eapply lts_parL. eapply Hp; eauto. simpl; lia.
    - assert (lts (NewVarC k p2) τ q2); eauto. assert (exists p', q2 = NewVarC k p') as (p'1 & eq); subst.
      { eapply inversion_NewVarC_par2. eauto. } assert (NewVarC k (p1 ‖ p'1) = NewVarC k p'); eauto.
      eapply NewVarC_inj in H1; subst. eapply lts_parR. eapply Hp; eauto. simpl; lia.
  * inversion H.
  * dependent destruction H; simpl in *. replace (rec n • NewVarC k p) with (NewVarC k (rec n •  p)) in x; eauto.
    rewrite pr_subst_and_NewVarC in x. eapply NewVarC_inj in x. subst. constructor.
  * dependent destruction H; simpl in *.
    - eapply lts_ifOne; eauto. eapply Hp; simpl; eauto. lia.
    - eapply lts_ifZero; eauto. eapply Hp; simpl; eauto. lia.
  * dependent destruction H; simpl in *.
    assert (lts (NewVarC (S k) p) τ p'0); eauto.
    eapply NewVarC_tau_proc in H as (p'' & eq); subst.
    assert (NewVarC k (ν p'') = NewVarC k p') as Hyp; eauto.
    eapply NewVarC_inj in Hyp. subst. eapply lts_res_tau. eapply Hp; eauto.
  * destruct g; simpl in *.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
    - dependent destruction H; simpl in *. eapply NewVarC_inj in x. subst. constructor.
    - dependent destruction H; simpl in *.
      + assert (lts (NewVarC k (g g1)) τ (NewVarC k p')); eauto. eapply lts_choiceL. eapply Hp; simpl; eauto. lia.
      + assert (lts (NewVarC k (g g2)) τ (NewVarC k p')); eauto. eapply lts_choiceR. eapply Hp; simpl; eauto. lia.
Qed.

(** ******* p 'is equivalent some r 'and r performs α to q , the congruence and the Transition can be reversed : *)
Lemma Congruence_Respects_Transition  : forall p q α, sc_then_lts p α q -> lts_then_sc p α q.
Proof. 
(** ******* by induction on the congruence and the step then...*)
  intros p q α (p' & hcgr & l).
  revert q α l.
  dependent induction hcgr.
  - dependent induction H. 
(** ******* reasonning about all possible cases due to the structure of terms *)
    + intros. exists q.  split.  exact l. reflexivity.
    + intros. exists q0.  split. eapply lts_ifOne; eauto. reflexivity.
    + intros. dependent destruction l.
      -- exists p'. split; eauto. reflexivity.
      -- eauto. rewrite H in H0. inversion H0.
    + intros. exists q0.  split. eapply lts_ifZero; eauto. reflexivity.
    + intros. dependent destruction l.
      -- eauto. rewrite H in H0. inversion H0.
      -- exists q'. split; eauto. reflexivity.
    + intros. exists (q ‖ 𝟘). split. apply lts_parL. assumption. auto with cgr (*par contexte parallele*). 
    + intros. dependent destruction l. inversion l2. inversion l1. exists p2. split. exact l. auto with cgr. 
      inversion l.
    + intros. dependent destruction l.
      -- exists (q2 ‖ p2). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). exact l1. exact l2. auto with cgr.
      -- exists (p2 ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). exact l1. exact l2. auto with cgr.
      -- exists (p ‖ p2). split. apply lts_parR. assumption. auto with cgr.
      -- exists (q2 ‖ q). split. apply lts_parL. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l2. 
         * exists ((p2 ‖ p0) ‖ r). split.
           apply lts_parL. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). assumption. assumption. auto with cgr.
         * exists ((p2 ‖ q) ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). apply lts_parL. assumption. assumption.
           apply cgr_par_assoc.
      -- dependent destruction l1. 
         * exists ((q2 ‖ p2) ‖ r). split. apply lts_parL. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption.
           assumption. auto with cgr.
         * exists ((q2 ‖ q) ‖ q0). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption. apply lts_parL.
           assumption. auto with cgr.
      -- exists ((p2 ‖ q) ‖ r). split. apply lts_parL. apply lts_parL. assumption. auto with cgr.
      -- dependent destruction l.
         * exists ((p ‖ p2) ‖ q2). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). apply lts_parR. assumption. assumption.
           auto with cgr.
         * exists ((p ‖ q2) ‖ p2). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption. apply lts_parR.
           assumption. auto with cgr.
         * exists ((p ‖ p2) ‖ r). split. apply lts_parL. apply lts_parR. assumption. auto with cgr.
         * exists ((p ‖ q) ‖ q2). split. apply lts_parR. assumption. auto with cgr.
    + intros. dependent destruction l.
      -- dependent destruction l1. 
         * exists (p2 ‖ (q ‖ q2)). split.
           eapply lts_comL. instantiate (1:= v). instantiate (1:= c). assumption. apply lts_parR. assumption. auto with cgr.
         * exists (p ‖ (q0 ‖ q2)). split. apply lts_parR. eapply lts_comL. instantiate (1:= v). instantiate (1:= c). assumption.
           assumption. auto with cgr.
      -- dependent destruction l2. 
         * exists (p0 ‖ (q ‖ p2)). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). apply lts_parR. assumption.
           assumption. auto with cgr.
         * exists (p ‖ (q2 ‖ p2)). split. apply lts_parR.  eapply lts_comR. instantiate (1:= v). instantiate (1:= c). assumption.
           assumption. auto with cgr.
      -- dependent destruction l.
         * exists (p2 ‖ (q2 ‖ r)). split. eapply lts_comL. instantiate (1:= v). instantiate (1:= c).  assumption. apply lts_parL.
           assumption. auto with cgr.
         * exists (q2 ‖ (p2 ‖ r)). split. eapply lts_comR. instantiate (1:= v). instantiate (1:= c). apply lts_parL. assumption.
           assumption. auto with cgr.
         * exists (p2 ‖ ( q ‖ r)). split. apply lts_parL. assumption. auto with cgr.
         * exists (p ‖ (q2 ‖ r)). split. apply lts_parR. apply lts_parL. assumption. auto with cgr.
      -- exists (p ‖ (q ‖ q2)). split. apply lts_parR.  auto. apply lts_parR. assumption. auto with cgr.
    + intros. inversion l.
    + intros. inversion l; subst.
      -- inversion H0.
      -- inversion H0.
    + intros. dependent destruction l.
      -- dependent destruction l. exists ((ν (ν VarSwap_in_proc 0 p'))). split.
         eapply lts_res_ext. eapply lts_res_ext. rewrite VarC_action_add_add in l. simpl in *.
         eapply VarSwap_swap_proc in l. rewrite VarC_action_add_add. simpl in *. eauto. eapply cgr_res_swap_rev.
      -- dependent destruction l. exists ((ν (ν VarSwap_in_proc 0 p'))). split. eapply lts_res_tau.
         eapply lts_res_tau. eapply VarSwap_swap_tau_proc. eauto. eapply cgr_res_swap_rev.
    + intros. dependent destruction l.
      -- dependent destruction l. exists ((ν (ν VarSwap_in_proc 0 p'))). split.
         eapply lts_res_ext. eapply lts_res_ext. rewrite VarC_action_add_add. simpl.
         eapply VarSwap_swap_proc. rewrite VarSwap_in_proc_invol. rewrite VarC_action_add_add in l. simpl in *.
         eauto. eapply cgr_res_swap_rev.
      -- dependent destruction l. exists ((ν (ν VarSwap_in_proc 0 p'))). split. eapply lts_res_tau.
         eapply lts_res_tau. eapply VarSwap_swap_tau_proc. rewrite VarSwap_in_proc_invol. eauto. eapply cgr_res_swap_rev.
    + intros. dependent destruction l.
      -- inversion l1; subst. simpl in *. eapply (NewVarC_preserves_transition 0) in l2.
         rewrite NewVarCzero_and_add_Channel in H1. simpl in *.
         exists (ν (p' ‖ (NewVarC 0 q2))). split. eapply lts_res_tau.
         eapply lts_comL; eauto. eapply cgr_res_scope.
      -- inversion l2; subst. simpl in *. eapply (NewVarC_preserves_transition 0) in l1. simpl in *.
         exists (ν (p' ‖ (NewVarC 0 p2))). split. eapply lts_res_tau.
         eapply lts_comR; eauto. eapply cgr_res_scope.
      -- dependent destruction l.
         * exists (ν (p' ‖ NewVarC 0 q)). split. eapply lts_res_ext. eapply lts_parL. eauto.
           eapply cgr_res_scope.
         * exists (ν (p' ‖ NewVarC 0 q)). split. eapply lts_res_tau. eapply lts_parL. eauto.
           eapply cgr_res_scope.
      -- exists (ν (p ‖ NewVarC 0 q2)). destruct α.
         * split. eapply lts_res_ext. eapply lts_parR. replace (NewVarC 0 q) with (NewVarCn 0 1 q); eauto.
           replace (NewVarC 0 q2) with (NewVarCn 0 1 q2); eauto. eapply NewVarC_preserves_transition. eauto.
           eapply cgr_res_scope.
         * split. eapply lts_res_tau. eapply lts_parR. replace (NewVarC 0 q) with (NewVarCn 0 1 q); eauto.
           replace (NewVarC 0 q2) with (NewVarCn 0 1 q2); eauto. eapply NewVarC_preserves_reduction. eauto.
           eapply cgr_res_scope.
    + intros. dependent destruction l.
      -- dependent destruction l.
         * exists (ν p2 ‖ q). split. eapply lts_parL. eapply lts_res_ext. eauto. eapply cgr_res_scope_rev.
         * rewrite NewVarCzero_and_add in l. assert (exists q'2, q2 = NewVarC 0 q'2) as (q'2 & eq). 
           { eapply NewVarC_ext_proc in l as (μ' & p'' & eq1 & eq2).
             subst. exists p''. eauto. } subst.
           assert (lts q (ActExt μ) q'2). { eapply NewVarC_ext_proc_rev. eauto. }
           exists (ν p ‖ q'2). split. eapply lts_parR. eauto.
           eapply cgr_res_scope_rev.
      -- dependent destruction l.
         * assert (lts (NewVarC 0 q) (((c , v)) ?) q2) ;eauto.
           eapply NewVarC_ext_proc in l2 as (μ' & p'' & eq1 & eq2); subst.
           rewrite eq1 in H. eapply NewVarC_in_ext_rev_Input in eq1 as (c' & v' & eq' & eq'' & eq'''); subst.
           simpl in *. exists ((ν p2) ‖ p''). split. eapply lts_comL. eapply lts_res_ext. rewrite NewVarCzero_and_add.
           eauto. eapply NewVarC_ext_proc_rev; eauto. eapply cgr_res_scope_rev.
         * assert (lts (NewVarC 0 q) (((c , v)) !) p2) ;eauto.
           eapply NewVarC_ext_proc in l1 as (μ' & p'' & eq1 & eq2); subst.
           rewrite eq1 in H. eapply NewVarC_in_ext_rev_Output in eq1 as (c' & v' & eq' & eq'' & eq'''); subst.
           simpl in *. exists ((ν q2) ‖ p''). split. eapply lts_comR. eapply NewVarC_ext_proc_rev; eauto.
           eapply lts_res_ext. rewrite NewVarCzero_and_add.
           eauto. eapply cgr_res_scope_rev.
         * exists ((ν p2) ‖ q). split. eapply lts_parL. eapply lts_res_tau. eauto.
           eapply cgr_res_scope_rev.
         * assert (lts (NewVarC 0 q) τ q2); eauto. eapply NewVarC_tau_proc in l as (q'' & eq''); subst.
           eapply NewVarC_tau_proc_rev in H. exists ((ν p) ‖ q''). split.
           eapply lts_parR. eauto. eapply cgr_res_scope_rev.
    + intros. exists q.  split. apply lts_choiceL. assumption. auto with *.
    + intros. dependent destruction l.
      -- exists q. split. assumption. auto with *.
      -- inversion l.
    + intros. dependent destruction l.
      -- exists q0. split. apply lts_choiceR. assumption. auto with *.
      -- exists q0. split. apply lts_choiceL. assumption. auto with *.
    + intros. dependent destruction l.
      -- exists q0. split. apply lts_choiceL. apply lts_choiceL. assumption. auto with *.
      -- dependent destruction l.
         * exists q0. split. apply lts_choiceL. apply lts_choiceR. assumption. auto with *.
         * exists q0. split. apply lts_choiceR. assumption. auto with *.
    + intros. dependent destruction l.
      -- dependent destruction l.
         * exists q0. split. apply lts_choiceL. assumption. auto with *.
         * exists q0. split. apply lts_choiceR. apply lts_choiceL. assumption. auto with *.
      -- exists q0. split. apply lts_choiceR. apply lts_choiceR. assumption. auto with *.
    + intros. dependent destruction l. exists (pr_subst x p (rec x • p)). split. apply lts_recursion. 
      apply cgr_subst. assumption.
    + intros. dependent destruction l. exists p.  split. apply lts_tau.
      constructor. assumption.
    + intros. dependent destruction l. exists (p^v). split. apply lts_input.
      apply Congruence_Respects_Substitution. constructor. apply H.
    + intros. dependent destruction l. exists p. split. apply lts_output. 
      constructor. assumption.
    + intros. dependent destruction l.
      -- destruct (IHcgr_step eq_refl p2 (((c , v)) ! )).  exact l1. destruct H0. exists (x ‖ q2).
          split. eapply lts_comL. exact H0. assumption.
          apply cgr_fullpar. assumption. reflexivity.
      -- destruct (IHcgr_step eq_refl q2 (((c , v)) ?)). assumption. destruct H0. exists (x ‖ p2).
          split.  eapply lts_comR. exact l1. assumption.
          apply cgr_fullpar. assumption. reflexivity.
      -- destruct (IHcgr_step eq_refl p2 α). assumption. destruct H0. eexists.
          split. instantiate (1:= (x ‖ r)). apply lts_parL. assumption. apply cgr_fullpar.
          assumption. reflexivity.
      -- eexists. split. instantiate (1:= (p ‖ q2)). apply lts_parR.
          assumption. apply cgr_par.
          constructor. assumption.
    + intros. inversion l; subst.
      -- destruct (IHcgr_step eq_refl p' (ActExt (VarC_action_add 1 μ))) as (q'1 & l' & equiv'). eauto.
         exists (ν q'1). split; eauto. eapply lts_res_ext. eauto. eapply cgr_res. eauto.
      -- destruct (IHcgr_step eq_refl p' τ) as (q'1 & l' & equiv'). eauto. exists (ν q'1). split.
         eapply lts_res_tau. eauto. eapply cgr_res. eauto.
    + intros. dependent destruction l.
      -- eexists. split. instantiate (1:= p'). apply lts_ifOne; eauto. reflexivity.
      -- destruct (IHcgr_step eq_refl q'0 α) as (q'1 & l' & equiv'). eauto.
         eexists. split. apply lts_ifZero; eauto. eauto.
    + intros. dependent destruction l.
      -- destruct (IHcgr_step eq_refl p'0 α) as (p'1 & l' & equiv'). eauto.
         eexists. split. apply lts_ifOne; eauto. eauto.
      -- eexists. split. instantiate (1:= q'). apply lts_ifZero; eauto. reflexivity.
    + intros. dependent destruction l.
      -- destruct (IHcgr_step eq_refl q α). assumption. destruct H0. exists x. split. apply lts_choiceL. assumption. assumption.
      -- eexists. instantiate (1:= q). split. apply lts_choiceR. assumption. reflexivity.
  - intros. destruct (IHhcgr2 eq_refl q α). assumption. destruct (IHhcgr1 eq_refl x0 α). destruct H. assumption. exists x1. split. destruct H0. assumption.
    destruct H. destruct H0. eauto with *.
Qed.

Lemma lts_res_ext_n n p p' μ : lts p (ActExt (VarC_action_add n μ)) p' -> lts (Ѵ  n p) (ActExt μ) (Ѵ  n p').
Proof.
  revert p p' μ.
  induction n.
  + simpl; eauto. intros. rewrite VarC_add_zero_ext in H. eauto.
  + intros. simpl in *. eapply lts_res_ext. eapply IHn. replace (S n) with (n + 1)%nat in H by lia.
    rewrite VarC_action_add_add; eauto.
Qed.

Lemma lts_res_tau_n n p p' : lts p τ p' -> lts (Ѵ  n p) τ (Ѵ  n p').
Proof.
  revert p p'.
  induction n.
  + simpl; eauto.
  + intros. simpl in *. eapply lts_res_tau. eapply IHn. eauto.
Qed.

(** ******* One side of the Harmony Lemma *)
Lemma Reduction_Implies_TausAndCong : forall P Q, (sts P Q) -> (lts_then_sc P τ Q).
Proof. 
intros P Q Reduction. 
assert ((exists c v P1 P2 G1 G2 S n, ((P ≡* Ѵ  n ((((c ! v • P1) + G1) ‖ ((c ? • P2) + G2)) ‖ S))) /\ (Q ≡* Ѵ  n ((P1 ‖ (P2^v)) ‖ S)))
\/ (exists P1 G1 S n, (P ≡* Ѵ  n (((𝛕 • P1) + G1) ‖ S)) /\ (Q ≡* Ѵ  n (P1 ‖ S)))
\/ (exists n P1 S n', (P ≡* Ѵ  n' ((rec n • P1) ‖ S)) /\ (Q ≡* Ѵ  n' (pr_subst n P1 (rec n • P1) ‖ S)))
). 
apply ReductionShape. exact Reduction.
destruct H as [IH|[IH|IH]];  decompose record IH. 

(** ******* First case τ by communication *)

- assert (lts (Ѵ x6 (((x ! x0 • x1) + x3) ‖ ((x ? • x2) + x4) ‖ x5)) τ (Ѵ x6 (x1 ‖ (x2^x0) ‖ x5))).
  * eapply lts_res_tau_n.
    apply lts_parL.   
    eapply lts_comL. apply lts_choiceL. instantiate (2:= x). instantiate (1:= x0).
    apply lts_output. apply lts_choiceL. apply lts_input.
  * assert (sc_then_lts P τ (Ѵ x6 ((x1 ‖ x2^x0) ‖ x5))). exists ((Ѵ x6 (((x ! x0 • x1 + x3) ‖ (gpr_input x x2 + x4)) ‖ x5))). split. assumption. assumption.
    assert (lts_then_sc P τ (Ѵ x6 ((x1 ‖ x2^x0) ‖ x5))). apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3.
    exists x7. split. assumption. apply transitivity with (Ѵ x6 ((x1 ‖ x2^x0) ‖ x5)). assumption. symmetry. assumption.

(** ******* Second case τ by Tau Action *)

- assert (lts (Ѵ x2 ((𝛕 • x + x0) ‖ x1)) τ (Ѵ x2 (x ‖ x1))). eapply lts_res_tau_n. constructor.
  apply lts_choiceL. apply lts_tau.
  assert (sc_then_lts P τ (Ѵ x2 (x ‖ x1))). exists (Ѵ x2 ((𝛕 • x + x0) ‖ x1)). split. assumption.
  eapply lts_res_tau_n. apply lts_parL. apply lts_choiceL. apply lts_tau.
  assert (lts_then_sc P τ (Ѵ x2 (x ‖ x1))). apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3. 
  exists x3. split. assumption. apply transitivity with (Ѵ x2 (x ‖ x1)). assumption. symmetry. assumption.

(** ******* Third case τ by recursion *)

- assert (lts (Ѵ x2 (rec x • x0 ‖ x1)) τ (Ѵ x2 (pr_subst x x0 (rec x • x0) ‖ x1))). eapply lts_res_tau_n.
  constructor. apply lts_recursion. assert (sc_then_lts P τ (Ѵ x2 ((pr_subst x x0 (rec x • x0) ‖ x1)))). 
  exists (Ѵ x2 (rec x • x0 ‖ x1)). split. assumption. assumption.
  assert (lts_then_sc P τ (Ѵ x2 (pr_subst x x0 (rec x • x0) ‖ x1))). 
  apply Congruence_Respects_Transition. assumption. destruct H3. destruct H3. 
  exists x3. split. assumption. apply transitivity with (Ѵ x2 (pr_subst x x0 (rec x • x0) ‖ x1)). assumption.
  symmetry. assumption.
Qed.


(** ******* Some lemmas for multiple parallele processes to simplify the statements of proof *)
Lemma InversionParallele : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (P ‖ R) ‖ (Q ‖ S) . 
Proof. 
intros.
apply transitivity with (((P ‖ Q) ‖ R) ‖ S). apply cgr_par_assoc_rev.
apply transitivity with ((P ‖ (Q ‖ R)) ‖ S). apply cgr_par. apply cgr_par_assoc.
apply transitivity with (((Q ‖ R) ‖ P) ‖ S). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ‖ R) ‖ (P ‖ S)). apply cgr_par_assoc.
apply transitivity with ((R ‖ Q) ‖ (P ‖ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with (((R ‖ Q) ‖ P) ‖ S). apply cgr_par_assoc_rev.
apply transitivity with ((P ‖ (R ‖ Q)) ‖ S). apply cgr_par. apply cgr_par_com.
apply transitivity with (((P ‖ R) ‖ Q) ‖ S). apply cgr_par. apply cgr_par_assoc_rev.
apply transitivity with ((P ‖ R) ‖ (Q ‖ S)). apply cgr_par_assoc.
reflexivity. 
Qed.
Lemma InversionParallele2 : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (R ‖ P) ‖ (S ‖ Q).
Proof.
intros. 
apply transitivity with ((P ‖ R) ‖ (Q ‖ S)). apply InversionParallele.
apply transitivity with ((R ‖ P) ‖ (Q ‖ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ‖ S) ‖ (R ‖ P)). apply cgr_par_com.
apply transitivity with ((S ‖ Q) ‖ (R ‖ P)). apply cgr_par. apply cgr_par_com.
apply cgr_par_com.
Qed.
Lemma InversionParallele3 : forall P Q R S, (P ‖ Q) ‖ (R ‖ S) ≡* (R ‖ Q) ‖ (P ‖ S).
Proof.
intros.
apply transitivity with ((Q ‖ P) ‖ (R ‖ S)). apply cgr_par. apply cgr_par_com.
apply transitivity with ((Q ‖ R) ‖ (P ‖ S)). apply InversionParallele. apply cgr_par. apply cgr_par_com.
Qed.

(** ******* The More Stronger Harmony Lemma (in one side) is more stronger *)
Lemma Congruence_Simplicity : (forall α , ((forall P Q, (((lts P α Q) -> (sts P Q)))) 
-> (forall P Q, ((lts_then_sc P α Q) -> (sts P Q))))).
Proof.
intros. destruct H0. destruct H0. eapply sts_cong. instantiate (1:=P). apply cgr_refl. instantiate (1:=x). apply H. exact H0. 
exact H1.
Qed.

Lemma sts_res_n n P Q : sts P Q → sts (Ѵ n P) (Ѵ n Q).
Proof.
  revert P Q. induction n.
  + intros; simpl; eauto.
  + intros; simpl. eapply sts_res. eauto.
Qed.

Lemma Taus_Implies_Reduction : forall P Q, (lts P τ Q) -> (sts P Q).
Proof. 
intros.
dependent induction H.
  - eapply sts_cong.  instantiate (1:=  ((𝛕 • P) + 𝟘)). apply cgr_choice_nil_rev. instantiate (1:=P).
    apply sts_tau. constructor. constructor.
  - apply sts_recursion.
  - eapply sts_cong.
    + eapply cgr_if_true; eauto.
    + eauto.
    + reflexivity.
  - eapply sts_cong.
    + eapply cgr_if_false; eauto.
    + eauto.
    + reflexivity.
  - eapply sts_res. eauto.
  - destruct (TransitionShapeForOutput p1 p2 c v). assumption. decompose record H1.
    destruct (TransitionShapeForInput q1 q2 c v). assumption. decompose record H4.
    eapply sts_cong. etrans. instantiate (1:= Ѵ x2 ((VarC_add x2 c ! v • x + x0) ‖ x1) ‖ Ѵ x6 ((gpr_input (VarC_add x6 c) x3 + x4) ‖ x5)).
    eapply cgr_fullpar; eauto. etrans. eapply cgr_res_scope_n. rewrite NewVarCn_res. etrans.
    eapply cgr_res_n. eapply cgr_par_com. etrans. eapply cgr_res_n. eapply cgr_res_scope_n. etrans.
    eapply cgr_res_n. etrans. eapply cgr_res_n. simpl. rewrite simpl_NewVarCn_par_plus.
    rewrite simpl_NewVarCn_plus_par. etrans. 
    instantiate (1 := ((VarC_add (x6 + x2) c ! v • NewVarCn 0 x6 x + gNewVarCn 0 x6 x0) ‖ NewVarCn x6 x2 x5) ‖
           ((gpr_input (VarC_add (x6 + x2) c) (NewVarCn x6 x2 x3) + gNewVarCn x6 x2 x4) ‖ NewVarCn 0 x6 x1)). etrans.
    apply InversionParallele. etrans. 
    instantiate (1:= ((VarC_add (x6 + x2) c ! v • NewVarCn 0 x6 x + gNewVarCn 0 x6 x0)
        ‖ (gpr_input (VarC_add (x6 + x2) c) (NewVarCn x6 x2 x3) + gNewVarCn x6 x2 x4))
        ‖ (NewVarCn x6 x2 x5 ‖ NewVarCn 0 x6 x1)). apply cgr_fullpar; eauto. eapply cgr_par_com. reflexivity.
    apply InversionParallele. apply InversionParallele. reflexivity. reflexivity.
    eapply sts_res_n. eapply sts_res_n. eapply sts_par. eapply sts_com. symmetry. etrans.
    eapply cgr_fullpar; eauto. etrans. eapply cgr_res_scope_n. eapply cgr_res_n.
    etrans. rewrite NewVarCn_res. eapply cgr_par_com. etrans. eapply cgr_res_scope_n.
    eapply cgr_res_n. simpl. rewrite NewVarCn_par. rewrite NewVarCn_par. rewrite subst_and_NewVarCn.
    etrans. eapply InversionParallele. eapply cgr_fullpar. eapply cgr_par_com. reflexivity.
  - destruct (TransitionShapeForOutput p1 p2 c v). assumption. decompose record H1.
    destruct (TransitionShapeForInput q1 q2 c v). assumption. decompose record H4.
    eapply sts_cong. etrans. instantiate (1:= Ѵ x6 ((gpr_input (VarC_add x6 c) x3 + x4) ‖ x5) ‖ Ѵ x2 ((VarC_add x2 c ! v • x + x0) ‖ x1)).
    eapply cgr_fullpar; eauto. etrans. eapply cgr_res_scope_n. rewrite NewVarCn_res. etrans.
    eapply cgr_res_n. eapply cgr_par_com. etrans. eapply cgr_res_n. eapply cgr_res_scope_n. etrans.
    eapply cgr_res_n. etrans. eapply cgr_res_n. simpl. rewrite NewVarCn_par. rewrite NewVarCn_par.
    rewrite NewVarCn_choice. rewrite NewVarCn_choice. rewrite NewVarCn_input. rewrite NewVarCn_output.
    apply InversionParallele. eapply cgr_res_n. reflexivity. etrans. eapply cgr_res_n. eapply cgr_res_n.
    reflexivity. eapply cgr_res_n. eapply cgr_res_n. reflexivity. eapply sts_res_n. eapply sts_res_n.
    eapply sts_par. replace (x6 + x2)%nat with (x2 + x6)%nat by lia. eapply sts_com. symmetry.
    etrans. eapply cgr_fullpar; eauto. etrans. eapply cgr_res_scope_n. eapply cgr_res_n.
    rewrite NewVarCn_res. etrans. eapply cgr_par_com. etrans. eapply cgr_res_scope_n.
    eapply cgr_res_n. simpl. rewrite NewVarCn_par. rewrite NewVarCn_par.
    rewrite<- subst_and_NewVarCn. etrans. apply InversionParallele. reflexivity.
  - apply sts_par. apply IHlts. reflexivity.
  - eapply sts_cong. instantiate (1:= q1 ‖ p). apply cgr_par_com. instantiate (1:= q2 ‖ p).
    apply sts_par. apply IHlts. reflexivity. apply cgr_par_com.
  - destruct (TransitionShapeForTauAndGuard (g p1) q). split. assumption. exists p1. reflexivity.
    decompose record H0.
    eapply sts_cong. instantiate (1:= ((𝛕 • x) + (x0 + p2))).
    apply transitivity with (g (((𝛕 • x) + x0) + p2)). apply cgr_choice. assumption. apply cgr_choice_assoc.
    instantiate (1:= x). apply sts_tau. symmetry. assumption.
  - destruct (TransitionShapeForTauAndGuard (g p2) q). split. assumption. exists p2. reflexivity.
    decompose record H0. eapply sts_cong. instantiate (1:= ((𝛕 • x) + (x0 + p1))).
    apply transitivity with (g (((𝛕 • x) + x0 ) + p1)). apply transitivity with (g (p2 + p1)). apply cgr_choice_com.
    apply cgr_choice. assumption. apply cgr_choice_assoc. instantiate (1:= x). apply sts_tau.
    symmetry. assumption.
Qed.

(** ******* One side of the Harmony Lemma *)
Lemma TausAndCong_Implies_Reduction: forall P Q, (lts_then_sc P τ Q) -> (sts P Q).
Proof.
intros P Q H.
apply Congruence_Simplicity with τ. exact Taus_Implies_Reduction. exact H.
Qed.

Theorem HarmonyLemmaForCCSWithValuePassing : forall P Q, (lts_then_sc P τ Q) <-> (sts P Q).
Proof.
intros. split.
* apply TausAndCong_Implies_Reduction.
* apply Reduction_Implies_TausAndCong.
Qed.

End VCCS_Harmony.