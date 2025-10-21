(*
   Copyright (c) 2024 Gaëtan Lopez <glopez@irif.fr>

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

From Coq Require ssreflect Setoid.
From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
Import ListNotations.
From Coq.Program Require Import Wf Equality.
From Coq.Wellfounded Require Import Inverse_Image.
From Coq.Logic Require Import JMeq ProofIrrelevance.

From stdpp Require Import base countable finite gmap list gmultiset strings.

From Must Require Import ActTau gLts VACCS_Instance VACCS_Good Bisimulation InputOutputActions 
        Completeness ParallelLTSConstruction InputOutputActions GeneralizeLtsOutputs.

Definition NewVar_in_label k (μ : ExtAct TypeOfActions) :=
match μ with 
| ActIn (c ⋉ d) => ActIn (c ⋉ (NewVar_in_Data k d))
| ActOut (c ⋉ d) => ActOut (c ⋉ (NewVar_in_Data k d))
end.

Fixpoint NewVar_in_trace k s :=
match s with
| [] => []
| a :: l => (NewVar_in_label k a) :: NewVar_in_trace k l
end.

Definition Succ_bvar_for k (X : Data) : Data :=
match X with
| cst v => cst v
| bvar i => bvar (i + k)
end.


Lemma Succ_bvar_and_NewVar_in_Data_0 : forall v, NewVar_in_Data 0 v = Succ_bvar v.
Proof.
intros. induction v; simpl; reflexivity.
Qed.


Lemma All_According_To_Data : forall k v d, (subst_Data k v (NewVar_in_Data k d) = d).
Proof.
intros. destruct d. 
- simpl. auto.
- simpl. destruct (decide (k < S n)). (* case decide. *)
  * simpl. destruct (decide (S n = k)) as [e | e].
    ** exfalso. dependent destruction l. eapply Nat.neq_succ_diag_l. exact e. 
       rewrite <-e in l. lia.
    ** destruct (decide (S n < k)). 
       *** lia.
       *** auto.
  * simpl. destruct (decide (n = k)).
    ** lia. 
    ** destruct n. 
      -- assert ( 0 < k). lia. destruct (decide (0 < k)). 
         *** auto. 
         *** exfalso. auto with arith.
      -- destruct (decide (S n < k)).
        *** auto.
        *** exfalso. lia.
Qed.

Lemma All_According_To_Eq : forall e k v, (subst_in_Equation k v (NewVar_in_Equation k e) = e).
Proof.
intros E. dependent induction E; intros.
- simpl. rewrite All_According_To_Data. rewrite All_According_To_Data. eauto.
Qed.

Lemma All_According : forall p k v, subst_in_proc k v (NewVar k p) = p.
Proof.
intros. revert v. revert k.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros. 
* simpl. assert (subst_in_proc k v (NewVar k p1) = p1) as eq1.
  { apply Hp. simpl. auto with arith. }
  assert (subst_in_proc k v (NewVar k p2) = p2) as eq2.
  { apply Hp. simpl. auto with arith. }
  rewrite eq1, eq2. auto.
* simpl. auto.
* simpl. assert (subst_in_proc k v (NewVar k p) = p).
  { apply Hp. simpl. auto with arith. }
  rewrite H. auto.
* simpl. rewrite All_According_To_Eq.
  assert (subst_in_proc k v (NewVar k p1) = p1) as eq1.
  { apply Hp. simpl. auto with arith. }
  assert (subst_in_proc k v (NewVar k p2) = p2) as eq2.
  { apply Hp. simpl. auto with arith. }
  rewrite eq1, eq2. auto.
* simpl. rewrite All_According_To_Data. reflexivity.
* destruct g.
  - simpl. auto.
  - simpl. auto.
  - simpl. assert (subst_in_proc (S k) (NewVar_in_Data 0 v) (NewVar (S k) p) = p) as eq.
    { apply Hp. simpl. auto with arith. }
    rewrite<- Succ_bvar_and_NewVar_in_Data_0. rewrite eq. auto.
  - simpl. assert (subst_in_proc k v (NewVar k p) = p) as eq.
    { apply Hp. simpl. auto with arith. }
    rewrite eq. auto.
  - simpl. assert (subst_in_proc k v (NewVar k (g g1)) = g g1) as eq1.
    { apply Hp. simpl. auto with arith. }
    assert (subst_in_proc k v (NewVar k (g g2)) = g g2) as eq2.
    { apply Hp. simpl. auto with arith. }
    dependent destruction eq1. dependent destruction eq2. rewrite x0, x. auto.
Qed.

Lemma Eval_simpl_true v : Eval_Eq (v == v) = Some true <-> v = v.
Proof.
  split.
  - intro e. inversion e. destruct v; rewrite decide_True in H0; eauto.
  - intro e. subst. simpl. destruct v; rewrite decide_True; eauto.
Qed.

Lemma Eval_simpl_false v1 v2 : v1 ≠ v2 ->  Eval_Eq (cst v1 == cst v2) = Some false.
Proof.
  - intro e. simpl. rewrite decide_False; eauto.
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

Fixpoint gen_test_raw Vs s p {struct s}:=
  match s with
  | [] => p
  | ActIn (c ⋉ d) :: s' => match Vs with
                            | [] => (g 𝟘)     (*whatever*)
                            | ActIn (c ⋉ d') :: s'' =>  (c ! d' • 𝟘) ‖ (gen_test_raw s'' s' p)
                            | ActOut (c ⋉ d') :: s'' => (g 𝟘)     (*whatever*)
                            end
  | ActOut (c ⋉ d) :: s' => match Vs with
                            | [] => 𝟘     (*whatever*)
                            | ActIn (c ⋉ d') :: s'' => (g 𝟘)
                            | ActOut (c ⋉ d') :: s'' => (c ? x • (If ( bvar 0 ==  NewVar_in_Data 0 d' )
                                   Then (gen_test_raw (NewVar_in_trace 0 s'') s' (NewVar 0 p))
                                   Else ①)) + (t • ①)
                            end
  end.

Definition gen_test s p := gen_test_raw s s p.

Lemma All_According_to_gen_test s s' d k p : subst_in_proc k d (gen_test_raw (NewVar_in_trace k s') s (NewVar k p)) = gen_test_raw s' s p.
Proof.
  revert d k p s'. induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s; intros; simpl in *.
  - eapply All_According.
  - destruct e as [ (*Input*) (c , v) | (*Output*) (c , v)].
    + case_eq s'.
      * intros. simpl. reflexivity.
      * intros. subst. simpl.
        case_eq (NewVar_in_label k e). intros.
        -- case_eq a. intros. subst. case_eq e.
           ++ intros. subst. inversion H. destruct a. simpl.
              inversion H1. subst. rewrite All_According_To_Data.
              assert (subst_in_proc k d (gen_test_raw (NewVar_in_trace k l) s (NewVar k p))
                  = gen_test_raw l s p) as eq1.
              { eapply Hlength; eauto with arith. }
              rewrite eq1. eauto.
           ++ intros. destruct a. subst. inversion H.
        -- intros. case_eq a. intros. subst. case_eq e.
           ++ intros. subst. inversion H. destruct a. inversion H1.
           ++ intros. subst. destruct a. simpl. reflexivity.
    + case_eq (NewVar_in_trace k s').
      * intros. case_eq s'.
        -- intros. subst. simpl. reflexivity.
        -- intros. subst. simpl. case_eq e.
           ++ intros. subst. destruct a. reflexivity.
           ++ intros. destruct a. subst. simpl in *. inversion H.
      * intros. case_eq e.
        -- intros. subst. destruct a. case_eq s'.
           ++ intros. subst. simpl. inversion H.
           ++ intros. case_eq e.
              ** intros. subst. destruct a. simpl. reflexivity.
              ** subst. intros. subst. simpl in *. destruct a. inversion H.
        -- intros. destruct a. subst. case_eq s'.
           ++ intros. subst. inversion H.
           ++ intros. subst. case_eq e.
              ** intros. subst. simpl in *. destruct a. inversion H.
              ** intros. destruct a. subst. simpl in H. inversion H. subst.
                 simpl. assert (k = 0+k)%nat as eq1 by eauto with arith.
                 assert (subst_Data (S k) (Succ_bvar d) (NewVar_in_Data 0 (NewVar_in_Data k d1)) 
                        = NewVar_in_Data 0 d1) as eq.
                 { rewrite eq1 at 2. rewrite<- New_Var_And_NewVar_in_Data.
                   simpl in *. eapply All_According_To_Data. }
                 rewrite eq. assert (subst_in_proc (S k) (Succ_bvar d) (gen_test_raw
                            (NewVar_in_trace 0 (NewVar_in_trace k l0)) s
                            (NewVar 0 (NewVar k p))) = gen_test_raw (NewVar_in_trace 0 l0) s (NewVar 0 p)) as eq2.
                 { rewrite eq1 at 3. rewrite<- New_Var_And_NewVar. rewrite eq1 at 2.
                   rewrite<- New_Var_And_NewVar_in_Trace. simpl in *.
                 { eapply Hlength; eauto with arith. } }
                 rewrite eq2. eauto.
Qed.

Lemma gen_test_lts_mu μ s p :
   (gen_test (μ :: s) p) ⟶⋍[co μ] (gen_test s p).
Proof.
  intros. destruct μ as [ (* Input *) (c , v) | (* Output *) (c , v) ].
  - simpl in *. exists (𝟘 ‖ gen_test s p). split.
    + unfold gen_test. simpl.
      constructor. constructor.
    + etrans. eapply cgr_par_com. eapply cgr_par_nil.
  - unfold gen_test. simpl in *.
    eexists. split.
    + eapply lts_choiceL. eapply lts_input.
    + simpl. rewrite All_According_To_Data.
      etrans. eapply cgr_if_true.
      * eapply Eval_simpl_true. eauto.
      * rewrite All_According_to_gen_test. reflexivity.
Qed.

Lemma gen_test_ungood_if p : ¬ good_VACCS p -> forall s, ¬ good_VACCS (gen_test s p).
Proof.
  unfold gen_test.
  intros nhp s nhg.
  induction s as [|μ s']; simpl in *.
  - contradiction.
  - destruct μ; destruct a; subst.
    + inversion nhg; subst. destruct H0. inversion H. contradiction.
    + inversion nhg; subst. destruct H0; inversion H.
Qed.

Lemma gen_test_gen_spec_out_lts_tau_ex s p :
  (exists q, lts p τ q) -> exists e, lts (gen_test s p) τ e.
Proof.
  unfold gen_test.
  intros hq. induction s; [| simpl; destruct a ].
  + eauto with ccs.
  + destruct a. simpl. destruct IHs. eexists; eauto with ccs.
  + destruct a. simpl. destruct IHs. eexists; eauto with ccs.
Qed.

Lemma gen_test_gen_spec_out_lts_tau_ex_inst a s p :
  exists e', lts (gen_test (ActOut a :: s) p) τ e'.
Proof. unfold gen_test. simpl. destruct a. eauto with ccs. Qed.

Lemma gen_test_gen_spec_out_lts_tau_good a s e p :
  lts (gen_test (ActOut a :: s) p) τ e -> good_VACCS e.
Proof.
  unfold gen_test. simpl. destruct a.
  inversion 1; subst; inversion H4; subst; eauto with ccs.
Qed.

Lemma gen_test_gen_spec_out_lts_mu_uniq e a s p :
  lts (gen_test (ActOut a :: s) p) (ActExt $ ActIn a) e -> e ≡ gen_test s p.
Proof.
  unfold gen_test. simpl. destruct a.
  intros. inversion H; subst; inversion H4; subst; eauto.
  simpl. rewrite All_According_To_Data. rewrite All_According_to_gen_test.
  eapply cgr_if_true_step. rewrite Eval_simpl_true; eauto. 
Qed.

Lemma gen_test_gen_spec_good_not_mu e a μ' s p :
  Well_Defined_ExtAction (ActOut a)
  -> Well_Defined_ExtAction (μ') 
    -> lts (gen_test (ActOut a :: s) p) (ActExt $ μ') e -> μ' ≠ ActIn a -> good_VACCS e.
Proof.
  intros WD_trace WD_action tr neq. unfold gen_test in tr. simpl in *. 
  destruct a. inversion tr.
  + subst. inversion H3. subst.
    simpl in *. rewrite All_According_To_Data.
    inversion WD_trace; subst.
    inversion WD_action; subst.
    assert (v1 ≠ v0) as neq'. 
    { intro. subst. contradiction. }
    eapply Eval_simpl_false in neq'.
    assert ((If cst v1 == cst v0
               Then gen_test_raw (NewVar_in_trace 0 s) s (NewVar 0 p) ^ v1 
               Else ①) ≡ ①).
    { eapply cgr_if_false_step; eauto. }
    eapply good_preserved_by_cgr_step; eauto. eapply good_success.
    eapply cgr_if_false_rev_step; eauto.
  + subst. inversion H3.
Qed.

Inductive Well_Defined_Trace : trace (ExtAct TypeOfActions) -> Prop :=
| empty_list_is_always_defined : Well_Defined_Trace ε
| cons_is_defined_up_to_data : forall a s, Well_Defined_ExtAction a -> Well_Defined_Trace s
                                                    -> Well_Defined_Trace (a :: s).


Fixpoint unroll_fw (L : list PreAct) : gproc :=
  match L with
  | [] => 𝟘
  | Inputs_on c :: l => (c ? x • ①) + unroll_fw l
  end.

Definition gen_acc (G : gset PreAct) s := gen_test s (g (unroll_fw (elements G))).

Lemma unroll_a_eq_perm (xs ys : list PreAct) : xs ≡ₚ ys -> (g (unroll_fw xs)) ≡* (g (unroll_fw ys)).
Proof.
  intro hperm. dependent induction hperm; simpl; eauto with ccs.
  - reflexivity.
  - destruct x; eauto. eapply cgr_fullchoice; eauto with ccs. reflexivity.
  - destruct y ; destruct x.
    + etrans. symmetry. eapply cgr_choice_assoc. etrans. eapply cgr_fullchoice.
      eapply cgr_choice_com. reflexivity. eapply cgr_choice_assoc.
Qed.

Lemma not_good_P G : ¬ (good_VACCS (gen_acc G ε)).
Proof.
  intros imp.
  unfold gen_acc in imp. unfold gen_test in imp.
  simpl in *. induction G using set_ind_L. 
  + simpl in *. admit.
  + simpl in *. admit. 
Admitted.

Parameter O : Value.



#[global] Program Instance gen_acc_gen_test_inst G 
  {Hyp_WD : forall α s e, lts (gen_acc G s) α e -> Well_Defined_Trace s /\ Well_Defined_Action α}
    : gen_spec co (fun s => gen_acc G s).
Next Obligation.
  intros. unfold parallel_inter. unfold dual. destruct μ; simpl; eauto.
Qed.
Next Obligation.
  intros. symmetry in H. unfold parallel_inter in H. unfold dual in H. simpl in *.
  destruct μ'.
  + rewrite simplify_match_input in H. destruct μ. simpl in *. inversion H.
    subst; eauto. simpl in *. inversion H.
  + rewrite simplify_match_output in H. destruct μ. simpl in *. inversion H.
    subst; eauto. simpl in *. inversion H. subst. eauto.
Qed.
Next Obligation.
  intros g s hh. eapply gen_test_ungood_if; try eassumption.
  eapply not_good_P; eauto.
Qed.
Next Obligation.
  intros. eapply gen_test_lts_mu.
Qed.
Next Obligation.
  intros. destruct μ.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
  + eapply gen_test_gen_spec_out_lts_tau_ex_inst.
Qed.
Next Obligation.
  intros. destruct μ.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
  + eapply gen_test_gen_spec_out_lts_tau_good. simpl in H. eassumption.
Qed.
Next Obligation.
  intros. destruct μ.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
  + unfold eq_rel. simpl. constructor. eapply gen_test_gen_spec_out_lts_mu_uniq. eassumption.
Qed.
Next Obligation.
  intros. simpl in *.
  destruct μ.
  + exfalso. eapply H. simpl. unfold non_blocking_output. unfold is_output. exists a; eauto.
  + simpl in *. assert (lts (gen_acc G (ActOut a :: s)) (ActExt μ') e) as Hyp_tr; eauto.
    eapply Hyp_WD in Hyp_tr as (WD_trace & WD_action) ; eauto.
    inversion WD_trace; subst. inversion WD_action; subst.
    ++ eapply gen_test_gen_spec_good_not_mu in H0; eauto. constructor.
    ++ eapply gen_test_gen_spec_good_not_mu in H0; eauto. constructor.
Qed.

Lemma gen_acc_does_not_not_blocking_actions : forall l p a, ¬ (lts (unroll_fw l) (ActExt $ ActOut a) p).
Proof.
  intros g.
  induction g as [| b g'].
  - cbn. intros p a R. inversion R.
  - cbn. intros p a R. destruct b.
    + inversion R; subst.
      * inversion H3.
      * eapply IHg'. eauto.
Qed.

Lemma gen_acc_does_not_tau : forall g p, ~ lts (unroll_fw g) τ p.
Proof.
  intros g.
  induction g as [| b g'].
  - cbn. intros p R. inversion R.
  - cbn. intros p R. destruct b.
    + inversion R; subst.
      * inversion H3.
      * eapply IHg'. eauto.
Qed.


Lemma gen_acc_gen_spec_acc_nil_mem_lts_inp G c : Inputs_on c ∈ G 
          -> exists r v, lts (gen_acc G []) (ActExt $ ActIn ((c ⋉ v))) r.
Proof.
  remember G. revert g Heqg.
  induction G using set_ind_L; intros g0 Heqg0 mem.
  - subst. inversion mem.
  - assert (hn : {[x]} ## X) by set_solver.
    destruct (decide (x = (Inputs_on c))).
    + subst.
      set (h := elements_disj_union {[Inputs_on c]} X hn).
      cbn. assert (exists p, lts (unroll_fw ((Inputs_on c) :: elements X)) (ActExt $ ActIn (c ⋉ O)) p).
      simpl. eauto with ccs.
      destruct H0 as (r & hl).
      edestruct (eq_spec (g (unroll_fw (elements ({[(Inputs_on c)]} ∪ X)))) r (ActExt $ ActIn (c ⋉ O))) 
          as (p & hlt & heqt).
      exists (unroll_fw ((Inputs_on c) :: elements X)).
      split. eapply unroll_a_eq_perm.
      replace (elements {[Inputs_on c]}) with [Inputs_on c] in h. eauto.
      now rewrite elements_singleton.
      simpl in *. eapply hl. eauto.
    + assert (mem' : Inputs_on c ∈ X) by set_solver.
      edestruct (IHG X eq_refl mem') as (r & hlr); eauto.
      destruct x.
      * destruct hlr. unfold gen_acc in H0. unfold gen_test in H0.
        simpl in *. 
        edestruct (eq_spec (g (unroll_fw (elements ({[Inputs_on c0]} ∪ X))))
             r  (ActExt $ ActIn (c ⋉ x))) as (p & hlt & heqt).
        exists (g (unroll_fw (Inputs_on c0 :: elements X))).
        split. eapply unroll_a_eq_perm.
        set (h := elements_disj_union {[Inputs_on c0]} X hn).
        replace (elements {[Inputs_on c0]}) with [Inputs_on c0] in h. eauto.
        now rewrite elements_singleton. simpl in *.
        eapply lts_choiceR. eauto. subst. eauto.
Qed.

#[global] Program Instance gen_acc_gen_spec_acc_inst
  {Hyp_WD : forall α s e L, lts (gen_acc L s) α e -> Well_Defined_Trace s /\ Well_Defined_Action α}
  : gen_spec_acc PreAct co gen_acc (fun x => 𝝳 (Φ x)).
Next Obligation.
  intros. eapply gen_acc_gen_test_inst. intros. eapply Hyp_WD. eauto.
Qed.
Next Obligation.
  intros Hyp g. simpl. unfold proc_stable. cbn.
  remember (lts_set_tau (unroll_fw (elements g))) as ps.
  destruct ps using set_ind_L; eauto.
  assert (mem : x ∈ lts_set_tau (unroll_fw (elements g))) by set_solver.
  eapply lts_set_tau_spec0 in mem.
  now eapply gen_acc_does_not_tau in mem.
Qed.
Next Obligation.
  intros Hyp g a. simpl. unfold proc_stable. cbn. intro nb.
  unfold non_blocking_output in nb. destruct nb as (c & eq); subst. reflexivity.
Qed.
Next Obligation.
  intros Hyp g.
  induction g using set_ind_L; intros.
  - inversion H0.
  - destruct μ.
    * edestruct (eq_spec (g (unroll_fw (x :: elements X))) e (ActExt (ActIn a))) as (p & hlt & heqt).
      ++ exists (gen_acc ({[x]} ∪ X) []).
         split.
         +++ eapply unroll_a_eq_perm.
             assert (hn : {[x]} ## X) by set_solver.
             set (h := elements_disj_union {[x]} X hn).
             replace (elements {[x]}) with [x] in h. symmetry. eauto.
             now rewrite elements_singleton.
         +++ eassumption.
      ++ cbn in hlt. destruct x.
         +++ inversion hlt; subst. 
             ** inversion H6; subst. set_solver.
             ** set_solver.
    * destruct H0. exists a. reflexivity.
Qed.
Next Obligation.
  intros. destruct pη.
  + eapply gen_acc_gen_spec_acc_nil_mem_lts_inp in H; eauto.
    destruct H as (r & v & Tr). exists r , (ActIn $ (c ⋉ v)). split; eauto.
Qed.
Next Obligation.
  intros Hyp a e' g. revert a e'.
  induction g using set_ind_L; intros a e' b hl.
  - inversion hl.
  - edestruct (eq_spec (g (unroll_fw (x :: elements X))) e' (ActExt a)) as (p & hlt & heqt).
    ++ exists (gen_acc ({[x]} ∪ X) []).
       split; eauto.
       eapply unroll_a_eq_perm.
       assert (hn : {[x]} ## X) by set_solver.
       set (h := elements_disj_union {[x]} X hn).
       replace (elements {[x]}) with [x] in h
           by now rewrite elements_singleton.
       symmetry. eauto.
    ++ simpl in hlt. destruct x.
       +++ inversion hlt; subst.
           ++++ inversion H4; subst. simpl in *. eapply good_preserved_by_cgr; eauto. constructor.
           ++++ eapply good_preserved_by_cgr. eapply IHg; eauto. eauto.
Qed.
