(* begin hide *)
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
(* end hide *)

From stdpp Require Import base countable finite list gmap gmultiset.
From Stdlib.Program Require Import Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.
From TestingTheory Require Import 
  ActTau InputOutputActions Clos_n InListPropHelper Subset_Act
  gLts Bisimulation Lts_OBA Lts_Finite_Non_Blocking_Chain Lts_OBA_FB Lts_FW FiniteImageLTS
  Must InteractionBetweenLts MultisetLTSConstruction ParallelLTSConstruction ForwarderConstruction
  DefinitionAS Equivalence coFiniteImage.
From TestingTheory Require Export VACCS.Language.LTS VACCS.Helper.Substitution VACCS.Language.Congruence VACCS.Harmony_Lemma.Harmony.

Section VACCS_lts.

Context `{VP : VACCS_Parameters}.
Existing Instance VP.

(** ******* The next work is for making 'bvar' always relates to an input *) 

(** ******* Definition for Well Abstracted bvariable *)
Inductive Well_Defined_Data : nat -> ValueData -> Prop :=
| bvar_is_defined_up_to_k: forall k x, (x < k) -> Well_Defined_Data k (bvar x)
| cst_is_always_defined : forall k v, Well_Defined_Data k (cst v).

Inductive Well_Defined_Condition : nat -> Equation ValueData -> Prop :=
| equationOnValueXX : forall k x y, Well_Defined_Data k x ->
    Well_Defined_Data k y -> Well_Defined_Condition k (x == y).

Inductive Well_Defined_Input_in : nat -> proc -> Prop :=
| WD_par : forall k p1 p2, Well_Defined_Input_in k p1 -> Well_Defined_Input_in k p2 
                -> Well_Defined_Input_in k (p1 ‖ p2)
| WD_res : forall k p, Well_Defined_Input_in k p -> Well_Defined_Input_in k (ν p)
| WD_var : forall k i, Well_Defined_Input_in k (pr_var i)
| WD_rec : forall k x p1, Well_Defined_Input_in k p1 -> Well_Defined_Input_in k (rec x • p1)
| WD_if_then_else : forall k p1 p2 C, Well_Defined_Condition k C -> Well_Defined_Input_in k p1 
                    -> Well_Defined_Input_in k p2 
                        -> Well_Defined_Input_in k (If C Then p1 Else p2)
| WD_success : forall k, Well_Defined_Input_in k (①)
| WD_nil : forall k, Well_Defined_Input_in k (𝟘)
| WD_input : forall k c p, Well_Defined_Input_in (S k) p
                  -> Well_Defined_Input_in k (c ? • p)
| WD_output : forall k c v, Well_Defined_Data k v 
                  -> Well_Defined_Input_in k (c ! v • 𝟘)
| WD_tau : forall k p,  Well_Defined_Input_in k p -> Well_Defined_Input_in k (𝛕 • p)
| WD_choice : forall k p1 p2,  Well_Defined_Input_in k (g p1) ->  Well_Defined_Input_in k (g p2) 
              ->  Well_Defined_Input_in k (p1 + p2).

Hint Constructors Well_Defined_Input_in:ccs.

Lemma Inequation_k_data : forall k d, Well_Defined_Data k d -> Well_Defined_Data (S k) d.
Proof.
intros. dependent destruction d. constructor. dependent destruction H. constructor. auto with arith.
Qed.

Lemma Inequation_k_equation : forall k c, Well_Defined_Condition k c -> Well_Defined_Condition (S k) c.
Proof.
intros. dependent destruction c. destruct v; destruct v0.
- constructor; constructor.
- dependent destruction H. constructor. constructor. apply Inequation_k_data. assumption.
- dependent destruction H. constructor. apply Inequation_k_data. assumption. constructor. 
- dependent destruction H. constructor; apply Inequation_k_data; assumption.
Qed.

Lemma Inequation_k_proc : forall k p, Well_Defined_Input_in k p -> Well_Defined_Input_in (S k) p.
Proof.
intros. revert H. revert k.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p.
- intros. dependent destruction H. constructor; apply Hp; simpl; auto with arith; assumption.
- intros. constructor.
- intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
- intros. dependent destruction H. constructor. 
  ** apply Inequation_k_equation. assumption.
  ** apply Hp. simpl; auto with arith. assumption.
  ** apply Hp. simpl; auto with arith. assumption.
- intros. constructor. dependent destruction H. apply Inequation_k_data. assumption.
- intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
- destruct g.
  ** intros. constructor.
  ** intros. constructor.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. dependent destruction H. constructor.
    -- apply Hp. simpl; auto with arith. assumption.
    -- apply Hp. simpl; auto with arith. assumption.
Qed.

(* Lemma Congruence_step_Respects_WD_k : forall p q k, Well_Defined_Input_in k p -> p ≡ q -> Well_Defined_Input_in k q. 
Proof.
intros. revert H. revert k. dependent induction H0 ; intros.
* auto.
* dependent destruction H; auto.
* constructor; auto. constructor.
* dependent destruction H;constructor; auto.
* dependent destruction H. dependent destruction H. constructor. auto. constructor;auto.
* dependent destruction H. dependent destruction H0. constructor;auto. constructor; auto.
* dependent destruction H; auto.
* constructor; auto. constructor.
* dependent destruction H. constructor; auto. 
* dependent destruction H. dependent destruction H. constructor; auto. constructor; auto.
* dependent destruction H. dependent destruction H0. constructor; auto. constructor; auto.
* dependent destruction H. constructor. apply IHcgr_step. auto.
* dependent destruction H. constructor. apply IHcgr_step. auto.
* constructor. dependent destruction H. apply IHcgr_step. auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
* dependent destruction H. constructor; auto.
Qed.

Lemma Congruence_Respects_WD_k : forall p q k, Well_Defined_Input_in k p -> p ≡* q -> Well_Defined_Input_in k q. 
Proof.
intros. dependent induction H0.
- apply Congruence_step_Respects_WD_k with x; auto.
- eauto.
Qed.

Lemma Congruence_Respects_WD : forall p q, Well_Defined_Input_in 0 p -> p ≡* q -> Well_Defined_Input_in 0 q.
Proof.
intros. eapply Congruence_Respects_WD_k; eauto.
Qed. *)

Lemma NotK : forall n k,  n < S k -> n ≠ k -> n < k.
Proof.
intros. assert (n ≤ k). auto with arith. destruct H1. exfalso. apply H0. reflexivity. auto with arith.
Qed.

Lemma ForData : forall k v d, Well_Defined_Data (S k) d -> Well_Defined_Data k (subst_Data k (cst v) d).
Proof.
intros. revert H. revert v. revert k. dependent induction d.
* intros. simpl. constructor.
* intros. simpl. destruct (decide (n = k )).
  - constructor. 
  - dependent destruction H.
    destruct (decide (n < k)). 
    -- constructor. assumption.
    -- constructor. apply NotK.  transitivity n. lia. (* pas top *) assumption. lia.
Qed.

Lemma ForEquation : forall k v e, Well_Defined_Condition (S k) e 
                -> Well_Defined_Condition k (subst_in_Equation k (cst v) e).
Proof.
intros. revert H. revert v. revert k. 
- dependent destruction e. dependent induction v; dependent induction v0.
  * intros. simpl. constructor; constructor.
  * intros. simpl. destruct (decide (n = k)).
    ** constructor; constructor.
    ** constructor. constructor. dependent destruction H. dependent destruction H0.
       destruct (decide(n < k)).
       --- constructor. assumption.
       --- constructor. lia.
  * intros. simpl. constructor; try constructor. destruct (decide (n = k)). constructor. dependent destruction H.
    dependent destruction H.
    destruct (decide(n < k)).
       --- constructor. assumption.
       --- constructor. lia. 
  * intros. simpl. constructor.
    ** destruct (decide (n = k)); try constructor. dependent destruction H. dependent destruction H. 
       destruct (decide(n < k)).
       --- constructor. assumption.
       --- constructor. lia. 
    ** destruct (decide (n0 = k)); try constructor. dependent destruction H. dependent destruction H0. 
       destruct (decide(n0 < k)).
       --- constructor. assumption.
       --- constructor. lia. 
Qed.

Lemma ForSTS : forall k p v, Well_Defined_Input_in (S k) p -> Well_Defined_Input_in k (subst_in_proc k (cst v) p).
Proof.
intros. revert v. revert H. revert k.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p.
* intros. dependent destruction H. simpl. constructor. 
  - apply Hp. simpl. auto with arith. assumption.
  - apply Hp. simpl. auto with arith. assumption.
* intros. simpl. constructor.
* intros. simpl. dependent destruction H. constructor. apply Hp. simpl. auto with arith. assumption.
* intros. simpl. dependent destruction H. constructor.
  - apply ForEquation. assumption.
  - apply Hp. simpl. auto with arith. assumption.
  - apply Hp. simpl. auto with arith. assumption.
* intros. simpl. dependent destruction H. constructor. apply ForData. assumption.
* intros. simpl. dependent destruction H. constructor. apply Hp. simpl. auto with arith. assumption.
* destruct g.
  - intros. simpl. constructor.
  - intros. simpl. constructor.
  - intros. simpl. constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. dependent destruction H. constructor.
    -- assert (Well_Defined_Input_in k (subst_in_proc k (cst v) (g1))). apply Hp.
      simpl.  auto with arith. assumption. assumption.
    -- assert (Well_Defined_Input_in k (subst_in_proc k (cst v) (g2))). apply Hp.
      simpl.  auto with arith. assumption. assumption.
Qed.

Lemma WD_data_and_NewVar : forall d k i, Well_Defined_Data (k + i) d 
                          -> Well_Defined_Data (S (k + i)) (NewVar_in_Data i d).
Proof.
dependent induction d; intros.
- simpl. constructor.
- simpl. destruct (decide (i < S n)).
  * constructor. simpl. dependent destruction H. auto with arith.
  * constructor. dependent destruction H.  transitivity i.
    apply Nat.nlt_succ_r. assumption.
    auto with arith. 
Qed.

Lemma WD_eq_and_NewVar : forall e k i, Well_Defined_Condition (k + i) e 
                          -> Well_Defined_Condition (S (k + i)) (NewVar_in_Equation i e).
Proof.
intro. dependent induction e; intros; simpl. 
* dependent induction H. constructor. 
  - apply WD_data_and_NewVar. assumption.
  - apply WD_data_and_NewVar. assumption.
Qed.

Lemma WD_and_NewVar : forall k i p, Well_Defined_Input_in (k + i) p -> Well_Defined_Input_in ((S k) + i) (NewVar i p).
Proof.
intros. revert H. revert k i.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros; simpl.
* dependent destruction H. constructor.
   - apply Hp. simpl. auto with arith. assumption.
   - apply Hp. simpl. auto with arith. assumption.
* constructor.
* constructor. dependent destruction H. apply Hp. simpl. auto with arith. assumption.
* dependent destruction H. constructor. apply  WD_eq_and_NewVar. assumption.
   - apply Hp. simpl. auto with arith. assumption.
   - apply Hp. simpl. auto with arith. assumption.
* constructor. dependent destruction H. apply WD_data_and_NewVar. assumption.
* constructor. dependent destruction H. apply Hp. simpl. auto with arith. assumption.
* destruct g; intros; simpl.
  - constructor.
  - constructor.
  - dependent destruction H. constructor. 
    assert (S (S (k + i)) = (S k + S i)%nat). simpl. auto with arith.
    rewrite H0. apply Hp. simpl. auto with arith. assert ((k + S i)%nat = S (k + i)).  auto with arith. rewrite H1. assumption.
  - constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - dependent destruction H. constructor.
    -- assert (S (k + i) = (S k + i)%nat). auto with arith. rewrite H1.
       assert (Well_Defined_Input_in (S k + i) (NewVar i (g g1))).
       apply Hp. simpl. auto with arith. assumption. assumption.
    -- assert (S (k + i) = (S k + i)%nat). auto with arith. rewrite H1.
       assert (Well_Defined_Input_in (S k + i) (NewVar i (g g2))).
       apply Hp. simpl. auto with arith. assumption. assumption.
Qed.

Lemma WD_and_NewVarC : forall k i p, Well_Defined_Input_in k p -> Well_Defined_Input_in k (NewVarC i p).
Proof.
intros. revert H. revert k i.
induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p; intros; simpl.
* dependent destruction H. constructor.
   - apply Hp. simpl. auto with arith. assumption.
   - apply Hp. simpl. auto with arith. assumption.
* constructor.
* constructor. dependent destruction H. apply Hp. simpl. auto with arith. assumption.
* dependent destruction H. constructor. eauto.
   - apply Hp. simpl. auto with arith. assumption.
   - apply Hp. simpl. auto with arith. assumption.
* constructor. dependent destruction H. eauto.
* constructor. dependent destruction H. apply Hp. simpl. auto with arith. assumption.
* destruct g; intros; simpl.
  - constructor.
  - constructor.
  - dependent destruction H. constructor. 
    apply Hp. simpl. auto with arith. eauto.
  - constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - dependent destruction H. constructor.
    -- assert (Well_Defined_Input_in k (NewVarC i (g g1))).
       apply Hp. simpl. auto with arith. assumption. assumption.
    -- assert (Well_Defined_Input_in k (NewVarC i (g g2))).
       apply Hp. simpl. auto with arith. assumption. assumption.
Qed.

Lemma ForRecursionSanity : forall p' p x k, Well_Defined_Input_in k p' -> Well_Defined_Input_in k p 
            -> Well_Defined_Input_in k (pr_subst x p' p).
Proof.
intros. revert H. revert H0. revert k. revert x. revert p.
induction p' as (p' & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
destruct p'.
* intros. simpl. constructor. 
  ** apply Hp. simpl. auto with arith. assumption. dependent destruction H. assumption.
  ** apply Hp. simpl. auto with arith. assumption. dependent destruction H. assumption.
* intros. simpl. destruct (decide (x = n)). assumption. assumption.
* intros. simpl. destruct (decide (x=n)). 
  ** dependent destruction H. assumption.
  ** constructor. apply Hp. simpl; auto with arith. assumption. dependent destruction H. assumption.
* intros. simpl. dependent destruction H. constructor.
  ** assumption.
  ** apply Hp. simpl; auto with arith. assumption. assumption.
  ** apply Hp. simpl; auto with arith. assumption. assumption.
* intros. simpl. assumption.
* intros. simpl. constructor. dependent destruction H. apply Hp.
    - simpl; auto with arith.
    - eapply WD_and_NewVarC. eauto.
    - eauto.
* destruct g.
  ** intros. simpl. constructor.
  ** intros. simpl. constructor.
  ** intros. simpl. constructor. dependent destruction H. apply Hp. 
    - simpl;auto with arith.
    - assert ((S k) = ((S k) + 0)%nat). auto with arith. rewrite H1. apply (WD_and_NewVar k 0 p0).
      assert (k = (k + 0)%nat). auto with arith. rewrite <-H2. assumption. 
    - assumption.
  ** intros. simpl. constructor. apply Hp.
    - simpl; auto with arith.
    - assumption.
    - dependent destruction H. assumption.
  ** intros. simpl. dependent destruction H. constructor.
    - assert (Well_Defined_Input_in k (pr_subst x (g g1) p)). apply Hp. simpl; auto with arith. assumption.
      assumption. assumption.
    - assert (Well_Defined_Input_in k (pr_subst x (g g2) p)). apply Hp. simpl; auto with arith. assumption.
      assumption. assumption.
Qed.

Lemma RecursionOverReduction_is_WD : forall k x p, Well_Defined_Input_in k (rec x • p) 
          -> Well_Defined_Input_in k (pr_subst x p (rec x • p)).
Proof.
intros. apply ForRecursionSanity. dependent destruction H. assumption. assumption.
Qed.

Lemma Well_Def_Data_Is_a_value : forall d, Well_Defined_Data 0 d <-> exists v, d = cst v.
Proof.
intros. split. 
- intro. dependent destruction H. exfalso. dependent induction H. exists v. reflexivity.
- intros. destruct H. subst. constructor.
Qed.

(* Lemma STS_Respects_WD : forall p q, Well_Defined_Input_in 0 p -> sts p q -> Well_Defined_Input_in 0 q.
Proof.
intros. revert H. rename H0 into Reduction. dependent induction Reduction.
* intros. constructor.
  - constructor.
  - dependent destruction H. dependent destruction H0. dependent destruction H0_. 
    dependent destruction H. apply Well_Def_Data_Is_a_value in H. destruct H. subst.  apply ForSTS. assumption. 
* intros. dependent destruction H. dependent destruction H. assumption.
* intros. dependent destruction H. apply RecursionOverReduction_is_WD. constructor. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H. constructor. apply IHReduction. assumption. assumption.
* intros. apply Congruence_Respects_WD with q2. apply IHReduction. apply Congruence_Respects_WD with p1. 
  assumption. assumption. assumption.
Qed. *)

Inductive Well_Defined_Action: (ActIO TypeOfActions) -> Prop :=
| ActionOutput_with_value_is_always_defined : forall c v, Well_Defined_Action ((c , (cst v))!)
| ActionInput_with_value_is_always_defined : forall c v, Well_Defined_Action ((c , (cst v))?)
| Tau_is_always_defined : Well_Defined_Action τ.

Inductive Well_Defined_ExtAction: (ExtAct TypeOfActions) -> Prop :=
| ExtActionOutput_with_value_is_always_defined : forall c v, Well_Defined_ExtAction (ActOut (c , (cst v)))
| ExtActionInput_with_value_is_always_defined : forall c v, Well_Defined_ExtAction (ActIn (c , (cst v))).

Lemma Output_are_good : forall p1 p2 c d, Well_Defined_Input_in 0 p1 -> lts p1 ((c , d) !) p2 
      -> exists v, d = cst v.
Proof.
intros. dependent induction H0. dependent destruction H. eapply Well_Def_Data_Is_a_value in H. destruct H.
subst. exists x. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. simpl in *. eapply IHlts with (VarC_add 1 c). assumption. simpl. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
- dependent destruction H. eapply IHlts with c. assumption. reflexivity.
Qed.

Lemma LTS_Respects_WD : forall p q α, Well_Defined_Input_in 0 p -> Well_Defined_Action α -> lts p α q 
            ->  Well_Defined_Input_in 0 q.
Proof.
intros. revert H. revert H0. rename H1 into Transition. dependent induction Transition.
* intros. dependent destruction H0. apply ForSTS. dependent destruction H. assumption.
* intros. constructor.
* intros. dependent destruction H. assumption.
* intros. apply ForRecursionSanity. dependent destruction H. assumption. assumption.
* intros. inversion H1; subst. eapply IHTransition; eauto.
* intros. inversion H1; subst. eapply IHTransition; eauto.
* intros. inversion H; subst. constructor. eapply IHTransition; eauto. destruct μ; destruct a; destruct v; simpl in *.
  + simpl. constructor.
  + simpl. inversion H0.
  + simpl. constructor.
  + simpl. inversion H0.
* intros. inversion H; subst. constructor. eapply IHTransition; eauto.
* intros. dependent destruction H. constructor. 
  ** apply IHTransition1. assert (exists v', v = cst v'). eapply Output_are_good. exact H.
     exact Transition1. destruct H2. subst. constructor. assumption.
  ** apply IHTransition2. assert (exists v', v = cst v'). eapply Output_are_good. exact H.
     exact Transition1. destruct H2. subst. constructor. assumption.
* intros. dependent destruction H. constructor.
  ** apply IHTransition2. assert (exists v', v = cst v'). eapply Output_are_good. exact H1.
     exact Transition1. destruct H2. subst. constructor. assumption.
  ** apply IHTransition1. assert (exists v', v = cst v'). eapply Output_are_good. exact H1.
     exact Transition1. destruct H2. subst. constructor. assumption.
* intros. dependent destruction H. constructor. apply IHTransition. assumption. assumption. assumption.
* intros. dependent destruction H. constructor. assumption. apply IHTransition. assumption. assumption.
* intros. dependent destruction H. apply IHTransition. assumption. assumption.
* intros. dependent destruction H. apply IHTransition. assumption. assumption.
Qed.

(** ******* Lemma to simplify the Data in Value for a transition *)
Lemma OutputWithValue : forall p q a, lts p (a !) q -> exists c v, a = (c , v).
Proof.
  intros. destruct a; eauto.
Qed.

Lemma InputWithValue : forall p q a, lts p (a ?) q -> exists c v, a = (c , v).
Proof.
  intros. destruct a; eauto.
Qed.

Lemma cgr_par_nil_n n r :  Ѵ n 𝟘 ‖ r ≡* r.
Proof.
  revert r. induction n.
  - simpl. intros. eauto with *.
  - simpl. intros. etrans. instantiate (1 := (𝟘 ‖ (ν Ѵ n 𝟘) ‖ r)).
    eapply cgr_par. symmetry. etrans. eapply cgr_par_com. eapply cgr_par_nil.
    etrans. eapply cgr_par. eapply cgr_par_com. etrans. eapply cgr_par.
    eapply cgr_res_scope_rev. simpl. etrans. eapply cgr_par. eapply cgr_res. eauto.
    etrans. eapply cgr_par. eapply cgr_res_nil. etrans. eapply cgr_par_com. eapply cgr_par_nil.
Qed.

(** ******* Peter Selinger Axioms (OutBuffered Agent with FeedBack) up to structural equivalence *)

Lemma OBA_with_FB_First_Axiom : forall p q r a α,
  lts p (a !) q -> lts q α r ->
  (exists r', lts p α r' /\ lts_then_sc r' (a !) r). (* output-commutativity *)
Proof.
  intros. assert (lts p (a !) q). assumption. apply OutputWithValue in H1.
  decompose record H1. subst. eapply TransitionShapeForOutputSimplified in H as eq.
  eapply lts_parR in H0. instantiate (1 := x ! x0 • 𝟘) in H0.
  edestruct (Congruence_Respects_Transition p ((x ! x0 • 𝟘) ‖ r) α).
  exists ((x ! x0 • 𝟘) ‖ q). split; assumption. destruct H2.
  assert (lts ((x ! x0 • 𝟘) ‖ r) ((x , x0) !) (𝟘 ‖ r)). constructor.
  constructor.
  edestruct (Congruence_Respects_Transition x1 (𝟘 ‖ r) ((x , x0) !)).
  exists ((x ! x0 • 𝟘) ‖ r). split ; assumption. destruct H5.
  assert (x2 ≡* r). etrans. eauto. etrans. eapply cgr_par_com. eapply cgr_par_nil.
  exists x1. split. assumption. exists x2. split; assumption.
Qed.

Lemma simpl_output_res n c v p μ : lts (Ѵ n (VarC_add n c ! v • 𝟘)) (ActExt μ) p -> μ = ActOut (c , v) /\ p = Ѵ n 𝟘.
Proof.
  revert c v p μ.
  induction n.
  + simpl in * ; intros. rewrite VarC_add_zero in H. inversion H; eauto; split ;eauto.
  + intros. simpl in *. inversion H. subst. replace (S n)%nat with (n + 1)%nat in H2 by lia.
    rewrite VarC_add_revert_def in H2. simpl in *. eapply IHn in H2 as (eq1 & eq2).
    subst. rewrite NewVarCzero_and_add in eq1.
    replace (ActOut (VarC_add 1 c , v)) with (VarC_action_add 1 (ActOut (c , v))) in eq1 by eauto.
    rewrite NewVarCzero_and_add in eq1. eapply NewVarC_in_ext_inv in eq1. subst. split ;eauto.
Qed.

Lemma OBA_with_FB_Second_Axiom : forall p q1 q2 a μ, 
  μ ≠ (ActOut a) ->
  lts p (a !) q1 ->
  lts p (ActExt μ) q2 ->
  ∃ r : proc, lts q1 (ActExt μ) r ∧ lts_then_sc q2 (a !) r. (* output-confluence  *)
Proof.
  intros. assert (lts p (a !) q1). assumption. apply OutputWithValue in H2.
  decompose record H2. subst. rename x into c. rename x0 into v.
  eapply TransitionShapeForOutputSimplified in H0.
  edestruct (Congruence_Respects_Transition ((c ! v • 𝟘) ‖ q1) q2 (ActExt μ)).
  exists p. split. symmetry. assumption. assumption.
  destruct H3. inversion H3; subst.
  - inversion H9. subst. assert (ActOut (c , v) = ActOut (c , v)). eauto. exfalso. eapply H. eauto.
  - exists q3. split. assumption.
    assert (lts ((c ! v • 𝟘) ‖ q3) ((c , v) !) (𝟘 ‖ q3)). {
      constructor. constructor. }
    edestruct (Congruence_Respects_Transition q2 (𝟘 ‖ q3) ((c , v) !)).
    + exists ((c ! v • 𝟘) ‖ q3). split.
      * eauto with *.
      * assumption.
    + destruct H6. exists x. split. assumption.
      etrans. eauto. etrans. eapply cgr_par_com. eapply cgr_par_nil.
Qed.

Lemma OBA_with_FB_Third_Axiom : forall p1 p2 p3 a, 
            lts p1 (a !) p2 → lts p1 (a !) p3 -> p2 ≡* p3. (* output-determinacy *)
Proof.
  intros. assert (lts p1 (a !) p2). assumption. apply OutputWithValue in H1.
  decompose record H1. subst. rename x into c. rename x0 into v.
  revert H0. revert p3. dependent induction H.
  - intros. inversion H0. subst. eauto with *.
  - intros. inversion H2; subst.
    + eapply IHlts; eauto.
    + rewrite H in H8. inversion H8.
  - intros. inversion H2; subst.
    + rewrite H in H8. inversion H8.
    + eapply IHlts; eauto.
  - intros. inversion H0;subst. eapply cgr_res.
    eapply (IHlts (VarC_add 1 c) v); eauto.
  - intros. inversion H0;subst. 
    * apply cgr_fullpar. eapply IHlts. eauto. eauto. assumption. eauto with *.
    * apply TransitionShapeForOutputSimplified in H.
      apply TransitionShapeForOutputSimplified in H6.
       transitivity (p2 ‖ ((c ! v • 𝟘) ‖ q2)). eapply cgr_fullpar. 
      reflexivity. exact H6. etrans. symmetry. eapply cgr_par_assoc.
      eapply cgr_par. etrans. eapply cgr_par_com. symmetry. eauto.
  - intros. inversion H0 ; subst.
    + apply TransitionShapeForOutputSimplified in H.
      apply TransitionShapeForOutputSimplified in H6.
      transitivity (((c ! v • 𝟘) ‖ p2) ‖ q2); [eauto with cgr|].
      transitivity (( p2 ‖ (c ! v • 𝟘)) ‖ q2); [eauto with cgr|].
      transitivity ( p2 ‖ ((c ! v • 𝟘) ‖ q2)); [eauto with cgr|].
      apply cgr_fullpar; eauto with *.
    + apply cgr_fullpar. reflexivity. eapply IHlts. eauto. eauto. assumption.
  - intros. exfalso. eapply guarded_does_no_output. eassumption.
  - intros. exfalso. eapply guarded_does_no_output. eassumption.
Qed.

Lemma OBA_with_FB_Fourth_Axiom : forall p1 p2 p3 a, lts p1 (a !) p2 -> lts p2 (a ?) p3 
                              -> lts_then_sc p1 τ p3. (* feedback *)
Proof.
  intros. assert (lts p1 (a !) p2). assumption. apply OutputWithValue in H1.
  decompose record H1. subst. rename x into c. rename x0 into v.
  eapply TransitionShapeForOutputSimplified in H.
  assert (lts ((c ! v • 𝟘)) ((c , v) !) 𝟘).
  constructor.
  assert (lts ((c ! v • 𝟘) ‖ p2) τ  (𝟘 ‖ p3)). econstructor; eassumption.
  edestruct (Congruence_Respects_Transition p1 ( 𝟘 ‖ p3) τ). exists (( c ! v • 𝟘) ‖ p2).
  split; assumption. destruct H4. exists x. split. assumption. etrans. eauto. etrans.
  eapply cgr_par_com. eapply cgr_par_nil. 
Qed.

Hint Constructors Relation_Operators.clos_trans : cgr.

Lemma OBA_with_FB_Fifth_Axiom : forall p q1 q2 a,
  lts p (a !) q1 -> lts p τ q2 ->
  (∃ q : proc, lts q1 τ q /\ lts_then_sc q2 (a !) q) \/ lts_then_sc q1 (a ?) q2. (* output-tau  *)
Proof.
  intros. assert (lts p (a !) q1). assumption. apply OutputWithValue in H1.
  decompose record H1. subst. rename x into c. rename x0 into v.
  eapply TransitionShapeForOutputSimplified in H.
  edestruct (Congruence_Respects_Transition ((c ! v • 𝟘) ‖ q1) q2 τ).
  - exists p. split. eauto with *. assumption.
  - destruct H2. dependent induction H2.
    + inversion H2_; subst. right. exists q3; split. assumption.
      rewrite <- H3. transitivity (q3 ‖ 𝟘); eauto with *.
    + inversion H2_0.
    + inversion H2.
    + left. exists q3. split. assumption. 
      assert (lts ((c ! v • 𝟘) ‖ q3) ((c , v) !) (𝟘 ‖ q3)). constructor. constructor.
      edestruct (Congruence_Respects_Transition q2 (𝟘 ‖ q3) ((c , v) !)). exists ((c ! v • 𝟘) ‖ q3).
      split.
      * eauto with *.
      * assumption.
      * destruct H5. exists x. split. assumption.
        etransitivity; eauto. eauto with *.
Qed.

Lemma ExtraAxiom : forall p1 p2 q1 q2 a,
      lts p1 (a !) q1 -> lts p2 (a !) q2 -> q1 ≡* q2 -> p1 ≡* p2.
Proof.
  intros. assert (lts p1 (a !) q1). assumption. apply OutputWithValue in H2.
  decompose record H2. subst. rename x into c. rename x0 into v.
  eapply TransitionShapeForOutputSimplified in H0.
  eapply TransitionShapeForOutputSimplified in H.
   transitivity ((c ! v • 𝟘) ‖ q1). assumption.
   transitivity ((c ! v • 𝟘) ‖ q2); eauto with *.
Qed.

Lemma Equation_dec : forall (x y : Equation ValueData) , {x = y} + {x <> y}.
Proof.
decide equality. apply Data_dec. apply Data_dec.
Qed.

#[global] Instance equation_dec : EqDecision (Equation ValueData). exact Equation_dec. Defined.

Definition encode_equation (E : Equation ValueData) : gen_tree (nat + ValueData) :=
match E with
  | D1 == D2 => GenNode 0 [GenLeaf (inr D1) ; GenLeaf (inr D2)]
end.

Definition decode_equation (tree : gen_tree (nat + ValueData)) : option (Equation ValueData) :=
match tree with
  | GenNode 0 [GenLeaf (inr d); GenLeaf (inr d')] => Some (d == d')
  | _ => None
end. 

Lemma encode_decide_equations p : decode_equation (encode_equation p) = Some p.
Proof. 
induction p.
* simpl. reflexivity.
Qed.

#[global] Instance equation_countable : Countable (Equation ValueData).
Proof.
  refine (inj_countable encode_equation decode_equation _).
  apply encode_decide_equations.
Qed.

Lemma TypeOfActions_dec : forall (x y : TypeOfActions) , {x = y} + {x <> y}.
Proof.
decide equality. 
* destruct (decide(b = v)). left. assumption. right. assumption.
* destruct (decide (a = c)). left. assumption. right. assumption.
Defined.

#[global] Instance TypeOfActions_eqdecision : EqDecision TypeOfActions. by exact TypeOfActions_dec . Defined.

Fixpoint proc_dec (x y : proc) : { x = y } + { x <> y }
with gproc_dec (x y : gproc) : { x = y } + { x <> y }.
Proof.
decide equality. 
* destruct (decide(n = n0));eauto.
* destruct (decide(n = n0));eauto.
* destruct (decide(e = e0));eauto. 
* destruct (decide(v = v0));eauto.
* destruct (decide(c = c0));eauto.
* decide equality. destruct (decide(c = c0));eauto.
Qed.

#[global] Instance proc_eqdecision : EqDecision proc. by exact proc_dec. Defined.

Definition encode_TypeOfActions (a : TypeOfActions) : gen_tree (nat + (ChannelData + ValueData)) :=
match a with
  | (c , v) => GenNode 0 [GenLeaf (inr (inl c)) ; GenLeaf (inr (inr v))]
end.

Definition decode_TypeOfActions (tree :gen_tree (nat + (ChannelData + ValueData))) : option TypeOfActions :=
match tree with
  | GenNode 0 [GenLeaf (inr (inl c)); GenLeaf (inr (inr v))] => Some (c , v)
  | _ => None
end.

Lemma encode_decide_TypeOfActions p : decode_TypeOfActions (encode_TypeOfActions  p) = Some p.
Proof. 
induction p. 
* simpl. reflexivity.
Qed.

#[global] Instance TypeOfActions_countable : Countable TypeOfActions.
Proof.
  eapply inj_countable with encode_TypeOfActions decode_TypeOfActions. 
  intro. apply encode_decide_TypeOfActions.
Qed.

Definition encode_ExtAct_TypeOfActions (a : ExtAct TypeOfActions) : 
    gen_tree (nat + (ChannelData + ValueData)) :=
match a with
  | ActIn a => GenNode 0 [encode_TypeOfActions a]
  | ActOut a => GenNode 1 [encode_TypeOfActions a]
end.

Definition decode_ExtAct_TypeOfActions_raw (tree :gen_tree (nat + (ChannelData + ValueData))) 
  : option (ExtAct (option TypeOfActions)) :=
match tree with
  | GenNode 0 [l] => Some (ActIn (decode_TypeOfActions l))
  | GenNode 1 [l] => Some (ActOut (decode_TypeOfActions l))
  | _ => None
end.

Definition simpl_option (a : option (ExtAct (option TypeOfActions)))
  : option (ExtAct TypeOfActions) :=
match a with
  | Some (ActIn None) => None
  | Some (ActIn (Some b)) => Some (ActIn b)
  | Some (ActOut None) => None
  | Some (ActOut (Some b)) => Some (ActOut b)
  | None => None
end.

Definition decode_ExtAct_TypeOfActions (tree :gen_tree (nat + (ChannelData + ValueData))) 
  : option (ExtAct TypeOfActions) := simpl_option (decode_ExtAct_TypeOfActions_raw tree).

Lemma encode_decide_ExtAct_TypeOfActions a : 
  decode_ExtAct_TypeOfActions (encode_ExtAct_TypeOfActions  a) = Some a.
Proof. 
induction a. 
* unfold decode_ExtAct_TypeOfActions. simpl.
  rewrite encode_decide_TypeOfActions. eauto.
* unfold decode_ExtAct_TypeOfActions. simpl.
  rewrite encode_decide_TypeOfActions. eauto.
Qed.

#[global] Instance ExtAct_TypeOfActions_countable : Countable (ExtAct TypeOfActions).
Proof.
  eapply inj_countable with encode_ExtAct_TypeOfActions decode_ExtAct_TypeOfActions. 
  intro. apply encode_decide_ExtAct_TypeOfActions.
Defined.

Fixpoint encode_proc (p: proc) : gen_tree (nat + (((Equation ValueData ) + TypeOfActions) + ChannelData)) :=
  match p with
  | p ‖ q  => GenNode 0 [encode_proc p; encode_proc q]
  | c ! v • 𝟘  => GenLeaf (inr $ inl $ inr $ (c , v))
  | pr_var i => GenNode 2 [GenLeaf $ inl i]
  | rec x • P => GenNode 3 [GenLeaf $ inl x; encode_proc P]
  | If C Then A Else B => GenNode 4 [GenLeaf (inr ( inl (inl C))) ; encode_proc A; encode_proc B]
  | ν p => GenNode 5 [encode_proc p]
  | g gp => GenNode 1 [encode_gproc gp]
  end
with
encode_gproc (gp: gproc) : gen_tree (nat + (((Equation ValueData ) + TypeOfActions) + ChannelData)) :=
  match gp with
  | ① => GenNode 1 []
  | 𝟘 => GenNode 0 []
  | c ? • p => GenNode 2 [GenLeaf (inr $ inr c); encode_proc p]
  | 𝛕 • p => GenNode 3 [encode_proc p]
  | gp + gq => GenNode 4 [encode_gproc gp; encode_gproc gq]
  end.

Fixpoint decode_proc (t': gen_tree (nat + (((Equation ValueData ) + TypeOfActions) + ChannelData))) : proc :=
  match t' with
  | GenNode 0 [ep; eq] => (decode_proc ep) ‖ (decode_proc eq)
  | GenLeaf (inr ( inl (inr a))) => (ChannelData_of a) ! (ValueData_of a) • 𝟘
  | GenNode 2 [GenLeaf (inl i)] => pr_var i
  | GenNode 3 [GenLeaf (inl i); egq] => rec i • (decode_proc egq)
  | GenNode 4 [GenLeaf (inr ( inl (inl C))); A; B] => If C Then (decode_proc A) Else (decode_proc B)
  | GenNode 5 [eq] => ν (decode_proc eq)
  | GenNode 1 [egp] => g (decode_gproc egp)
  | _ => ① 
  end
with
decode_gproc (t': gen_tree (nat + (((Equation ValueData ) + TypeOfActions) + ChannelData))): gproc :=
  match t' with
  | GenNode 1 [] => ①
  | GenNode 0 [] => 𝟘
  | GenNode 2 [GenLeaf (inr (inr c)); ep] => c ? • (decode_proc ep)
  | GenNode 3 [eq] => 𝛕 • (decode_proc eq)
  | GenNode 4 [egp; egq] => (decode_gproc egp) + (decode_gproc egq)
  | _ => ① 
  end.

Lemma encode_decide_procs p : decode_proc (encode_proc p) = p
with encode_decide_gprocs p : decode_gproc (encode_gproc p) = p.
Proof. all: case p; intros; simpl; repeat rewrite encode_decide_procs; auto with *.
Qed.

#[global] Instance proc_count : Countable proc.
refine (inj_countable' encode_proc decode_proc _).
  apply encode_decide_procs.
Qed.

Fixpoint moutputs_of (k : nat) p : gmultiset TypeOfActions := 
match p with
  | P ‖ Q => (moutputs_of k P) ⊎ (moutputs_of k Q)
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | If E Then P Else Q => match (Eval_Eq 0 E) with 
                          | Some true => moutputs_of k P
                          | Some false => moutputs_of k Q
                          | None => ∅
                          end
  | (cst c) ! v • 𝟘 => {[+ ((cst c) , v) +]}
  | (bvar i) ! v • 𝟘 => if decide(k < (S i)) then {[+ ((bvar (i - k)) , v) +]}
                                            else ∅
  | ν p => moutputs_of (S k) p
  | g _ => ∅
end.

Definition outputs_of p := dom (moutputs_of 0 p).

Lemma VarSwap_and_moutputs j p k : moutputs_of (j + S (S k)) p =
moutputs_of (j + S (S k)) (VarSwap_in_proc j p).
Proof.
  revert j k.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *; try multiset_solver.
  + assert (moutputs_of (j + S (S k)) p1 
      = moutputs_of (j + S (S k)) (VarSwap_in_proc j p1)) as eq1. 
    { eapply Hp. simpl. lia. }
    assert (moutputs_of (j + S (S k)) p2 
      = moutputs_of (j + S (S k)) (VarSwap_in_proc j p2)) as eq2. 
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto. 
  + case_eq (Eval_Eq 0 e); intros; try multiset_solver.
    destruct b.
    ++ eapply Hp. simpl. lia.
    ++ eapply Hp. simpl. lia.
  + destruct c.
      * simpl. eauto.
      * simpl. destruct (decide (j + S (S k) < S n)).
        ++ destruct (decide (n = j)); subst.
           +++ rewrite decide_True ; try lia.
           +++ destruct (decide (n = S j)); subst.
               ++++ destruct (decide (j + S (S k) < S j)).
                    +++++ lia.
                    +++++ lia.
               ++++ rewrite decide_True ; try lia. eauto.
        ++ destruct (decide (n = j)); subst.
           +++ rewrite decide_False ; try lia. eauto.
           +++ destruct (decide (n = S j)); subst.
               ++++ rewrite decide_False ; try lia. eauto.
               ++++ rewrite decide_False ; try lia. eauto.
  + replace (S (j + S (S k)))%nat with ((S j) + S (S k))%nat by lia. eauto. 
Qed.

Lemma NewVarC_and_moutputs p j : moutputs_of (S j) (NewVarC j p) = moutputs_of j p.
Proof.
  revert j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *; try multiset_solver.
  + assert (moutputs_of (S j) (NewVarC j p1)
      = moutputs_of j p1 ) as eq1. 
    { eapply Hp. simpl. lia. }
    assert (moutputs_of (S j) (NewVarC j p2)
      = moutputs_of j p2) as eq2. 
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto. 
  + case_eq (Eval_Eq 0 e); intros; try multiset_solver.
    destruct b.
    ++ eapply Hp. simpl. lia.
    ++ eapply Hp. simpl. lia.
  + destruct c.
      * simpl. eauto.
      * simpl. destruct (decide (j < S n)).
        ++ rewrite decide_True; try lia. eauto.
        ++ rewrite decide_False; try lia. eauto.
Qed.

Lemma NewVarCn_and_moutputs j p k : moutputs_of j p =
moutputs_of (k + j) (NewVarCn j k p).
Proof.
  revert p j.
  induction k.
  + simpl; eauto.
  + intros. simpl. rewrite<- NewVarCn_revert_def.
    replace (S (k + j))%nat with (k + (S j))%nat by lia.
    assert ((NewVarCn j k (NewVarC j p)) = (NewVarCn (S j) k (NewVarC j p))) as eq.
    { rewrite simpl_bvar_in_NewVarCn. eauto. } rewrite eq. rewrite<- (IHk  (NewVarC j p)).
    rewrite NewVarC_and_moutputs. eauto.
Qed.

Lemma moutputs_and_NewVar k p j : moutputs_of (k + j) p = moutputs_of (k + S j) (NewVarC j p).
Proof.
  revert j k.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  + assert (moutputs_of (k + j) p1 = moutputs_of (k + S j) (NewVarC j p1)) as eq1.
    { eapply Hp. lia. }
    assert (moutputs_of (k + j) p2 = moutputs_of (k + S j) (NewVarC j p2)) as eq2.
    { eapply Hp. lia. }
    rewrite eq1, eq2. eauto.
  + eauto.
  + eauto.
  + assert (moutputs_of (k + j) p1 = moutputs_of (k + S j) (NewVarC j p1)) as eq1.
    { eapply Hp. lia. }
    assert (moutputs_of (k + j) p2 = moutputs_of (k + S j) (NewVarC j p2)) as eq2.
    { eapply Hp. lia. }
    rewrite eq1, eq2. eauto.
  + destruct c.
      * simpl. eauto.
      * destruct (decide (k + j < S n)).
        ++ simpl. rewrite decide_True; try lia.
           rewrite decide_True; try lia.
           replace ((S n - (k + S j)))%nat with (n - (k + j))%nat by lia.
           eauto.
        ++ simpl. destruct (decide (j < S n)).
           +++ rewrite decide_False; try lia. eauto.
           +++ rewrite decide_False; try lia. eauto.
  + replace ((S (k + j)))%nat with (k + S j)%nat by lia.
    replace (S (k + S j))%nat with (k + S (S j))%nat by lia.
    eapply Hp. simpl. eauto.
  + eauto.
Qed.

Lemma NewVarCn_and_moutputs2 j p k : moutputs_of k p =
moutputs_of (j + k) (NewVarCn 0 j p).
Proof.
  revert p k.
  induction j.
  + intros; simpl; eauto.
  + intros. simpl. rewrite<- NewVarCn_revert_def.
    replace (S (j+ k))%nat with (j + (S k))%nat by lia.
    rewrite<- (IHj (NewVarC 0 p)).
    assert ((NewVarCn j k (NewVarC j p)) = (NewVarCn (S j) k (NewVarC j p))) as eq.
    { rewrite simpl_bvar_in_NewVarCn. eauto. } replace k%nat with (k + 0)%nat by lia.
    rewrite moutputs_and_NewVar. replace (k + 1)%nat with (S k)%nat by lia.
    replace (S (k + 0))%nat with (S k)%nat by lia. eauto.
Qed.

Lemma mo_equiv_spec_step : forall {p q k}, p ≡ q -> moutputs_of k p = moutputs_of k q.
Proof. intros. revert k. dependent induction H ; try multiset_solver; simpl in *; try rewrite H; eauto.
+ intros. replace (S (S k))%nat with (0 + (S (S k)))%nat by lia. rewrite VarSwap_and_moutputs. eauto.
+ intros. replace (S (S k))%nat with (0 + (S (S k)))%nat by lia. symmetry. rewrite VarSwap_and_moutputs. eauto.
+ intros. f_equal. replace (NewVarC 0 q) with (NewVarCn 0 1 q); eauto.
  replace (S k)%nat with (1 + k)%nat; eauto. rewrite<- NewVarCn_and_moutputs2. eauto.
+ intros. f_equal. replace (NewVarC 0 q) with (NewVarCn 0 1 q); eauto.
  replace (S k)%nat with (1 + k)%nat; eauto. rewrite<- NewVarCn_and_moutputs2. eauto.
+ destruct (Eval_Eq 0 C); eauto. destruct b; eauto.
+ destruct (Eval_Eq 0 C); eauto. destruct b; eauto.
Qed.

Lemma mo_equiv_spec : forall {p q k}, p ≡* q -> moutputs_of k p = moutputs_of k q.
Proof.
  intros p q l hcgr.
  induction hcgr.
  - now eapply mo_equiv_spec_step.
  - etrans; eauto.
Qed.

Lemma simpl_new_output n k c v : moutputs_of k (c ! v • 𝟘) = moutputs_of k (Ѵ n (VarC_add n c ! v • 𝟘)).
Proof.
  revert k c v.
  induction n.
  - intros; simpl; eauto. destruct c; simpl; eauto.
  - intros; simpl. destruct c ; simpl.
    + replace (cst c ! v • 𝟘) with (VarC_add n (cst c) ! v • 𝟘) by eauto.
      rewrite<- IHn. simpl. eauto.
    + destruct (decide (k < S n0)).
      ++ replace (S (n + n0))%nat with (n + S n0)%nat by lia.
         replace (bvar (n + S n0) ! v • 𝟘) with (VarC_add n (bvar (S n0)) ! v • 𝟘) by (simpl; eauto). rewrite<- IHn.
         simpl. rewrite decide_True; try lia. eauto.
      ++ replace (S (n + n0))%nat with (n + S n0)%nat by lia.
         replace (bvar (n + S n0) ! v • 𝟘) with (VarC_add n (bvar (S n0)) ! v • 𝟘) by (simpl; eauto). rewrite<- IHn.
         simpl. rewrite decide_False; try lia. eauto.
Qed.

Lemma mo_spec p a q : lts p (a !) q -> moutputs_of 0 p = {[+ a +]} ⊎ moutputs_of 0 q.
Proof.
  intros l. assert (lts p (a !) q). assumption. apply OutputWithValue in H.
  decompose record H. subst. rename x into c. rename x0 into v.
  eapply TransitionShapeForOutputSimplified in l. eapply mo_equiv_spec in l. simpl in l.
  rewrite l. f_equal. simpl. destruct c; eauto.
  replace (n - 0)%nat with n%nat; try lia. eauto.
Qed.

Lemma mo_spec_l e a k :
  a ∈ moutputs_of k e -> {e' | lts (Ѵ  k e) (ActExt $ ActOut a) (Ѵ  k e') /\ moutputs_of k e' = moutputs_of k e ∖ {[+ a +]}}.
Proof.
  intros mem.
  dependent induction e.
  + cbn in mem.
    destruct (decide (a ∈ moutputs_of k e1)).
    destruct (IHe1 a k e) as (e1' & lts__e1 & eq).
    exists (e1' ‖ e2). repeat split; eauto with ccs.
    eapply inversion_res_ext in lts__e1. eapply lts_res_ext_n.
    eapply lts_parL. eauto.
    multiset_solver.
    destruct (decide (a ∈ moutputs_of k e2)).
    destruct (IHe2 a k e) as (e2' & lts__e2 & eq).
    exists (e1 ‖ e2'). repeat split; eauto with ccs.
    eapply inversion_res_ext in lts__e2. eapply lts_res_ext_n.
    eapply lts_parR. eauto.
    multiset_solver.
    contradict mem. intro mem. multiset_solver.
  + exfalso. multiset_solver.
  + exfalso. multiset_solver.
  + simpl in *. case_eq (Eval_Eq 0 e1); intros.
    ++ rewrite H in mem. destruct b.
       +++ eapply IHe1 in mem as (e' & l & eq).
           exists e'. split ;eauto. eapply lts_res_ext_n. eapply lts_ifOne; eauto.
           eapply inversion_res_ext. eauto.
       +++ eapply IHe2 in mem as (e' & l & eq).
           exists e'. split ;eauto. eapply lts_res_ext_n. eapply lts_ifZero; eauto.
           eapply inversion_res_ext. eauto.
    ++ rewrite H in mem. exfalso. inversion mem.
  + exists (g 𝟘).
    destruct c.
    ++ simpl in *.
       assert (a = (cst c , v)). multiset_solver. subst.
       repeat split; eauto with ccs. eapply lts_res_ext_n. simpl. constructor. multiset_solver.
    ++ simpl in *. destruct (decide (k < S n)).
       +++ split. eapply lts_res_ext_n. simpl. destruct a. assert ((c , v0) = (bvar (n - k) , v)). multiset_solver.
           inversion H; subst. simpl in *. replace (k + (n - k))%nat with n%nat by lia. constructor.
           multiset_solver.
       +++ inversion mem.
  + simpl in *. eapply IHe in mem as (e' & eq1 & eq2).
    exists (ν e'). split. rewrite BigNew_reverse_def_one. rewrite BigNew_reverse_def_one.
    simpl in *; eauto. simpl. eauto.
  + simpl in mem. exfalso. set_solver. 
Qed.

Lemma mo_spec_r e a k:
  {e' | lts (Ѵ  k e) (ActExt $ ActOut a) (Ѵ  k e') /\ moutputs_of k e' = moutputs_of k e ∖ {[+ a +]}} -> a ∈ moutputs_of k e.
Proof.
  dependent induction e; intros (e' & l & mem).
  + cbn. eapply inversion_res_ext in l.
    inversion l; subst.
    eapply gmultiset_elem_of_disj_union. left.
    eapply IHe1. exists p2. split. eapply lts_res_ext_n; eauto. cbn in mem.
    multiset_solver.
    eapply gmultiset_elem_of_disj_union. right.
    eapply IHe2. exists q2. split. eapply lts_res_ext_n; eauto. cbn in mem.
    multiset_solver.
  + eapply inversion_res_ext in l. inversion l.
  + eapply inversion_res_ext in l. inversion l.
  + eapply inversion_res_ext in l. inversion l; subst; simpl in *; rewrite H4 in mem; rewrite H4.
    ++ destruct a. eapply IHe1 ; eauto. exists e'. split. eapply lts_res_ext_n. simpl; eauto. multiset_solver.
    ++ destruct a. eapply IHe2 ; eauto. exists e'. split. eapply lts_res_ext_n. simpl; eauto. multiset_solver.
  + eapply inversion_res_ext in l. inversion l; subst. destruct a.
    inversion H; subst. destruct c0.
    ++ simpl. subst. multiset_solver.
    ++ simpl. rewrite decide_True; try lia. replace (k + n - k)%nat with n%nat by lia. multiset_solver.
  + eapply inversion_res_ext in l. inversion l; subst. destruct a. simpl. eapply IHe. exists p'. split.
    eapply lts_res_ext_n. simpl in *. rewrite<- VarC_add_revert_def in H1. simpl in *. eauto. multiset_solver.
  + destruct a. simpl in *. eapply inversion_res_ext in l. now eapply guarded_does_no_output in l.
Qed.

Lemma outputs_of_spec2 p a : a ∈ outputs_of p -> {q | lts p (ActExt (ActOut a)) q}.
Proof.
  intros mem.
  eapply gmultiset_elem_of_dom in mem.
  eapply mo_spec_l in mem.
  firstorder.
Qed.

Lemma outputs_of_spec1_raw (e : proc) (a : TypeOfActions) k : {e' | lts (Ѵ  k e) (ActExt (ActOut a)) (Ѵ  k e')} 
      -> a ∈ moutputs_of k e.
Proof.
  dependent induction e; intros (e' & l).
  + cbn. eapply inversion_res_ext in l.
    inversion l; subst.
    eapply gmultiset_elem_of_disj_union. left.
    eapply IHe1. exists p2. eapply lts_res_ext_n; eauto.
    eapply gmultiset_elem_of_disj_union. right.
    eapply IHe2. exists q2. eapply lts_res_ext_n; eauto.
  + eapply inversion_res_ext in l. inversion l.
  + eapply inversion_res_ext in l. inversion l.
  + eapply inversion_res_ext in l. inversion l; subst; simpl in *; rewrite H4.
    ++ destruct a. eapply IHe1 ; eauto. exists e'. eapply lts_res_ext_n. simpl; eauto.
    ++ destruct a. eapply IHe2 ; eauto. exists e'. eapply lts_res_ext_n. simpl; eauto.
  + eapply inversion_res_ext in l. inversion l; subst. destruct a.
    inversion H; subst. destruct c0.
    ++ simpl. subst. multiset_solver.
    ++ simpl. rewrite decide_True; try lia. replace (k + n - k)%nat with n%nat by lia. multiset_solver.
  + eapply inversion_res_ext in l. inversion l; subst. destruct a. simpl. eapply IHe. exists p'.
    eapply lts_res_ext_n. simpl in *. rewrite<- VarC_add_revert_def in H1. simpl in *. eauto.
  + destruct a. simpl in *. eapply inversion_res_ext in l. now eapply guarded_does_no_output in l.
Qed.

Lemma outputs_of_spec1 (p : proc) (a : TypeOfActions) (q : proc) : lts p (ActExt (ActOut a)) q
      -> a ∈ outputs_of p.
Proof.
  intros mem.
  eapply gmultiset_elem_of_dom.
  eapply outputs_of_spec1_raw.
  firstorder.
Qed.

Fixpoint lts_set_output (p : proc) (a : TypeOfActions) : gset proc:=
match p with
  | p1 ‖ p2 => 
      let ps1 := lts_set_output p1 a in
      let ps2 := lts_set_output p2 a in
      (set_map (fun p => p ‖ p2) ps1) ∪ (set_map (fun p => p1 ‖ p) ps2)
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | If E Then A Else B => match (Eval_Eq 0 E) with 
                          | Some true => lts_set_output A a
                          | Some false => lts_set_output B a
                          | None => ∅
                          end
  | c ! v • 𝟘 => if decide(a = (c , v)) then {[ (g 𝟘) ]} else ∅
  | ν p => (set_map (fun q => ν q) (lts_set_output p (VarC_TypeOfActions_add 1 a))) 
  | g _  => ∅
end.

Fixpoint lts_set_input_g (g : gproc) (a : TypeOfActions) : gset proc :=
  match g with
  | c ? • p => if decide(ChannelData_of a = c) then {[ p^(ValueData_of a) ]} else ∅
  | g1 + g2 => lts_set_input_g g1 a ∪ lts_set_input_g g2 a
  | ① => ∅
  | 𝟘 => ∅
  | 𝛕 • p => ∅
  end.

Fixpoint lts_set_input (p : proc) (a : TypeOfActions) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1 := lts_set_input p1 a in
      let ps2 := lts_set_input p2 a in
      (set_map (fun p => p ‖ p2) ps1) ∪ (set_map (fun p => p1 ‖ p) ps2)
  | pr_var _ => ∅
  | rec _ • _ => ∅ 
  | c ! v • 𝟘 => ∅
  | If E Then A Else B => match (Eval_Eq 0 E) with 
                          | Some true => lts_set_input A a
                          | Some false => lts_set_input B a
                          | None => ∅
                          end
  | ν p => set_map (fun q => ν q) (lts_set_input p (VarC_TypeOfActions_add 1 a)) 
  | g gp => lts_set_input_g gp a  
  end.

Fixpoint lts_set_tau_g (gp : gproc) : gset proc :=
match gp with
  | c ? • p => ∅
  | ① => ∅
  | 𝟘 => ∅
  | 𝛕 • p => {[ p ]}
  | gp1 + gp2 => lts_set_tau_g gp1 ∪ lts_set_tau_g gp2
end.

Fixpoint lts_set_tau (p : proc) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1_tau : gset proc := set_map (fun p => p ‖ p2) (lts_set_tau p1) in
      let ps2_tau : gset proc := set_map (fun p => p1 ‖ p) (lts_set_tau p2) in
      let ps_tau := ps1_tau ∪ ps2_tau in
      let acts1 := outputs_of p1 in
      let acts2 := outputs_of p2 in
      let ps1 :=
        flat_map (fun a =>
                    map
                      (fun '(p1 , p2) => p1 ‖ p2)
                      (list_prod (elements $ lts_set_output p1 a) (elements $ lts_set_input p2 a)))
        (elements $ outputs_of p1) in
      let ps2 :=
        flat_map
          (fun a =>
             map
               (fun '(p1 , p2) => p1 ‖ p2)
               (list_prod (elements $ lts_set_input p1 a) (elements $ lts_set_output p2 a)))
          (elements $ outputs_of p2)
      in
      ps_tau ∪ list_to_set ps1 ∪ list_to_set ps2
  | c ! v • 𝟘 => ∅
  | pr_var _ => ∅
  | rec x • p => {[ pr_subst x p (rec x • p) ]}
  | If C Then A Else B => match (Eval_Eq 0 C) with 
                          | Some true => lts_set_tau A
                          | Some false => lts_set_tau B
                          | None => ∅
                          end
  | ν p => set_map (fun q => ν q) (lts_set_tau p)
  | g gp => lts_set_tau_g gp
end.

Lemma lts_set_output_spec0 p a q : q ∈ lts_set_output p a -> lts p (ActExt (ActOut a)) q.
Proof.
  intro mem.
  dependent induction p; simpl in mem; try now inversion mem.
  - eapply elem_of_union in mem as [mem | mem]. 
    * eapply elem_of_list_to_set, list_elem_of_fmap in mem as (q' & eq & mem). subst.
    apply lts_parL. apply IHp1. rewrite elem_of_elements in mem. set_solver.
    * eapply elem_of_list_to_set, list_elem_of_fmap in mem as (q' & eq & mem). subst.
    apply lts_parR. apply IHp2. rewrite elem_of_elements in mem. exact mem.
  - case_eq (Eval_Eq 0 e).
    * intros. destruct b.
      ** rewrite H in mem. eapply lts_ifOne; eauto.
      ** rewrite H in mem. eapply lts_ifZero; eauto.
    * intros. rewrite H in mem. exfalso. inversion mem.
  -  case (TypeOfActions_dec a (c , v)) in mem.
    + rewrite e. rewrite e in mem. rewrite decide_True in mem;eauto.
      assert (q = (g 𝟘)). set_solver.
      rewrite H. apply lts_output.
    + destruct (decide (a = (c , v))). exfalso. apply n. assumption. set_solver.
  - eapply elem_of_list_to_set, list_elem_of_fmap in mem as (q' & eq & mem). subst.
    apply lts_res_ext. rewrite elem_of_elements in mem. eapply IHp in mem. simpl. destruct a. eauto.
Qed.

Lemma lts_set_output_spec1 p a q : lts p (ActExt $ ActOut a) q -> q ∈ lts_set_output p a.
Proof.
  intro l. dependent induction l; try set_solver.
  - simpl. rewrite decide_True;eauto. set_solver.
  - simpl in *. rewrite H. eapply IHl; eauto ; simpl.
  - simpl in *. rewrite H. eapply IHl; eauto ; simpl.
  - simpl in *. destruct a. try set_solver.
Qed.

Lemma lts_set_input_spec0 p a q : q ∈ lts_set_input p a -> lts p (ActExt $ ActIn a) q.
Proof.
  intro mem.
  dependent induction p; simpl in mem; try set_solver.
  + eapply elem_of_union in mem. destruct mem.
    ++ eapply elem_of_list_to_set in H.
       eapply list_elem_of_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. eauto with cgr.
    ++ eapply elem_of_list_to_set in H.
       eapply list_elem_of_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. eauto with cgr.
  + case_eq (Eval_Eq 0 e).
    - intros. rewrite H in mem. destruct b.
      ++ eapply lts_ifOne; eauto.
      ++ eapply lts_ifZero; eauto.
    - intros. rewrite H in mem. exfalso. inversion mem.
  + eapply elem_of_list_to_set, list_elem_of_fmap in mem as (q' & eq & mem). subst.
    apply lts_res_ext. rewrite elem_of_elements in mem. eapply IHp in mem. simpl. destruct a. eauto. 
  + dependent induction g; simpl in mem; try set_solver.
      ++ destruct (decide (ChannelData_of a = c)).
         +++ subst. eapply elem_of_singleton_1 in mem. subst. destruct a. simpl. apply lts_input.
         +++ destruct a. simpl in *. inversion mem.
      ++ eapply elem_of_union in mem. destruct mem; eauto with cgr.
Qed.

Lemma lts_set_input_spec1 p a q : lts p (ActExt $ ActIn a) q -> q ∈ lts_set_input p a.
Proof.
  intro l. destruct a. destruct v.
  + dependent induction l; try set_solver.
    ++ simpl. rewrite decide_True; eauto. set_solver.
    ++ simpl in *. rewrite H. eauto.
    ++ simpl in *. rewrite H. eauto.
  + dependent induction l; try set_solver.
    ++ simpl. rewrite decide_True; eauto. set_solver.
    ++ simpl in *. rewrite H. eauto.
    ++ simpl in *. rewrite H. eauto.
Qed.

Lemma lts_set_tau_spec0 p q : q ∈ lts_set_tau p -> lts p τ q.
Proof.
  - intro mem.
    dependent induction p; simpl in mem.
    + eapply elem_of_union in mem. destruct mem as [mem1 | mem2].
      ++ eapply elem_of_union in mem1.
         destruct mem1.
         eapply elem_of_union in H as [mem1 | mem2]. 
         eapply elem_of_list_to_set, list_elem_of_fmap in mem1 as (t' & eq & h); subst.
         rewrite elem_of_elements in h. eauto with cgr.
         eapply elem_of_list_to_set, list_elem_of_fmap in mem2 as (t' & eq & h); subst.
         rewrite elem_of_elements in h. eauto with cgr.
         eapply elem_of_list_to_set, list_elem_of_In, in_flat_map in H as (t' & eq & h); subst.
         eapply list_elem_of_In, list_elem_of_fmap in h as ((t1 & t2) & eq' & h'). subst.
         eapply list_elem_of_In, in_prod_iff in h' as (mem1 & mem2).
         eapply list_elem_of_In in mem1. rewrite elem_of_elements in mem1.
         eapply list_elem_of_In in mem2. rewrite elem_of_elements in mem2.
         eapply lts_set_output_spec0 in mem1.
         eapply lts_set_input_spec0 in mem2. destruct t'. eapply lts_comL. exact mem1. exact mem2.
      ++ eapply elem_of_list_to_set, list_elem_of_In, in_flat_map in mem2 as (t' & eq & h); subst.
         eapply list_elem_of_In, list_elem_of_fmap in h as ((t1 & t2) & eq' & h'). subst.
         eapply list_elem_of_In, in_prod_iff in h' as (mem1 & mem2).
         eapply list_elem_of_In in mem1. rewrite elem_of_elements in mem1.
         eapply list_elem_of_In in mem2. rewrite elem_of_elements in mem2.
         eapply lts_set_input_spec0 in mem1.
         eapply lts_set_output_spec0 in mem2. destruct t'. eapply lts_comR. exact mem2. exact mem1.
    + inversion mem.
    + eapply elem_of_singleton_1 in mem. subst; eauto with cgr.
    + case_eq (Eval_Eq 0 e); intros; rewrite H in mem.
      ++ destruct b.
         +++ eapply lts_ifOne; eauto.
         +++ eapply lts_ifZero; eauto.
      ++ exfalso. inversion mem.
    + inversion mem.
    + eapply elem_of_list_to_set, list_elem_of_fmap in mem as (t' & eq & h); subst.
      eapply lts_res_tau. eapply IHp. eapply elem_of_elements. eauto.
    + dependent induction g; simpl in mem; try set_solver;
        try eapply elem_of_singleton_1 in mem; subst; eauto with cgr.
      eapply elem_of_union in mem as [mem1 | mem2]; eauto with cgr.
Qed.

Lemma lts_set_tau_spec1 p q : lts p τ q -> q ∈ lts_set_tau p.
Proof. 
  intro l. dependent induction l; simpl; try set_solver.
  - rewrite H. set_solver. 
  - rewrite H. set_solver. 
  - eapply elem_of_union. left.
    eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    rewrite list_elem_of_In. rewrite in_flat_map.
    exists (c , v). split.
    + eapply list_elem_of_In, elem_of_elements.
      eapply outputs_of_spec1. eauto.
    + eapply list_elem_of_In, list_elem_of_fmap.
      exists (p2 , q2). split.
      ++ reflexivity.
      ++ eapply list_elem_of_In, in_prod_iff; split; eapply list_elem_of_In, elem_of_elements.
         eapply lts_set_output_spec1; eauto with ccs.
         eapply lts_set_input_spec1; eauto with ccs.
  - eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    rewrite list_elem_of_In. rewrite in_flat_map.
    exists (c , v). split.
    + eapply list_elem_of_In, elem_of_elements.
      eapply outputs_of_spec1. exact l1.
    + eapply list_elem_of_In, list_elem_of_fmap.
      exists (q2 , p2). split.
      ++ reflexivity.
      ++ eapply list_elem_of_In, in_prod_iff; split; eapply list_elem_of_In, elem_of_elements.
         eapply lts_set_input_spec1; eauto with ccs.
         eapply lts_set_output_spec1; eauto with ccs.
Qed.

Definition lts_set (p : proc) (α : ActIO TypeOfActions): gset proc :=
  match α with
  | τ => lts_set_tau p
  | ActExt (ActIn a) => lts_set_input p a
  | ActExt (ActOut a) => lts_set_output p a
  end.

Lemma lts_set_spec0 p α q : q ∈ lts_set p α -> lts p α q.
Proof.
  destruct α as [[a|a]|].
  - now eapply lts_set_input_spec0.
  - now eapply lts_set_output_spec0.
  - now eapply lts_set_tau_spec0.
Qed.

Lemma lts_set_spec1 p α q : lts p α q -> q ∈ lts_set p α.
Proof.
  destruct α as [[a|a]|].
  - now eapply lts_set_input_spec1.
  - now eapply lts_set_output_spec1.
  - now eapply lts_set_tau_spec1.
Qed.

Definition proc_stable p α := lts_set p α = ∅.

Lemma lts_dec p α q : { lts p α q } + { ~ lts p α q }.
Proof.
  destruct (decide (q ∈ lts_set p α)).
  - eapply lts_set_spec0 in e. eauto.
  - right. intro l. now eapply lts_set_spec1 in l.
Qed.

Lemma proc_stable_dec p α : Decision (proc_stable p α).
Proof. destruct (decide (lts_set p α = ∅)); [ left | right ]; eauto. Qed.

Lemma gset_nempty_ex (g : gset proc) : g ≠ ∅ -> {p | p ∈ g}.
Proof.
  intro n. destruct (elements g) eqn:eq.
  + destruct n. eapply elements_empty_iff in eq. set_solver.
  + exists p. eapply elem_of_elements. rewrite eq. set_solver.
Qed.

Definition non_blocking_output (μ : ExtAct TypeOfActions) := (is_output μ).

(** ******* VACCS satisfies the axioms for soundness and completeness *)

#[global] Program Instance VACCS_ExtAction : ExtAction (ExtAct TypeOfActions) :=
  {| non_blocking η := non_blocking_output η ;
      dual μ1 μ2 := ext_act_match μ1 μ2 |}.
Next Obligation.
 intros. simpl. destruct μ.
 * right. intro Hyp. destruct Hyp as (a' & eq). inversion eq.
 * left. exists a. eauto.
Defined.
Next Obligation.
 intros ? ? ? dual nb; simpl in *.
 destruct nb as (a & eq). subst.
 eapply simplify_match_output in dual.
 subst. destruct H. inversion H.
Defined.
Next Obligation.
 intros μ; simpl in *.
 exists (InputOutputActions.io_co μ).
 symmetry. eapply dual_co.
Defined.

#[global] Instance VACCS_UniqueDual : UniqueDual (ExtAct TypeOfActions).
Proof.
  intros μ1 μ2 dual; subst.
  simpl in *.
  destruct μ2 as [ (* Input *) a' | (* Output *) a' ].
  + apply simplify_match_input in dual; subst. eauto.
  + apply simplify_match_output in dual; subst. eauto.
Defined.

Local Program Definition VACCS_gLts : gLts proc VACCS_ExtAction :=
  {| lts_step x α y  := lts x α y ;
     lts_state_eqdec := proc_dec ;
     lts_step_decidable p α q := lts_dec p α q ;
     lts_performs p α := ¬ proc_stable p α;
     lts_performs_decidable p α := not_dec (proc_stable_dec p α)
    |}.
Next Obligation.
  intros p [[a|a]|]; intro hs;eapply gset_nempty_ex in hs as (r & l); eapply lts_set_spec0 in l; 
  exists r; assumption.
Qed.
Next Obligation.
  intros p [[a|a]|]; intros (q & mem); intro eq; eapply lts_set_spec1 in mem; set_solver.
Qed.

#[global] Program Instance VACCS_gLtsEq : gLtsEq proc VACCS_ExtAction :=
  {| gLtsEq_gLts := VACCS_gLts ;
     eq_rel x y  := cgr 0 x y; |}.
Next Obligation.
  apply cgr_is_eq_rel.
Defined.
Next Obligation.
  eapply Congruence_Respects_Transition.
Defined.

#[global] Program Instance VACCS_gLtsOBA : gLtsOba proc.
(*   {| lts_oba_output_commutativity p q r a α := OBA_with_FB_First_Axiom p q r a α;
     lts_oba_output_confluence p q1 q2 a μ := OBA_with_FB_Second_Axiom p q1 q2 a μ;
     lts_oba_output_deter p1 p2 p3 a := OBA_with_FB_Third_Axiom p1 p2 p3 a;
     lts_oba_output_tau p q1 q2 a := OBA_with_FB_Fifth_Axiom p q1 q2 a;
     lts_oba_output_deter_inv p1 p2 q1 q2 a := ExtraAxiom p1 p2 q1 q2 a;
     lts_oba_mo p := moutputs_of 0 p 
  |}. *)
Next Obligation. (* lts_oba_non_blocking_action_delay *)
  intros ? ? ? ? ? nb l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst. 
  eapply OBA_with_FB_First_Axiom; eauto.
Qed.
Next Obligation. (* lts_oba_non_blocking_action_confluence *)
  intros ? ? ? ? ? nb eq l1 l2 ;simpl in *.
  destruct nb as (a & eq'); subst.
  eapply OBA_with_FB_Second_Axiom; eauto.
Qed.
Next Obligation. (* lts_oba_output_tau *)
  intros ? ? ? ? nb l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst.
  eapply OBA_with_FB_Fifth_Axiom in l1 as cases; eauto.
  destruct cases as [computation_without_a | computation_with_a].
  + left. destruct computation_without_a. 
    eexists; eauto.
  + right. exists (ActIn a). split; eauto.
    unfold sc. simpl. eauto.
Qed.
Next Obligation. (* lts_oba_output_deter *)
  intros ? ? ? ? nb l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst. 
  eapply OBA_with_FB_Third_Axiom; eauto.
Qed.
Next Obligation. (* lts_oba_non_blocking_action_deter_inv *)
  intros ? ? ? ? ? nb l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst.
  eapply ExtraAxiom; eauto.
Qed.

#[global] Program Instance VACCS_gLtsOBAFB : gLtsObaFB proc (ExtAct TypeOfActions).
Next Obligation.
  intros ? ? ? ? ? nb dual l1 l2 ;simpl in *.
  destruct nb as (a & eq); subst. symmetry in dual.
  eapply simplify_match_output in dual; subst.
  eapply OBA_with_FB_Fourth_Axiom; eauto.
Qed.

Definition label_to_output (a : TypeOfActions) : ExtAct TypeOfActions := ActOut a.

Definition mo_label_to_mo_output (m : gmultiset TypeOfActions) : gmultiset (ExtAct TypeOfActions) :=
    gmultiset_map label_to_output m.

#[global] Program Instance VACCS_gFiniteNonBlockingChain_LtsOba
 : FiniteNonBlockingChain_LtsOba proc :=
  {| lts_oba_mo p := mo_label_to_mo_output (moutputs_of 0 p) ; |}.
Next Obligation.
  intros ? ? ? nb l.
  destruct η as [a | a].
  + exfalso. inversion nb. inversion H.
  + simpl. eapply elem_of_gmultiset_map.
    exists a. split.
      ++ unfold label_to_output. eauto.
      ++ eapply mo_spec_r. 
         exists p2. split ;simpl ; eauto. 
         eapply mo_spec in l. multiset_solver.
Defined.
Next Obligation.
  intros ? ? Hyp. 
  eapply elem_of_gmultiset_map in Hyp.
  assert ({ x : TypeOfActions | η = label_to_output x ∧ x ∈ moutputs_of 0 p1}) as (a & eq & mem).
  eapply choice; eauto. intros.
  destruct (decide (η = label_to_output x)) as [eq | not_eq].
  + destruct (decide (x ∈ moutputs_of 0 p1)).
    ++ left. split; eauto.
    ++ right. intro Hyp'. destruct Hyp' as (eq' & imp). contradiction.
  + right. intro Hyp'. destruct Hyp' as (eq' & imp). contradiction.
  + eapply mo_spec_l in mem as (q & l & eq'). simpl; subst; eauto.
    exists q. split.
    ++ exists a. subst. eauto.
    ++ unfold label_to_output. exact l.
Defined.
Next Obligation.
  intros ? ? ? nb Hyp;simpl in *.
  destruct nb as (a & eq). subst.
  assert (moutputs_of 0 p = {[+ a +]} ⊎ moutputs_of 0 q) as mem.
  eapply mo_spec. exact Hyp.
  rewrite mem. simpl in *. unfold mo_label_to_mo_output at 1.
  rewrite gmultiset_map_disj_union. rewrite gmultiset_map_singleton.
  unfold label_to_output at 1. reflexivity.
Qed.

#[global] Program Instance VACCS_gLtsFiniteImage : FiniteImagegLts proc (ExtAct TypeOfActions).
Next Obligation.
  intros p α. unfold dsig.
  destruct α as [[a|a]|].
  - eapply (in_list_finite (elements (lts_set_input p a))).
    intros q Htrans%bool_decide_unpack.
    now eapply elem_of_elements, lts_set_input_spec1.
  - eapply (in_list_finite (elements (lts_set_output p a))).
    intros q Htrans%bool_decide_unpack.
    now eapply elem_of_elements, lts_set_output_spec1.
  - eapply (in_list_finite (elements (lts_set_tau p))).
    intros q Htrans%bool_decide_unpack.
    now eapply elem_of_elements, lts_set_tau_spec1.
Defined.

#[global] Program Instance Interaction_between_parallel_VACCS :
  Prop_of_Inter proc proc (ExtAct TypeOfActions) (ExtAct TypeOfActions) dual :=
  {| lts_essential_actions_left p := set_map ActOut (outputs_of p) ;
       lts_essential_actions_right q := set_map ActOut (outputs_of q)|}.
Next Obligation.
  intros ? ? Hyp ;simpl in *.
  unfold set_map in Hyp. simpl in *.
  eapply elem_of_list_to_set in Hyp.
  eapply list_elem_of_fmap in Hyp.
  destruct ξ.
  + exfalso. destruct Hyp as (a' & eq & mem). inversion eq.
  + eapply outputs_of_spec2. destruct Hyp as (a' & eq & mem).
    inversion eq. subst. eapply elem_of_elements. eauto.
Defined.
Next Obligation.
  intros q ? Hyp ;simpl in *.
  unfold set_map in Hyp. simpl in *.
  eapply elem_of_list_to_set in Hyp.
  eapply list_elem_of_fmap in Hyp.
  destruct ξ.
  + exfalso. destruct Hyp as (a' & eq & mem). inversion eq.
  + eapply outputs_of_spec2. destruct Hyp as (a' & eq & mem).
    inversion eq. subst. eapply elem_of_elements. eauto.
Defined.
Next Obligation.
  intros ? ? ? q ? q' ? ? inter;simpl in *.
  destruct μ1 as [ (*Input*) a | (*Output*) a].
  + right. eapply simplify_match_input in inter. subst.
    eapply elem_of_list_to_set.
    eapply list_elem_of_fmap. exists a. split; eauto. 
    eapply elem_of_elements. eapply outputs_of_spec1; eauto.
  + left. eapply simplify_match_output in inter. subst.
    eapply elem_of_list_to_set.
    eapply list_elem_of_fmap. exists a. split; eauto. 
    eapply elem_of_elements. eapply outputs_of_spec1; eauto.
Defined.
Next Obligation.
  intros ξ p;simpl in *.
  destruct ξ as [ (*Input*) a | (*Output*) a ].
  + exact empty. 
  + exact {[ ActIn a ]}.
Defined.
Next Obligation.
  unfold Interaction_between_parallel_VACCS_obligation_4.
  intros ? ? ? ? q mem l inter;simpl in *. 
  eapply elem_of_list_to_set in mem.
  eapply list_elem_of_fmap in mem.
  destruct mem as ( a & eq & mem ); subst.
  symmetry in inter. eapply simplify_match_output in inter. subst. set_solver.
Defined.
Next Obligation.
  intros ξ q;simpl in *.
  destruct ξ as [ (*Input*) a | (*Output*) a ].
  + exact empty. 
  + exact {[ ActIn a ]}.
Defined.
Next Obligation.
  unfold Interaction_between_parallel_VACCS_obligation_6.
  intros ? ? ? ? q mem l inter;simpl in *. 
  eapply elem_of_list_to_set in mem.
  eapply list_elem_of_fmap in mem.
  destruct mem as ( a & eq & mem ); subst. symmetry in inter.
  symmetry in inter. eapply simplify_match_output in inter. subst. set_solver.
Defined.

#[global] Program Instance Interaction_between_VACCS_and_MB: Prop_of_Inter proc (MO (ExtAct TypeOfActions)) (ExtAct TypeOfActions) (ExtAct TypeOfActions) fw_inter :=
    {| lts_essential_actions_left p := empty ;
       lts_essential_actions_right m := dom (MO_without_not_nb m) ; 
       lts_co_inter_action_right m := fun x => empty |}.
Next Obligation. 
  intros ? ? Hyp ;simpl in *.
  inversion Hyp.
Qed.
Next Obligation.
  intros m ? Hyp ;simpl in *.
  eapply gmultiset_elem_of_dom in Hyp. 
  assert (ξ ∈ MO_without_not_nb m) as mem. eauto.
  eapply lts_MO_nb_with_nb_spec1 in mem as (nb & eq).
  eapply gmultiset_disj_union_difference' in eq.
  exists (m ∖ {[+ ξ +]}). rewrite eq at 1.
  eapply lts_multiset_minus; eauto.
Defined.
Next Obligation.
  intros ? ? ? m ? m' ? ? inter;simpl in *.
  right. destruct inter as (duo & nb).
  eapply non_blocking_action_in_ms in nb as eq'; eauto. 
  rewrite<- eq'.
  assert (MO_without_not_nb ({[+ μ2 +]} ⊎ m') 
  = {[+ μ2 +]} ⊎ (MO_without_not_nb m')) as eq.
  eapply lts_MO_nb_spec1; eauto. rewrite eq.
  eapply gmultiset_elem_of_dom.
  multiset_solver.
Defined.
Next Obligation.
  intros ξ p;simpl in *.
  destruct (decide (non_blocking ξ)) as [ nb (* Input_case *) | not_nb (* Ouput_case *)].
  + exact {[ co ξ ]}.
  + exact empty.
Defined.
Next Obligation.
  intros ? ? ? ? m mem l inter;simpl in *.
  unfold Interaction_between_VACCS_and_MB_obligation_4.
  destruct inter as (duo & nb). rewrite decide_True; eauto.
  assert (μ = co ξ). { eapply VACCS_UniqueDual. symmetry. exact duo. }
  subst; set_solver.
Defined.
Next Obligation.
  intros ? ? ? ? m mem l inter;simpl in *.
  inversion mem.
Qed.

#[global] Program Instance Interaction_between_FW_VACCS_and_VACCS :
  Prop_of_Inter (proc * MO (ExtAct TypeOfActions)) proc (ExtAct TypeOfActions) (ExtAct TypeOfActions) dual :=
    {| lts_essential_actions_left p := set_map ActOut (outputs_of p.1) ∪ (dom (MO_without_not_nb p.2)); 
       lts_essential_actions_right q := set_map ActOut (outputs_of q)|}.
Next Obligation.
  intros (p , m) ? ?. simpl in *.
  eapply elem_of_union in H. destruct (decide (ξ ∈ dom (MO_without_not_nb m))).
  + eapply gmultiset_elem_of_dom in e.
    eapply lts_MO_nb_with_nb_spec1 in e as (nb & mem).
    assert ({ m'| m = {[+ ξ +]} ⊎ m'}) as (m' & eq).
    { exists (m ∖ {[+ ξ +]}). multiset_solver. }
    subst. exists (p , m'). eapply ParRight. eapply lts_multiset_minus; eauto.
  + assert (ξ ∈ @set_map TypeOfActions (gset TypeOfActions) _ (ExtAct TypeOfActions) (gset (ExtAct TypeOfActions)) _ _ _  ActOut (outputs_of p)) as Hyp.
    { destruct H as [case1 | case2]. exact case1. contradiction. }
    unfold set_map in Hyp. simpl in *.
    eapply elem_of_list_to_set in Hyp.
    eapply list_elem_of_fmap in Hyp.
    destruct ξ.
    ++ exfalso. destruct Hyp as (a' & eq & mem). inversion eq.
    ++ assert (a ∈ elements (outputs_of p)) as mem.
       { destruct Hyp as (y & Hyp'); destruct Hyp' as (eq' & mem). 
         inversion eq'; subst. eauto. }
       apply elem_of_elements in mem. eapply outputs_of_spec2 in mem.
       destruct mem as (p' & l). exists (p' , m). eapply ParLeft. eauto.
Defined.
Next Obligation.
  intros e ? Hyp ;simpl in *.
  unfold set_map in Hyp. simpl in *.
  eapply elem_of_list_to_set in Hyp.
  eapply list_elem_of_fmap in Hyp.
  destruct ξ as [ (*Input*) a | (*Output*) a].
  + exfalso. destruct Hyp. destruct H. inversion H.
  + assert (a ∈ elements (outputs_of e)) as mem.
    { destruct Hyp as (y & Hyp'); destruct Hyp' as (eq' & mem). 
      inversion eq'; subst. eauto. }
    apply elem_of_elements in mem. eapply outputs_of_spec2 in mem. eauto.
Defined.
Next Obligation.
  intros (p1 , m1) ? (p'1, m'1) ? ? ? Tr ? inter;simpl in *.
 destruct μ2 as [ (*Input*) a | (*Output*) a].
  - symmetry in inter. eapply simplify_match_input in inter. subst. left.
    inversion Tr; subst.
    + eapply elem_of_union. left. eapply elem_of_list_to_set.
      eapply list_elem_of_fmap. exists a. split; eauto.
      eapply elem_of_elements. eapply outputs_of_spec1. eauto.
    + eapply elem_of_union. right. eapply gmultiset_elem_of_dom.
      destruct (decide (non_blocking (ActOut a))) as [nb | b].
      * eapply non_blocking_action_in_ms in l; eauto.
        rewrite<- l. 
        eapply lts_MO_nb_spec1 in nb. rewrite nb. multiset_solver.
      * eapply blocking_action_in_ms in l as (eq & duo & nb);eauto.
        eapply simplify_match_output in duo. subst.
        rewrite duo in Tr, nb. destruct nb. inversion H0.
  - symmetry in inter. eapply simplify_match_output in inter. subst. right.
    eapply elem_of_list_to_set.
    eapply list_elem_of_fmap. exists a. split; eauto.
    eapply elem_of_elements. eapply outputs_of_spec1. eauto.
Qed.
Next Obligation.
  intros ξ p ;simpl in *. destruct ξ as [ (*Input*) a | (*Output*) a].
  + exact empty. 
  + exact {[ ActIn a ]}.
Defined.
Next Obligation.
  intros p q ? μ ? mem ? inter;simpl in *.
  unfold Interaction_between_FW_VACCS_and_VACCS_obligation_4. destruct ξ as [ (*Input*) a | (*Output*) a].
  - eapply elem_of_list_to_set in mem.
    eapply list_elem_of_fmap in mem. destruct mem as (? & eq & ?).
    inversion eq.
  - symmetry in inter. eapply simplify_match_output in inter. subst. set_solver.
Defined.
Next Obligation.
  intros ξ e;simpl in *.
  destruct ξ as [ a (* Input_case *) | a (* Ouput_case *)].
  + exact {[ ActOut a ]}.
  + exact {[ ActIn a ]}.
Defined.
Next Obligation.
  intros p q ? μ (p1 , m1) mem ? inter;simpl in *.
  unfold Interaction_between_FW_VACCS_and_VACCS_obligation_6. symmetry in inter.
  destruct ξ as [ (*Input*) a | (*Output*) a].
  - symmetry in inter. eapply simplify_match_input in inter. subst.
    eapply elem_of_union in mem. destruct mem as [case1 | case2].
    + set_solver.
    + set_solver.
  - symmetry in inter. eapply simplify_match_output in inter. subst. set_solver.
Defined.

Inductive FinA :=
| Inputs (c : ChannelData)
.

Definition Φᴠᴀᴄᴄꜱ (μ : ExtAct TypeOfActions) : FinA :=
match μ with
| ActIn (c , v) => (Inputs c)
| ActOut (c , v) => (Inputs c)
end.

Definition PreAct := FinA.

Definition 𝝳ᴠᴀᴄᴄꜱ (pre_μ : FinA) : PreAct := pre_μ.

#[global] Program Instance EqPreAct : EqDecision PreAct.
Next Obligation.
  intros. destruct x , y.
  + destruct (decide( c = c0)).
    - left. f_equal. subst. eauto.
    - right. intro. inversion H. contradiction.
Qed.

Definition encode_PreAct (c : PreAct) : gen_tree ChannelData :=
match c with
  | Inputs c => GenLeaf c
end.

Definition decode_PreAct (tree : gen_tree ChannelData) : option PreAct :=
match tree with
  | GenLeaf c => Some (Inputs c)
  | _ => None
end.

Lemma encode_decide_PreAct c : decode_PreAct (encode_PreAct c) = Some c.
Proof. case c. 
* intros. simpl. reflexivity.
Qed.

#[global] Instance CountPreAct : Countable PreAct.
Proof.
  refine (inj_countable encode_PreAct decode_PreAct _).
  apply encode_decide_PreAct.
Qed.

Fixpoint  mPreCoAct_of (k : nat) p : gmultiset PreAct := 
match p with
  | P ‖ Q => (mPreCoAct_of k P) ⊎ (mPreCoAct_of k Q)
  | (cst c) ! v • 𝟘 => {[+ Inputs (cst c) +]}
  | (bvar i) ! v • 𝟘 => if decide(k < (S i)) then {[+ Inputs (bvar (i - k)) +]}
                                              else ∅
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | If E Then P Else Q => match (Eval_Eq 0 E) with 
                          | Some true => mPreCoAct_of k P
                          | Some false => mPreCoAct_of k Q
                          | None => ∅
                          end
  | ν p => mPreCoAct_of (S k) p
  | g p => ∅
end.

Definition PreCoAct_of p := dom (mPreCoAct_of 0 p).

Lemma mPreCoAct_of_res_n_g j n g1 : mPreCoAct_of j (Ѵ n (g g1)) = mPreCoAct_of (n + j) (g g1).
Proof.
  revert g1 j.
  induction n.
  + simpl; eauto.
  + intros; simpl in *. replace (S (n + j))%nat with (n + (S j))%nat by lia.
    eapply IHn.
Qed.

Lemma mPreCoAct_of_res_n j n p1 : mPreCoAct_of j (Ѵ n p1) = mPreCoAct_of (n + j) p1.
Proof.
  revert p1 j.
  induction n.
  + simpl; eauto.
  + intros; simpl in *. replace (S (n + j))%nat with (n + (S j))%nat by lia.
    eapply IHn.
Qed.

Lemma PreCoAct_NewVarC k j p : mPreCoAct_of (k + S j) (NewVarC j p) = mPreCoAct_of (k + j) p.
Proof.
  revert k j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0));
  destruct p; intros k j; simpl in *; eauto.
  + assert (mPreCoAct_of (k + S j) (NewVarC j p1) = mPreCoAct_of (k + j) p1) as eq1.
    { eapply Hp. simpl. lia. }
    assert (mPreCoAct_of (k + S j) (NewVarC j p2) = mPreCoAct_of (k + j) p2) as eq2.
    { eapply Hp. simpl. lia. }
    rewrite eq1, eq2. eauto.
  + case_eq (Eval_Eq 0 e).
    ++ intros. destruct b.
       +++ eauto with lia.
       +++ eauto with lia.
    ++ eauto with lia.
  + destruct c; simpl.
      ++ eauto.
      ++ destruct (decide (j < S n)).
         +++ destruct (decide (k + j < S n)).
             ++++ rewrite decide_True; try lia.
                  replace (S n - (k + S j))%nat with (n - (k + j))%nat by lia. eauto.
             ++++ rewrite decide_False; try lia. eauto.
         +++ rewrite decide_False; try lia.
             rewrite decide_False; try lia. eauto.
  + replace (S (k + S j))%nat with (k + S (S j))%nat by lia.
    replace (S (k + j))%nat with (k + S j)%nat by lia.
    eapply Hp. simpl; eauto.
Qed.

Lemma PreCoAct_VarSwap k j p : mPreCoAct_of (j + S (S k)) p = mPreCoAct_of (j + S (S k)) (VarSwap_in_proc j p).
Proof.
  revert k j.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0));
  destruct p; intros k j; simpl in *; eauto.
  + assert (mPreCoAct_of (j + S (S k)) p1 = mPreCoAct_of (j + S (S k)) (VarSwap_in_proc j p1)) as eq1.
    { eapply Hp; simpl; eauto. lia. }
    assert (mPreCoAct_of (j + S (S k)) p2 = mPreCoAct_of (j + S (S k)) (VarSwap_in_proc j p2)) as eq2.
    { eapply Hp; simpl; eauto. lia. } rewrite eq1, eq2. eauto.
  + case_eq (Eval_Eq 0 e).
    ++ intros. destruct b.
       +++ eauto with lia.
       +++ eauto with lia.
    ++ eauto with lia.
  + destruct c.
      ++ simpl. eauto.
      ++ simpl. destruct (decide (j + S (S k) < S n)).
         ++++ destruct (decide (n = j)).
              +++++ subst. destruct (decide (j + S (S k) < S (S j))).
                    ++++++ lia.
                    ++++++ lia.
              +++++ destruct (decide (n = S j)).
                    ++++++ subst. lia.
                    ++++++ rewrite decide_True; try lia. eauto.
         ++++ destruct (decide (n = j)).
              +++++ subst. rewrite decide_False; try lia. eauto.
              +++++ destruct (decide (n = S j)).
                    ++++++ subst. rewrite decide_False; try lia. eauto.
                    ++++++ rewrite decide_False; try lia. eauto.
  + replace (S (j + S (S k)))%nat with ((S j) + S (S k))%nat by lia.
    eapply Hp. simpl; eauto.
Qed.

Lemma PreCoEquiv (k : nat) (p : proc) (q : proc) (c : PreAct) : p ≡* q -> c ∈ mPreCoAct_of k p -> c ∈ mPreCoAct_of k q.
Proof.
  intros eq mem. revert k c mem. dependent induction eq.
  + dependent induction H; intros; simpl in *; subst; eauto; try multiset_solver.
    * rewrite H in mem; eauto.
    * rewrite H; eauto.
    * rewrite H in mem; eauto.
    * rewrite H; eauto.
    * replace (S (S k))%nat with (0 + (S (S k)))%nat by lia. rewrite<- PreCoAct_VarSwap. simpl; eauto.
    * replace (S (S k))%nat with (0 + (S (S k)))%nat in mem by lia. rewrite<- PreCoAct_VarSwap in mem. simpl; eauto.
    * eapply gmultiset_elem_of_disj_union in mem. destruct mem.
      - eapply gmultiset_elem_of_disj_union. left. eauto.
      - eapply gmultiset_elem_of_disj_union. right.
        replace (S k)%nat with (k + S 0)%nat in H by lia. rewrite PreCoAct_NewVarC in H.
        replace (k + 0)%nat with k%nat in H by lia. eauto.
    * eapply gmultiset_elem_of_disj_union in mem. destruct mem.
      - eapply gmultiset_elem_of_disj_union. left. eauto.
      - eapply gmultiset_elem_of_disj_union. right.
        replace (S k)%nat with (k + S 0)%nat by lia. rewrite PreCoAct_NewVarC.
        replace (k + 0)%nat with k%nat by lia. eauto.
    * case_eq (Eval_Eq 0 C).
      ++ intros. destruct b.
         +++ rewrite H0 in mem; eauto.
         +++ rewrite H0 in mem; eauto.
      ++ intros. rewrite H0 in mem; eauto.
    * case_eq (Eval_Eq 0 C).
      ++ intros. destruct b.
         +++ rewrite H0 in mem; eauto.
         +++ rewrite H0 in mem; eauto.
      ++ intros. rewrite H0 in mem; eauto.
  + eauto.
Qed.

Definition VarC_preaction_add (k : nat) (pre_μ : PreAct) : PreAct :=
match pre_μ with
| Inputs c => Inputs (VarC_add k c)
end.

Lemma VarC_preaction_add_zero pre_μ : VarC_preaction_add 0 pre_μ = pre_μ.
Proof.
  destruct pre_μ; simpl. destruct c; simpl; eauto.
Qed.

(* Lemma VarC_preaction_add_rev j k pre_μ μ' : 
      VarC_preaction_add (j + k) pre_μ = Φᴠᴀᴄᴄꜱ  (VarC_action_add (j + k) μ') 
      -> VarC_preaction_add k pre_μ = Φᴠᴀᴄᴄꜱ  (VarC_action_add k μ').
Proof.
  revert k pre_μ μ'.
  induction j.
  + simpl; eauto.
  + intros; simpl. destruct pre_μ; destruct μ'.
    ++ destruct f; destruct a.
       +++ simpl in *. destruct c0.
           ++++ inversion H; subst. f_equal. destruct c. simpl; eauto.
           ++++ simpl in *. inversion H.
       +++ simpl in *. destruct c.
           ++++ simpl in *. inversion H.
           ++++ simpl in *. inversion H. f_equal. assert (n = n0)%nat by lia. subst; eauto.
    ++ destruct c; destruct a.
       +++ simpl in *. destruct c0.
           ++++ simpl; eauto.
           ++++ simpl in *. inversion H.
       +++ simpl in *. destruct c.
           ++++ simpl in *. inversion H.
           ++++ simpl in *. inversion H.
Qed. *)

Lemma simpl_dual_VarC_add μ'' μ' k : dual μ'' (VarC_action_add k μ') -> μ'' = VarC_action_add k (co μ').
Proof.
  revert μ'' μ'.
  intros; eauto. destruct μ'; destruct a; destruct c; symmetry in H;
    destruct μ''; simpl in * ; try inversion H; subst; eauto.
Qed.

Lemma simpl_dual_VarC j k μ': dual (VarC_action_add (j + k) (co μ')) (VarC_action_add (j + k) μ') 
              -> dual (VarC_action_add k (co μ')) (VarC_action_add k μ').
Proof.
  intros. destruct μ'; destruct a; destruct c; simpl; eauto.
Qed.

Lemma simpl_blocking_Varc j k μ' : ¬ non_blocking (VarC_action_add (j + k) μ')
  -> ¬ non_blocking (VarC_action_add k μ').
Proof.
  intros. destruct μ'; destruct a; destruct c; simpl; eauto.
  + intro imp; inversion imp; inversion H0.
  + intro. simpl in *. inversion H0. inversion H1. subst.
    assert (non_blocking_output (ActOut (bvar (j + k + n) , v))).
    exists (bvar (j + k + n) , v). eauto. contradiction.
Qed.

Lemma VarC_action_add_co_rev j k μ' p : VarC_action_add (j + k) μ' ∈ coR p
                        -> VarC_action_add k μ' ∈ coR (Ѵ  j p).
Proof.
  revert k μ' p.
  induction j.
  + simpl ;eauto.
  + intros; simpl in *. rewrite<- BigNew_reverse_def_one.
    eapply IHj. exists (VarC_action_add (j + k) (co μ')).
    destruct H as (μ'' & eq1 & eq2 & eq3).
    eapply lts_performs_spec1 in eq1 as (p' & tr). 
    assert (dual μ'' (VarC_action_add (S (j + k)) μ')); eauto.
    eapply simpl_dual_VarC_add in eq2. subst.
    repeat split.
    ++ eapply lts_performs_spec2. exists (ν p'). eapply lts_res_ext.
       rewrite VarC_action_add_add; simpl; eauto.
    ++ eapply (simpl_dual_VarC 1). simpl; eauto.
    ++ eapply (simpl_blocking_Varc 1). simpl ; eauto.
Qed.

Lemma delta_phi_newVarC j μ : VarC_preaction_add j ((𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ) μ) = (𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ) (VarC_action_add j μ).
Proof.
  destruct μ; destruct a; destruct c; eauto ; simpl.
Qed.
 
Lemma delta_phi_newVarC_inversion j μ μ' :
  VarC_preaction_add j μ' = (𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ) μ -> (exists μ'', μ = VarC_action_add j μ'' /\ μ' = (𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ) μ'').
Proof.
  intro.
  destruct μ; destruct a; destruct c; eauto ; simpl in *.
  + destruct μ'; destruct c0; simpl in *; inversion H; subst.
    exists (ActIn (cst c , v)). split ; eauto.
  + destruct μ'; destruct c; simpl in *; inversion H; subst.
    exists (ActIn (bvar n0 , v)). split ; eauto.
  + destruct μ'; destruct c0; simpl in *; inversion H; subst.
    exists (ActOut (cst c , v)). split ; eauto.
  + destruct μ'; destruct c; simpl in *; inversion H; subst.
    exists (ActOut (bvar n0 , v)). split ; eauto.
Qed.

Lemma VarC_action_add_co_rev_map j k μ' p : VarC_preaction_add (j + k) μ' ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR p)
                        -> VarC_preaction_add k μ' ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR (Ѵ  j p)).
Proof.
  revert k μ' p.
  induction j.
  + simpl ;eauto.
  + intros; simpl in *. rewrite<- BigNew_reverse_def_one.
    eapply IHj. destruct H as (μ & duo & eq).
    assert (exists μ'', μ = VarC_action_add (S (j + k)) μ'' /\ μ' = (𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ) μ'') as (μ'' & eq'' & eq''').
    { eapply delta_phi_newVarC_inversion; eauto. } subst.
    assert (S (j + k) = 1 + (j + k))%nat as eq'''' by lia.
    rewrite eq'''' in duo. eapply VarC_action_add_co_rev in duo.
    exists (VarC_action_add (j + k) μ''). split; eauto.
    eapply delta_phi_newVarC.
Qed.

Lemma specPreAct1 k : ∀ (pre_μ : PreAct) (p : proc),
   pre_μ ∈ (λ p0 : proc, mPreCoAct_of k p0) p -> (VarC_preaction_add k pre_μ) ∈ ⌈ (𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ) ⌉ (coR p).
Proof.
  intros. simpl in *. revert k pre_μ H.
  induction p as (p & Hp) using
        (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros.
  * simpl in *. eapply gmultiset_elem_of_disj_union in H. destruct H.
    -- eapply (Hp p1) in H. destruct H as (μ' & eq & mem).
       destruct eq as (μ'' & Tr & duo & b). exists μ'. split; eauto. 
       exists μ''. repeat split; eauto. eapply lts_performs_spec1 in Tr as (p'1 & Tr).
       eapply lts_performs_spec2. exists (p'1 ‖ p2). constructor. eauto. simpl. lia.
    -- eapply (Hp p2) in H. destruct H as (μ' & eq & mem).
       exists μ'. split; eauto. destruct eq as (μ'' & Tr & duo & b).
       exists μ''. repeat split; eauto. eapply lts_performs_spec1 in Tr as (p'2 & Tr).
       eapply lts_performs_spec2. exists (p1 ‖ p'2). constructor. eauto. simpl. lia.
  * simpl in *. inversion H.
  * simpl in *. inversion H.
  * case_eq (Eval_Eq 0 e); intros; simpl in *. rewrite H0 in H. destruct b.
    -- eapply (Hp p1) in H. destruct H as (μ' & eq & mem).
       exists μ'. split; eauto. destruct eq as (μ'' & Tr & duo & b).
       exists μ''. repeat split; eauto. eapply lts_performs_spec1 in Tr as (p'1 & Tr).
       eapply lts_performs_spec2. exists p'1. constructor; eauto. lia.
    -- eapply (Hp p2) in H. destruct H as (μ' & eq & mem).
       exists μ'. split; eauto. destruct eq as (μ'' & Tr & duo & b).
       exists μ''. repeat split; eauto. eapply lts_performs_spec1 in Tr as (p'2 & Tr).
       eapply lts_performs_spec2. exists p'2. eapply lts_ifZero; eauto. lia.
    -- eapply gmultiset_elem_of_dom in H. simpl in *. rewrite H0 in H. inversion H.
  * simpl in *. destruct c.
    ** assert (pre_μ = Inputs (cst c)) by multiset_solver.
       rewrite H0. simpl. assert ((𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ) (ActIn (cst c , v)) = Inputs (cst c)). simpl; eauto.
       rewrite<- H1. eapply map_gamma_of_action. exists (ActOut (cst c , v)). repeat split.
       eapply lts_performs_spec2. exists (g 𝟘). constructor. intro. inversion H2. inversion H3.
    ** destruct (decide ((k < S n))).
       - assert (pre_μ = Inputs (bvar (n - k))) by multiset_solver.
         rewrite H0. simpl. assert ((k + (n - k) = n)%nat) by lia. subst. rewrite H1.
         assert ((𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ) (ActIn (bvar n , v)) = Inputs (bvar n)). simpl; eauto.
         rewrite<- H0. eapply map_gamma_of_action. exists (ActOut (bvar n , v)). repeat split.
         eapply lts_performs_spec2. exists (g 𝟘). constructor. intro. inversion H2. inversion H3.
       - inversion H.
  * simpl in *. assert (S k = 1 + k)%nat as eq'' by lia.
    rewrite eq'' in H.
    eapply (VarC_action_add_co_rev_map 1 k).
    eapply Hp; try lia. eauto.
  * simpl in *. inversion H.
Qed.

#[global] Program Instance AbsVACCS :
  @AbsAction proc proc FinA PreAct (ExtAct TypeOfActions) VACCS_ExtAction Φᴠᴀᴄᴄꜱ 𝝳ᴠᴀᴄᴄꜱ _ _ (@gLtsEq_gLts proc _ _ VACCS_gLtsEq) VACCS_gLtsEq _.
Next Obligation.
  intros. destruct β; destruct β'; destruct a; destruct a0.
  - inversion H1; subst.
    eapply lts_performs_spec1 in H2 as (e' & Tr).
    eapply TransitionShapeForInput in Tr as (P1 & G & R & n & eq & eq' & Hyp).
    assert (Ѵ n ((gpr_input (VarC_add n c0) P1 + G) ‖ R) ⟶{(c0 , v0) ?}) as accepts.
    { eapply lts_performs_spec2. exists (Ѵ n (P1 ^ v0 ‖ R)). eapply lts_res_ext_n. eapply lts_parL. eapply lts_choiceL. constructor. }
    eapply (@accepts_preserved_by_eq proc (ExtAct TypeOfActions) VACCS_ExtAction VACCS_gLtsEq) in accepts.
    exact accepts. symmetry. eauto.
  - exfalso. eapply H0. exists (c0 , v0). eauto.
  - exfalso. eapply H. exists (c , v). eauto.
  - exfalso. eapply H. exists (c , v). eauto.
Qed.
Next Obligation.
  - intros. destruct H2 as (μ'' & eq & mem). destruct β.
    + destruct a. simpl in *. destruct μ''.
      * simpl in *. destruct a. inversion mem. subst. destruct β'.
        -- destruct a. simpl in *. inversion H1; subst.
           destruct eq as (μ'' & tr & duo & b).
           symmetry in duo. eapply simplify_match_input in duo. subst.
           exists (ActIn(c , v0)). split ;eauto. exists (ActOut (c , v0)).
           repeat split ;eauto.
        -- exfalso. eapply H0. exists a. eauto.
      * destruct eq as (a' & Tr' & duo' & b).
        exfalso. eapply b. exists a; eauto.
    + destruct a. simpl in *. exfalso. eapply H. exists (c , v);eauto.
Qed.

#[global] Program Instance FinitaryAbsVACCS :
  @FinitaryAbsAction proc proc FinA PreAct (ExtAct TypeOfActions) VACCS_ExtAction Φᴠᴀᴄᴄꜱ 𝝳ᴠᴀᴄᴄꜱ _ _ (@gLtsEq_gLts proc _ _ VACCS_gLtsEq) VACCS_gLtsEq _ _ _ :=
  {| coR_abs p := PreCoAct_of p ; |}.
Next Obligation.
  intros; subst. eapply gmultiset_elem_of_dom in H.
  eapply (specPreAct1 0) in H. rewrite VarC_preaction_add_zero in H. eauto.
Qed.
Next Obligation.
  intros. simpl in *. destruct H as (μ & eq & mem).
  destruct μ.
  + destruct eq as (μ' & Tr & duo & b). symmetry in duo.
    destruct a. eapply simplify_match_input in duo. subst.
    eapply lts_performs_spec1 in Tr as (p' & Tr).
    eapply TransitionShapeForOutput in Tr as (R & n & eq & eq').
    assert ((𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ) (ActIn (c , v)) ∈ PreCoAct_of (Ѵ n ((VarC_add n c ! v • 𝟘) ‖ R))).
    { eapply gmultiset_elem_of_dom. simpl. rewrite mPreCoAct_of_res_n.
      simpl. destruct c; simpl.
      + multiset_solver.
      + rewrite decide_True; try lia. replace (n + n0 - (n + 0))%nat with n0%nat by lia.
        multiset_solver. }
    eapply gmultiset_elem_of_dom. eapply PreCoEquiv. symmetry. eauto.
    eapply gmultiset_elem_of_dom. eauto.
  + destruct eq as (μ' & Tr & duo & b).
    destruct b. exists a; eauto.
Qed.

End VACCS_lts.

Section VACCS_CoFiniteImage.

Context `{VP : VACCS_Parameters}.

#[local] Instance VACCS_gLts_reexport : gLts proc VACCS_ExtAction :=
  @gLtsEq_gLts proc _ _ VACCS_gLtsEq.

Lemma vaccs_dual_image_in_iff (p : proc) (a : TypeOfActions) (q : proc) :
  (exists α' : ExtAct TypeOfActions, dual α' (ActIn a) /\ p ⟶[α'] q) <-> p ⟶[ActOut a] q.
Proof.
  split.
  - intros (α' & duo & tr). destruct α' as [x|x]; simpl in duo; [done|].
    assert (x = a) as -> by exact duo. exact tr.
  - intros tr. exists (ActOut a). split; [reflexivity | exact tr].
Qed.

Lemma vaccs_dual_image_out_iff (p : proc) (a : TypeOfActions) (q : proc) :
  (exists α' : ExtAct TypeOfActions, dual α' (ActOut a) /\ p ⟶[α'] q) <-> p ⟶[ActIn a] q.
Proof.
  split.
  - intros (α' & duo & tr). destruct α' as [x|x]; simpl in duo; [|done].
    assert (x = a) as -> by exact duo. exact tr.
  - intros tr. exists (ActIn a). split; [reflexivity | exact tr].
Qed.

#[global] Instance VACCS_gLtsCoFiniteImage : coFiniteImagegLts proc (ExtAct TypeOfActions).
Proof.
  unshelve refine {|
    cofolts_states_countable := proc_count;
    cofolts_tau_next_states_finite := _;
    cofolts_next_states_decidable := _;
    cofolts_next_states_finite := _;
  |}.
  - intros p α q. destruct α as [a|a].
    + destruct (decide (p ⟶[ActOut a] q)) as [Hd|Hd].
      * left. eapply vaccs_dual_image_in_iff. exact Hd.
      * right. intro Hc. eapply Hd. eapply vaccs_dual_image_in_iff. exact Hc.
    + destruct (decide (p ⟶[ActIn a] q)) as [Hd|Hd].
      * left. eapply vaccs_dual_image_out_iff. exact Hd.
      * right. intro Hc. eapply Hd. eapply vaccs_dual_image_out_iff. exact Hc.
  - intros p α. unfold dsig. destruct α as [a|a].
    + unshelve eapply (in_list_finite (elements (lts_set_output p a))).
      intros q Htrans%bool_decide_unpack.
      eapply elem_of_elements, lts_set_output_spec1, vaccs_dual_image_in_iff.
      exact Htrans.
    + unshelve eapply (in_list_finite (elements (lts_set_input p a))).
      intros q Htrans%bool_decide_unpack.
      eapply elem_of_elements, lts_set_input_spec1, vaccs_dual_image_out_iff.
      exact Htrans.
Defined.

End VACCS_CoFiniteImage.
