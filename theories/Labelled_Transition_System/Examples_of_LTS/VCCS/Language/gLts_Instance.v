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

From Stdlib.Program Require Import Equality.
From Stdlib.Strings Require Import String.
From Stdlib Require Import Relations.
From Stdlib.Wellfounded Require Import Inverse_Image.

From stdpp Require Import base countable finite gmap list gmultiset strings.

From TestingTheory Require Import
  ActTau InputOutputActions Clos_n InListPropHelper Subset_Act
  gLts Bisimulation Lts_OBA Lts_Finite_Non_Blocking_Chain Lts_OBA_FB Lts_FW FiniteImageLTS
  Must InteractionBetweenLts MultisetLTSConstruction ParallelLTSConstruction ForwarderConstruction
  DefinitionAS Equivalence coFiniteImage.
From TestingTheory Require Export VCCS.Language.LTS VCCS.Helper.Substitution VCCS.Language.Congruence VCCS.Harmony_Lemma.Harmony.



Section VCCS_lts.

Context `{VP : VCCS_Parameters}.
Existing Instance VP.

Inductive Well_Defined_Data : nat -> ValueData -> Prop :=
| bvar_is_defined_up_to_k: forall k x, (x < k) -> Well_Defined_Data k (bvar x)
| cst_is_always_defined : forall k x, Well_Defined_Data k (cst x).

Inductive Well_Defined_Condition : nat -> Equation ValueData -> Prop :=
| equationOnValueXX : forall k x y, Well_Defined_Data k x -> Well_Defined_Data k y -> Well_Defined_Condition k (x == y).

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
| WD_output : forall k c v p, Well_Defined_Data k v 
                    -> Well_Defined_Input_in k p -> Well_Defined_Input_in k (c ! v • p)
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
- intros. dependent destruction H. constructor; apply Hp; simpl; auto with arith; assumption.
- destruct g.
  ** intros. constructor.
  ** intros. constructor.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. constructor. apply Inequation_k_data. dependent destruction H. assumption.
     apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. constructor. apply Hp. simpl; auto with arith. dependent destruction H. assumption.
  ** intros. dependent destruction H. constructor.
    -- apply Hp. simpl; auto with arith. assumption.
    -- apply Hp. simpl; auto with arith. assumption.
Qed.

(* False for the moment due to congruence on IF THEN ELSE *)
(* Lemma Congruence_step_Respects_WD_k : forall p q k, Well_Defined_Input_in k p -> p ≡ q -> Well_Defined_Input_in k q. 
Proof.
intros. revert H. revert k. dependent induction H0 ; intros.
* auto.
* dependent destruction H0; auto.
* constructor; eauto. dependent destruction H0; auto.
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
    -- constructor. apply NotK. apply transitivity with n. lia.         assumption. lia.
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
* intros. simpl. dependent destruction H. constructor. apply Hp. simpl. auto with arith. assumption.
* destruct g.
  - intros. simpl. constructor.
  - intros. simpl. constructor.
  - intros. simpl. constructor. apply Hp. simpl. auto. dependent destruction H. assumption.
  - intros. simpl. constructor.
    -- eapply ForData. dependent destruction H. assumption.
    -- apply Hp. simpl. auto. dependent destruction H. assumption.
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
  * constructor. dependent destruction H. apply transitivity with i.
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
* constructor. dependent destruction H. apply Hp. simpl. auto with arith. assumption.
* destruct g; intros; simpl.
  - constructor.
  - constructor.
  - dependent destruction H. constructor. 
    assert (S (S (k + i)) = (S k + S i)%nat). simpl. auto with arith.
    rewrite H0. apply Hp. simpl. auto with arith. assert ((k + S i)%nat = S (k + i)).  auto with arith. rewrite H1. assumption.
  - dependent destruction H. constructor. apply WD_data_and_NewVar. assumption.
    apply Hp. simpl. auto with arith. assumption.
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
* constructor. dependent destruction H. apply Hp. simpl. auto with arith. assumption.
* destruct g; intros; simpl.
  - constructor.
  - constructor.
  - dependent destruction H. constructor. 
    apply Hp. simpl. auto with arith. eauto.
  - dependent destruction H. constructor. eauto.
    apply Hp. simpl. auto with arith. assumption.
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
* intros. simpl. dependent destruction H. constructor. 
  apply Hp. simpl; auto with arith. eapply WD_and_NewVarC. eauto. eauto.
* destruct g. 
  ** intros. simpl. constructor.
  ** intros. simpl. constructor.
  ** intros. simpl. constructor. dependent destruction H. apply Hp. 
    - simpl;auto with arith.
    - assert ((S k) = ((S k) + 0)%nat). auto with arith. rewrite H1. apply (WD_and_NewVar k 0 p0).
      assert (k = (k + 0)%nat). auto with arith. rewrite <-H2. assumption. 
    - assumption.
  ** intros. simpl. constructor. dependent destruction H. assumption. apply Hp.
    - simpl; auto with arith.
    - assumption.
    - dependent destruction H. assumption.
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

Lemma RecursionOverReduction_is_WD : forall k x p, Well_Defined_Input_in k (rec x • p) -> Well_Defined_Input_in k (pr_subst x p (rec x • p)).
Proof.
intros. apply ForRecursionSanity. dependent destruction H. assumption. assumption.
Qed.

Lemma Well_Def_Data_Is_a_value : forall d, Well_Defined_Data 0 d <-> exists v, d = cst v.
Proof.
intros. split. 
- intro. dependent destruction H. exfalso. dependent induction H. exists x. reflexivity.
- intros. destruct H. subst. constructor.
Qed.

(* Lemma STS_Respects_WD : forall p q, Well_Defined_Input_in 0 p -> sts p q -> Well_Defined_Input_in 0 q.
Proof.
intros. revert H. rename H0 into Reduction. dependent induction Reduction.
* intros. constructor.
  - dependent destruction H. dependent destruction H. dependent destruction H. assumption.
  - dependent destruction H. dependent destruction H0. dependent destruction H0_. apply ForSTS. assumption. 
* intros. dependent destruction H. dependent destruction H. assumption.
* intros. dependent destruction H. apply RecursionOverReduction_is_WD. constructor. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H0. assumption.
* intros. dependent destruction H. constructor. apply IHReduction. assumption. assumption.
* intros. apply Congruence_Respects_WD with q2. apply IHReduction. apply Congruence_Respects_WD with p1. 
  assumption. assumption. assumption.
Qed. *)

Inductive Well_Defined_Action: (ActIO TypeOfActions) -> Prop :=
| ActionOuput_with_value_is_always_defined : forall c v, Well_Defined_Action ((c , (cst v))!)
| ActionInput_with_value_is_always_defined : forall c v, Well_Defined_Action ((c , (cst v))?)
| Tau_is_always_defined : Well_Defined_Action τ.

Inductive Well_Defined_ExtAction: (ExtAct TypeOfActions) -> Prop :=
| ExtActionOuput_with_value_is_always_defined : forall c v, Well_Defined_ExtAction (ActOut (c , (cst v)))
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

Lemma LTS_Respects_WD : forall p q 𝜆, Well_Defined_Input_in 0 p -> Well_Defined_Action 𝜆 -> 
        lts p 𝜆 q ->  Well_Defined_Input_in 0 q.
Proof.
intros. revert H. revert H0. rename H1 into Transition. dependent induction Transition.
* intros. dependent destruction H0. apply ForSTS. dependent destruction H. assumption.
* intros. dependent destruction H. assumption.
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

Lemma TypeOfActions_dec : forall (x y : TypeOfActions) , {x = y} + {x <> y}.
Proof.
decide equality. 
* destruct (decide(b = v)). left. assumption. right. assumption.
* destruct (decide (a = c)). left. assumption. right. assumption.
Defined.

#[global] Instance TypeOfActions_eqdecision : EqDecision TypeOfActions. by exact TypeOfActions_dec . Defined.

Definition encode_TypeOfActions (a : TypeOfActions) : gen_tree (nat + (ChannelData + ValueData)) :=
match a with
  | (c ,v)=> GenNode 0 [GenLeaf (inr (inl c)) ; GenLeaf (inr (inr v))]
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

Fixpoint proc_dec (x y : proc) : { x = y } + { x <> y }
with gproc_dec (x y : gproc) : { x = y } + { x <> y }.
Proof.
decide equality. 
* destruct (decide(n = n0));eauto.
* destruct (decide(n = n0));eauto.
* destruct (decide(e = e0));eauto. 
* decide equality; destruct (decide(c = c0));eauto.
  destruct (decide(v = v0));eauto.
Qed.

#[global] Instance proc_eqdecision : EqDecision proc. by exact proc_dec. Defined.


Fixpoint encode_proc (p: proc) : gen_tree (nat + (((Equation ValueData ) + TypeOfActions) + ChannelData)) :=
  match p with
  | p ‖ q  => GenNode 0 [encode_proc p; encode_proc q]
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
  | c ! v • p  => GenNode 5 [GenLeaf (inr $ inl $ inr $ ((c , v))); encode_proc p]
  | 𝛕 • p => GenNode 3 [encode_proc p]
  | gp + gq => GenNode 4 [encode_gproc gp; encode_gproc gq]
  end.

Fixpoint decode_proc (t': gen_tree (nat + (((Equation ValueData ) + TypeOfActions) + ChannelData))) : proc :=
  match t' with
  | GenNode 0 [ep; eq] => (decode_proc ep) ‖ (decode_proc eq)
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
  | GenNode 5 [GenLeaf (inr ( inl (inr a))) ; ep] => (ChannelData_of a) ! (ValueData_of a) • (decode_proc ep)
  | GenNode 3 [eq] => 𝛕 • (decode_proc eq)
  | GenNode 4 [egp; egq] => (decode_gproc egp) + (decode_gproc egq)
  | _ => ① 
  end.

Lemma encode_decide_procs p : decode_proc (encode_proc p) = p
with encode_decide_gprocs p : decode_gproc (encode_gproc p) = p.
Proof. all: case p. 
* intros. simpl. rewrite (encode_decide_procs p0). rewrite (encode_decide_procs p1). reflexivity.
* intros. simpl. reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). rewrite (encode_decide_procs p1). reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). eauto.
* intros. simpl. rewrite (encode_decide_gprocs g). reflexivity.
* intros. simpl. reflexivity. 
* intros. simpl. reflexivity. 
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_procs p0). reflexivity.
* intros. simpl. rewrite (encode_decide_gprocs g). rewrite (encode_decide_gprocs g0). reflexivity.
Qed.

#[global] Instance proc_count : Countable proc.
refine (inj_countable' encode_proc decode_proc _).
  apply encode_decide_procs.
Qed.

Fixpoint moutputs_of_g (k : nat) (gp : gproc) : gmultiset (TypeOfActions) :=
  match gp with
  | ① => ∅
  | 𝟘 => ∅
  | c ? • p => ∅
  | (cst c) ! v • p => {[+ ((cst c) , v) +]}
  | (bvar i) ! v • p => if decide(k < (S i)) then {[+ ((bvar (i - k)) , v) +]}
                                            else ∅
  | 𝛕 • p => ∅
  | g1 + g2 => moutputs_of_g k g1 ⊎ moutputs_of_g k g2
  end.


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
  | ν p => moutputs_of (S k) p
  | g p => moutputs_of_g k p
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
  + replace (S (j + S (S k)))%nat with ((S j) + S (S k))%nat by lia. eauto. 
  + destruct g; intros; try multiset_solver. 
    - destruct c.
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
    - simpl. assert (moutputs_of (j + S (S k)) (g g1)
        = moutputs_of (j + S (S k)) (VarSwap_in_proc j (g g1))) as eq1. 
      { eapply Hp. simpl. lia. }
      assert (moutputs_of (j + S (S k)) (g g2)
        = moutputs_of (j + S (S k)) (VarSwap_in_proc j (g g2))) as eq2. 
      { eapply Hp. simpl. lia. }
      inversion eq1. inversion eq2. eauto. 
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
  + destruct g; intros; try multiset_solver. 
    - destruct c.
      * simpl. eauto.
      * simpl. destruct (decide (j < S n)).
        ++ rewrite decide_True; try lia. eauto.
        ++ rewrite decide_False; try lia. eauto.
    - simpl. assert (moutputs_of (S j) (NewVarC j (g g1))
        = moutputs_of j (g g1)) as eq1. 
      { eapply Hp. simpl. lia. }
      assert (moutputs_of (S j) (NewVarC j (g g2))
        = moutputs_of j (g g2)) as eq2. 
      { eapply Hp. simpl. lia. }
      inversion eq1. inversion eq2. eauto.
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
  + replace ((S (k + j)))%nat with (k + S j)%nat by lia.
    replace (S (k + S j))%nat with (k + S (S j))%nat by lia.
    eapply Hp. simpl. eauto.
  + destruct g; simpl in *.
    - eauto.
    - eauto.
    - eauto.
    - destruct c.
      * simpl. eauto.
      * destruct (decide (k + j < S n)).
        ++ simpl. rewrite decide_True; try lia.
           rewrite decide_True; try lia.
           replace ((S n - (k + S j)))%nat with (n - (k + j))%nat by lia.
           eauto.
        ++ simpl. destruct (decide (j < S n)).
           +++ rewrite decide_False; try lia. eauto.
           +++ rewrite decide_False; try lia. eauto.
    - eauto.
    - assert (moutputs_of (k + j) (g g1) = moutputs_of (k + S j) (NewVarC j (g g1))) as eq1.
      { eapply Hp. simpl. lia. }
      assert (moutputs_of (k + j) (g g2) = moutputs_of (k + S j) (NewVarC j (g g2))) as eq2.
      { eapply Hp. simpl. lia. }
      inversion eq1. inversion eq2. eauto.
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

Lemma mo_equiv_spec : forall {p q l}, p ≡* q -> moutputs_of l p = moutputs_of l q.
Proof.
  intros p q l hcgr.
  induction hcgr.
  - now eapply mo_equiv_spec_step.
  - etrans; eauto.
Qed.

Lemma inversion_res_n_lts k e1 μ e1' : lts (Ѵ k e1) (ActExt μ) e1' -> exists e'1, e1' = (Ѵ k e'1).
Proof.
  revert e1 μ e1'.
  induction k.
  + simpl; eauto.
  + intros; simpl in *. inversion H; subst. eapply IHk in H2 as (e'' & eq).
    subst. exists e''. eauto.
Qed.

Lemma inversion_res_ext k e1 μ e1' : lts (Ѵ k e1) (ActExt μ) (Ѵ k e1') -> lts e1 (ActExt (VarC_action_add k μ)) e1'.
Proof.
  revert e1 μ e1'.
  induction k.
  + simpl; eauto. intros. rewrite VarC_add_zero_ext. eauto.
  + intros; simpl in *. inversion H; subst. eapply IHk in H3.
    rewrite VarC_action_add_add in H3. replace (S k) with (k+1)%nat by lia.
    eauto.
Qed.

Lemma mo_spec_l e a k:
  a ∈ moutputs_of k e -> {e' | lts (Ѵ  k e) (ActExt $ ActOut a) (Ѵ  k e')}.
Proof.
  intros mem.
  dependent induction e.
  + cbn in mem.
    destruct (decide (a ∈ moutputs_of k e1)) as [mem_left | not_mem_left].
    ++ destruct (IHe1 a k) as (e1' & lts__e1); eauto.
       eapply inversion_res_ext in lts__e1.
       exists (e1' ‖ e2). eapply lts_res_ext_n.
       eapply lts_parL. eauto.
    ++ destruct (decide (a ∈ moutputs_of k e2)) as [mem_right | not_mem_right].
       +++ destruct (IHe2 a k) as (e2' & lts__e2); eauto.
           eapply inversion_res_ext in lts__e2.
           exists (e1 ‖ e2'). eapply lts_res_ext_n.
           eapply lts_parR. eauto.
       +++ exfalso. multiset_solver.
    + exfalso. multiset_solver.
    + exfalso. multiset_solver.
    + simpl in mem. case_eq (Eval_Eq 0 e1). 
      ++ intros. destruct b.
         +++ rewrite H in mem. 
             eapply IHe1 in mem as (e' & l').
             exists e'. eapply inversion_res_ext in l'.
             eapply lts_res_ext_n. eapply lts_ifOne; eauto.
         +++ rewrite H in mem. 
             eapply IHe2 in mem as (e' & l').
             exists e'. eapply inversion_res_ext in l'.
             eapply lts_res_ext_n. eapply lts_ifZero; eauto.
      ++ intro. rewrite H in mem. exfalso. inversion mem.
    + simpl in *. eapply IHe in mem as (e' & lts_e').
      exists (ν e'). replace (Ѵ k (ν e)) with (Ѵ (S k) e).
      replace (Ѵ k (ν e')) with (Ѵ (S k) e'). eauto.
      replace (ν e') with (Ѵ 1 e'); eauto. rewrite BigNew_reverse_def. simpl; eauto.
      replace (ν e) with (Ѵ 1 e); eauto. rewrite BigNew_reverse_def. simpl; eauto.
    + unfold moutputs_of in mem.
      dependent induction g; simpl in *.
      ++ exfalso;inversion mem.
      ++ exfalso;inversion mem.
      ++ exfalso;inversion mem.
      ++ subst. destruct c.
         +++ assert (a = (cst c , v)). multiset_solver. subst. exists p.
             eapply lts_res_ext_n. simpl. eauto with *.
         +++ destruct (decide (k < S n)).
             ++++ assert (a = (bvar (n - k) , v)). multiset_solver. subst.
                  exists p. eapply lts_res_ext_n. simpl.
                  replace (k + (n - k))%nat with n by lia. eauto with *.
             ++++ exfalso. inversion mem.
      ++ exfalso;inversion mem.
      ++ destruct (decide (a ∈ moutputs_of k g2)) as [mem_right | not_mem_right].
         +++ destruct (IHg2 a k) as (e2' & lts__e2); eauto.
             subst. eapply inversion_res_ext in lts__e2. exists e2'.
             eapply lts_res_ext_n. eapply lts_choiceR. eauto.
         +++ destruct (decide (a ∈ moutputs_of k g1)) as [mem_left | not_mem_left].
             ++++ destruct (IHg1 a k) as (e1' & lts__e1); eauto.
                  eapply inversion_res_ext in lts__e1.
                  subst. exists e1'. eapply lts_res_ext_n. eapply lts_choiceL. eauto.
             ++++ exfalso. multiset_solver.
Qed.

Lemma mo_spec_r p a k :
  {p' | lts (Ѵ  k p) (ActExt $ ActOut a) (Ѵ  k p')} -> a ∈ moutputs_of k p.
Proof.
  revert a k.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros a k (e' & l); eapply inversion_res_ext in l; inversion l; subst.
  + simpl. eapply gmultiset_elem_of_disj_union. left.
    eapply Hp. simpl. lia. exists p3. eapply lts_res_ext_n. eauto.
  + simpl. eapply gmultiset_elem_of_disj_union. right.
    eapply Hp. simpl. lia. exists q2. eapply lts_res_ext_n. eauto.
  + simpl. rewrite H4. eapply Hp. simpl. lia.
    exists e'. eapply lts_res_ext_n. eauto.
  + simpl. rewrite H4. eapply Hp. simpl. lia.
    exists e'. eapply lts_res_ext_n. eauto.
  + simpl. destruct a. eapply Hp. simpl. lia. exists p'.
    eapply lts_res_ext_n. simpl in *. rewrite<- VarC_add_revert_def in H1.
    simpl in *. eauto.
  + simpl. destruct a. inversion H.
  + simpl. destruct a. destruct c.
    ++ simpl in *. inversion H. subst. destruct c0.
       +++ simpl in *. rewrite H1. multiset_solver.
       +++ inversion H1.
    ++ inversion H. subst. destruct c0.
       +++ simpl; inversion H1.
       +++ simpl in *. subst. inversion H1.
           rewrite decide_True; try lia. replace (k + n0 - k)%nat with n0%nat by lia.
           multiset_solver.
  + simpl. eapply gmultiset_elem_of_disj_union. left.
    assert (a ∈ moutputs_of k (g p1)).
    { eapply (Hp (g p1)). simpl. lia. exists e'. eapply lts_res_ext_n. eauto. }
    simpl in *; eauto.
  + simpl. eapply gmultiset_elem_of_disj_union. right.
    assert (a ∈ moutputs_of k (g p2)).
    { eapply (Hp (g p2)). simpl. lia. exists e'. eapply lts_res_ext_n. eauto. }
    simpl in *; eauto.
Qed.

Lemma outputs_of_spec2 p a : a ∈ outputs_of p -> {q | lts p (ActExt (ActOut a)) q}.
Proof.
  intros mem.
  eapply gmultiset_elem_of_dom in mem.
  eapply mo_spec_l in mem.
  firstorder.
Qed.

Lemma outputs_of_spec1 (p : proc) (a : TypeOfActions) (q : proc) : lts p (ActExt (ActOut a)) q
      -> a ∈ outputs_of p.
Proof.
intros. eapply gmultiset_elem_of_dom. eapply mo_spec_r. eauto.
Qed.


Fixpoint lts_set_output_g (g : gproc) (a : TypeOfActions) : gset proc :=
  match g with
  | ① => ∅
  | 𝟘 => ∅
  | c ? • p => ∅
  | c ! v • p => if decide(a = ((c , v))) then {[ p ]} else ∅
  | 𝛕 • p => ∅
  | g1 + g2 => lts_set_output_g g1 a ∪ lts_set_output_g g2 a
  end.

Fixpoint lts_set_output (p : proc) (a : TypeOfActions) : gset proc:=
match p with
  | p1 ‖ p2 => 
      let ps1 := lts_set_output p1 a in
      let ps2 := lts_set_output p2 a in
      (set_map (fun p => p ‖ p2) ps1) ∪ (set_map (fun p => p1 ‖ p) ps2)
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | If C Then A Else B => match (Eval_Eq 0 C) with 
                          | Some true => lts_set_output A a
                          | Some false => lts_set_output B a
                          | None => ∅
                          end
  | ν p => set_map (fun q => ν q) (lts_set_output p (VarC_TypeOfActions_add 1 a)) 
  | g gp  => lts_set_output_g gp a
end.

Fixpoint lts_set_input_g (g : gproc) (a : TypeOfActions) : gset proc :=
 match g with
  | ① => ∅
  | 𝟘 => ∅
  | c' ? • p => if decide(ChannelData_of a = c') then {[ p^(ValueData_of a) ]} else ∅
  | c' ! v • p => ∅
  | 𝛕 • p => ∅
  | g1 + g2 => lts_set_input_g g1 a ∪ lts_set_input_g g2 a
  end.


Fixpoint lts_set_input (p : proc) (a : TypeOfActions) : gset proc :=
match p with
  | p1 ‖ p2 =>
      let ps1 := lts_set_input p1 a in
      let ps2 := lts_set_input p2 a in
      (set_map (fun p => p ‖ p2) ps1) ∪ (set_map (fun p => p1 ‖ p) ps2)
  | pr_var _ => ∅
  | rec _ • _ => ∅ 
  | If C Then A Else B => match (Eval_Eq 0 C) with 
                          | Some true => lts_set_input A a
                          | Some false => lts_set_input B a
                          | None => ∅
                          end
  | ν p => set_map (fun q => ν q) (lts_set_input p (VarC_TypeOfActions_add 1 a)) 
  | g gp => lts_set_input_g gp a  
  end.


Fixpoint lts_set_tau_g (gp : gproc) : gset proc :=
match gp with
  | ① => ∅
  | 𝟘 => ∅
  | c ? • p => ∅
  | c ! v • p => ∅
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

Lemma lts_set_output_spec0 p a q : q ∈ lts_set_output p a
                -> lts p (ActExt (ActOut a)) q.
Proof.
  revert q a.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0));
  destruct p; intros q a mem; simpl in mem.
  - eapply elem_of_union in mem as [mem | mem]. 
    * eapply elem_of_list_to_set, list_elem_of_fmap in mem as (q' & eq & mem). subst.
      apply lts_parL. rewrite elem_of_elements in mem. eapply Hp. simpl ; lia. eauto. 
    * eapply elem_of_list_to_set, list_elem_of_fmap in mem as (q' & eq & mem). subst.
      apply lts_parR. eapply Hp. simpl; lia. rewrite elem_of_elements in mem.  exact mem.
  - inversion mem.
  - inversion mem.
  - case_eq (Eval_Eq 0 e).
    * intros. destruct b.
      ** rewrite H in mem. eapply lts_ifOne; eauto. eapply Hp; simpl. lia ; eauto. eauto.
      ** rewrite H in mem. eapply lts_ifZero; eauto. eapply Hp; simpl. lia ; eauto. eauto.
    * intros. rewrite H in mem. exfalso. inversion mem.
  - eapply elem_of_list_to_set, list_elem_of_fmap in mem as (q' & eq & mem). subst.
    apply lts_res_ext. rewrite elem_of_elements in mem. eapply Hp in mem. simpl. destruct a. eauto. simpl ; lia. 
  - destruct g; simpl in mem;  try now inversion mem.
    + case (TypeOfActions_dec a (c , v)) in mem.
          +++ subst. rewrite decide_True in mem; eauto.
              assert (q = p). set_solver. subst. eauto with *.
          +++ rewrite decide_False in mem; eauto. inversion mem.
    + eapply elem_of_union in mem as [mem | mem].
      ++ eapply lts_choiceL.
         eapply Hp. simpl; lia. eauto.
      ++ eapply lts_choiceR.
         eapply Hp. simpl; lia. eauto.
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
       rewrite elem_of_elements in mem. eauto with *.
    ++ eapply elem_of_list_to_set in H.
       eapply list_elem_of_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. eauto with *.
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
      ++ eapply elem_of_union in mem. destruct mem; eauto with *.
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
         rewrite elem_of_elements in h. eauto with *.
         eapply elem_of_list_to_set, list_elem_of_fmap in mem2 as (t' & eq & h); subst.
         rewrite elem_of_elements in h. eauto with *.
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
    + eapply elem_of_singleton_1 in mem. subst; eauto with *.
    + case_eq (Eval_Eq 0 e); intros; rewrite H in mem.
      ++ destruct b.
         +++ eapply lts_ifOne; eauto.
         +++ eapply lts_ifZero; eauto.
      ++ exfalso. inversion mem.
    + eapply elem_of_list_to_set, list_elem_of_fmap in mem as (t' & eq & h); subst.
      eapply lts_res_tau. eapply IHp. eapply elem_of_elements. eauto.
    + dependent induction g; simpl in mem; try set_solver;
        try eapply elem_of_singleton_1 in mem; subst; eauto with *.
      eapply elem_of_union in mem as [mem1 | mem2]; eauto with *.
Qed.

Lemma lts_set_tau_spec1 p q : lts p τ q -> q ∈ lts_set_tau p.
Proof. 
  intro l. dependent induction l; simpl; try set_solver.
  - rewrite H. eauto.
  - rewrite H. eauto.
  - eapply elem_of_union. left.
    eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    rewrite list_elem_of_In. rewrite in_flat_map.
    exists ((c , v)). split.
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
    exists ((c , v)). split.
    + eapply list_elem_of_In, elem_of_elements.
      eapply outputs_of_spec1. exact l1.
    + eapply list_elem_of_In, list_elem_of_fmap.
      exists (q2 , p2). split.
      ++ reflexivity.
      ++ eapply list_elem_of_In, in_prod_iff; split; eapply list_elem_of_In, elem_of_elements.
         eapply lts_set_input_spec1; eauto with ccs.
         eapply lts_set_output_spec1; eauto with ccs.
Qed.

Definition lts_set (p : proc) (𝜆 : ActIO TypeOfActions): gset proc :=
  match 𝜆 with
  | τ => lts_set_tau p
  | a ? => lts_set_input p a
  | a ! => lts_set_output p a
  end.

Lemma lts_set_spec0 p 𝜆 q : q ∈ lts_set p 𝜆 -> lts p 𝜆 q.
Proof.
  destruct 𝜆 as [[a|a]|].
  - now eapply lts_set_input_spec0.
  - now eapply lts_set_output_spec0.
  - now eapply lts_set_tau_spec0.
Qed.

Lemma lts_set_spec1 p 𝜆 q : lts p 𝜆 q -> q ∈ lts_set p 𝜆.
Proof.
  destruct 𝜆 as [[a|a]|].
  - now eapply lts_set_input_spec1.
  - now eapply lts_set_output_spec1.
  - now eapply lts_set_tau_spec1.
Qed.

Definition proc_stable p 𝜆 := lts_set p 𝜆 = ∅.

Lemma lts_dec p 𝜆 q : { lts p 𝜆 q } + { ~ lts p 𝜆 q }.
Proof.
  destruct (decide (q ∈ lts_set p 𝜆)).
  - eapply lts_set_spec0 in e. eauto.
  - right. intro l. now eapply lts_set_spec1 in l.
Qed.

Lemma proc_stable_dec p 𝜆 : Decision (proc_stable p 𝜆).
Proof. destruct (decide (lts_set p 𝜆 = ∅)); [ left | right ]; eauto. Qed.

Lemma gset_nempty_ex (g : gset proc) : g ≠ ∅ -> {p | p ∈ g}.
Proof.
  intro n. destruct (elements g) eqn:eq.
  + destruct n. eapply elements_empty_iff in eq. set_solver.
  + exists p. eapply elem_of_elements. rewrite eq. set_solver.
Qed.

Definition all_blocking_action (μ : ExtAct TypeOfActions) := False.

#[global] Program Instance VCCS_ExtAction : ExtAction (ExtAct TypeOfActions) :=
  {| non_blocking η := all_blocking_action η ;
      dual μ1 μ2 := ext_act_match μ1 μ2 |}.
Next Obligation.
  simpl. intros ? ? Imp. inversion Imp. 
Qed.
Next Obligation.
  intro μ; simpl in *.
  exists (InputOutputActions.io_co μ).
  symmetry. eapply dual_co.
Defined.

#[global] Instance VCCS_UniqueDual : UniqueDual (ExtAct TypeOfActions).
Proof.
  intros η β duo; simpl; subst.
  simpl in *.
  destruct β as [ (* Input *) a' | (* Output *) a' ].
  + apply simplify_match_input in duo; subst. eauto.
  + apply simplify_match_output in duo; subst. eauto.
Defined.

Local Program Definition VCCS_gLts : gLts proc VCCS_ExtAction :=
  {| lts_step x 𝜆 y  := lts x 𝜆 y ;
     lts_state_eqdec := proc_dec ;
     lts_step_decidable p 𝜆 q := lts_dec p 𝜆 q ;
     lts_performs p 𝜆 := ¬ proc_stable p 𝜆;
     lts_performs_decidable p 𝜆 := not_dec (proc_stable_dec p 𝜆)
    |}.
Next Obligation.
  intros p [[a|a]|]; intro hs ;eapply gset_nempty_ex in hs as (r & l) ; eapply lts_set_spec0 in l; 
  exists r; assumption.
Qed.
Next Obligation.
  intros p [[a|a]|]; intros (q & mem); intro eq; eapply lts_set_spec1 in mem; set_solver.
Qed.

#[global] Program Instance VCCS_gLtsEq : gLtsEq proc VCCS_ExtAction :=
  {| gLtsEq_gLts := VCCS_gLts;
     eq_rel x y  := x ≡* y; |}.
Next Obligation.
  apply cgr_is_eq_rel.
Defined.
Next Obligation.
  eapply Congruence_Respects_Transition.
Defined.

#[global] Program Instance VCCS_gLtsOBA : gLtsOba proc _.
Next Obligation.
  intros ? ? ? ? ? Imp ;simpl in *.
  inversion Imp.
Qed.
Next Obligation.
  intros ? ? ? ? ? Imp ;simpl in *.
  inversion Imp.
Qed.
Next Obligation.
  intros ? ? ? ? Imp ;simpl in *.
  inversion Imp.
Qed.
Next Obligation.
  intros ? ? ? ? Imp ;simpl in *.
  inversion Imp.
Qed.
Next Obligation.
  intros ? ? ? ? ? Imp ;simpl in *.
  inversion Imp.
Qed.

#[global] Program Instance VCCS_gLtsOBAFB : gLtsObaFB proc (ExtAct TypeOfActions).
Next Obligation.
  intros ? ? ? ? ? Imp ;simpl in *.
  inversion Imp.
Qed.

#[global] Program Instance VCCS_gLtsOBAFW : gLtsObaFW proc (ExtAct TypeOfActions).
Next Obligation.
  intros ? η η' ;simpl in *.
  exists (g 𝟘). intro Imp. inversion Imp.
Qed.
Next Obligation.
  intros ? ? ? ? ? Imp ;simpl in *.
  inversion Imp.
Qed.

#[global] Program Instance VCCS_gFiniteNonBlockingChain_LtsOba
 : FiniteNonBlockingChain_LtsOba proc := {| lts_oba_mo p := empty ; |}.
Next Obligation.
  intros ? ? ? Imp ;simpl in *.
  inversion Imp.
Qed.
Next Obligation.
  intros. simpl in *. exists (g 𝟘). inversion H.
Qed.
Next Obligation.
  intros. simpl in *. inversion H.
Qed.

#[global] Program Instance VCCS_gLtsFiniteImage : FiniteImagegLts proc (ExtAct TypeOfActions).
Next Obligation.
  intros. unfold dsig. destruct 𝜆 as [[a|a]|].
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

#[global] Program Instance Interaction_between_parallel_VCCS :
  @Prop_of_Inter proc proc (ExtAct TypeOfActions) (ExtAct TypeOfActions) dual VCCS_ExtAction (@gLtsEq_gLts proc _ _ VCCS_gLtsEq) VCCS_ExtAction (@gLtsEq_gLts proc _ _ VCCS_gLtsEq):=
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
  unfold Interaction_between_parallel_VCCS_obligation_4.
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
  unfold Interaction_between_parallel_VCCS_obligation_6.
  intros ? ? ? ? q mem l inter;simpl in *. 
  eapply elem_of_list_to_set in mem.
  eapply list_elem_of_fmap in mem.
  destruct mem as ( a & eq & mem ); subst. symmetry in inter.
  symmetry in inter. eapply simplify_match_output in inter. subst. set_solver.
Defined.

#[global] Program Instance Interaction_between_VCCS_and_MB: 
    @Prop_of_Inter proc (MO (ExtAct TypeOfActions)) (ExtAct TypeOfActions) (ExtAct TypeOfActions) fw_inter VCCS_ExtAction (@gLtsEq_gLts proc _ _ VCCS_gLtsEq) VCCS_ExtAction _:=
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
  right. destruct inter as (duo & nb). inversion nb.
Defined.
Next Obligation.
  intros ξ p;simpl in *.
  destruct (decide (non_blocking ξ)) as [ nb (* Input_case *) | not_nb (* Ouput_case *)].
  + exact {[ co ξ ]}.
  + exact empty.
Defined.
Next Obligation.
  intros ? ? ? ? m mem l inter;simpl in *.
  destruct inter as (duo & nb). inversion nb.
Defined.
Next Obligation.
  intros ? ? ? ? m mem l inter;simpl in *.
  inversion mem.
Qed.

#[global] Program Instance Interaction_between_FW_VCCS_and_VCCS :
  @Prop_of_Inter (proc * MO (ExtAct TypeOfActions)) proc (ExtAct TypeOfActions) (ExtAct TypeOfActions) dual VCCS_ExtAction (toFW (@gLtsEq_gLts proc _ _ VCCS_gLtsEq)) VCCS_ExtAction _:=
    {| lts_essential_actions_left p := set_map ActOut (outputs_of p.1) ∪ (dom (MO_without_not_nb p.2)); 
       lts_essential_actions_right q := set_map ActOut (outputs_of q)|}.
Next Obligation.
  intros (p , m) ? mem. simpl in *.
  eapply elem_of_union in mem. destruct (decide (ξ ∈ dom (MO_without_not_nb m))).
  + eapply gmultiset_elem_of_dom in e.
    eapply lts_MO_nb_with_nb_spec1 in e as (nb & mem').
    inversion nb.
  + assert (ξ ∈ @set_map TypeOfActions (gset TypeOfActions) _ (ExtAct TypeOfActions) (gset (ExtAct TypeOfActions)) _ _ _  ActOut (outputs_of p)) as Hyp.
    { destruct mem as [case1 | case2]. exact case1. contradiction. }
    unfold set_map in Hyp.
    eapply elem_of_list_to_set in Hyp.
    eapply list_elem_of_fmap in Hyp.
    destruct ξ.
    ++ exfalso. destruct Hyp as (a' & eq & mem'). inversion eq.
    ++ assert (a ∈ elements (outputs_of p)) as mem'.
       { destruct Hyp as (y & Hyp'); destruct Hyp' as (eq' & mem'). 
         inversion eq'; subst. eauto. }
       apply elem_of_elements in mem'. eapply outputs_of_spec2 in mem'.
       destruct mem' as (p' & l). exists (p' , m). eapply ParLeft. eauto.
Defined.
Next Obligation.
  intros e ? Hyp ;simpl in *.
  unfold set_map in Hyp. simpl in *.
  eapply elem_of_list_to_set in Hyp.
  eapply list_elem_of_fmap in Hyp.
  destruct ξ as [ (*Input*) a | (*Output*) a].
  + exfalso. destruct Hyp as (a' & Imp & Hyp). inversion Hyp; subst. inversion Imp. inversion Imp.
  + assert (a ∈ elements (outputs_of e)) as mem.
    { destruct Hyp as (y & Hyp'); destruct Hyp' as (eq' & mem). 
      inversion eq'; subst. eauto. }
    apply elem_of_elements in mem. eapply outputs_of_spec2 in mem. eauto.
Qed.
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
      * inversion nb.
      * eapply blocking_action_in_ms in l as (eq & duo & nb);eauto.
        eapply simplify_match_output in duo. subst.
        rewrite duo in Tr, nb. destruct nb.
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
  unfold Interaction_between_FW_VCCS_and_VCCS_obligation_4. destruct ξ as [ (*Input*) a | (*Output*) a].
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
  unfold Interaction_between_FW_VCCS_and_VCCS_obligation_6. symmetry in inter.
  destruct ξ as [ (*Input*) a | (*Output*) a].
  - symmetry in inter. eapply simplify_match_input in inter. subst.
    eapply elem_of_union in mem. destruct mem as [case1 | case2].
    + set_solver.
    + set_solver.
  - symmetry in inter. eapply simplify_match_output in inter. subst. set_solver.
Defined.

Inductive FinA :=
| Inputs (c : ChannelData)
| Output (c : ChannelData) (v : ValueData)
.

Definition αᴛᴠᴄᴄꜱ (μ : ExtAct TypeOfActions) : FinA :=
match μ with
| ActIn ((c , v)) => Inputs c
| ActOut ((c , v)) => Output c v
end.

Lemma same_input_channel c v c' v' : αᴛᴠᴄᴄꜱ (ActIn ((c , v))) =  αᴛᴠᴄᴄꜱ (ActIn (c' , v')) -> c = c'.
Proof.
  simpl. intros. inversion H. eauto.
Qed.

Inductive PreAct :=
| Inputs_on (c : ChannelData)
| Outputs_on (c : ChannelData)
.

#[global] Instance EqPreAct : EqDecision PreAct.
Proof.
  intros x y. destruct x ; destruct y; destruct (decide (c = c0)); subst; try (now (left; eauto)).
  + right. intro. inversion H. eauto.
  + right. intro. inversion H.
  + right. intro. inversion H.
  + right. intro. inversion H.
  + right. intro. inversion H.
  + right. intro. inversion H. eauto.
Qed.

Definition encode_PreAct (c : PreAct) : gen_tree (ChannelData + ChannelData) :=
match c with
  | Inputs_on c => GenLeaf (inr c)
  | Outputs_on c => GenLeaf (inl c)
end.

Definition decode_PreAct (tree : gen_tree (ChannelData + ChannelData)) : option PreAct :=
match tree with
  | GenLeaf (inr c) => Some (Inputs_on c)
  | GenLeaf (inl c) => Some (Outputs_on c)
  | _ => None
end.

Lemma encode_decide_PreAct c : decode_PreAct (encode_PreAct c) = Some c.
Proof. case c. 
* intros. simpl. reflexivity.
* intros. simpl. reflexivity.
Qed.

#[global] Instance CountPreAct : Countable PreAct.
Proof.
  refine (inj_countable encode_PreAct decode_PreAct _).
  apply encode_decide_PreAct.
Qed.

Definition αᴘᴠᴄᴄꜱ (pre_μ : FinA) : PreAct :=
match pre_μ with
| Inputs c => Inputs_on c
| Output c v => Outputs_on c
end.

Fixpoint mPreCoAct_of_g (k : nat) (gp : gproc) : gmultiset PreAct :=
  match gp with
  | ① => ∅
  | 𝟘 => ∅
  | (cst c) ? • p => {[+ Outputs_on c +]}
  | (bvar i) ? • p => if decide(k < (S i)) then {[+ Outputs_on (i - k) +]}
                                              else ∅
  | (cst c) ! v • p => {[+ Inputs_on c +]}
  | (bvar i) ! v • p => if decide(k < (S i)) then {[+ Inputs_on (i - k) +]}
                                              else ∅
  | 𝛕 • p => ∅
  | g1 + g2 => mPreCoAct_of_g k g1 ⊎ mPreCoAct_of_g k g2
  end.

Fixpoint  mPreCoAct_of (k : nat) p : gmultiset PreAct := 
match p with
  | P ‖ Q => (mPreCoAct_of k P) ⊎ (mPreCoAct_of k Q)
  | pr_var _ => ∅
  | rec _ • _ => ∅
  | If E Then P Else Q => match (Eval_Eq 0 E) with 
                          | Some true => mPreCoAct_of k P
                          | Some false => mPreCoAct_of k Q
                          | None => ∅
                          end
  | ν p => mPreCoAct_of (S k) p
  | g p => mPreCoAct_of_g k p
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
  + replace (S (k + S j))%nat with (k + S (S j))%nat by lia.
    replace (S (k + j))%nat with (k + S j)%nat by lia.
    eapply Hp. simpl; eauto.
  + destruct g; simpl in *; eauto.
    - destruct c; simpl.
      ++ eauto.
      ++ destruct (decide (j < S n)).
         +++ destruct (decide (k + j < S n)).
             ++++ rewrite decide_True; try lia.
                  replace (S n - (k + S j))%nat with (n - (k + j))%nat by lia. eauto.
             ++++ rewrite decide_False; try lia. eauto.
         +++ rewrite decide_False; try lia.
             rewrite decide_False; try lia. eauto.
    - destruct c; simpl.
      ++ eauto.
      ++ destruct (decide (j < S n)).
         +++ destruct (decide (k + j < S n)).
             ++++ rewrite decide_True; try lia.
                  replace (S n - (k + S j))%nat with (n - (k + j))%nat by lia. eauto.
             ++++ rewrite decide_False; try lia. eauto.
         +++ rewrite decide_False; try lia.
             rewrite decide_False; try lia. eauto.
    - assert (mPreCoAct_of (k + S j) (NewVarC j (g g1)) = mPreCoAct_of (k + j) (g g1)) as eq1.
      { eapply Hp. simpl. lia. }
      assert (mPreCoAct_of (k + S j) (NewVarC j (g g2)) = mPreCoAct_of (k + j) (g g2)) as eq2.
      { eapply Hp. simpl. lia. }
      inversion eq1. inversion eq2. eauto.
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
  + replace (S (j + S (S k)))%nat with ((S j) + S (S k))%nat by lia.
    eapply Hp. simpl; eauto.
  + destruct g; simpl in *; eauto.
    - destruct c.
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
    - destruct c.
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
     - assert (mPreCoAct_of (j + S (S k)) (g g1) = mPreCoAct_of (j + S (S k)) (VarSwap_in_proc j (g g1))) as eq1.
       { eapply Hp. simpl; lia. }
       assert (mPreCoAct_of (j + S (S k)) (g g2) = mPreCoAct_of (j + S (S k)) (VarSwap_in_proc j (g g2))) as eq2.
       { eapply Hp. simpl; lia. }
       inversion eq1. inversion eq2. eauto.
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
| Inputs_on c => Inputs_on (VarC_add k c)
| Outputs_on c => Outputs_on (VarC_add k c)
end.

Lemma VarC_preaction_add_zero pre_μ : VarC_preaction_add 0 pre_μ = pre_μ.
Proof.
  destruct pre_μ; simpl; destruct c; eauto.
Qed.

Lemma VarC_preaction_add_rev j k pre_μ μ' : 
      VarC_preaction_add (j + k) pre_μ = αᴘᴠᴄᴄꜱ (αᴛᴠᴄᴄꜱ (VarC_action_add (j + k) μ'))
      -> VarC_preaction_add k pre_μ = αᴘᴠᴄᴄꜱ (αᴛᴠᴄᴄꜱ (VarC_action_add k μ')).
Proof.
  revert k pre_μ μ'.
  induction j.
  + simpl; eauto.
  + intros; simpl. destruct pre_μ; destruct μ'.
    ++ destruct c; destruct a.
       +++ simpl in *. destruct c0.
           ++++ simpl; eauto.
           ++++ simpl in *. inversion H.
       +++ simpl in *. destruct c.
           ++++ simpl in *. inversion H.
           ++++ simpl in *. inversion H. f_equal. assert (n = n0)%nat by lia. subst; eauto.
    ++ destruct c; destruct a.
       +++ simpl in *. inversion H.
       +++ simpl in *. inversion H.
    ++ destruct c; destruct a.
       +++ simpl in *. inversion H.
       +++ simpl in *. inversion H.
    ++ destruct c; destruct a.
       +++ simpl in *. destruct c0.
           ++++ simpl; eauto.
           ++++ simpl in *. inversion H.
       +++ simpl in *. destruct c.
           ++++ simpl in *. inversion H.
           ++++ simpl in *. inversion H. f_equal. assert (n = n0)%nat by lia. subst; eauto.
Qed.

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

Lemma simpl_blocking_Varc j k μ' : blocking (VarC_action_add (j + k) μ') -> blocking (VarC_action_add k μ').
Proof.
  intros. destruct μ'; destruct a; destruct c; simpl; eauto.
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

Lemma delta_phi_newVarC j μ : VarC_preaction_add j ((αᴘᴠᴄᴄꜱ ∘ αᴛᴠᴄᴄꜱ) μ) = (αᴘᴠᴄᴄꜱ ∘ αᴛᴠᴄᴄꜱ) (VarC_action_add j μ).
Proof.
  destruct μ; destruct a; destruct c; eauto ; simpl.
Qed.
 
Lemma delta_phi_newVarC_inversion j μ μ' :
  VarC_preaction_add j μ' = (αᴘᴠᴄᴄꜱ ∘ αᴛᴠᴄᴄꜱ) μ -> (exists μ'', μ = VarC_action_add j μ'' /\ μ' = (αᴘᴠᴄᴄꜱ ∘ αᴛᴠᴄᴄꜱ) μ'').
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

Lemma VarC_action_add_co_rev_map j k μ' p : VarC_preaction_add (j + k) μ' ∈ ⌈ αᴘᴠᴄᴄꜱ ∘ αᴛᴠᴄᴄꜱ ⌉ (coR p)
                        -> VarC_preaction_add k μ' ∈ ⌈ αᴘᴠᴄᴄꜱ ∘ αᴛᴠᴄᴄꜱ ⌉ (coR (Ѵ  j p)).
Proof.
  revert k μ' p.
  induction j.
  + simpl ;eauto.
  + intros; simpl in *. rewrite<- BigNew_reverse_def_one.
    eapply IHj. destruct H as (μ & duo & eq).
    assert (exists μ'', μ = VarC_action_add (S (j + k)) μ'' /\ μ' = (αᴘᴠᴄᴄꜱ ∘ αᴛᴠᴄᴄꜱ) μ'') as (μ'' & eq'' & eq''').
    { eapply delta_phi_newVarC_inversion; eauto. } subst.
    assert (S (j + k) = 1 + (j + k))%nat as eq'''' by lia.
    rewrite eq'''' in duo. eapply VarC_action_add_co_rev in duo.
    exists (VarC_action_add (j + k) μ''). split; eauto.
    eapply delta_phi_newVarC.
Qed.

Lemma specPreAct1 k : ∀ (pre_μ : PreAct) (p : proc),
   pre_μ ∈ (λ p0 : proc, mPreCoAct_of k p0) p -> (VarC_preaction_add k pre_μ) ∈ ⌈ (αᴘᴠᴄᴄꜱ ∘ αᴛᴠᴄᴄꜱ) ⌉ (coR p).
Proof.
  intros. simpl in *. revert k pre_μ H.
  induction p as (p & Hp) using
        (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; intros; simpl in *.
  * eapply gmultiset_elem_of_disj_union in H. destruct H.
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
  * eapply Hp in H as ( μ' & eq1 & eq2); simpl ; eauto.
    assert (S k = 1 + k)%nat as eq'' by lia. rewrite eq'' in eq2.
    assert ((ν p) = Ѵ 1 p) as eq'''. { simpl; eauto. } rewrite eq'''.
    eapply (VarC_action_add_co_rev_map 1 k). rewrite eq2. eapply map_gamma_of_action. eauto.
  * destruct g.
    ** simpl in *. inversion H.
    ** simpl in *. inversion H.
    ** simpl in *.
       destruct pre_μ.
       + simpl in *. subst. destruct c.
         ++ multiset_solver.
         ++ destruct (decide (k < S n)).
            +++ multiset_solver.
            +++ multiset_solver.
       + simpl in *. destruct c.
         ++ simpl. assert ((VarC_add k c0) = c) by multiset_solver.
            destruct c0; simpl in *.
            +++ inversion H0. subst.
                exists (ActOut (cst c , (bvar 0))). split.
                -- exists (ActIn (cst c , (bvar 0))). repeat split ;eauto.
                   eapply lts_performs_spec2. exists (p^0). constructor.
                -- simpl. reflexivity.
            +++ inversion H0.
         ++ destruct (decide (k < S n)); simpl.
            destruct c0.
            +++ simpl in *. multiset_solver.
            +++ simpl in *. assert ((@bvar (@Channel VP) n0) = (n - k)) by multiset_solver.
                inversion H0.
                exists (ActOut (bvar (n0 + k), bvar 0)). split.
                -- exists (ActIn (bvar (n0 + k), (bvar 0))). repeat split ;eauto.
                   eapply lts_performs_spec2. exists (p^0).
                   replace (n0 + k)%nat with n by lia.
                   constructor.
                -- simpl in *. rewrite H2. f_equal. f_equal.  lia.
            +++ inversion H.
    ** simpl in *.
       destruct pre_μ.
       + simpl in *. subst. destruct c.
         ++ assert (c0 = c) by multiset_solver. subst.
            exists (ActIn (cst c , v)). split.
            -- exists (ActOut (cst c , v)). repeat split ;eauto.
               eapply lts_performs_spec2. exists p. constructor.
            -- simpl in *. reflexivity.
         ++ destruct (decide (k < S n)).
            +++ assert (c0 = (n - k)) by multiset_solver. subst.
                exists (ActIn (bvar n , v)). split.
                -- exists (ActOut (bvar n , v)). repeat split ;eauto.
                   eapply lts_performs_spec2. exists p. constructor.
                -- simpl in *. f_equal. f_equal. lia.
            +++ inversion H.
       + simpl in *. subst. destruct c.
         ++ multiset_solver.
         ++ destruct (decide (k < S n)); multiset_solver.
    ** simpl in *. inversion H.
    ** simpl in *.
       eapply gmultiset_elem_of_disj_union in H. destruct H as [mem1 | mem2].
       -- assert (VarC_preaction_add k pre_μ
          ∈ ⌈ αᴘᴠᴄᴄꜱ ∘ αᴛᴠᴄᴄꜱ ⌉ (coR (g g1))).
          { eapply Hp. simpl. lia. simpl. eauto. }
          destruct H as (μ' & eq & mem).
          destruct eq as (μ'' & Tr & duo & b). exists μ'. split; eauto. 
          exists μ''. repeat split; eauto. eapply lts_performs_spec1 in Tr as (p'1 & Tr).
          eapply lts_performs_spec2. exists p'1. constructor. eauto.
       -- assert (VarC_preaction_add k pre_μ
          ∈ ⌈ αᴘᴠᴄᴄꜱ ∘ αᴛᴠᴄᴄꜱ ⌉ (coR (g g2))).
          { eapply Hp. simpl. lia. simpl. eauto. }
          destruct H as (μ' & eq & mem).
          destruct eq as (μ'' & Tr & duo & b). exists μ'. split; eauto. 
          exists μ''. repeat split; eauto. eapply lts_performs_spec1 in Tr as (p'1 & Tr).
          eapply lts_performs_spec2. exists p'1. eapply lts_choiceR. eauto.
Qed.

#[global] Program Instance AbsVCCS :
  AbsAction (gLtsP := (@gLtsEq_gLts proc _ _ VCCS_gLtsEq)) (gLtsT := VCCS_gLtsEq) proc proc αᴛᴠᴄᴄꜱ αᴘᴠᴄᴄꜱ.
Next Obligation.
  intros. destruct β; destruct β'; destruct a; destruct a0.
  - inversion H1; subst.
    eapply lts_performs_spec1 in H2 as (e' & Tr).
    eapply TransitionShapeForInput in Tr as (P1 & G & R & n & eq & eq' & Hyp).
    assert (Ѵ n ((gpr_input (VarC_add n c0) P1 + G) ‖ R) ⟶{(c0 , v0) ?}) as accepts.
    { eapply lts_performs_spec2. exists (Ѵ n (P1 ^ v0 ‖ R)). eapply lts_res_ext_n. eapply lts_parL. eapply lts_choiceL. constructor. }
    eapply (@accepts_preserved_by_eq proc (ExtAct TypeOfActions) VCCS_ExtAction VCCS_gLtsEq) in accepts.
    exact accepts. symmetry. eauto.
  - simpl in *. inversion H1.
  - simpl in *. inversion H1.
  - inversion H1; subst. eapply lts_performs_spec1 in H2 as (e' & Tr). simpl in *.
    eapply TransitionShapeForOutput in Tr as (P1 & G & R & n & eq & eq' & Hyp).
    assert (Ѵ n ((VarC_add n c0 ! v0 • P1 + G) ‖ R) ⟶{(c0 , v0) !}) as accepts.
    { eapply lts_performs_spec2. exists (Ѵ n (P1 ‖ R)). eapply lts_res_ext_n. eapply lts_parL. eapply lts_choiceL. constructor. }
    eapply (@accepts_preserved_by_eq proc (ExtAct TypeOfActions) VCCS_ExtAction VCCS_gLtsEq) in accepts.
    exact accepts. symmetry. eauto.
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
        -- destruct a. simpl in *. inversion H1.
      * simpl in *. destruct a. inversion mem.
    + destruct a. simpl in *. destruct μ''.
      * simpl in *. destruct a. inversion mem.
      * simpl in *. destruct a. inversion mem. subst.
        destruct β'.
        -- destruct a. simpl in *. inversion H1; subst.
        -- destruct a. simpl in *. inversion H1; subst.
           destruct eq as (μ'' & tr & duo & b).
           symmetry in duo. eapply simplify_match_output in duo. subst.
           exists (ActOut(c , v)). split ;eauto. exists (ActIn (c , v)).
           repeat split ;eauto.
           eapply lts_performs_spec1 in tr as (p' & Tr).
           eapply TransitionShapeForInput in Tr as (P1 & P2 & R & n & eq & eq' & Hyp).
           assert (Ѵ n ((gpr_input (VarC_add n c) P1 + P2) ‖ R) ⟶{(c , v) ?}) as accepts.
           { eapply lts_performs_spec2. exists (Ѵ n (P1 ^ v ‖ R)). eapply lts_res_ext_n. eapply lts_parL. eapply lts_choiceL. constructor. }
           eapply (@accepts_preserved_by_eq proc (ExtAct TypeOfActions) VCCS_ExtAction VCCS_gLtsEq) in accepts.
           exact accepts. symmetry. eauto.
Qed.

#[global] Program Instance FinitaryAbsVCCS :
  FinitaryAbsAction (gLtsP := (@gLtsEq_gLts proc _ _ VCCS_gLtsEq)) (gLtsT := VCCS_gLtsEq) proc proc αᴛᴠᴄᴄꜱ αᴘᴠᴄᴄꜱ :=
  {| coR_abs p := PreCoAct_of p ; |}.
Next Obligation.
  intros; subst. eapply gmultiset_elem_of_dom in H.
  eapply (specPreAct1 0) in H. rewrite VarC_preaction_add_zero in H.
  eauto.
Qed.
Next Obligation.
  intros.
  destruct H as (μ & eq & mem).
  destruct μ.
  + destruct a. simpl in *. subst.
    destruct eq as (μ' & Tr & duo & b). symmetry in duo.
    eapply simplify_match_input in duo. subst.
    eapply lts_performs_spec1 in Tr as (p' & Tr).
    eapply TransitionShapeForOutput in Tr as (P1 & P2 & R & n & eq & eq' & Hyp).
    assert (αᴘᴠᴄᴄꜱ  (αᴛᴠᴄᴄꜱ  (ActIn (c , v))) ∈ PreCoAct_of (Ѵ n ((VarC_add n c ! v • P1 + P2) ‖ R))).
      { unfold PreCoAct_of. eapply gmultiset_elem_of_dom. rewrite mPreCoAct_of_res_n.
        simpl. destruct c; simpl.
        + multiset_solver.
        + rewrite decide_True; try lia. replace (n + n0 - (n + 0))%nat with n0%nat by lia.
          multiset_solver. }
      eapply gmultiset_elem_of_dom. eapply PreCoEquiv. symmetry. eauto.
      eapply gmultiset_elem_of_dom. eauto.
    + destruct a. simpl in *. subst.
      destruct eq as (μ' & Tr & duo & b). symmetry in duo.
      eapply simplify_match_output in duo. subst.
      eapply lts_performs_spec1 in Tr as (p' & Tr).
      eapply TransitionShapeForInput in Tr as (P1 & P2 & R & n & eq & eq' & Hyp).
      assert (αᴘᴠᴄᴄꜱ (αᴛᴠᴄᴄꜱ (ActOut (c , v))) ∈ PreCoAct_of (Ѵ n ((gpr_input (VarC_add n c) P1 + P2) ‖ R))).
      { unfold PreCoAct_of. eapply gmultiset_elem_of_dom. rewrite mPreCoAct_of_res_n.
        simpl. destruct c.
        + simpl. multiset_solver.
        + simpl. rewrite decide_True; try lia. replace (n + n0 - (n + 0))%nat with n0%nat by lia.
          multiset_solver. }
      eapply gmultiset_elem_of_dom. eapply PreCoEquiv. symmetry. eauto.
      eapply gmultiset_elem_of_dom. eauto.
Qed.

End VCCS_lts.

Section VCCS_CoFiniteImage.

Context `{VP : VCCS_Parameters}.

#[local] Instance VCCS_gLts_reexport : gLts proc VCCS_ExtAction :=
  @gLtsEq_gLts proc _ _ VCCS_gLtsEq.

Lemma vccs_dual_image_in_iff (p : proc) (a : TypeOfActions) (q : proc) :
  (exists 𝜆' : ExtAct TypeOfActions, dual 𝜆' (ActIn a) /\ p ⟶[𝜆'] q) <-> p ⟶[ActOut a] q.
Proof.
  split.
  - intros (𝜆' & duo & tr). destruct 𝜆' as [x|x]; simpl in duo; [done|].
    assert (x = a) as -> by exact duo. exact tr.
  - intros tr. exists (ActOut a). split; [reflexivity | exact tr].
Qed.

Lemma vccs_dual_image_out_iff (p : proc) (a : TypeOfActions) (q : proc) :
  (exists 𝜆' : ExtAct TypeOfActions, dual 𝜆' (ActOut a) /\ p ⟶[𝜆'] q) <-> p ⟶[ActIn a] q.
Proof.
  split.
  - intros (𝜆' & duo & tr). destruct 𝜆' as [x|x]; simpl in duo; [|done].
    assert (x = a) as -> by exact duo. exact tr.
  - intros tr. exists (ActIn a). split; [reflexivity | exact tr].
Qed.

#[global] Instance VCCS_gLtsCoFiniteImage : coFiniteImagegLts proc (ExtAct TypeOfActions).
Proof.
  unshelve refine {|
    cofolts_states_countable := proc_count;
    cofolts_tau_next_states_finite := _;
    cofolts_next_states_decidable := _;
    cofolts_next_states_finite := _;
  |}.
  - intros p 𝜆 q. destruct 𝜆 as [a|a].
    + destruct (decide (p ⟶[ActOut a] q)) as [Hd|Hd].
      * left. eapply vccs_dual_image_in_iff. exact Hd.
      * right. intro Hc. eapply Hd. eapply vccs_dual_image_in_iff. exact Hc.
    + destruct (decide (p ⟶[ActIn a] q)) as [Hd|Hd].
      * left. eapply vccs_dual_image_out_iff. exact Hd.
      * right. intro Hc. eapply Hd. eapply vccs_dual_image_out_iff. exact Hc.
  - intros p 𝜆. unfold dsig. destruct 𝜆 as [a|a].
    + unshelve eapply (in_list_finite (elements (lts_set_output p a))).
      intros q Htrans%bool_decide_unpack.
      eapply elem_of_elements, lts_set_output_spec1, vccs_dual_image_in_iff.
      exact Htrans.
    + unshelve eapply (in_list_finite (elements (lts_set_input p a))).
      intros q Htrans%bool_decide_unpack.
      eapply elem_of_elements, lts_set_input_spec1, vccs_dual_image_out_iff.
      exact Htrans.
Defined.

End VCCS_CoFiniteImage.
