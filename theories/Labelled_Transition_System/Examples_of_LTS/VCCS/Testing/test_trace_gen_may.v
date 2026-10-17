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
(* end hide *)

From Stdlib Require ssreflect Setoid.
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Wf Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.

From stdpp Require Import base countable finite gmap list gmultiset strings.

From TestingTheory Require Import ActTau gLts VCCS.Language.gLts_Instance VCCS_Good Bisimulation
  InputOutputActions Completeness ParallelLTSConstruction InputOutputActions
  VCCS.Testing.ta_tc_gen MayTestSpec Testing_Predicate.

(** ******* The May test generator for VCCS *)

Section VCCS_May_Gen.

Context `{VP : VCCS_Parameters}.

Fixpoint gen_may_raw (Vs : trace (ExtAct (ChannelData * ValueData)))
  (s : trace (ExtAct TypeOfActions)) {struct s} : proc :=
  match s with
  | [] => 𝛕 • ①
  | ActIn (_, _) :: s' =>
      match Vs with
      | ActIn (c0, v') :: s'' =>
          c0
          ? • (If bvar 0 == NewVar_in_Data 0 v'
                Then gen_may_raw (NewVar_in_trace 0 s'') s'
                Else 𝟘) +
          (𝛕 • 𝟘)
      | _ => 𝟘
      end
  | ActOut (_, _) :: s' =>
      match Vs with
      | ActOut (c0, v') :: s'' => c0 ! v' • gen_may_raw s'' s' + (𝛕 • 𝟘)
      | _ => 𝟘
      end
  end.

Definition gen_may (s : trace (ExtAct (ChannelData * ValueData))) : proc :=
  gen_may_raw s s.

(** ******* Substitution commutes with the shift *)

Lemma All_Accordingto_gen_may s s' d k :
  subst_in_proc k d (gen_may_raw (NewVar_in_trace k s') s) = gen_may_raw s' s.
Proof.
  revert d k s'. induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s; intros; simpl in *.
  - reflexivity.
  - destruct e as [ (c,v) | (c,v) ].
    + case_eq (NewVar_in_trace k s').
      * intros. case_eq s'.
        -- intros. subst. simpl. reflexivity.
        -- intros. subst. simpl. case_eq e.
           ++ intros. destruct a. subst. simpl in *. inversion H.
           ++ intros. subst. destruct a. reflexivity.
      * intros. case_eq e.
        -- intros. destruct a. subst. case_eq s'.
           ++ intros. subst. inversion H.
           ++ intros. subst. case_eq e.
              ** intros. destruct a. subst. simpl in H. inversion H. subst.
                 simpl. assert (k = 0+k)%nat as eq1 by eauto with arith.
                 assert (subst_Data (S k) (Succ_bvar d) (NewVar_in_Data 0 (NewVar_in_Data k v1))
                        = NewVar_in_Data 0 v1) as eq.
                 { rewrite eq1 at 2. rewrite<- New_Var_And_NewVar_in_Data.
                   simpl in *. eapply subst_NewVar_Data_cancel. }
                 rewrite eq. assert (subst_in_proc (S k) (Succ_bvar d) (gen_may_raw
                            (NewVar_in_trace 0 (NewVar_in_trace k l0)) s) = gen_may_raw (NewVar_in_trace 0 l0) s) as eq2.
                 { rewrite eq1 at 2. rewrite<- New_Var_And_NewVar_in_Trace. simpl in *.
                 { eapply Hlength; eauto with arith. } }
                 rewrite eq2. eauto.
              ** intros. subst. simpl in *. destruct a. inversion H.
        -- intros. subst. destruct a. case_eq s'.
           ++ intros. subst. simpl. inversion H.
           ++ intros. case_eq e.
              ** subst. intros. subst. simpl in *. destruct a. inversion H.
              ** intros. subst. destruct a. simpl. reflexivity.
    + case_eq s'.
      * intros. simpl. reflexivity.
      * intros. subst. simpl.
        case_eq (NewVar_in_label k e).
        -- intros. case_eq a. intros. subst. case_eq e.
           ++ intros. subst. destruct a. simpl. reflexivity.
           ++ intros. subst. inversion H. destruct a. inversion H1.
        -- intros. case_eq a. intros. subst. case_eq e.
           ++ intros. destruct a. subst. inversion H.
           ++ intros. subst. inversion H. destruct a. simpl.
              inversion H1. subst. rewrite subst_NewVar_Data_cancel.
              assert (subst_in_proc k d (gen_may_raw (NewVar_in_trace k l) s)
                  = gen_may_raw l s) as eq1.
              { eapply Hlength; eauto with arith. }
              rewrite eq1. eauto.
Qed.

Lemma gen_may_ungood s : ~ good_VCCS (gen_may s).
Proof.
  unfold gen_may. destruct s as [|[(c,v)|(c,v)] s']; simpl.
  - intro hg. inversion hg.
  - intro hg. inversion hg; subst.
    destruct H0 as [h|h]; inversion h.
  - intro hg. inversion hg; subst.
    destruct H0 as [h|h]; inversion h.
Qed.

Lemma gen_may_lts_mu μ s :
  (gen_may (μ :: s)) ⟶⋍[μ] (gen_may s).
Proof.
  intros. destruct μ as [ (c , v) | (c , v) ].
  - unfold gen_may. simpl in *.
    eexists. split.
    + eapply lts_choiceL. eapply lts_input.
    + simpl. rewrite subst_NewVar_Data_cancel.
      etrans. eapply cgr_if_true.
      * eapply Eval_simpl_true. eauto.
      * rewrite All_Accordingto_gen_may. reflexivity.
  - simpl in *. exists (gen_may s). split.
    + unfold gen_may. simpl.
      constructor. constructor.
    + reflexivity.
Qed.

Lemma gen_may_mu_uniq e μ s :
  lts (gen_may (μ :: s)) (ActExt μ) e -> e ≡ gen_may s.
Proof.
  unfold gen_may. simpl. destruct μ; destruct a; simpl in *.
  + intros. inversion H; subst; inversion H4; subst; eauto.
    simpl. rewrite subst_NewVar_Data_cancel. rewrite All_Accordingto_gen_may.
    eapply cgr_if_true_step. rewrite Eval_simpl_true; eauto.
  + intros. inversion H; subst; inversion H4; subst; eauto. reflexivity.
Qed.

Lemma cgr_to_eqrel p q : p ≡ q -> p ⋍ q.
Proof. intro h. eapply Relation_Operators.t_step. exact h. Qed.

Lemma gen_may_follows_trace_determinacy β s t :
  blocking β -> lts (gen_may (β :: s)) (ActExt β) t -> t ⋍ gen_may s.
Proof.
  intros _ hl. eapply cgr_to_eqrel. eapply gen_may_mu_uniq. eauto.
Qed.

Lemma DEAD_no_lts_tau : forall t, ~ lts (g 𝟘) τ t.
Proof. intros t h. inversion h. Qed.

Lemma DEAD_no_lts_mu : forall μ t, ~ lts (g 𝟘) (ActExt μ) t.
Proof. intros μ t h. inversion h. Qed.

Lemma DEAD_never_outcome : never_outcome good_VCCS (g 𝟘).
Proof.
  intros u t' hwt hgood.
  remember (g 𝟘) as p0 eqn:heq0.
  induction hwt.
  - subst. inversion hgood.
  - subst. exfalso. eapply DEAD_no_lts_tau. eauto.
  - subst. exfalso. eapply DEAD_no_lts_mu. eauto.
Qed.

Lemma if_not_true_no_lts E P a t :
  Eval_Eq 0 E <> Some true -> ~ lts (If E Then P Else 𝟘) a t.
Proof.
  intros hne h. inversion h; subst.
  - contradiction.
  - match goal with H : lts (g 𝟘) _ _ |- _ => inversion H end.
Qed.

Lemma if_not_true_never_outcome E P :
  Eval_Eq 0 E <> Some true -> never_outcome good_VCCS (If E Then P Else 𝟘).
Proof.
  intros hne u t' hwt hgood.
  remember (If E Then P Else 𝟘) as p0 eqn:heq0.
  induction hwt.
  - subst. inversion hgood; subst; try congruence.
    match goal with H : good_VCCS (g 𝟘) |- _ => inversion H end.
  - subst. exfalso. eapply if_not_true_no_lts; eauto.
  - subst. exfalso. eapply if_not_true_no_lts; eauto.
Qed.

Lemma gen_may_step_dichotomy β s 𝜆 t :
  lts (gen_may (β :: s)) 𝜆 t ->
  (𝜆 = ActExt β /\ t ≡ gen_may s) \/ never_outcome good_VCCS t.
Proof.
  unfold gen_may. destruct β as [(c,v)|(c,v)]; simpl; intro hl; inversion hl; subst.
  { inversion H3; subst.
    destruct (decide (v0 = v)) as [->|hneq].
    - left. split; [reflexivity|]. simpl.
      rewrite subst_NewVar_Data_cancel. rewrite All_Accordingto_gen_may.
      eapply cgr_if_true_step. eapply Eval_simpl_true; eauto.
    - right. simpl. eapply if_not_true_never_outcome.
      intro hcontra. apply hneq.
      destruct v0 as [v0'|i0]; destruct v as [v'|i]; simpl in hcontra; try discriminate.
      + destruct (decide (v0' = v')) as [->|]; [reflexivity | discriminate].
      + destruct (decide (i0 = i)) as [->|]; [reflexivity | discriminate]. }
  { right. inversion H3; subst. eapply DEAD_never_outcome. }
  { inversion H3; subst. left. split; [reflexivity | reflexivity]. }
  { right. inversion H3; subst. eapply DEAD_never_outcome. }
Qed.

Lemma gen_may_deviation_is_fatal β μ s t :
  blocking β -> lts (gen_may (β :: s)) (ActExt μ) t -> μ <> β -> never_outcome good_VCCS t.
Proof.
  intros _ hl hneq.
  destruct (gen_may_step_dichotomy β s (ActExt μ) t hl) as [[heq _]|hno].
  - injection heq as ->. contradiction.
  - exact hno.
Qed.

Lemma gen_may_tau_on_blocking_is_fatal β s t :
  blocking β -> lts (gen_may (β :: s)) τ t -> never_outcome good_VCCS t.
Proof.
  intros _ hl.
  destruct (gen_may_step_dichotomy β s τ t hl) as [[heq _]|hno].
  - discriminate.
  - exact hno.
Qed.

Lemma gen_may_can_compute : exists e, lts (gen_may []) τ e.
Proof.
  exists ①. unfold gen_may. simpl. eapply lts_tau.
Qed.

Lemma gen_may_computes_to_good e : lts (gen_may []) τ e -> good_VCCS e.
Proof.
  unfold gen_may. simpl. intro hl. inversion hl; subst. eapply good_success.
Qed.

#[global] Program Instance VCCS_may_test_spec : may_test_spec gen_may := {|
  may_test_ungood := gen_may_ungood;
  may_test_next_step := gen_may_lts_mu;
  may_test_follows_trace_determinacy := gen_may_follows_trace_determinacy;
  may_test_deviation_is_fatal := gen_may_deviation_is_fatal;
  may_test_can_compute := gen_may_can_compute;
  may_test_computes_to_good := gen_may_computes_to_good;
  may_test_tau_on_blocking_is_fatal := gen_may_tau_on_blocking_is_fatal;
|}.

End VCCS_May_Gen.
