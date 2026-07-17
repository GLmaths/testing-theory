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

From Stdlib Require ssreflect Setoid.
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Wf Equality.
From Stdlib.Wellfounded Require Import Inverse_Image.

From stdpp Require Import base countable finite gmap list gmultiset strings.

From TestingTheory Require Import ActTau gLts VCCS_Instance VCCS_Good Bisimulation
  InputOutputActions Completeness ParallelLTSConstruction InputOutputActions
  VCCS_ta_tc_gen MayTestSpec Testing_Predicate.

(** * The May test generator for VCCS

    Builds the [gen : trace A -> proc] required by [may_test_spec]
    ([MayTestSpec.v]) for VCCS, and discharges the [may_test_spec] instance
    used by [Trace_Inclusion/EquivalenceTI.v]'s [equivalence_ti_fw]/
    [equivalence_ti_fb] theorems.

    All of the de-Bruijn index-shifting machinery ([NewVar_in_trace],
    [NewVar_in_Data], [All_AccordingTo_Data], [Eval_simpl_true], ...) is
    reused verbatim from Must's own generator ([VCCS_ta_tc_gen.v]): it is
    purely about VCCS's own binder mechanics, agnostic to May vs Must. Only
    the generator itself, and the lemmas about its behaviour, are new here.

    [gen_may] differs from Must's [gen_test] in two ways, both forced by
    May's polarity (see [MayTestSpec.v]'s header comment): it carries no
    continuation parameter [p] (Must threads the process under test through;
    May's test is self-contained), and a deviation reduces to the dead
    process [𝟘] rather than to the successful [①] — deviating from the
    trace must make success *unreachable*, not merely bypassed. *)

Section VCCS_May_Gen.

Context `{VP : VCCS_Parameters}.

(** ** The generator itself *)

Fixpoint gen_may_raw (Vs : trace (ExtAct (ChannelData * ValueData)))
  (s : trace (ExtAct TypeOfActions)) {struct s} : proc :=
  match s with
  | [] => 𝛕 • ①
  | ActIn (_, _) :: s' =>
      match Vs with
      | ActIn (c0, v') :: s'' =>
          c0
          ? (If bvar 0 == NewVar_in_Data 0 v'
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

(** ** Substitution commutes with the shift, for [gen_may]

    May counterpart of [All_Accordingto_gen_test], without the continuation
    parameter [p]: the base case is now a closed term ([𝛕 • ①] has no free
    de-Bruijn indices) so it closes by [reflexivity] instead of routing
    through [All_According]. *)

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
                   simpl in *. eapply All_AccordingTo_Data. }
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
              inversion H1. subst. rewrite All_AccordingTo_Data.
              assert (subst_in_proc k d (gen_may_raw (NewVar_in_trace k l) s)
                  = gen_may_raw l s) as eq1.
              { eapply Hlength; eauto with arith. }
              rewrite eq1. eauto.
Qed.

(** ** [gen_may] is never immediately good ([may_test_spec] field 1)

    [gen_may_raw] always returns [𝛕•①], [c?(...)+(𝛕•𝟘)] or [c!v•(...)+(𝛕•𝟘)]
    — none of these shapes matches any [good_VCCS] constructor directly
    (action-prefixed processes and choices between action-prefixed
    processes are never immediately good). *)

Lemma gen_may_ungood s : ~ good_VCCS (gen_may s).
Proof.
  unfold gen_may. destruct s as [|[(c,v)|(c,v)] s']; simpl.
  - intro hg. inversion hg.
  - intro hg. inversion hg; subst.
    destruct H0 as [h|h]; inversion h.
  - intro hg. inversion hg; subst.
    destruct H0 as [h|h]; inversion h.
Qed.

(** ** [gen_may] performs the expected step ([may_test_spec] field 2) *)

Lemma gen_may_lts_mu mu s :
  (gen_may (mu :: s)) ⟶⋍[mu] (gen_may s).
Proof.
  intros. destruct mu as [ (c , v) | (c , v) ].
  - unfold gen_may. simpl in *.
    eexists. split.
    + eapply lts_choiceL. eapply lts_input.
    + simpl. rewrite All_AccordingTo_Data.
      etrans. eapply cgr_if_true.
      * eapply Eval_simpl_true. eauto.
      * rewrite All_Accordingto_gen_may. reflexivity.
  - simpl in *. exists (gen_may s). split.
    + unfold gen_may. simpl.
      constructor. constructor.
    + reflexivity.
Qed.

Lemma gen_may_mu_uniq e mu s :
  lts (gen_may (mu :: s)) (ActExt mu) e -> e ≡ gen_may s.
Proof.
  unfold gen_may. simpl. destruct mu; destruct a; simpl in *.
  + intros. inversion H; subst; inversion H4; subst; eauto.
    simpl. rewrite All_AccordingTo_Data. rewrite All_Accordingto_gen_may.
    eapply cgr_if_true_step. rewrite Eval_simpl_true; eauto.
  + intros. inversion H; subst; inversion H4; subst; eauto. reflexivity.
Qed.

Lemma cgr_to_eqrel p q : p ≡ q -> p ⋍ q.
Proof. intro h. eapply Relation_Operators.t_step. exact h. Qed.

(** ** Determinacy on the expected trace element ([may_test_spec] field 3) *)

Lemma gen_may_follows_trace_determinacy beta s t :
  blocking beta -> lts (gen_may (beta :: s)) (ActExt beta) t -> t ⋍ gen_may s.
Proof.
  intros _ hl. eapply cgr_to_eqrel. eapply gen_may_mu_uniq. eauto.
Qed.

(** ** The dead process [𝟘] has no transitions, and reaches success never *)

Lemma DEAD_no_lts_tau : forall t, ~ lts (g 𝟘) τ t.
Proof. intros t h. inversion h. Qed.

Lemma DEAD_no_lts_mu : forall mu t, ~ lts (g 𝟘) (ActExt mu) t.
Proof. intros mu t h. inversion h. Qed.

Lemma DEAD_never_outcome : never_outcome good_VCCS (g 𝟘).
Proof.
  intros u t' hwt hgood.
  remember (g 𝟘) as p0 eqn:heq0.
  induction hwt.
  - subst. inversion hgood.
  - subst. exfalso. eapply DEAD_no_lts_tau. eauto.
  - subst. exfalso. eapply DEAD_no_lts_mu. eauto.
Qed.

(** ** A conditional whose [Else] branch is dead and whose condition is not
      provably true, is itself dead — this is what a deviating input step
      reduces to (see [gen_may_step_dichotomy] below): either the concrete
      values genuinely differ ([Eval_Eq = Some false]), or the comparison is
      stuck on a bound variable ([Eval_Eq = None]); both cases leave [𝟘] as
      the only reachable branch, hence no transition at all. *)

Lemma if_not_true_no_lts E P a t :
  Eval_Eq E <> Some true -> ~ lts (If E Then P Else 𝟘) a t.
Proof.
  intros hne h. inversion h; subst.
  - contradiction.
  - match goal with H : lts (g 𝟘) _ _ |- _ => inversion H end.
Qed.

Lemma if_not_true_never_outcome E P :
  Eval_Eq E <> Some true -> never_outcome good_VCCS (If E Then P Else 𝟘).
Proof.
  intros hne u t' hwt hgood.
  remember (If E Then P Else 𝟘) as p0 eqn:heq0.
  induction hwt.
  - subst. inversion hgood; subst; try congruence.
    match goal with H : good_VCCS (g 𝟘) |- _ => inversion H end.
  - subst. exfalso. eapply if_not_true_no_lts; eauto.
  - subst. exfalso. eapply if_not_true_no_lts; eauto.
Qed.

(** ** Every step from [gen_may (beta :: s)] is either the expected [beta]
      step to [gen_may s], or leads somewhere success can never be reached
      from — the key case split everything else is built from. *)

Lemma gen_may_step_dichotomy beta s alpha t :
  lts (gen_may (beta :: s)) alpha t ->
  (alpha = ActExt beta /\ t ≡ gen_may s) \/ never_outcome good_VCCS t.
Proof.
  unfold gen_may. destruct beta as [(c,v)|(c,v)]; simpl; intro hl; inversion hl; subst.
  { inversion H3; subst.
    destruct (decide (v0 = v)) as [->|hneq].
    - left. split; [reflexivity|]. simpl.
      rewrite All_AccordingTo_Data. rewrite All_Accordingto_gen_may.
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

(** ** Deviation is fatal ([may_test_spec] field 4) *)

Lemma gen_may_deviation_is_fatal beta mu s t :
  blocking beta -> lts (gen_may (beta :: s)) (ActExt mu) t -> mu <> beta -> never_outcome good_VCCS t.
Proof.
  intros _ hl hneq.
  destruct (gen_may_step_dichotomy beta s (ActExt mu) t hl) as [[heq _]|hno].
  - injection heq as ->. contradiction.
  - exact hno.
Qed.

(** ** A silent move on a blocking head is fatal ([may_test_spec] field 7) *)

Lemma gen_may_tau_on_blocking_is_fatal beta s t :
  blocking beta -> lts (gen_may (beta :: s)) τ t -> never_outcome good_VCCS t.
Proof.
  intros _ hl.
  destruct (gen_may_step_dichotomy beta s τ t hl) as [[heq _]|hno].
  - discriminate.
  - exact hno.
Qed.

(** ** [gen_may ε] computes silently to success ([may_test_spec] fields 5, 6) *)

Lemma gen_may_can_compute : exists e, lts (gen_may []) τ e.
Proof.
  exists ①. unfold gen_may. simpl. eapply lts_tau.
Qed.

Lemma gen_may_computes_to_good e : lts (gen_may []) τ e -> good_VCCS e.
Proof.
  unfold gen_may. simpl. intro hl. inversion hl; subst. eapply good_success.
Qed.

(** ** The instance *)

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
