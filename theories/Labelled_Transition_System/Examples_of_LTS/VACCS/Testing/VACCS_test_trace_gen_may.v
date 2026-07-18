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

From TestingTheory Require Import ActTau gLts VACCS_Instance VACCS_Good Bisimulation
  InputOutputActions Completeness ParallelLTSConstruction InputOutputActions
  VACCS_ta_tc_gen MayTestSpec Testing_Predicate.

(** * The May test generator for VACCS

    VACCS counterpart of [VCCS/Testing/VCCS_test_trace_gen_may.v]. The
    de-Bruijn machinery is reused verbatim from Must's own generator
    ([VACCS_ta_tc_gen.v]).

    Two differences from VCCS, both forced by VACCS's asynchronous outputs
    ([non_blocking_output := is_output], [VACCS_Instance.v]):

    - The output branch is a parallel composition ([‖]), mirroring Must's
      own [gen_test_raw]'s output case: the emitted message [c!v•𝟘] is put
      in parallel with the rest of the run, exactly as [pr_output]'s own
      grammar forces (an output prefix can only be followed by [𝟘] — there
      is nothing to sequentialise onto). It carries no deviation branch
      either: unlike an input mismatch, there is no "wrong output" to
      reject, so nothing here plays the role of VCCS's trailing [+(𝛕•𝟘)].
    - Every [blocking β]-guarded [may_test_spec] field is proved by cases
      on [β]: the input case does the real work, the output case is
      discharged by contradiction against [blocking], since
      [non_blocking_output] already covers every output — matching how
      Must's own [test_spec]/[test_co_acceptance_set_spec] instances in
      [VACCS_ta_tc_gen.v] dispatch on [β]. *)

Section VACCS_May_Gen.

Context `{VP : VACCS_Parameters}.

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
      | ActOut (c0, v') :: s'' => (c0 ! v' • 𝟘) ‖ gen_may_raw s'' s'
      | _ => 𝟘
      end
  end.

Definition gen_may (s : trace (ExtAct (ChannelData * ValueData))) : proc :=
  gen_may_raw s s.

(** ** Substitution commutes with the shift, for [gen_may]

    Identical strategy and identical proof shape to VCCS's
    [All_Accordingto_gen_may] — the output branch's [‖] instead of [+]
    never enters this argument, since substitution/shift commute with
    every connective structurally, and the case split is entirely driven
    by [s]'s head tag ([ActIn]/[ActOut]), not by what connects the
    branches. *)

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
                   simpl in *. eapply All_According_To_Data. }
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
              inversion H1. subst. rewrite All_According_To_Data.
              assert (subst_in_proc k d (gen_may_raw (NewVar_in_trace k l) s)
                  = gen_may_raw l s) as eq1.
              { eapply Hlength; eauto with arith. }
              rewrite eq1. eauto.
Qed.

(** ** [gen_may] performs the expected step ([may_test_spec] field 2)

    Unlike every [blocking β]-guarded field below, this one is unconditional
    — it must hold for outputs too, so both cases of [gen_may_lts_mu] do
    real work. *)

Lemma gen_may_lts_mu mu s :
  (gen_may (mu :: s)) ⟶⋍[mu] (gen_may s).
Proof.
  intros. destruct mu as [ (c , v) | (c , v) ].
  - unfold gen_may. simpl in *.
    eexists. split.
    + eapply lts_choiceL. eapply lts_input.
    + simpl. rewrite All_According_To_Data.
      etrans. eapply cgr_if_true.
      * eapply Eval_simpl_true. eauto.
      * rewrite All_Accordingto_gen_may. reflexivity.
  - simpl in *. exists (𝟘 ‖ gen_may s). split.
    + unfold gen_may. simpl.
      constructor. constructor.
    + etrans. eapply cgr_par_com. eapply cgr_par_nil.
Qed.

Lemma gen_may_mu_uniq e a s :
  lts (gen_may (ActIn a :: s)) (ActExt (ActIn a)) e -> e ≡ gen_may s.
Proof.
  unfold gen_may. simpl. destruct a.
  intros. inversion H; subst; inversion H4; subst; eauto.
  simpl. rewrite All_According_To_Data. rewrite All_Accordingto_gen_may.
  eapply cgr_if_true_step. rewrite Eval_simpl_true; eauto.
Qed.

Lemma cgr_to_eqrel p q : p ≡ q -> p ⋍ q.
Proof. intro h. eapply Relation_Operators.t_step. exact h. Qed.

(** ** Determinacy on the expected trace element ([may_test_spec] field 3) *)

Lemma gen_may_follows_trace_determinacy beta s t :
  blocking beta -> lts (gen_may (beta :: s)) (ActExt beta) t -> t ⋍ gen_may s.
Proof.
  intros hb hl. destruct beta as [a|a].
  - eapply cgr_to_eqrel. eapply gen_may_mu_uniq. eauto.
  - exfalso. eapply hb. simpl. unfold non_blocking_output, is_output. exists a; eauto.
Qed.

(** ** [gen_may] is never immediately good ([may_test_spec] field 1)

    Unlike VCCS, the output case is not a closed dead subterm: it recurses
    into [gen_may s'] through the parallel composition ([good_par] is
    disjunctive), so this needs genuine induction on [s], not just a case
    split. *)

Lemma gen_may_ungood s : ~ good_VACCS (gen_may s).
Proof.
  induction s as [|mu s' IH].
  - unfold gen_may. simpl. intro hg. inversion hg.
  - destruct mu as [(c,v)|(c,v)].
    + unfold gen_may. simpl. intro hg. inversion hg; subst.
      destruct H0 as [h|h]; inversion h.
    + unfold gen_may. simpl. intro hg. inversion hg; subst.
      destruct H0 as [h|h].
      * inversion h.
      * apply IH. unfold gen_may. exact h.
Qed.

(** ** The dead process [𝟘] has no transitions, and reaches success never *)

Lemma DEAD_no_lts_tau : forall t, ~ lts (g 𝟘) τ t.
Proof. intros t h. inversion h. Qed.

Lemma DEAD_no_lts_mu : forall mu t, ~ lts (g 𝟘) (ActExt mu) t.
Proof. intros mu t h. inversion h. Qed.

Lemma DEAD_never_outcome : never_outcome good_VACCS (g 𝟘).
Proof.
  intros u t' hwt hgood.
  remember (g 𝟘) as p0 eqn:heq0.
  induction hwt.
  - subst. inversion hgood.
  - subst. exfalso. eapply DEAD_no_lts_tau. eauto.
  - subst. exfalso. eapply DEAD_no_lts_mu. eauto.
Qed.

(** ** A conditional whose [Else] branch is dead and whose condition is not
      provably true, is itself dead — same argument as VCCS's
      [if_not_true_never_outcome]. *)

Lemma if_not_true_no_lts E P a t :
  Eval_Eq 0 E <> Some true -> ~ lts (If E Then P Else 𝟘) a t.
Proof.
  intros hne h. inversion h; subst.
  - contradiction.
  - match goal with H : lts (g 𝟘) _ _ |- _ => inversion H end.
Qed.

Lemma if_not_true_never_outcome E P :
  Eval_Eq 0 E <> Some true -> never_outcome good_VACCS (If E Then P Else 𝟘).
Proof.
  intros hne u t' hwt hgood.
  remember (If E Then P Else 𝟘) as p0 eqn:heq0.
  induction hwt.
  - subst. inversion hgood; subst; try congruence.
    match goal with H : good_VACCS (g 𝟘) |- _ => inversion H end.
  - subst. exfalso. eapply if_not_true_no_lts; eauto.
  - subst. exfalso. eapply if_not_true_no_lts; eauto.
Qed.

(** ** Every step from [gen_may (ActIn a :: s)] is either the expected step
      to [gen_may s], or leads somewhere success can never be reached from.
      Restricted to inputs: this is only ever consumed by the
      [blocking β]-guarded fields below, and outputs are never blocking. *)

Lemma gen_may_step_dichotomy a s alpha t :
  lts (gen_may (ActIn a :: s)) alpha t ->
  (alpha = ActExt (ActIn a) /\ t ≡ gen_may s) \/ never_outcome good_VACCS t.
Proof.
  unfold gen_may. destruct a as (c,v); simpl; intro hl; inversion hl; subst.
  { inversion H3; subst.
    destruct (decide (v0 = v)) as [->|hneq].
    - left. split; [reflexivity|]. simpl.
      rewrite All_According_To_Data. rewrite All_Accordingto_gen_may.
      eapply cgr_if_true_step. eapply Eval_simpl_true; eauto.
    - right. simpl. eapply if_not_true_never_outcome.
      intro hcontra. apply hneq.
      destruct v0 as [v0'|i0]; destruct v as [v'|i]; simpl in hcontra; try discriminate.
      + destruct (decide (v0' = v')) as [->|]; [reflexivity | discriminate].
      + destruct (decide (i0 = i)) as [->|]; [reflexivity | discriminate]. }
  { right. inversion H3; subst. eapply DEAD_never_outcome. }
Qed.

(** ** Deviation is fatal ([may_test_spec] field 4) *)

Lemma gen_may_deviation_is_fatal beta mu s t :
  blocking beta -> lts (gen_may (beta :: s)) (ActExt mu) t -> mu <> beta -> never_outcome good_VACCS t.
Proof.
  intros hb hl hneq.
  destruct beta as [a|a].
  - destruct (gen_may_step_dichotomy a s (ActExt mu) t hl) as [[heq _]|hno].
    + injection heq as ->. contradiction.
    + exact hno.
  - exfalso. eapply hb. simpl. unfold non_blocking_output, is_output. exists a; eauto.
Qed.

(** ** A silent move on a blocking head is fatal ([may_test_spec] field 7) *)

Lemma gen_may_tau_on_blocking_is_fatal beta s t :
  blocking beta -> lts (gen_may (beta :: s)) τ t -> never_outcome good_VACCS t.
Proof.
  intros hb hl.
  destruct beta as [a|a].
  - destruct (gen_may_step_dichotomy a s τ t hl) as [[heq _]|hno].
    + discriminate.
    + exact hno.
  - exfalso. eapply hb. simpl. unfold non_blocking_output, is_output. exists a; eauto.
Qed.

(** ** [gen_may ε] computes silently to success ([may_test_spec] fields 5, 6) *)

Lemma gen_may_can_compute : exists e, lts (gen_may []) τ e.
Proof.
  exists ①. unfold gen_may. simpl. eapply lts_tau.
Qed.

Lemma gen_may_computes_to_good e : lts (gen_may []) τ e -> good_VACCS e.
Proof.
  unfold gen_may. simpl. intro hl. inversion hl; subst. eapply good_success.
Qed.

(** ** The instance *)

#[global] Program Instance VACCS_may_test_spec : may_test_spec gen_may := {|
  may_test_ungood := gen_may_ungood;
  may_test_next_step := gen_may_lts_mu;
  may_test_follows_trace_determinacy := gen_may_follows_trace_determinacy;
  may_test_deviation_is_fatal := gen_may_deviation_is_fatal;
  may_test_can_compute := gen_may_can_compute;
  may_test_computes_to_good := gen_may_computes_to_good;
  may_test_tau_on_blocking_is_fatal := gen_may_tau_on_blocking_is_fatal;
|}.

End VACCS_May_Gen.
