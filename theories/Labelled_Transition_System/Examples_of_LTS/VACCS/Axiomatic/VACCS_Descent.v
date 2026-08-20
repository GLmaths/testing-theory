(*
   Copyright (c) 2026 Gaëtan Lopez <gaetanlopez.maths@gmail.com>

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

(** * Descending into a normal form's summands

    The completeness recursion has to move from a normal form
    [NF n l M = Ѵⁿ (msgs l ‖ g M)] to the state reached by committing to
    one of [M]'s summands, and it needs that state to be [⊢]-equal to a
    **strictly smaller** [Static] process, so the recursion terminates.

    [normal_form_strong]'s [dom] supplies exactly that: the summand's
    transition is a transition of the normal form, [step_dominated] matches
    it by a transition of the *original* process, and
    [Static_lts_decrease] makes the match strictly smaller.

    ** A structural point worth stating

    The state reached is [Ѵⁿ (msgs l ‖ q)] — the **whole** configuration,
    not the continuation [q] alone.  That is unavoidable: the messages and
    the restriction block stay put, and a message is not a [gproc], so [q]
    cannot be pulled out of its context the way VCCS pulls a
    [𝛕]-continuation out of a guarded sum.

    But it is also *enough*, and this is what makes the recursion work
    without a recursive normal-form predicate: the object the recursion
    descends to is a whole configuration, exactly the kind of thing
    [normal_form_strong] applies to again.  So VACCS needs no analogue of
    VCCS's [tau_normalize_conts] — the stage that does not port
    ([VACCS_Canonical.v]) is simply not needed, because the recursion never
    rewrites a continuation *in place*; it recurses on the reduct. *)

From Stdlib.Wellfounded Require Import Inverse_Image.
From Stdlib Require Import List Permutation PeanoNat Lia.
From stdpp Require Import base sets gmap.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Shift VACCS_Precongruence VACCS_Expansion VACCS_ResNormalize
  VACCS_Copycat VACCS_DefinitionAxiomatic VACCS_SoundnessAx VACCS_NormalForm
  VACCS_ReadySet VACCS_Canonical VACCS_Forwarder.
Import ListNotations.

Section VACCS_Descent.

Context `{VP : VACCS_Parameters}.

(** ** A summand's transition is a transition of the sum *)

Lemma summand_lts_tau : forall M q, In (𝛕 • q) (summands M) -> lts (g M) τ q.
Proof.
  induction M; intros q Hin; simpl in Hin.
  - destruct Hin as [H|H]; [ discriminate H | contradiction ].
  - destruct Hin as [H|H]; [ discriminate H | contradiction ].
  - destruct Hin as [H|H]; [ discriminate H | contradiction ].
  - destruct Hin as [H|H]; [ | contradiction ].
    injection H as H. subst. apply lts_tau.
  - apply in_app_or in Hin as [H|H].
    + apply lts_choiceL. apply IHM1. exact H.
    + apply lts_choiceR. apply IHM2. exact H.
Qed.

Lemma summand_lts_in : forall M c P v, In (c ? P) (summands M) ->
  lts (g M) (ActExt (ActIn (c,v))) (P ^ v).
Proof.
  induction M as [ | | c0 p0 | p0 | M1 IH1 M2 IH2 ]; intros c P v Hin; simpl in Hin.
  - destruct Hin as [H|H]; [ discriminate H | contradiction ].
  - destruct Hin as [H|H]; [ discriminate H | contradiction ].
  - destruct Hin as [H|H]; [ | contradiction ].
    injection H as H1 H2. subst. apply lts_input.
  - destruct Hin as [H|H]; [ discriminate H | contradiction ].
  - apply in_app_or in Hin as [H|H].
    + apply lts_choiceL. eapply IH1. exact H.
    + apply lts_choiceR. eapply IH2. exact H.
Qed.

(** ** …and a transition of the normal form

    For an input the visible channel is the *unshifted* one: [lts_res_ext_n]
    reads the restriction block off, so a summand on [VarC_add n c₀] is what
    the environment sees on [c₀].  Summands on channels that do not survive
    the block are internal only, which is exactly [resg]'s [bvar 0] case. *)

Lemma NF_lts_tau_summand : forall n l M q, In (𝛕 • q) (summands M) ->
  lts (NF n l M) τ (Ѵ n (msgs l ‖ q)).
Proof.
  intros n l M q Hin. unfold NF.
  apply lts_res_tau_n. apply lts_parR. apply summand_lts_tau. exact Hin.
Qed.

Lemma NF_lts_in_summand : forall n l M c0 P v, In ((VarC_add n c0) ? P) (summands M) ->
  lts (NF n l M) (ActExt (ActIn (c0, v))) (Ѵ n (msgs l ‖ (P ^ v))).
Proof.
  intros n l M c0 P v Hin. unfold NF.
  apply lts_res_ext_n. apply lts_parR.
  apply (summand_lts_in M (VarC_add n c0) P v). exact Hin.
Qed.

(** ** The descent

    Committing to a summand lands on a configuration that is [⊢]-equal to a
    strictly smaller [Static] process — which is what the completeness
    recursion needs at a [𝛕]-branch and at a matched input guard. *)

Theorem tau_summand_reduct : forall p n l M q,
  Static p -> dom p (NF n l M) -> In (𝛕 • q) (summands M) ->
  exists u, Static u /\ (size u < size p)%nat
            /\ ax_pre (Ѵ n (msgs l ‖ q)) u /\ ax_pre u (Ѵ n (msgs l ‖ q)).
Proof.
  intros p n l M q Hp (_ & _ & Hs) Hin.
  destruct (Hs τ (Ѵ n (msgs l ‖ q)) (NF_lts_tau_summand n l M q Hin)) as (u & Hu & Ha & Hb).
  exists u. split; [ eapply Static_preserved_by_lts; eassumption | ].
  split; [ eapply Static_lts_decrease; eassumption | split; assumption ].
Qed.

Theorem in_summand_reduct : forall p n l M c0 P v,
  Static p -> dom p (NF n l M) -> In ((VarC_add n c0) ? P) (summands M) ->
  exists u, Static u /\ (size u < size p)%nat
            /\ ax_pre (Ѵ n (msgs l ‖ (P ^ v))) u /\ ax_pre u (Ѵ n (msgs l ‖ (P ^ v))).
Proof.
  intros p n l M c0 P v Hp (_ & _ & Hs) Hin.
  destruct (Hs _ _ (NF_lts_in_summand n l M c0 P v Hin)) as (u & Hu & Ha & Hb).
  exists u. split; [ eapply Static_preserved_by_lts; eassumption | ].
  split; [ eapply Static_lts_decrease; eassumption | split; assumption ].
Qed.

(** ** The UNIFORM descent

    [in_summand_reduct] matches an input guard's transition one value at a
    time, so its witness [u] depends on [v].  The omega rule [ax_input]
    needs a single **open** continuation instead, and [dom_u] supplies it:
    the whole value-indexed family of configurations
    [Ѵⁿ (msgs l ‖ P ^ v)] is matched by [U ^ v] for one open [U], with
    every member a strictly smaller [Static] reduct of [p].

    The open term the family is read off is
    [Ѵⁿ ((NewVar 0 (msgs l)) ‖ P)] — the message bag has to be *shifted*,
    because the guard's binder sits between it and [P]; [NewVar_subst_cancel]
    puts it back at every instance. *)

Lemma NF_in_summand_family : forall n l M c0 P,
  In ((VarC_add n c0) ? P) (summands M) ->
  forall v, lts (NF n l M) (ActExt (ActIn (c0,v)))
                (subst_in_proc 0 v (Ѵ n ((NewVar 0 (msgs l)) ‖ P))).
Proof.
  intros n l M c0 P Hin v.
  rewrite subst_res_n. simpl. rewrite NewVar_subst_cancel.
  apply NF_lts_in_summand. exact Hin.
Qed.

Theorem in_summand_reduct_u : forall p n l M c0 P,
  Static p -> dom_u p (NF n l M) -> In ((VarC_add n c0) ? P) (summands M) ->
  exists U, (forall v : ValueData, lts p (ActExt (ActIn (c0,v))) (subst_in_proc 0 v U))
         /\ (forall v : ValueData, Static (subst_in_proc 0 v U))
         /\ (forall v : ValueData, (size (subst_in_proc 0 v U) < size p)%nat)
         /\ (forall v : ValueData,
               ax_pre (Ѵ n (msgs l ‖ (subst_in_proc 0 v P))) (subst_in_proc 0 v U))
         /\ (forall v : ValueData,
               ax_pre (subst_in_proc 0 v U) (Ѵ n (msgs l ‖ (subst_in_proc 0 v P)))).
Proof.
  intros p n l M c0 P Hp (_ & Hu) Hin.
  destruct (Hu c0 (Ѵ n ((NewVar 0 (msgs l)) ‖ P))
              (NF_in_summand_family n l M c0 P Hin)) as (U & Ha & Hb & Hc).
  assert (HE : forall v : ValueData,
                 subst_in_proc 0 v (Ѵ n ((NewVar 0 (msgs l)) ‖ P))
               = Ѵ n (msgs l ‖ (subst_in_proc 0 v P))).
  { intro v. rewrite subst_res_n. simpl. rewrite NewVar_subst_cancel. reflexivity. }
  exists U. split; [ exact Ha | ].
  split; [ intro v; eapply Static_preserved_by_lts; [ exact Hp | apply Ha ] | ].
  split; [ intro v; eapply Static_lts_decrease; [ exact Hp | apply Ha ] | ].
  split; intro v; [ rewrite <- (HE v); apply Hb | rewrite <- (HE v); apply Hc ].
Qed.

(** ** The outer recursion's premise, at the WRAPPED level

    This is what the level-mismatch analysis was about, stated as a
    theorem.  The completeness recursion runs on [size q] and, at a matched
    input guard of [q]'s normal form, has to discharge an inequation
    against that guard's continuation.  Stated against the **bare**
    continuation it cannot be discharged — no measure bounds a bare
    continuation, because normalisation is not size-decreasing.  Stated
    against the **wrapped** configuration [Ѵⁿ (msgs l ‖ Q ^ v)] it is
    discharged outright, by [in_summand_reduct_u] plus one [ax_trans]:
    the uniform descent produces a strictly smaller [Static] witness
    [U ^ v] that is [⊢]-equal to it, the induction hypothesis applies
    there, and the result transports back along the equality.

    So the measure side of the recursion is settled: what remains is
    entirely on the matching side, namely stating its premise at the
    wrapped level (equivalently, moving the [Ѵⁿ (msgs l ‖ ·)] wrapper
    inside the input guard).  Note the hypothesis and the conclusion are
    both value-indexed families over one open [X], which is the shape
    [ax_input]'s omega rule consumes — that is what [dom_u] buys over
    [dom]. *)
Theorem wrapped_premise_from_IH : forall q n l N c0 Q,
  Static q -> dom_u q (NF n l N) -> In ((VarC_add n c0) ? Q) (summands N) ->
  (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
     ctx_pre p' q' -> ax_pre p' q') ->
  forall X : proc,
    (forall v : ValueData, Static (subst_in_proc 0 v X)) ->
    (forall v : ValueData,
       ctx_pre (subst_in_proc 0 v X) (Ѵ n (msgs l ‖ subst_in_proc 0 v Q))) ->
    (forall v : ValueData,
       ax_pre (subst_in_proc 0 v X) (Ѵ n (msgs l ‖ subst_in_proc 0 v Q))).
Proof.
  intros q n l N c0 Q Hq Hd Hin IH X HXs HX v.
  destruct (in_summand_reduct_u q n l N c0 Q Hq Hd Hin)
    as (U & Ha & Hb & Hc & Hd1 & He).
  eapply ax_trans; [ | apply He ].
  apply IH; [ apply HXs | apply Hb | apply Hc | ].
  intros t Ht. apply (soundness_ax _ _ (Hd1 v)). apply HX. exact Ht.
Qed.

End VACCS_Descent.
