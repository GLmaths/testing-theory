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

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Equality Basics.
From stdpp Require Import base countable list decidable finite gmap gmultiset.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_FW Subset_Act
    WeakTransitions Convergence coWeakTransition coConvergence Termination
    FiniteImageLTS Testing_Predicate StateTransitionSystems InteractionBetweenLts
    DefinitionAS DefinitionASco NormalForm Normalisation.

(** * Normalisation of co-traces

    A co-trace is read from the point of view of the *observer*: a step
    labelled [μ] in a co-trace is realised in the LTS by *some* action dual to
    [μ].  Nothing here assumes that this action is unique: as in
    [coWeakTransition.v] and [coConvergence.v], every statement quantifies over
    the actions dual to a label, and the uniqueness axiom [unique_nb] is never
    used -- except, at the very end of the file, to exhibit one canonical
    classification of the co-actions.

    Because of this, the classification of the labels of a co-trace cannot be
    computed from a single co-action: it is taken as a parameter, subject to
    the specification [CoClassifier] below.  The three classes are, for a label
    [μ] of the co-trace,

    - [CNB] every action dual to [μ] is non-blocking ([co_non_blocking]); those
      are the labels the observer inputs and the process answers with an
      output;
    - [CIN] the actions dual to [μ] are all dual to one and the same
      non-blocking action ([co_exist_co_nba]);
    - [COP] the remaining, opaque, labels. *)

(** ** Classes of the labels of a co-trace *)

(** The co variant of [exist_co_nba]: it is exactly the hypothesis that
    [cowt_input_swap] and [cowt_input_perm] require. *)
Definition co_exist_co_nba `{ExtAction A} (μ : A) : Prop :=
  exists η, non_blocking η /\ forall ν, dual ν μ -> dual ν η.

(** Two labels of a co-trace cancel out when the actions realising the second
    are co-actions of the actions realising the first. *)
Definition co_feedback `{ExtAction A} (μ1 μ2 : A) : Prop :=
  forall ν1 ν2, dual ν1 μ1 -> dual ν2 μ2 -> dual ν2 ν1.

Lemma dual_co `{ExtAction A} (μ : A) : dual (co μ) μ.
Proof. symmetry. exact (proj2_sig (exists_dual μ)). Qed.

(** The second label of a feedback always admits a non-blocking co-action.
    Only the *existence* of a co-action is used here. *)
Lemma co_feedback_CIN `{ExtAction A} (μ1 μ2 : A) :
  co_non_blocking μ1 -> co_feedback μ1 μ2 -> co_exist_co_nba μ2.
Proof.
  intros nb hfb. exists (co μ1). split.
  - eapply nb, dual_co.
  - intros ν dν. eapply hfb; [eapply dual_co | exact dν].
Qed.

(** The redex of the feedback on co-traces. *)
Definition co_fb_rel `{ExtAction A} (μ1 μ2 : A) : Prop :=
  co_non_blocking μ1 /\ co_feedback μ1 μ2.

(** Two feedback redexes never overlap: as on traces, this is [dual_blocks],
    applied to the co-actions that [exists_dual] provides.  No determinacy is
    involved. *)
Lemma co_fb_rel_disjoint `{ExtAction A} (x y z : A) : co_fb_rel x y -> ¬ co_fb_rel y z.
Proof.
  intros (nbx & hfb) (nby & _).
  eapply (dual_blocks (co y) (co x)).
  - eapply nbx, dual_co.
  - eapply hfb; eapply dual_co.
  - eapply nby, dual_co.
Qed.

(** A classification of the labels that is faithful to the two predicates
    above.  Any concrete LTS may provide its own; one canonical choice is given
    at the end of this file. *)
Class CoClassifier `{ExtAction A} (cls : A -> act_class) := {
    cls_CNB_iff : forall μ, cls μ = CNB <-> co_non_blocking μ;
    cls_CIN_iff : forall μ, cls μ = CIN <-> co_exist_co_nba μ;
  }.

(** The two non-opaque classes are indeed disjoint. *)
Lemma co_nb_not_co_exist_co_nba `{ExtAction A} (μ : A) :
  co_non_blocking μ -> ¬ co_exist_co_nba μ.
Proof.
  intros hnb (η & nbη & hη).
  assert (duo : dual (co μ) μ) by (symmetry; exact (proj2_sig (exists_dual μ))).
  eapply (dual_blocks (co μ) η nbη (hη (co μ) duo)). now eapply hnb.
Qed.

(** ** Co-convergence is preserved by the swaps of two consecutive labels

    The two lemmas below are the co variants of [cnv_non_blocking_action_swap]
    and of [cnv_input_swap]; they are missing from [coConvergence.v]. *)

Section CoSwaps.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.

  Lemma cocnv_non_blocking_action_swap (p : P) η1 η2 s :
    co_non_blocking η1 -> co_non_blocking η2 ->
    p ⇓ᶜᵒ η1 :: η2 :: s -> p ⇓ᶜᵒ η2 :: η1 :: s.
  Proof.
    intros nb1 nb2 hcnv.
    assert (hterm : p ⤓) by (eapply cocnv_terminate; exact hcnv).
    eapply cocnv_act; [exact hterm |].
    intros q hw1.
    eapply cocnv_act.
    - eapply (terminate_preserved_by_cowt_non_blocking_action p q η2 nb2);
        [exact hterm | exact hw1].
    - intros t hw2.
      assert (hw3 : p ⟹ᶜᵒ[[η2 ; η1]] t) by (eapply cowt_push_left; eassumption).
      eapply (cowt_non_blocking_action_swap p t η2 η1 nb2 nb1) in hw3 as (t' & hw4 & eq').
      eapply cocnv_preserved_by_eq; [exact eq' | reflexivity |].
      eapply (cocnv_cowt_prefix [η1 ; η2] s p); [exact hcnv | exact hw4].
  Qed.

  (* The co-step of [p] along [μ1] that the proof needs is built by input
     receptivity ([boomerang]) out of *one* action dual to [μ1]; which one does
     not matter, since [co_exist_co_nba μ1] makes all of them dual to the same
     non-blocking [η1]. *)
  Lemma cocnv_input_swap (p : P) μ1 μ2 s :
    co_exist_co_nba μ1 -> co_exist_co_nba μ2 ->
    p ⇓ᶜᵒ μ1 :: μ2 :: s -> p ⇓ᶜᵒ μ2 :: μ1 :: s.
  Proof.
    intros hμ1 hμ2 hcnv.
    destruct hμ1 as (η1 & nb1 & h1).
    assert (hterm : p ⤓) by (eapply cocnv_terminate; exact hcnv).
    assert (hclause : forall q, p ⟹ᶜᵒ{μ1} q -> q ⇓ᶜᵒ μ2 :: s)
      by (intros q w; eapply (cocnv_preserved_by_cowt_act (μ2 :: s) p μ1); eassumption).
    destruct (exists_dual μ1) as (ν1 & duo1).
    assert (dν1 : dual ν1 μ1) by (now symmetry).
    destruct (boomerang p η1 ν1) as (t0 & Hb).
    destruct (Hb nb1 (h1 ν1 dν1)) as (l1 & l2).
    assert (w0 : p ⟹ᶜᵒ{μ1} t0) by (eapply lts_to_cowt; [exact dν1 | exact l1]).
    eapply cocnv_act; [exact hterm |].
    intros q w1.
    eapply cocnv_act.
    - destruct (delay_cowt_non_blocking_action nb1 (mk_lts_eq l2) w1)
        as (t' & w2 & (t2 & hlt2 & heqt2)).
      assert (ht' : t' ⤓).
      { eapply (cocnv_terminate t' s).
        exact (cocnv_preserved_by_cowt_act s t0 μ2 (hclause t0 w0) t' w2). }
      eapply (terminate_preserved_by_eq2 heqt2).
      exact (terminate_preserved_by_lts_non_blocking_action nb1 hlt2 ht').
    - intros r w2.
      destruct (cowt_input_swap p r μ2 μ1 (ex_intro _ η1 (conj nb1 h1))
                  (cowt_push_left w1 w2)) as (t & w' & heq').
      eapply cocnv_preserved_by_eq; [exact heq' | reflexivity |].
      eapply (cocnv_cowt_prefix [μ1 ; μ2] s p); [exact hcnv | exact w'].
  Qed.

  (* The co variant of [wt_annhil]: the two actions that realise [μ1] and [μ2]
     are whichever the derivation happens to use, and [co_feedback] guarantees
     that they cancel out, whatever they are. *)
  Lemma cowt_annhil_pair (p q : P) μ1 μ2 :
    co_non_blocking μ1 -> co_feedback μ1 μ2 -> p ⟹ᶜᵒ[[μ1 ; μ2]] q -> p ⟹ᶜᵒ⋍ q.
  Proof.
    intros nb hfb w.
    eapply cowt_to_wt_dual in w as (s' & hf & w').
    inversion hf as [| x1 y1 la1 lb1 d1 hf1]; subst.
    inversion hf1 as [| x2 y2 la2 lb2 d2 hf2]; subst.
    inversion hf2; subst.
    assert (hw : p ⟹⋍ q).
    { eapply (wt_annhil p q y1 y2).
      - eapply nb. now symmetry.
      - eapply hfb; now symmetry.
      - exact w'. }
    destruct hw as (r & hwr & heqr). exists r. split; [| exact heqr].
    eapply (wt_to_cowt_dual p [] r hwr []). constructor.
  Qed.

End CoSwaps.

(** ** Transfer of the LTS predicates along the normalisation *)

Section TransferCo.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.
  Context (cls : A -> act_class) `{!CoClassifier cls}.

  Notation "⟪ s ⟫ᶜᵒ" := (nlin (nform cls s)) (at level 30).

  (** *** Co-weak transitions *)

  Lemma cowt_tequiv (p q : P) s t : tequiv cls s t -> p ⟹ᶜᵒ[s] q -> p ⟹ᶜᵒ⋍[t] q.
  Proof.
    intro hte. revert p q.
    induction hte as [ s | s t u h1 IH1 h2 IH2 | s1 μ ν s2 heq hne ]; intros p q w.
    - exists q. split; [exact w | reflexivity].
    - destruct (IH1 p q w) as (r & w1 & heqr).
      destruct (IH2 p r w1) as (r' & w2 & heqr').
      exists r'. split; [exact w2 | etransitivity; eassumption].
    - eapply cowt_split in w as (r & w1 & w2).
      replace (μ :: ν :: s2) with ([μ ; ν] ++ s2) in w2 by reflexivity.
      eapply cowt_split in w2 as (r' & w3 & w4).
      assert (hsw : r ⟹ᶜᵒ⋍[[ν ; μ]] r').
      { destruct (cls μ) eqn:hμ.
        - eapply cowt_non_blocking_action_swap; [| | exact w3].
          + eapply cls_CNB_iff, hμ.
          + eapply cls_CNB_iff. now rewrite <- heq.
        - eapply cowt_input_swap; [| exact w3].
          eapply cls_CIN_iff. now rewrite <- heq.
        - now exfalso. }
      replace (s1 ++ ν :: μ :: s2) with (s1 ++ ([ν ; μ] ++ s2)) by reflexivity.
      eapply cowt_join_eq_r; [exact w1 |].
      eapply cowt_join_eq_l; eassumption.
  Qed.

  (** *** Co-convergence *)

  Lemma cocnv_tequiv (p : P) s t : tequiv cls s t -> p ⇓ᶜᵒ s -> p ⇓ᶜᵒ t.
  Proof.
    intro hte. revert p.
    induction hte as [ s | s t u h1 IH1 h2 IH2 | s1 μ ν s2 heq hne ]; intros p hcnv.
    - exact hcnv.
    - eapply IH2, IH1, hcnv.
    - eapply cocnv_jump.
      + eapply cocnv_prefix. exact hcnv.
      + intros r w.
        assert (hr : r ⇓ᶜᵒ μ :: ν :: s2)
          by (eapply (cocnv_cowt_prefix s1 (μ :: ν :: s2) p); eassumption).
        destruct (cls μ) eqn:hμ.
        * eapply cocnv_non_blocking_action_swap; [| | exact hr].
          -- eapply cls_CNB_iff, hμ.
          -- eapply cls_CNB_iff. now rewrite <- heq.
        * eapply cocnv_input_swap; [| | exact hr].
          -- eapply cls_CIN_iff, hμ.
          -- eapply cls_CIN_iff. now rewrite <- heq.
        * now exfalso.
  Qed.

  (** *** A co-trace and (the linearisation of) its normal form are
      interchangeable *)

  Corollary cowt_norm (p q : P) s : p ⟹ᶜᵒ[s] q -> p ⟹ᶜᵒ⋍[⟪ s ⟫ᶜᵒ] q.
  Proof. eapply cowt_tequiv, tequiv_nform. Qed.

  Corollary cowt_norm_rev (p q : P) s : p ⟹ᶜᵒ[⟪ s ⟫ᶜᵒ] q -> p ⟹ᶜᵒ⋍[s] q.
  Proof. eapply cowt_tequiv, tequiv_sym, tequiv_nform. Qed.

  Corollary cocnv_norm (p : P) s : p ⇓ᶜᵒ s -> p ⇓ᶜᵒ ⟪ s ⟫ᶜᵒ.
  Proof. eapply cocnv_tequiv, tequiv_nform. Qed.

  Corollary cocnv_norm_rev (p : P) s : p ⇓ᶜᵒ ⟪ s ⟫ᶜᵒ -> p ⇓ᶜᵒ s.
  Proof. eapply cocnv_tequiv, tequiv_sym, tequiv_nform. Qed.

  Corollary cowt_of_nform (p q : P) s t :
    nform cls s = nform cls t -> p ⟹ᶜᵒ[s] q -> p ⟹ᶜᵒ⋍[t] q.
  Proof. intro heq. eapply cowt_tequiv, tequiv_of_nform, heq. Qed.

  Corollary cocnv_of_nform (p : P) s t :
    nform cls s = nform cls t -> p ⇓ᶜᵒ s -> p ⇓ᶜᵒ t.
  Proof. intro heq. eapply cocnv_tequiv, tequiv_of_nform, heq. Qed.

End TransferCo.


(** ** A preorder on co-traces

    The observer's counterpart of [trace_leq] and [trace_pre] of
    [Normalisation.v], that is of the laws of Table 2 and Definition 5.1 of
    Boreale, De Nicola and Pugliese, read on the traces of the observer rather
    than on those of the process. *)

Inductive cotrace_leq `{ExtAction A} : trace A -> trace A -> Prop :=
| ctl_refl s : cotrace_leq s s
| ctl_trans s t u : cotrace_leq s t -> cotrace_leq t u -> cotrace_leq s u
| ctl_delay s1 η α s2 :
  co_non_blocking η -> cotrace_leq (s1 ++ η :: α :: s2) (s1 ++ α :: η :: s2)
| ctl_anticipate s1 α μ s2 :
  co_exist_co_nba μ -> cotrace_leq (s1 ++ α :: μ :: s2) (s1 ++ μ :: α :: s2)
| ctl_feedback s1 μ1 μ2 s2 :
  co_non_blocking μ1 -> co_feedback μ1 μ2 ->
  cotrace_leq (s1 ++ μ1 :: μ2 :: s2) (s1 ++ s2).

Notation "s ⊑ᶜᵒₜ t" := (cotrace_leq s t) (at level 70).

Inductive cotrace_pre `{ExtAction A} : trace A -> trace A -> Prop :=
| ctp_leq s t : cotrace_leq s t -> cotrace_pre s t
| ctp_trans s t u : cotrace_pre s t -> cotrace_pre t u -> cotrace_pre s u
| ctp_drop s1 η s2 : co_non_blocking η -> cotrace_pre (s1 ++ η :: s2) (s1 ++ s2).

Notation "s ≼ᶜᵒₜ t" := (cotrace_pre s t) (at level 70).

Section CoTracePreorder.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.

  (** [⊑ᶜᵒₜ] is sound for co-weak transitions. *)
  Lemma cowt_cotrace_leq (p q : P) s t : s ⊑ᶜᵒₜ t -> p ⟹ᶜᵒ[s] q -> p ⟹ᶜᵒ⋍[t] q.
  Proof.
    intro hle. revert p q.
    induction hle
      as [ s | s t u h1 IH1 h2 IH2 | s1 η α s2 nb | s1 α μ s2 i | s1 μ1 μ2 s2 nb hfb ];
      intros p q w.
    - exists q. split; [exact w | reflexivity].
    - destruct (IH1 p q w) as (r & w1 & heqr).
      destruct (IH2 p r w1) as (r' & w2 & heqr').
      exists r'. split; [exact w2 | etransitivity; eassumption].
    - eapply cowt_split in w as (r & w1 & w2).
      replace (η :: α :: s2) with ([η ; α] ++ s2) in w2 by reflexivity.
      eapply cowt_split in w2 as (r' & w3 & w4).
      assert (hsw : r ⟹ᶜᵒ⋍[[α ; η]] r').
      { eapply (push_cowt_non_blocking_action (η := η) (s := [α])); assumption. }
      replace (s1 ++ α :: η :: s2) with (s1 ++ ([α ; η] ++ s2)) by reflexivity.
      eapply cowt_join_eq_r; [exact w1 |]. eapply cowt_join_eq_l; eassumption.
    - eapply cowt_split in w as (r & w1 & w2).
      replace (α :: μ :: s2) with ([α ; μ] ++ s2) in w2 by reflexivity.
      eapply cowt_split in w2 as (r' & w3 & w4).
      assert (hsw : r ⟹ᶜᵒ⋍[[μ ; α]] r') by (eapply cowt_input_swap; eassumption).
      replace (s1 ++ μ :: α :: s2) with (s1 ++ ([μ ; α] ++ s2)) by reflexivity.
      eapply cowt_join_eq_r; [exact w1 |]. eapply cowt_join_eq_l; eassumption.
    - eapply cowt_split in w as (r & w1 & w2).
      replace (μ1 :: μ2 :: s2) with ([μ1 ; μ2] ++ s2) in w2 by reflexivity.
      eapply cowt_split in w2 as (r' & w3 & w4).
      assert (hsw : r ⟹ᶜᵒ⋍ r') by (eapply cowt_annhil_pair; eassumption).
      eapply cowt_join_eq_r; [exact w1 |].
      replace s2 with ([] ++ s2) by reflexivity.
      eapply cowt_join_eq_l; eassumption.
  Qed.

  (** Dropping a label only preserves the *existence* of a co-weak transition. *)
  Lemma cowt_cotrace_pre (p q : P) s t : s ≼ᶜᵒₜ t -> p ⟹ᶜᵒ[s] q -> ∃ q', p ⟹ᶜᵒ[t] q'.
  Proof.
    intro hle. revert p q.
    induction hle as [ s t hle | s t u h1 IH1 h2 IH2 | s1 η s2 nb ]; intros p q w.
    - eapply cowt_cotrace_leq in w as (q' & w' & _); [| exact hle]. now exists q'.
    - destruct (IH1 p q w) as (r & w1). eapply (IH2 p r w1).
    - eapply cowt_split in w as (r & w1 & w2).
      eapply push_cowt_non_blocking_action in w2 as (r' & w3 & _); [| exact nb].
      eapply cowt_split in w3 as (t & w4 & _).
      exists t. eapply cowt_concat; eassumption.
  Qed.

  (** Testing along a co-trace that performs a feedback is testing along a
      shorter co-trace: the co-convergence counterpart of [ctl_feedback] is
      [cocnv_annhil]. *)
  Lemma cocnv_feedback (p : P) s1 s2 s3 μ η :
    Forall non_blocking s1 -> Forall non_blocking s2 -> non_blocking η -> dual μ η ->
    p ⇓ᶜᵒ (s1 ++ [η] ++ s2 ++ [μ] ++ s3) -> p ⇓ᶜᵒ (s1 ++ s2 ++ s3).
  Proof. eapply cocnv_annhil. Qed.

End CoTracePreorder.

(** ** The normal form is the canonical representative of a class *)

Section CoMinimality.

  Context `{H : !ExtAction A}.
  Context (cls : A -> act_class) `{!CoClassifier cls}.

  Lemma cotrace_leq_of_tequiv (s t : trace A) : tequiv cls s t -> s ⊑ᶜᵒₜ t.
  Proof.
    induction 1 as [ s | s t u h1 IH1 h2 IH2 | s1 μ ν s2 heq hne ].
    - constructor.
    - eapply ctl_trans; eassumption.
    - destruct (cls μ) eqn:hμ.
      + eapply ctl_delay. eapply cls_CNB_iff, hμ.
      + eapply ctl_anticipate. eapply cls_CIN_iff. now rewrite <- heq.
      + now exfalso.
  Qed.

  Lemma cotrace_pre_of_tequiv (s t : trace A) : tequiv cls s t -> s ≼ᶜᵒₜ t.
  Proof. intro h. eapply ctp_leq, cotrace_leq_of_tequiv, h. Qed.

  Corollary cotrace_leq_nform (s : trace A) :
    s ⊑ᶜᵒₜ nlin (nform cls s) /\ nlin (nform cls s) ⊑ᶜᵒₜ s.
  Proof.
    split; eapply cotrace_leq_of_tequiv;
      [eapply tequiv_nform | eapply tequiv_sym, tequiv_nform].
  Qed.

  Lemma cls_pre_of_cotrace_leq (s t : trace A) : s ⊑ᶜᵒₜ t -> cls_pre cls s t.
  Proof.
    induction 1
      as [ s | s t u h1 IH1 h2 IH2 | s1 η α s2 nb | s1 α μ s2 i | s1 μ1 μ2 s2 nb hfb ].
    - constructor.
    - eapply cp_trans; eassumption.
    - eapply cp_delay. now eapply cls_CNB_iff.
    - eapply cp_anticipate. now eapply cls_CIN_iff.
    - eapply (cp_erase _ s1 μ1 [μ2] s2). now eapply cls_CNB_iff.
  Qed.

  Lemma cls_pre_of_cotrace_pre (s t : trace A) : s ≼ᶜᵒₜ t -> cls_pre cls s t.
  Proof.
    induction 1 as [ s t hle | s t u h1 IH1 h2 IH2 | s1 η s2 nb ].
    - now eapply cls_pre_of_cotrace_leq.
    - eapply cp_trans; eassumption.
    - eapply (cp_erase _ s1 η [] s2). now eapply cls_CNB_iff.
  Qed.

  Theorem nform_iff_cotrace_leq (s t : trace A) :
    nform cls s = nform cls t <-> (s ⊑ᶜᵒₜ t /\ t ⊑ᶜᵒₜ s).
  Proof.
    split.
    - intro heq. split; eapply cotrace_leq_of_tequiv;
        [now eapply tequiv_of_nform | eapply tequiv_sym; now eapply tequiv_of_nform].
    - intros (h1 & h2). eapply nform_iff_cls_pre.
      split; now eapply cls_pre_of_cotrace_leq.
  Qed.

  Theorem nform_iff_cotrace_pre (s t : trace A) :
    nform cls s = nform cls t <-> (s ≼ᶜᵒₜ t /\ t ≼ᶜᵒₜ s).
  Proof.
    split.
    - intro heq. split; eapply cotrace_pre_of_tequiv;
        [now eapply tequiv_of_nform | eapply tequiv_sym; now eapply tequiv_of_nform].
    - intros (h1 & h2). eapply nform_iff_cls_pre.
      split; now eapply cls_pre_of_cotrace_pre.
  Qed.

  (** *** Simplifying a co-trace *)

  Lemma cotrace_leq_app_l (u : trace A) s t : s ⊑ᶜᵒₜ t -> u ++ s ⊑ᶜᵒₜ u ++ t.
  Proof.
    induction 1
      as [ s | s t v h1 IH1 h2 IH2 | s1 η α s2 nb | s1 α μ s2 i | s1 μ1 μ2 s2 nb hfb ].
    - constructor.
    - eapply ctl_trans; eassumption.
    - rewrite 2 app_assoc. now eapply ctl_delay.
    - rewrite 2 app_assoc. now eapply ctl_anticipate.
    - rewrite 2 app_assoc. now eapply ctl_feedback.
  Qed.

  Lemma cotrace_pre_app_l (u : trace A) s t : s ≼ᶜᵒₜ t -> u ++ s ≼ᶜᵒₜ u ++ t.
  Proof.
    induction 1 as [ s t hle | s t v h1 IH1 h2 IH2 | s1 η s2 nb ].
    - eapply ctp_leq. now eapply cotrace_leq_app_l.
    - eapply ctp_trans; eassumption.
    - rewrite 2 app_assoc. now eapply ctp_drop.
  Qed.

  Lemma cotrace_pre_drop_nb (s : trace A) :
    s ≼ᶜᵒₜ filter (fun μ => cls μ ≠ CNB) s.
  Proof.
    induction s as [| μ s IH].
    - constructor. constructor.
    - destruct (decide (cls μ = CNB)) as [h | h].
      + rewrite (filter_cons_False (fun ν => cls ν ≠ CNB) μ s)
          by (intro hne; exact (hne h)).
        eapply ctp_trans; [| exact IH].
        eapply (ctp_drop [] μ s). now eapply cls_CNB_iff.
      + rewrite (filter_cons_True (fun ν => cls ν ≠ CNB) μ s h).
        exact (cotrace_pre_app_l [μ] s _ IH).
  Qed.

  Lemma cotrace_pre_move_cin (l1 : trace A) (μ : A) (l2 : trace A) :
    Forall (fun ν => cls ν = CIN) l1 -> μ :: (l1 ++ l2) ≼ᶜᵒₜ l1 ++ μ :: l2.
  Proof.
    induction l1 as [| ν l1 IH]; intro hl1; simpl.
    - constructor. constructor.
    - eapply Forall_cons_1 in hl1 as (hν & hl1).
      eapply ctp_trans.
      + eapply ctp_leq. eapply (ctl_anticipate [] μ ν (l1 ++ l2)).
        now eapply cls_CIN_iff.
      + exact (cotrace_pre_app_l [ν] _ _ (IH hl1)).
  Qed.

  Lemma cotrace_pre_sort (u : trace A) :
    Forall (fun μ => cls μ ≠ CNB) u -> u ≼ᶜᵒₜ csimpl cls u.
  Proof.
    induction u as [| μ u IH]; intro hu.
    - constructor. constructor.
    - eapply Forall_cons_1 in hu as (hμ & hu). unfold csimpl.
      destruct (decide (cls μ = CIN)) as [h | h].
      + rewrite (filter_cons_True (fun ν => cls ν = CIN) μ u h).
        rewrite (filter_cons_False (fun ν => cls ν = COP) μ u)
          by (rewrite h; discriminate).
        exact (cotrace_pre_app_l [μ] u (csimpl cls u) (IH hu)).
      + assert (hcop : cls μ = COP).
        { destruct (cls μ) eqn:e.
          - exfalso. now eapply hμ.
          - exfalso. now eapply h.
          - reflexivity. }
        rewrite (filter_cons_False (fun ν => cls ν = CIN) μ u)
          by (rewrite hcop; discriminate).
        rewrite (filter_cons_True (fun ν => cls ν = COP) μ u hcop).
        eapply ctp_trans with (t := μ :: csimpl cls u).
        * exact (cotrace_pre_app_l [μ] u (csimpl cls u) (IH hu)).
        * unfold csimpl. eapply cotrace_pre_move_cin, Forall_filter_self.
  Qed.

  Theorem cotrace_pre_csimpl (s : trace A) : s ≼ᶜᵒₜ csimpl cls s.
  Proof.
    eapply ctp_trans; [eapply cotrace_pre_drop_nb |].
    rewrite <- (csimpl_filter_no_nb cls s).
    eapply cotrace_pre_sort, Forall_filter_self.
  Qed.

  (** Nothing strictly simpler lies below [csimpl cls s]. *)
  Theorem cotrace_simplification (s : trace A) :
    s ≼ᶜᵒₜ csimpl cls s
    /\ forall t, csimpl cls s ≼ᶜᵒₜ t
                -> tmeasure cls t = tmeasure cls (csimpl cls s).
  Proof.
    split; [eapply cotrace_pre_csimpl |].
    intros t hpre. eapply cls_min_csimpl. now eapply cls_pre_of_cotrace_pre.
  Qed.

  (** *** Simplifying a co-trace by feedback only

      Without the deletion law the least co-traces are the sorted ones: they
      are permutations of the original co-trace, and they carry no feedback. *)

  Lemma cotrace_leq_delay_run (s1 u v : trace A) (η : A) :
    co_non_blocking η -> s1 ++ η :: (u ++ v) ⊑ᶜᵒₜ s1 ++ u ++ η :: v.
  Proof.
    intro nb. revert s1.
    induction u as [| x u IH]; intro s1; simpl.
    - constructor.
    - eapply ctl_trans; [eapply (ctl_delay s1 η x (u ++ v)), nb |].
      specialize (IH (s1 ++ [x])).
      rewrite <- !app_assoc in IH. simpl in IH. exact IH.
  Qed.

  Lemma cotrace_leq_feedback_mid (s1 s2 s3 : trace A) (μ1 μ2 : A) :
    co_non_blocking μ1 -> co_feedback μ1 μ2 ->
    s1 ++ μ1 :: (s2 ++ μ2 :: s3) ⊑ᶜᵒₜ s1 ++ s2 ++ s3.
  Proof.
    intros nb hfb.
    eapply ctl_trans; [eapply (cotrace_leq_delay_run s1 s2 (μ2 :: s3) μ1), nb |].
    rewrite 2 app_assoc. now eapply ctl_feedback.
  Qed.

  Lemma cotrace_leq_move_cin (l1 : trace A) (μ : A) (l2 : trace A) :
    Forall (fun ν => cls ν = CIN) l1 -> μ :: (l1 ++ l2) ⊑ᶜᵒₜ l1 ++ μ :: l2.
  Proof.
    induction l1 as [| ν l1 IH]; intro hl1; simpl.
    - constructor.
    - eapply Forall_cons_1 in hl1 as (hν & hl1).
      eapply ctl_trans.
      + eapply (ctl_anticipate [] μ ν (l1 ++ l2)). now eapply cls_CIN_iff.
      + exact (cotrace_leq_app_l [ν] _ _ (IH hl1)).
  Qed.

  Theorem cotrace_leq_tsort (s : trace A) : s ⊑ᶜᵒₜ tsort cls s.
  Proof.
    induction s as [| x s IH]; [constructor |]. unfold tsort in *.
    destruct (cls x) eqn:e.
    - rewrite (filter_cons_False (fun ν => cls ν = CIN) x s) by (rewrite e; discriminate).
      rewrite (filter_cons_False (fun ν => cls ν = COP) x s) by (rewrite e; discriminate).
      rewrite (filter_cons_True (fun ν => cls ν = CNB) x s e).
      eapply ctl_trans with (t := x :: (filter (fun ν => cls ν = CIN) s
                                        ++ filter (fun ν => cls ν = COP) s
                                        ++ filter (fun ν => cls ν = CNB) s)).
      + exact (cotrace_leq_app_l [x] s _ IH).
      + rewrite 2 app_assoc.
        exact (cotrace_leq_delay_run []
                 (filter (fun ν => cls ν = CIN) s ++ filter (fun ν => cls ν = COP) s)
                 (filter (fun ν => cls ν = CNB) s) x (proj1 (cls_CNB_iff x) e)).
    - rewrite (filter_cons_True (fun ν => cls ν = CIN) x s e).
      rewrite (filter_cons_False (fun ν => cls ν = COP) x s) by (rewrite e; discriminate).
      rewrite (filter_cons_False (fun ν => cls ν = CNB) x s) by (rewrite e; discriminate).
      rewrite <- app_comm_cons.
      exact (cotrace_leq_app_l [x] s _ IH).
    - rewrite (filter_cons_False (fun ν => cls ν = CIN) x s) by (rewrite e; discriminate).
      rewrite (filter_cons_True (fun ν => cls ν = COP) x s e).
      rewrite (filter_cons_False (fun ν => cls ν = CNB) x s) by (rewrite e; discriminate).
      rewrite <- app_comm_cons.
      eapply ctl_trans with (t := x :: (filter (fun ν => cls ν = CIN) s
                                        ++ filter (fun ν => cls ν = COP) s
                                        ++ filter (fun ν => cls ν = CNB) s)).
      + exact (cotrace_leq_app_l [x] s _ IH).
      + eapply cotrace_leq_move_cin, Forall_filter_self.
  Qed.

  Lemma cls_pre_of_cotrace_leq' (s t : trace A) : s ⊑ᶜᵒₜ t -> cls_pre cls s t.
  Proof. eapply cls_pre_of_cotrace_leq. Qed.

  Lemma cotrace_leq_length (u t : trace A) :
    u ⊑ᶜᵒₜ t -> tmeasure cls u = length u -> length t = length u.
  Proof.
    induction 1
      as [ s | s t v h1 IH1 h2 IH2 | s1 η α s2 nb | s1 α μ s2 i | s1 μ1 μ2 s2 nb hfb ];
      intro hm.
    - reflexivity.
    - assert (hlt : length t = length s) by (eapply IH1, hm).
      assert (hmt : tmeasure cls t = length t).
      { pose proof (cls_pre_measure cls s t (cls_pre_of_cotrace_leq s t h1)).
        pose proof (tmeasure_ge_length cls t). lia. }
      rewrite (IH2 hmt). exact hlt.
    - symmetry. eapply length_middle_swap.
    - symmetry. eapply length_middle_swap.
    - exfalso.
      assert (hcnb : cls μ1 = CNB) by (eapply cls_CNB_iff, nb).
      assert (hcin : cls μ2 = CIN)
        by (eapply cls_CIN_iff, (co_feedback_CIN μ1 μ2 nb hfb)).
      assert (hge : 1 <= inv_nb cls (s1 ++ μ1 :: μ2 :: s2)).
      { unfold inv_nb. rewrite inv_cnt_middle. unfold bit.
        destruct (decide (cls μ1 = CNB)) as [_ | hno]; [| exfalso; exact (hno hcnb)].
        destruct (decide (cls μ2 ≠ CNB)) as [_ | hno]; [lia |].
        exfalso. eapply hno. rewrite hcin. discriminate. }
      unfold tmeasure in hm. lia.
  Qed.

  Definition cotrace_min (u : trace A) : Prop :=
    forall t, u ⊑ᶜᵒₜ t -> tmeasure cls t = tmeasure cls u.

  Lemma cotrace_min_of_measure (u : trace A) :
    tmeasure cls u = length u -> cotrace_min u.
  Proof.
    intros hm t hle.
    pose proof (cotrace_leq_length u t hle hm) as hl.
    pose proof (cls_pre_measure cls u t (cls_pre_of_cotrace_leq u t hle)).
    pose proof (tmeasure_ge_length cls t). lia.
  Qed.

  Theorem cotrace_simplification_leq (s : trace A) :
    s ⊑ᶜᵒₜ tsort cls s /\ tsort cls s ≡ₚ s /\ cotrace_min (tsort cls s).
  Proof.
    repeat split.
    - eapply cotrace_leq_tsort.
    - eapply tsort_perm.
    - eapply cotrace_min_of_measure, tmeasure_tsort.
  Qed.

  Corollary tsort_co_feedback_free (s s1 s2 s3 : trace A) (μ1 μ2 : A) :
    tsort cls s = s1 ++ μ1 :: (s2 ++ μ2 :: s3) ->
    co_non_blocking μ1 -> co_feedback μ1 μ2 -> False.
  Proof.
    intros heq nb hfb.
    assert (hle : tsort cls s ⊑ᶜᵒₜ s1 ++ s2 ++ s3)
      by (rewrite heq; eapply cotrace_leq_feedback_mid; assumption).
    pose proof (cotrace_leq_length _ _ hle (tmeasure_tsort cls s)) as hl.
    rewrite heq in hl.
    rewrite !length_app' in hl. simpl in hl.
    rewrite !length_app' in hl. simpl in hl. lia.
  Qed.

End CoMinimality.

Section CoSimplification.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.
  Context (cls : A -> act_class) `{!CoClassifier cls}.

  (** Testing along [s] is subsumed by testing along the simplified co-trace. *)
  Corollary cowt_csimpl (p q : P) s : p ⟹ᶜᵒ[s] q -> ∃ q', p ⟹ᶜᵒ[csimpl cls s] q'.
  Proof.
    intro w.
    exact (cowt_cotrace_pre p q s (csimpl cls s) (cotrace_pre_csimpl cls s) w).
  Qed.

  (** Contrary to [cowt_csimpl], the state that is reached is preserved: the
      sorted co-trace loses nothing. *)
  Corollary cowt_tsort (p q : P) s : p ⟹ᶜᵒ[s] q -> p ⟹ᶜᵒ⋍[tsort cls s] q.
  Proof.
    intro w.
    exact (cowt_cotrace_leq p q s (tsort cls s) (cotrace_leq_tsort cls s) w).
  Qed.

End CoSimplification.

(** ** Consuming the feedbacks of a co-trace

    As on traces, the feedback rule alone is an orthogonal rewriting system
    ([co_fb_rel_disjoint]) and it terminates.  Its redexes quantify over all
    the actions dual to a label, so deciding whether one occurs is not
    automatic without a determinacy assumption: we take that decision as a
    parameter rather than appealing to [unique_nb]. *)

Section CoFeedbackNormal.

  Context `{H : !ExtAction A}.
  Context (cls : A -> act_class) `{!CoClassifier cls}.
  Context `{!forall μ1 μ2 : A, Decision (co_fb_rel μ1 μ2)}.

  Lemma co_fb_normal_exists_aux (n : nat) (s : trace A) :
    length s <= n ->
    ∃ t, s ⊑ᶜᵒₜ t /\ no_redex co_fb_rel t /\ length t <= length s.
  Proof.
    revert s. induction n as [| n IH]; intros s hn.
    - exists s. repeat split.
      + constructor.
      + eapply no_redex_short. lia.
      + lia.
    - destruct (has_redex co_fb_rel s) eqn:e.
      + eapply has_redex_true in e as (s1 & x & y & s2 & -> & (nb & hfb)).
        destruct (IH (s1 ++ s2)) as (t & hle & hnf & hlen).
        { rewrite !length_app' in *. simpl in hn. lia. }
        exists t. repeat split.
        * eapply ctl_trans; [now eapply ctl_feedback | exact hle].
        * exact hnf.
        * rewrite !length_app' in *. simpl. lia.
      + exists s. repeat split.
        * constructor.
        * now eapply has_redex_false.
        * lia.
  Qed.

  Corollary co_fb_normal_exists (s : trace A) :
    ∃ t, s ⊑ᶜᵒₜ t /\ no_redex co_fb_rel t /\ length t <= length s.
  Proof. eapply (co_fb_normal_exists_aux (length s) s). lia. Qed.

  Theorem cotrace_simplification_full (s : trace A) :
    ∃ t, s ⊑ᶜᵒₜ t
       /\ cotrace_min cls t
       /\ length t <= length s
       /\ (forall s1 s2 s3 μ1 μ2,
              t = s1 ++ μ1 :: (s2 ++ μ2 :: s3) ->
              co_non_blocking μ1 -> co_feedback μ1 μ2 -> False).
  Proof.
    destruct (co_fb_normal_exists s) as (u & hle & _ & hlen).
    exists (tsort cls u). repeat split.
    - eapply ctl_trans; [exact hle | exact (cotrace_leq_tsort cls u)].
    - exact (cotrace_min_of_measure cls (tsort cls u) (tmeasure_tsort cls u)).
    - rewrite length_tsort. exact hlen.
    - intros s1 s2 s3 μ1 μ2 heq nb hfb.
      exact (tsort_co_feedback_free cls u s1 s2 s3 μ1 μ2 heq nb hfb).
  Qed.

  Corollary cotrace_simplification_strict (s1 s2 s3 : trace A) (μ1 μ2 : A) :
    co_non_blocking μ1 -> co_feedback μ1 μ2 ->
    ∃ t, (s1 ++ μ1 :: (s2 ++ μ2 :: s3)) ⊑ᶜᵒₜ t
       /\ cotrace_min cls t
       /\ length t < length (s1 ++ μ1 :: (s2 ++ μ2 :: s3)).
  Proof.
    intros nb hfb.
    destruct (cotrace_simplification_full (s1 ++ s2 ++ s3)) as (t & hle & hmin & hlen & _).
    exists t. repeat split.
    - eapply ctl_trans; [eapply cotrace_leq_feedback_mid; eassumption | exact hle].
    - exact hmin.
    - rewrite !length_app' in *. simpl. rewrite !length_app'. simpl. lia.
  Qed.

End CoFeedbackNormal.

(** ** One canonical classification of the co-actions

    Everything above is parametric in the classification of the labels, and no
    determinacy of [dual] has been used.  When the co-action *is* unique --
    which is what the axiom [unique_nb] of [ExtAction] states -- the classes of
    a label [μ] of a co-trace are simply the classes of its co-action [co μ],
    and [cls_tr ∘ co] is a classifier.  This is the only statement of this file
    that uses [unique_nb]. *)

Definition cls_co `{ExtAction A} (μ : A) : act_class := cls_tr (co μ).

Lemma dual_unique `{ExtAction A} (μ μ' : A) : dual μ' μ -> μ' = co μ.
Proof. intro duo. eapply unique_nb. now symmetry. Qed.

#[global] Instance CoClassifier_cls_co `{ExtAction A} : CoClassifier (cls_co (A := A)).
Proof.
  split; intro μ; unfold cls_co.
  - rewrite cls_tr_CNB. split.
    + intros nb μ' duo. now rewrite (dual_unique μ μ' duo).
    + intro h. eapply h, dual_co.
  - rewrite cls_tr_CIN. split.
    + intros (η & nb & duo). exists η. split; [exact nb |].
      intros ν dν. now rewrite (dual_unique μ ν dν).
    + intros (η & nb & h). exists η. split; [exact nb |]. eapply h, dual_co.
Qed.

(** ** A normal form that consumes the feedbacks, on co-traces

    The mirror of [fbnf].  Both predicates involved in a co-feedback quantify
    over all the actions dual to a label, so their decidability is taken as a
    parameter rather than obtained from [unique_nb]. *)

Section CoFeedbackNormalForm.

  Context `{H : !ExtAction A}.
  Context `{!forall μ : A, Decision (co_non_blocking μ)}.
  Context `{!forall μ1 μ2 : A, Decision (co_feedback μ1 μ2)}.

  Fixpoint co_drop_dual (η : A) (l : trace A) : option (trace A) :=
    match l with
    | [] => None
    | μ :: l' =>
        if decide (co_feedback η μ) then Some l'
        else match co_drop_dual η l' with
             | Some t => Some (μ :: t)
             | None => None
             end
    end.

  Lemma co_drop_dual_spec η l : forall t,
    co_drop_dual η l = Some t ->
    exists l1 μ l2, l = l1 ++ μ :: l2 /\ t = l1 ++ l2 /\ co_feedback η μ.
  Proof.
    induction l as [| ν l IH]; intros t heq; [discriminate |].
    simpl in heq. destruct (decide (co_feedback η ν)) as [d | d].
    - injection heq. intro hl. subst t.
      exists [], ν, l. repeat split. exact d.
    - destruct (co_drop_dual η l) as [t0 |] eqn:e; [| discriminate].
      injection heq. intro hl. subst t.
      destruct (IH t0 eq_refl) as (l1 & μ & l2 & -> & -> & dμ).
      exists (ν :: l1), μ, l2. repeat split. exact dμ.
  Qed.

  Lemma co_drop_dual_none η l :
    co_drop_dual η l = None -> Forall (fun μ => ¬ co_feedback η μ) l.
  Proof.
    induction l as [| ν l IH]; intro heq; [constructor |].
    simpl in heq. destruct (decide (co_feedback η ν)) as [d | d]; [discriminate |].
    destruct (co_drop_dual η l) as [t0 |] eqn:e; [discriminate |].
    constructor; [exact d | exact (IH eq_refl)].
  Qed.

  Fixpoint co_drop_fb (s : trace A) : option (trace A) :=
    match s with
    | [] => None
    | η :: s' =>
        match (if decide (co_non_blocking η) then co_drop_dual η s' else None) with
        | Some t => Some t
        | None =>
            match co_drop_fb s' with
            | Some t => Some (η :: t)
            | None => None
            end
        end
    end.

  Lemma co_drop_fb_leq s : forall t,
    co_drop_fb s = Some t -> s ⊑ᶜᵒₜ t /\ S (S (length t)) = length s.
  Proof.
    induction s as [| η s IH]; intros t heq; [discriminate |].
    simpl in heq. destruct (decide (co_non_blocking η)) as [nb | nb].
    - destruct (co_drop_dual η s) as [t0 |] eqn:e.
      + injection heq. intro hl. subst t.
        eapply co_drop_dual_spec in e as (l1 & μ & l2 & -> & -> & d).
        split.
        * exact (cotrace_leq_feedback_mid [] l1 l2 η μ nb d).
        * simpl. rewrite !length_app'. simpl. lia.
      + destruct (co_drop_fb s) as [t1 |] eqn:e1; [| discriminate].
        injection heq. intro hl. subst t.
        destruct (IH t1 eq_refl) as (hle & hln).
        split; [exact (cotrace_leq_app_l [η] s t1 hle) | simpl; lia].
    - destruct (co_drop_fb s) as [t1 |] eqn:e1; [| discriminate].
      injection heq. intro hl. subst t.
      destruct (IH t1 eq_refl) as (hle & hln).
      split; [exact (cotrace_leq_app_l [η] s t1 hle) | simpl; lia].
  Qed.

  Lemma co_drop_fb_none s :
    co_drop_fb s = None ->
    forall s1 μ1 s2 μ2 s3,
      s = s1 ++ μ1 :: (s2 ++ μ2 :: s3) ->
      co_non_blocking μ1 -> co_feedback μ1 μ2 -> False.
  Proof.
    induction s as [| x s IH]; intros heq s1 μ1 s2 μ2 s3 hs nb d.
    - destruct s1; discriminate.
    - simpl in heq.
      destruct (decide (co_non_blocking x)) as [nbx | nbx]; simpl in heq.
      + destruct (co_drop_dual x s) as [t0 |] eqn:e; [discriminate |].
        destruct (co_drop_fb s) as [t1 |] eqn:e1; [discriminate |].
        destruct s1 as [| c s1]; simpl in hs; injection hs.
        * intros hs' hx. subst x. subst s.
          eapply co_drop_dual_none in e.
          eapply Forall_app_inv in e as (_ & e).
          eapply Forall_cons_1 in e as (e & _). exact (e d).
        * intros hs' _. exact (IH eq_refl s1 μ1 s2 μ2 s3 hs' nb d).
      + destruct (co_drop_fb s) as [t1 |] eqn:e1; [discriminate |].
        destruct s1 as [| c s1]; simpl in hs; injection hs.
        * intros _ hx. subst x. contradiction.
        * intros hs' _. exact (IH eq_refl s1 μ1 s2 μ2 s3 hs' nb d).
  Qed.

  Fixpoint co_fb_iter (n : nat) (s : trace A) : trace A :=
    match n with
    | 0 => s
    | S n => match co_drop_fb s with Some t => co_fb_iter n t | None => s end
    end.

  Definition co_fbnf (s : trace A) : trace A := co_fb_iter (length s) s.

  Lemma co_fb_iter_leq n :
    forall s, s ⊑ᶜᵒₜ co_fb_iter n s /\ length (co_fb_iter n s) <= length s.
  Proof.
    induction n as [| n IH]; intro s; simpl.
    - split; [constructor | lia].
    - destruct (co_drop_fb s) as [t |] eqn:e.
      + eapply co_drop_fb_leq in e as (hle & hln).
        destruct (IH t) as (hle' & hl').
        split; [eapply ctl_trans; eassumption | lia].
      + split; [constructor | lia].
  Qed.

  Lemma co_fb_iter_none n :
    forall s, length s <= n -> co_drop_fb (co_fb_iter n s) = None.
  Proof.
    induction n as [| n IH]; intros s hn; simpl.
    - destruct s as [| x s]; [reflexivity | simpl in hn; lia].
    - destruct (co_drop_fb s) as [t |] eqn:e.
      + eapply IH. eapply co_drop_fb_leq in e as (_ & hln). lia.
      + exact e.
  Qed.

  Theorem cotrace_leq_co_fbnf (s : trace A) : s ⊑ᶜᵒₜ co_fbnf s.
  Proof. exact (proj1 (co_fb_iter_leq (length s) s)). Qed.

  Theorem co_fbnf_length (s : trace A) : length (co_fbnf s) <= length s.
  Proof. exact (proj2 (co_fb_iter_leq (length s) s)). Qed.

  Theorem co_fbnf_feedback_free (s s1 s2 s3 : trace A) (μ1 μ2 : A) :
    co_fbnf s = s1 ++ μ1 :: (s2 ++ μ2 :: s3) ->
    co_non_blocking μ1 -> co_feedback μ1 μ2 -> False.
  Proof.
    eapply co_drop_fb_none. unfold co_fbnf. eapply co_fb_iter_none. lia.
  Qed.

End CoFeedbackNormalForm.

Section CoFeedbackNormalFormLts.

  Context `{H : !ExtAction A}.
  Context `{!forall μ : A, Decision (co_non_blocking μ)}.
  Context `{!forall μ1 μ2 : A, Decision (co_feedback μ1 μ2)}.
  Context (cls : A -> act_class) `{!CoClassifier cls}.

  (** The normal form: the feedbacks are consumed, then the consecutive labels
      of a same class are collected into multisets. *)
  Definition co_fnf (s : trace A) : ntrace A := nform cls (co_fbnf s).

  Lemma cotrace_leq_co_fnf (s : trace A) : s ⊑ᶜᵒₜ nlin (co_fnf s).
  Proof.
    eapply ctl_trans; [eapply cotrace_leq_co_fbnf |].
    exact (cotrace_leq_of_tequiv cls (co_fbnf s) (nlin (nform cls (co_fbnf s)))
             (tequiv_nform cls (co_fbnf s))).
  Qed.

  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.

  Corollary cowt_co_fbnf (p q : P) s : p ⟹ᶜᵒ[s] q -> p ⟹ᶜᵒ⋍[co_fbnf s] q.
  Proof.
    intro w.
    exact (cowt_cotrace_leq p q s (co_fbnf s) (cotrace_leq_co_fbnf s) w).
  Qed.

  Corollary cowt_co_fnf (p q : P) s : p ⟹ᶜᵒ[s] q -> p ⟹ᶜᵒ⋍[nlin (co_fnf s)] q.
  Proof.
    intro w.
    exact (cowt_cotrace_leq p q s (nlin (co_fnf s)) (cotrace_leq_co_fnf s) w).
  Qed.

End CoFeedbackNormalFormLts.

(** ** The co-preorder and co-convergence

    As on traces, [⊑ᶜᵒₜ] is sound for co-convergence contravariantly. *)

Section CoTracePreorderConvergence.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.

  Lemma cocnv_delay (p : P) (η α : A) s :
    co_non_blocking η -> p ⇓ᶜᵒ α :: η :: s -> p ⇓ᶜᵒ η :: α :: s.
  Proof.
    intros nb hcnv.
    assert (hterm : p ⤓) by (eapply cocnv_terminate; exact hcnv).
    eapply cocnv_act; [exact hterm |].
    intros q w1.
    eapply cocnv_act.
    - eapply (terminate_preserved_by_cowt_non_blocking_action p q η nb);
        [exact hterm | exact w1].
    - intros t w2.
      assert (w3 : p ⟹ᶜᵒ[[η ; α]] t) by (eapply cowt_push_left; eassumption).
      eapply push_cowt_non_blocking_action in w3 as (t' & w4 & heq); [| exact nb].
      eapply cocnv_preserved_by_eq; [exact heq | reflexivity |].
      eapply (cocnv_cowt_prefix [α ; η] s p); [exact hcnv | exact w4].
  Qed.

  Lemma cocnv_anticipate (p : P) (μ α : A) s :
    co_exist_co_nba μ -> p ⇓ᶜᵒ μ :: α :: s -> p ⇓ᶜᵒ α :: μ :: s.
  Proof.
    intros (η1 & nb1 & h1) hcnv.
    assert (hterm : p ⤓) by (eapply cocnv_terminate; exact hcnv).
    destruct (exists_dual μ) as (ν1 & duo1).
    assert (dν1 : dual ν1 μ) by (now symmetry).
    destruct (boomerang p η1 ν1) as (t0 & Hb).
    destruct (Hb nb1 (h1 ν1 dν1)) as (l1 & l2).
    assert (w0 : p ⟹ᶜᵒ{μ} t0) by (eapply lts_to_cowt; [exact dν1 | exact l1]).
    assert (h0 : t0 ⇓ᶜᵒ α :: s)
      by (exact (cocnv_preserved_by_cowt_act (α :: s) p μ hcnv t0 w0)).
    eapply cocnv_act; [exact hterm |].
    intros q w1.
    eapply cocnv_act.
    - destruct (delay_cowt_non_blocking_action nb1 (mk_lts_eq l2) w1)
        as (t' & w2 & (t2 & hlt2 & heqt2)).
      assert (ht' : t' ⤓).
      { eapply (cocnv_terminate t' s).
        exact (cocnv_preserved_by_cowt_act s t0 α h0 t' w2). }
      eapply (terminate_preserved_by_eq2 heqt2).
      exact (terminate_preserved_by_lts_non_blocking_action nb1 hlt2 ht').
    - intros r w2.
      destruct (cowt_input_swap p r α μ (ex_intro _ η1 (conj nb1 h1))
                  (cowt_push_left w1 w2)) as (t & w' & heq').
      eapply cocnv_preserved_by_eq; [exact heq' | reflexivity |].
      eapply (cocnv_cowt_prefix [μ ; α] s p); [exact hcnv | exact w'].
  Qed.

  Lemma cocnv_annhil_head (p : P) (μ1 μ2 : A) s :
    co_non_blocking μ1 -> co_feedback μ1 μ2 -> p ⇓ᶜᵒ s -> p ⇓ᶜᵒ μ1 :: μ2 :: s.
  Proof.
    intros nb hfb hcnv.
    assert (hterm : p ⤓) by (eapply cocnv_terminate; exact hcnv).
    eapply cocnv_act; [exact hterm |].
    intros q w1.
    eapply cocnv_act.
    - eapply (terminate_preserved_by_cowt_non_blocking_action p q μ1 nb);
        [exact hterm | exact w1].
    - intros t w2.
      assert (w3 : p ⟹ᶜᵒ[[μ1 ; μ2]] t) by (eapply cowt_push_left; eassumption).
      destruct (cowt_annhil_pair p t μ1 μ2 nb hfb w3) as (t' & w4 & heq).
      eapply cocnv_preserved_by_eq; [exact heq | reflexivity |].
      eapply cocnv_preserved_by_cowt_nil; [exact hcnv | exact w4].
  Qed.

  Lemma cocnv_drop_head (p : P) (η : A) s :
    co_non_blocking η -> p ⇓ᶜᵒ s -> p ⇓ᶜᵒ η :: s.
  Proof.
    intros nb hcnv.
    eapply cocnv_act; [eapply cocnv_terminate; exact hcnv |].
    intros q w. eapply cocnv_preserved_by_cowt_non_blocking_action; eassumption.
  Qed.

  Lemma cocnv_ctx (p : P) s1 u v :
    (forall r : P, r ⇓ᶜᵒ v -> r ⇓ᶜᵒ u) -> p ⇓ᶜᵒ s1 ++ v -> p ⇓ᶜᵒ s1 ++ u.
  Proof.
    intros h hcnv. eapply cocnv_jump.
    - eapply cocnv_prefix. exact hcnv.
    - intros r w. eapply h. eapply cocnv_cowt_prefix; eassumption.
  Qed.

  Theorem cocnv_cotrace_leq (p : P) s t : s ⊑ᶜᵒₜ t -> p ⇓ᶜᵒ t -> p ⇓ᶜᵒ s.
  Proof.
    intro hle. revert p.
    induction hle
      as [ s | s t u h1 IH1 h2 IH2 | s1 η α s2 nb | s1 α μ s2 i | s1 μ1 μ2 s2 nb hfb ];
      intros p hcnv.
    - exact hcnv.
    - eapply IH1, IH2, hcnv.
    - eapply cocnv_ctx; [| exact hcnv]. intros r. now eapply cocnv_delay.
    - eapply cocnv_ctx; [| exact hcnv]. intros r. now eapply cocnv_anticipate.
    - eapply (cocnv_ctx p s1 (μ1 :: μ2 :: s2) s2); [| exact hcnv].
      intros r. now eapply cocnv_annhil_head.
  Qed.

  Theorem cocnv_cotrace_pre (p : P) s t : s ≼ᶜᵒₜ t -> p ⇓ᶜᵒ t -> p ⇓ᶜᵒ s.
  Proof.
    intro hle. revert p.
    induction hle as [ s t hle | s t u h1 IH1 h2 IH2 | s1 η s2 nb ]; intros p hcnv.
    - eapply cocnv_cotrace_leq; eassumption.
    - eapply IH1, IH2, hcnv.
    - eapply (cocnv_ctx p s1 (η :: s2) s2); [| exact hcnv].
      intros r. now eapply cocnv_drop_head.
  Qed.

End CoTracePreorderConvergence.
