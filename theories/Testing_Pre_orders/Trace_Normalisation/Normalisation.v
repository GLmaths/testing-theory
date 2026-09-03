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
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_FW
    WeakTransitions Convergence Termination NormalForm.

(** * Normalisation of traces

    We instantiate the combinatorics of [NormalForm.v] on plain traces, and we
    show that the alternative (acceptance-set based) preorder [≼ₐₛ] only has to
    be checked on traces in normal form.

    The classification of actions used here generalises the input/output
    dichotomy of the original development:

    - [CNB] the non-blocking actions -- the outputs;
    - [CIN] the blocking actions admitting a non-blocking co-action
            ([exist_co_nba]) -- the inputs;
    - [COP] the blocking actions whose co-actions are blocking as well.  These
            have no counterpart in the original development, where every action
            was either an input or an output; they commute with nothing, hence
            they separate the runs of a normalised trace. *)

(** ** Classifying the actions of a trace *)

Definition cls_tr `{ExtAction A} (μ : A) : act_class :=
  if decide (non_blocking μ) then CNB
  else if decide (exist_co_nba μ) then CIN
  else COP.

Lemma cls_tr_CNB `{ExtAction A} (μ : A) : cls_tr μ = CNB <-> non_blocking μ.
Proof.
  unfold cls_tr. split.
  - destruct (decide (non_blocking μ)) as [nb | b]; [now intros _ |].
    destruct (decide (exist_co_nba μ)); discriminate.
  - intro nb. now rewrite decide_True.
Qed.

Lemma cls_tr_CIN `{ExtAction A} (μ : A) : cls_tr μ = CIN <-> exist_co_nba μ.
Proof.
  unfold cls_tr. split.
  - destruct (decide (non_blocking μ)) as [nb | b]; [discriminate |].
    destruct (decide (exist_co_nba μ)) as [i | ni]; [now intros _ | discriminate].
  - intros i. destruct i as (η & nb & duo).
    rewrite decide_False by (eapply dual_blocks; eassumption).
    rewrite decide_True; [reflexivity | now exists η].
Qed.

Lemma cls_tr_COP `{ExtAction A} (μ : A) :
  cls_tr μ = COP <-> (blocking μ /\ ¬ exist_co_nba μ).
Proof.
  unfold cls_tr. split.
  - destruct (decide (non_blocking μ)) as [nb | b]; [discriminate |].
    destruct (decide (exist_co_nba μ)) as [i | ni]; [discriminate | now intros _].
  - intros (b & ni). now rewrite decide_False, decide_False.
Qed.

(** Actions of the same non-opaque class are either both non-blocking, or both
    admit a non-blocking co-action. *)
Lemma cls_tr_same_class `{ExtAction A} (μ ν : A) :
  cls_tr μ = cls_tr ν -> cls_tr μ ≠ COP ->
  (non_blocking μ /\ non_blocking ν) \/ (exist_co_nba μ /\ exist_co_nba ν).
Proof.
  intros heq hne. destruct (cls_tr μ) eqn:hμ.
  - left. split; [now eapply cls_tr_CNB | eapply cls_tr_CNB; now rewrite <- heq].
  - right. split; [now eapply cls_tr_CIN | eapply cls_tr_CIN; now rewrite <- heq].
  - now exfalso.
Qed.

(** ** Normalised traces and their linearisation *)

(** [nf s] is the normal form of the trace [s]: the canonical linearisation of
    its normalised trace. *)
Definition nf `{ExtAction A} (s : trace A) : trace A := nlin (nform cls_tr s).

Notation "⟪ s ⟫" := (nf s) (at level 30).

(** ** Transfer of the LTS predicates along the normalisation *)

Section Transfer.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.

  (** *** Weak transitions *)

  Lemma wt_tequiv (p q : P) s t : tequiv cls_tr s t -> p ⟹[s] q -> p ⟹⋍[t] q.
  Proof.
    intro hte. revert p q.
    induction hte as [ s | s t u h1 IH1 h2 IH2 | s1 μ ν s2 heq hne ]; intros p q w.
    - exists q. split; [exact w | reflexivity].
    - destruct (IH1 p q w) as (r & w1 & heqr).
      destruct (IH2 p r w1) as (r' & w2 & heqr').
      exists r'. split; [exact w2 | etransitivity; eassumption].
    - eapply wt_split in w as (r & w1 & w2).
      replace (μ :: ν :: s2) with ([μ ; ν] ++ s2) in w2 by reflexivity.
      eapply wt_split in w2 as (r' & w3 & w4).
      assert (hsw : r ⟹⋍[[ν ; μ]] r').
      { destruct (cls_tr_same_class μ ν heq hne) as [ (nb1 & nb2) | (i1 & i2) ].
        - eapply wt_non_blocking_action_swap; eassumption.
        - eapply wt_input_swap; [exact i2 | exact w3]. }
      replace (s1 ++ ν :: μ :: s2) with (s1 ++ ([ν ; μ] ++ s2)) by reflexivity.
      eapply wt_join_eq_r; [exact w1 |].
      eapply wt_join_eq_l; eassumption.
  Qed.

  (** *** Convergence *)

  Lemma cnv_tequiv (p : P) s t : tequiv cls_tr s t -> p ⇓ s -> p ⇓ t.
  Proof.
    intro hte. revert p.
    induction hte as [ s | s t u h1 IH1 h2 IH2 | s1 μ ν s2 heq hne ]; intros p hcnv.
    - exact hcnv.
    - eapply IH2, IH1, hcnv.
    - eapply cnv_jump.
      + eapply cnv_prefix. exact hcnv.
      + intros r w.
        assert (hr : r ⇓ μ :: ν :: s2) by (eapply cnv_wt_prefix; eassumption).
        destruct (cls_tr_same_class μ ν heq hne) as [ (nb1 & nb2) | (i1 & i2) ].
        * eapply cnv_non_blocking_action_swap; eassumption.
        * eapply cnv_input_swap; eassumption.
  Qed.

  (** *** A trace and (the linearisation of) its normal form are interchangeable *)

  Corollary wt_norm (p q : P) s : p ⟹[s] q -> p ⟹⋍[⟪ s ⟫] q.
  Proof. eapply wt_tequiv, tequiv_nform. Qed.

  Corollary wt_norm_rev (p q : P) s : p ⟹[⟪ s ⟫] q -> p ⟹⋍[s] q.
  Proof. eapply wt_tequiv, tequiv_sym, tequiv_nform. Qed.

  Corollary cnv_norm (p : P) s : p ⇓ s -> p ⇓ ⟪ s ⟫.
  Proof. eapply cnv_tequiv, tequiv_nform. Qed.

  Corollary cnv_norm_rev (p : P) s : p ⇓ ⟪ s ⟫ -> p ⇓ s.
  Proof. eapply cnv_tequiv, tequiv_sym, tequiv_nform. Qed.

  (** *** Two traces with the same normal form cannot be told apart *)

  Corollary wt_of_nform (p q : P) s t :
    nform cls_tr s = nform cls_tr t -> p ⟹[s] q -> p ⟹⋍[t] q.
  Proof. intro heq. eapply wt_tequiv, tequiv_of_nform, heq. Qed.

  Corollary cnv_of_nform (p : P) s t :
    nform cls_tr s = nform cls_tr t -> p ⇓ s -> p ⇓ t.
  Proof. intro heq. eapply cnv_tequiv, tequiv_of_nform, heq. Qed.

End Transfer.


(** ** A preorder on traces

    The normalisation above only quotients traces by the *reversible*
    rearrangements, namely the swaps of two consecutive actions of the same
    class.  There are however rearrangements that only go one way.  They are
    the (complements of the) laws of Table 2 and Definition 5.1 of Boreale,
    De Nicola and Pugliese, *Trace and Testing Equivalence on Asynchronous
    Processes* (Inform. and Comput. 172, 2002), which we write [≼] below.
    Their laws are stated on the traces of the observer, ours on the traces of
    the process; the dictionary is [s ⊑ₜ t] iff [coₜ t ≼ coₜ s], and it reads:

    - (TO2, postponement) a non-blocking action may always be delayed
      ([push_wt_non_blocking_action]);  this is [tl_delay];
    - (TO3, annihilation) a non-blocking action immediately followed by one
      of its co-actions cancels out, which is the feedback of the forwarders
      ([wt_annhil]); testing along such a trace amounts to testing along the
      shorter trace where both actions have been erased.  This is
      [tl_feedback];
    - (TO4, commutativity of the observer's outputs, Definition 5.1) two
      consecutive actions admitting a non-blocking co-action commute; this is
      the instance of [tl_anticipate] where both actions are of class [CIN].
      Our [tl_anticipate] is more general: in a forwarder LTS an action with a
      non-blocking co-action may be anticipated past *any* action, because
      every state is input-receptive ([boomerang]).
    - (TO1, deletion) a non-blocking action may simply be dropped.  This law
      is the only one that does not preserve the state that is reached, so it
      is kept apart, in [trace_pre] below.

    Actions of class [COP] (blocking actions whose co-actions are blocking as
    well) have no counterpart in the original work; none of the laws applies
    to them. *)

Inductive trace_leq `{ExtAction A} : trace A -> trace A -> Prop :=
| tl_refl s : trace_leq s s
| tl_trans s t u : trace_leq s t -> trace_leq t u -> trace_leq s u
| tl_delay s1 η α s2 :
  non_blocking η -> trace_leq (s1 ++ η :: α :: s2) (s1 ++ α :: η :: s2)
| tl_anticipate s1 α μ s2 :
  exist_co_nba μ -> trace_leq (s1 ++ α :: μ :: s2) (s1 ++ μ :: α :: s2)
| tl_feedback s1 η μ s2 :
  non_blocking η -> dual μ η -> trace_leq (s1 ++ η :: μ :: s2) (s1 ++ s2).

Notation "s ⊑ₜ t" := (trace_leq s t) (at level 70).

(** [trace_pre] adds the deletion law TO1 of the original work.  Contrary to
    the three laws of [trace_leq], deletion does not preserve the state that is
    reached, hence the weaker conclusion of [wt_trace_pre] below. *)
Inductive trace_pre `{ExtAction A} : trace A -> trace A -> Prop :=
| tp_leq s t : trace_leq s t -> trace_pre s t
| tp_trans s t u : trace_pre s t -> trace_pre t u -> trace_pre s u
| tp_drop s1 η s2 : non_blocking η -> trace_pre (s1 ++ η :: s2) (s1 ++ s2).

Notation "s ≼ₜ t" := (trace_pre s t) (at level 70).

(** A non-blocking action has no non-blocking co-action. *)
Lemma nb_not_exist_co_nba `{ExtAction A} (η : A) : non_blocking η -> ¬ exist_co_nba η.
Proof.
  intros nb (ζ & nbζ & duo). eapply (dual_blocks η ζ nbζ duo). exact nb.
Qed.

(** *** [tequiv] is the symmetric part of the preorders that the normalisation
    quotients by *)

Lemma trace_leq_of_tequiv `{ExtAction A} (s t : trace A) : tequiv cls_tr s t -> s ⊑ₜ t.
Proof.
  induction 1 as [ s | s t u h1 IH1 h2 IH2 | s1 μ ν s2 heq hne ].
  - constructor.
  - eapply tl_trans; eassumption.
  - destruct (cls_tr_same_class μ ν heq hne) as [ (nb1 & nb2) | (i1 & i2) ].
    + now eapply tl_delay.
    + now eapply tl_anticipate.
Qed.

Lemma trace_pre_of_tequiv `{ExtAction A} (s t : trace A) : tequiv cls_tr s t -> s ≼ₜ t.
Proof. intro h. eapply tp_leq, trace_leq_of_tequiv, h. Qed.

Corollary trace_leq_nform `{ExtAction A} (s : trace A) : s ⊑ₜ ⟪ s ⟫ /\ ⟪ s ⟫ ⊑ₜ s.
Proof.
  split; eapply trace_leq_of_tequiv;
    [eapply tequiv_nform | eapply tequiv_sym, tequiv_nform].
Qed.

(** *** Soundness for the weak transitions *)

Section TracePreorderSoundness.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.

  Lemma wt_trace_leq (p q : P) s t : s ⊑ₜ t -> p ⟹[s] q -> p ⟹⋍[t] q.
  Proof.
    intro hle. revert p q.
    induction hle
      as [ s | s t u h1 IH1 h2 IH2 | s1 η α s2 nb | s1 α μ s2 i | s1 η μ s2 nb duo ];
      intros p q w.
    - exists q. split; [exact w | reflexivity].
    - destruct (IH1 p q w) as (r & w1 & heqr).
      destruct (IH2 p r w1) as (r' & w2 & heqr').
      exists r'. split; [exact w2 | etransitivity; eassumption].
    - eapply wt_split in w as (r & w1 & w2).
      replace (η :: α :: s2) with ([η ; α] ++ s2) in w2 by reflexivity.
      eapply wt_split in w2 as (r' & w3 & w4).
      assert (hsw : r ⟹⋍[[α ; η]] r').
      { eapply (push_wt_non_blocking_action (η := η) (s := [α])); assumption. }
      replace (s1 ++ α :: η :: s2) with (s1 ++ ([α ; η] ++ s2)) by reflexivity.
      eapply wt_join_eq_r; [exact w1 |]. eapply wt_join_eq_l; eassumption.
    - eapply wt_split in w as (r & w1 & w2).
      replace (α :: μ :: s2) with ([α ; μ] ++ s2) in w2 by reflexivity.
      eapply wt_split in w2 as (r' & w3 & w4).
      assert (hsw : r ⟹⋍[[μ ; α]] r') by (eapply wt_input_swap; eassumption).
      replace (s1 ++ μ :: α :: s2) with (s1 ++ ([μ ; α] ++ s2)) by reflexivity.
      eapply wt_join_eq_r; [exact w1 |]. eapply wt_join_eq_l; eassumption.
    - eapply wt_split in w as (r & w1 & w2).
      replace (η :: μ :: s2) with ([η ; μ] ++ s2) in w2 by reflexivity.
      eapply wt_split in w2 as (r' & w3 & w4).
      assert (hsw : r ⟹⋍ r') by (eapply wt_annhil; eassumption).
      eapply wt_join_eq_r; [exact w1 |].
      replace s2 with ([] ++ s2) by reflexivity.
      eapply wt_join_eq_l; eassumption.
  Qed.

  (** Deletion of a non-blocking action only preserves the *existence* of a
      weak transition: the state that is reached still owes the erased action.
      This is the analogue of Lemma 3.3 of Boreale, De Nicola and Pugliese. *)
  Lemma wt_trace_pre (p q : P) s t : s ≼ₜ t -> p ⟹[s] q -> ∃ q', p ⟹[t] q'.
  Proof.
    intro hle. revert p q.
    induction hle as [ s t hle | s t u h1 IH1 h2 IH2 | s1 η s2 nb ]; intros p q w.
    - eapply wt_trace_leq in w as (q' & w' & _); [| exact hle]. now exists q'.
    - destruct (IH1 p q w) as (r & w1). eapply (IH2 p r w1).
    - eapply wt_split in w as (r & w1 & w2).
      eapply push_wt_non_blocking_action in w2 as (r' & w3 & _); [| exact nb].
      eapply wt_split in w3 as (t & w4 & _).
      exists t. eapply wt_concat; eassumption.
  Qed.

  (** Testing along a trace that performs a feedback is testing along a shorter
      trace: the convergence counterpart of [tl_feedback] is [cnv_annhil]. *)
  Lemma cnv_feedback (p : P) s1 s2 s3 μ η :
    Forall exist_co_nba s1 -> Forall exist_co_nba s2 -> non_blocking η -> dual μ η ->
    p ⇓ s1 ++ [μ] ++ s2 ++ [η] ++ s3 -> p ⇓ s1 ++ s2 ++ s3.
  Proof. eapply cnv_annhil. Qed.

End TracePreorderSoundness.

(** *** The normal form is the canonical representative of a class

    Both preorders are instances of the combinatorial preorder [cls_pre] of
    [NormalForm.v], so the measure argument of Proposition 4.7 of Boreale,
    De Nicola and Pugliese applies verbatim. *)

Lemma cls_pre_of_trace_leq `{ExtAction A} (s t : trace A) : s ⊑ₜ t -> cls_pre cls_tr s t.
Proof.
  induction 1
    as [ s | s t u h1 IH1 h2 IH2 | s1 η α s2 nb | s1 α μ s2 i | s1 η μ s2 nb duo ].
  - constructor.
  - eapply cp_trans; eassumption.
  - eapply cp_delay. now eapply cls_tr_CNB.
  - eapply cp_anticipate. now eapply cls_tr_CIN.
  - eapply (cp_erase _ s1 η [μ] s2). now eapply cls_tr_CNB.
Qed.

Lemma cls_pre_of_trace_pre `{ExtAction A} (s t : trace A) : s ≼ₜ t -> cls_pre cls_tr s t.
Proof.
  induction 1 as [ s t hle | s t u h1 IH1 h2 IH2 | s1 η s2 nb ].
  - now eapply cls_pre_of_trace_leq.
  - eapply cp_trans; eassumption.
  - eapply (cp_erase _ s1 η [] s2). now eapply cls_tr_CNB.
Qed.

Theorem nform_iff_trace_leq `{ExtAction A} (s t : trace A) :
  nform cls_tr s = nform cls_tr t <-> (s ⊑ₜ t /\ t ⊑ₜ s).
Proof.
  split.
  - intro heq. split; eapply trace_leq_of_tequiv;
      [now eapply tequiv_of_nform | eapply tequiv_sym; now eapply tequiv_of_nform].
  - intros (h1 & h2). eapply nform_iff_cls_pre.
    split; now eapply cls_pre_of_trace_leq.
Qed.

Theorem nform_iff_trace_pre `{ExtAction A} (s t : trace A) :
  nform cls_tr s = nform cls_tr t <-> (s ≼ₜ t /\ t ≼ₜ s).
Proof.
  split.
  - intro heq. split; eapply trace_pre_of_tequiv;
      [now eapply tequiv_of_nform | eapply tequiv_sym; now eapply tequiv_of_nform].
  - intros (h1 & h2). eapply nform_iff_cls_pre.
    split; now eapply cls_pre_of_trace_pre.
Qed.

(** *** Simplifying a trace

    The three strict laws (delay past a blocking action, feedback, deletion)
    all make the measure decrease, so a trace cannot be simplified for ever:
    this is the analogue of Lemma 4.5 of Boreale, De Nicola and Pugliese.  The
    reduction is however not confluent -- on [η μ η'] with [dual μ η] and
    [dual μ η'], the feedback yields [η'] whereas delaying [η] yields
    [μ η η'], and neither can be simplified into the other -- so there is no
    unique reduct.  We therefore exhibit one canonical simplification,
    [csimpl], and prove that nothing strictly simpler lies below it. *)

Lemma trace_leq_app_l `{ExtAction A} (u : trace A) s t : s ⊑ₜ t -> u ++ s ⊑ₜ u ++ t.
Proof.
  induction 1
    as [ s | s t v h1 IH1 h2 IH2 | s1 η α s2 nb | s1 α μ s2 i | s1 η μ s2 nb duo ].
  - constructor.
  - eapply tl_trans; eassumption.
  - rewrite 2 app_assoc. now eapply tl_delay.
  - rewrite 2 app_assoc. now eapply tl_anticipate.
  - rewrite 2 app_assoc. now eapply tl_feedback.
Qed.

Lemma trace_pre_app_l `{ExtAction A} (u : trace A) s t : s ≼ₜ t -> u ++ s ≼ₜ u ++ t.
Proof.
  induction 1 as [ s t hle | s t v h1 IH1 h2 IH2 | s1 η s2 nb ].
  - eapply tp_leq. now eapply trace_leq_app_l.
  - eapply tp_trans; eassumption.
  - rewrite 2 app_assoc. now eapply tp_drop.
Qed.

(** All the non-blocking actions can be deleted. *)
Lemma trace_pre_drop_nb `{ExtAction A} (s : trace A) :
  s ≼ₜ filter (fun μ => cls_tr μ ≠ CNB) s.
Proof.
  induction s as [| μ s IH].
  - constructor. constructor.
  - destruct (decide (cls_tr μ = CNB)) as [h | h].
    + rewrite (filter_cons_False (fun ν => cls_tr ν ≠ CNB) μ s)
        by (intro hne; exact (hne h)).
      eapply tp_trans; [| exact IH].
      eapply (tp_drop [] μ s). now eapply cls_tr_CNB.
    + rewrite (filter_cons_True (fun ν => cls_tr ν ≠ CNB) μ s h).
      exact (trace_pre_app_l [μ] s _ IH).
Qed.

(** An action admitting a non-blocking co-action can be pulled in front of a
    whole run of such actions. *)
Lemma trace_pre_move_cin `{ExtAction A} (l1 : trace A) (μ : A) (l2 : trace A) :
  Forall (fun ν => cls_tr ν = CIN) l1 -> μ :: (l1 ++ l2) ≼ₜ l1 ++ μ :: l2.
Proof.
  induction l1 as [| ν l1 IH]; intro hl1; simpl.
  - constructor. constructor.
  - eapply Forall_cons_1 in hl1 as (hν & hl1).
    eapply tp_trans.
    + eapply tp_leq. eapply (tl_anticipate [] μ ν (l1 ++ l2)). now eapply cls_tr_CIN.
    + exact (trace_pre_app_l [ν] _ _ (IH hl1)).
Qed.

Lemma trace_pre_sort `{ExtAction A} (u : trace A) :
  Forall (fun μ => cls_tr μ ≠ CNB) u -> u ≼ₜ csimpl cls_tr u.
Proof.
  induction u as [| μ u IH]; intro hu.
  - constructor. constructor.
  - eapply Forall_cons_1 in hu as (hμ & hu). unfold csimpl.
    destruct (decide (cls_tr μ = CIN)) as [h | h].
    + rewrite (filter_cons_True (fun ν => cls_tr ν = CIN) μ u h).
      rewrite (filter_cons_False (fun ν => cls_tr ν = COP) μ u)
        by (rewrite h; discriminate).
      exact (trace_pre_app_l [μ] u (csimpl cls_tr u) (IH hu)).
    + assert (hcop : cls_tr μ = COP).
      { destruct (cls_tr μ) eqn:e.
        - exfalso. now eapply hμ.
        - exfalso. now eapply h.
        - reflexivity. }
      rewrite (filter_cons_False (fun ν => cls_tr ν = CIN) μ u)
        by (rewrite hcop; discriminate).
      rewrite (filter_cons_True (fun ν => cls_tr ν = COP) μ u hcop).
      eapply tp_trans with (t := μ :: csimpl cls_tr u).
      * exact (trace_pre_app_l [μ] u (csimpl cls_tr u) (IH hu)).
      * unfold csimpl. eapply trace_pre_move_cin, Forall_filter_self.
Qed.

Theorem trace_pre_csimpl `{ExtAction A} (s : trace A) : s ≼ₜ csimpl cls_tr s.
Proof.
  eapply tp_trans; [eapply trace_pre_drop_nb |].
  rewrite <- (csimpl_filter_no_nb cls_tr s).
  eapply trace_pre_sort, Forall_filter_self.
Qed.

(** Nothing strictly simpler lies below [csimpl s]. *)
Theorem trace_simplification `{ExtAction A} (s : trace A) :
  s ≼ₜ csimpl cls_tr s
  /\ forall t, csimpl cls_tr s ≼ₜ t
              -> tmeasure cls_tr t = tmeasure cls_tr (csimpl cls_tr s).
Proof.
  split; [eapply trace_pre_csimpl |].
  intros t hpre. eapply cls_min_csimpl. now eapply cls_pre_of_trace_pre.
Qed.

Section Simplification.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.

  (** Testing along [s] is subsumed by testing along the simplified trace. *)
  Corollary wt_csimpl (p q : P) s : p ⟹[s] q -> ∃ q', p ⟹[csimpl cls_tr s] q'.
  Proof. intro w. eapply wt_trace_pre; [eapply trace_pre_csimpl | exact w]. Qed.

End Simplification.

(** *** Simplifying a trace by feedback only

    The deletion law [tp_drop] is very strong: it allows to erase *any*
    non-blocking action, so the [≼ₜ]-least traces keep no output at all.  If
    one wants to simplify a trace only by the feedback -- the reading of point
    TO3 of Boreale, De Nicola and Pugliese -- the relevant preorder is [⊑ₜ],
    which erases nothing else.

    There, the least traces are the *sorted* ones, [tsort]: they are
    permutations of the original trace, and they carry no feedback at all,
    because a feedback needs a non-blocking action to occur *before* one of its
    co-actions, whereas in a sorted trace every non-blocking action comes
    last. *)

(** A non-blocking action can be delayed past a whole factor. *)
Lemma trace_leq_delay_run `{ExtAction A} (s1 u v : trace A) (η : A) :
  non_blocking η -> s1 ++ η :: (u ++ v) ⊑ₜ s1 ++ u ++ η :: v.
Proof.
  intro nb. revert s1.
  induction u as [| x u IH]; intro s1; simpl.
  - constructor.
  - eapply tl_trans; [eapply (tl_delay s1 η x (u ++ v)), nb |].
    specialize (IH (s1 ++ [x])).
    rewrite <- !app_assoc in IH. simpl in IH. exact IH.
Qed.

(** Hence a non-blocking action and one of its co-actions cancel out even when
    they are far apart in the trace. *)
Lemma trace_leq_feedback_mid `{ExtAction A} (s1 s2 s3 : trace A) (η μ : A) :
  non_blocking η -> dual μ η -> s1 ++ η :: (s2 ++ μ :: s3) ⊑ₜ s1 ++ s2 ++ s3.
Proof.
  intros nb duo.
  eapply tl_trans; [eapply (trace_leq_delay_run s1 s2 (μ :: s3) η), nb |].
  rewrite 2 app_assoc. now eapply tl_feedback.
Qed.

Lemma trace_leq_move_cin `{ExtAction A} (l1 : trace A) (μ : A) (l2 : trace A) :
  Forall (fun ν => cls_tr ν = CIN) l1 -> μ :: (l1 ++ l2) ⊑ₜ l1 ++ μ :: l2.
Proof.
  induction l1 as [| ν l1 IH]; intro hl1; simpl.
  - constructor.
  - eapply Forall_cons_1 in hl1 as (hν & hl1).
    eapply tl_trans.
    + eapply (tl_anticipate [] μ ν (l1 ++ l2)). now eapply cls_tr_CIN.
    + exact (trace_leq_app_l [ν] _ _ (IH hl1)).
Qed.

Theorem trace_leq_tsort `{ExtAction A} (s : trace A) : s ⊑ₜ tsort cls_tr s.
Proof.
  induction s as [| x s IH]; [constructor |]. unfold tsort in *.
  destruct (cls_tr x) eqn:e.
  - rewrite (filter_cons_False (fun ν => cls_tr ν = CIN) x s) by (rewrite e; discriminate).
    rewrite (filter_cons_False (fun ν => cls_tr ν = COP) x s) by (rewrite e; discriminate).
    rewrite (filter_cons_True (fun ν => cls_tr ν = CNB) x s e).
    eapply tl_trans with (t := x :: (filter (fun ν => cls_tr ν = CIN) s
                                     ++ filter (fun ν => cls_tr ν = COP) s
                                     ++ filter (fun ν => cls_tr ν = CNB) s)).
    + exact (trace_leq_app_l [x] s _ IH).
    + rewrite 2 app_assoc.
      exact (trace_leq_delay_run []
               (filter (fun ν => cls_tr ν = CIN) s ++ filter (fun ν => cls_tr ν = COP) s)
               (filter (fun ν => cls_tr ν = CNB) s) x (proj1 (cls_tr_CNB x) e)).
  - rewrite (filter_cons_True (fun ν => cls_tr ν = CIN) x s e).
    rewrite (filter_cons_False (fun ν => cls_tr ν = COP) x s) by (rewrite e; discriminate).
    rewrite (filter_cons_False (fun ν => cls_tr ν = CNB) x s) by (rewrite e; discriminate).
    rewrite <- app_comm_cons.
    exact (trace_leq_app_l [x] s _ IH).
  - rewrite (filter_cons_False (fun ν => cls_tr ν = CIN) x s) by (rewrite e; discriminate).
    rewrite (filter_cons_True (fun ν => cls_tr ν = COP) x s e).
    rewrite (filter_cons_False (fun ν => cls_tr ν = CNB) x s) by (rewrite e; discriminate).
    rewrite <- app_comm_cons.
    eapply tl_trans with (t := x :: (filter (fun ν => cls_tr ν = CIN) s
                                     ++ filter (fun ν => cls_tr ν = COP) s
                                     ++ filter (fun ν => cls_tr ν = CNB) s)).
    + exact (trace_leq_app_l [x] s _ IH).
    + eapply trace_leq_move_cin, Forall_filter_self.
Qed.

(** From a trace of minimal measure no feedback can ever fire, so the length is
    preserved along the whole preorder. *)
Lemma trace_leq_length `{ExtAction A} (u t : trace A) :
  u ⊑ₜ t -> tmeasure cls_tr u = length u -> length t = length u.
Proof.
  induction 1
    as [ s | s t v h1 IH1 h2 IH2 | s1 η α s2 nb | s1 α μ s2 i | s1 η μ s2 nb duo ];
    intro hm.
  - reflexivity.
  - assert (hlt : length t = length s) by (eapply IH1, hm).
    assert (hmt : tmeasure cls_tr t = length t).
    { pose proof (cls_pre_measure cls_tr s t (cls_pre_of_trace_leq s t h1)).
      pose proof (tmeasure_ge_length cls_tr t). lia. }
    rewrite (IH2 hmt). exact hlt.
  - symmetry. eapply length_middle_swap.
  - symmetry. eapply length_middle_swap.
  - exfalso.
    assert (hcnb : cls_tr η = CNB) by (eapply cls_tr_CNB, nb).
    assert (hcin : cls_tr μ = CIN) by (eapply cls_tr_CIN; exists η; split; assumption).
    assert (hge : 1 <= inv_nb cls_tr (s1 ++ η :: μ :: s2)).
    { unfold inv_nb. rewrite inv_cnt_middle. unfold bit.
      destruct (decide (cls_tr η = CNB)) as [_ | hno]; [| exfalso; exact (hno hcnb)].
      destruct (decide (cls_tr μ ≠ CNB)) as [_ | hno]; [lia |].
      exfalso. eapply hno. rewrite hcin. discriminate. }
    unfold tmeasure in hm. lia.
Qed.

(** A trace is [⊑ₜ]-least when nothing below it is strictly simpler. *)
Definition trace_min `{ExtAction A} (u : trace A) : Prop :=
  forall t, u ⊑ₜ t -> tmeasure cls_tr t = tmeasure cls_tr u.

Lemma trace_min_of_measure `{ExtAction A} (u : trace A) :
  tmeasure cls_tr u = length u -> trace_min u.
Proof.
  intros hm t hle.
  pose proof (trace_leq_length u t hle hm) as hl.
  pose proof (cls_pre_measure cls_tr u t (cls_pre_of_trace_leq u t hle)).
  pose proof (tmeasure_ge_length cls_tr t). lia.
Qed.

Theorem trace_simplification_leq `{ExtAction A} (s : trace A) :
  s ⊑ₜ tsort cls_tr s /\ tsort cls_tr s ≡ₚ s /\ trace_min (tsort cls_tr s).
Proof.
  repeat split.
  - eapply trace_leq_tsort.
  - eapply tsort_perm.
  - eapply trace_min_of_measure, tmeasure_tsort.
Qed.

(** No feedback is left in a sorted trace. *)
Corollary tsort_feedback_free `{ExtAction A} (s s1 s2 s3 : trace A) (η μ : A) :
  tsort cls_tr s = s1 ++ η :: (s2 ++ μ :: s3) -> non_blocking η -> dual μ η -> False.
Proof.
  intros heq nb duo.
  assert (hle : tsort cls_tr s ⊑ₜ s1 ++ s2 ++ s3)
    by (rewrite heq; eapply trace_leq_feedback_mid; assumption).
  pose proof (trace_leq_length _ _ hle (tmeasure_tsort cls_tr s)) as hl.
  rewrite heq in hl.
  rewrite !length_app' in hl. simpl in hl.
  rewrite !length_app' in hl. simpl in hl. lia.
Qed.

Section SimplificationLeq.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.

  (** Contrary to [wt_csimpl], the state that is reached is preserved: the
      sorted trace loses nothing. *)
  Corollary wt_tsort (p q : P) s : p ⟹[s] q -> p ⟹⋍[tsort cls_tr s] q.
  Proof. intro w. eapply wt_trace_leq; [eapply trace_leq_tsort | exact w]. Qed.

End SimplificationLeq.

(** *** Consuming the feedbacks

    Sorting a trace does not shorten it: it merely moves the non-blocking
    actions past their co-actions, so that no feedback is left.  To actually
    *consume* the feedbacks one first reduces by the feedback rule alone.

    That reduction is an orthogonal rewriting system: by [dual_blocks], if
    [η μ] is a feedback then [μ] is blocking, so [μ ν] can never be one -- two
    redexes never overlap ([fb_rel_disjoint]).  Together with the fact that
    each step removes two actions, this makes the reduction terminating, and
    its redexes pairwise disjoint. *)

Definition fb_rel `{ExtAction A} (x y : A) : Prop := non_blocking x /\ dual y x.

#[global] Instance fb_rel_dec `{ExtAction A} (x y : A) : Decision (fb_rel x y).
Proof. unfold fb_rel. solve_decision. Defined.

(** Two feedback redexes never overlap. *)
Lemma fb_rel_disjoint `{ExtAction A} (x y z : A) : fb_rel x y -> ¬ fb_rel y z.
Proof.
  intros (nb & duo) (nb' & _). eapply (dual_blocks y x nb duo). exact nb'.
Qed.

Lemma fb_normal_exists_aux `{ExtAction A} (n : nat) (s : trace A) :
  length s <= n ->
  ∃ t, s ⊑ₜ t /\ no_redex fb_rel t /\ length t <= length s.
Proof.
  revert s. induction n as [| n IH]; intros s hn.
  - exists s. repeat split.
    + constructor.
    + eapply no_redex_short. lia.
    + lia.
  - destruct (has_redex fb_rel s) eqn:e.
    + eapply has_redex_true in e as (s1 & x & y & s2 & -> & (nb & duo)).
      destruct (IH (s1 ++ s2)) as (t & hle & hnf & hlen).
      { rewrite !length_app' in *. simpl in hn. lia. }
      exists t. repeat split.
      * eapply tl_trans; [now eapply tl_feedback | exact hle].
      * exact hnf.
      * rewrite !length_app' in *. simpl. lia.
    + exists s. repeat split.
      * constructor.
      * now eapply has_redex_false.
      * lia.
Qed.

Corollary fb_normal_exists `{ExtAction A} (s : trace A) :
  ∃ t, s ⊑ₜ t /\ no_redex fb_rel t /\ length t <= length s.
Proof. eapply (fb_normal_exists_aux (length s) s). lia. Qed.

(** Consuming the feedbacks and then sorting yields a least trace that carries
    no feedback at all, not even between actions that are far apart. *)
Theorem trace_simplification_full `{ExtAction A} (s : trace A) :
  ∃ t, s ⊑ₜ t
     /\ trace_min t
     /\ length t <= length s
     /\ (forall s1 s2 s3 η μ,
            t = s1 ++ η :: (s2 ++ μ :: s3) -> non_blocking η -> dual μ η -> False).
Proof.
  destruct (fb_normal_exists s) as (u & hle & _ & hlen).
  exists (tsort cls_tr u). repeat split.
  - eapply tl_trans; [exact hle | eapply trace_leq_tsort].
  - eapply trace_min_of_measure, tmeasure_tsort.
  - rewrite length_tsort. exact hlen.
  - intros s1 s2 s3 η μ heq nb duo. eapply tsort_feedback_free; eassumption.
Qed.

(** A trace performing a feedback -- even between two distant actions -- is
    subsumed by a strictly shorter least trace.  This is the trace-level
    reading of the law TO3 of Boreale, De Nicola and Pugliese. *)
Corollary trace_simplification_strict `{ExtAction A} (s1 s2 s3 : trace A) (η μ : A) :
  non_blocking η -> dual μ η ->
  ∃ t, (s1 ++ η :: (s2 ++ μ :: s3)) ⊑ₜ t
     /\ trace_min t
     /\ length t < length (s1 ++ η :: (s2 ++ μ :: s3)).
Proof.
  intros nb duo.
  destruct (trace_simplification_full (s1 ++ s2 ++ s3)) as (t & hle & hmin & hlen & _).
  exists t. repeat split.
  - eapply tl_trans; [eapply trace_leq_feedback_mid; eassumption | exact hle].
  - exact hmin.
  - rewrite !length_app' in *. simpl. rewrite !length_app'. simpl. lia.
Qed.

(** ** A normal form that consumes the feedbacks

    [fbnf] is a *computable* simplification of a trace: as long as the trace
    contains a non-blocking action followed -- anywhere later -- by one of its
    co-actions, both are erased.  The result is [⊑ₜ]-above the original trace,
    so testing along [s] reduces to testing along [fbnf s], and it contains no
    such pair any more. *)

Section FeedbackNormalForm.

  Context `{H : !ExtAction A}.

  (** Erase the first action of [l] that is a co-action of [η]. *)
  Fixpoint drop_dual (η : A) (l : trace A) : option (trace A) :=
    match l with
    | [] => None
    | μ :: l' =>
        if decide (dual μ η) then Some l'
        else match drop_dual η l' with
             | Some t => Some (μ :: t)
             | None => None
             end
    end.

  Lemma drop_dual_spec η l : forall t,
    drop_dual η l = Some t ->
    exists l1 μ l2, l = l1 ++ μ :: l2 /\ t = l1 ++ l2 /\ dual μ η.
  Proof.
    induction l as [| ν l IH]; intros t heq; [discriminate |].
    simpl in heq. destruct (decide (dual ν η)) as [d | d].
    - injection heq. intro hl. subst t.
      exists [], ν, l. repeat split. exact d.
    - destruct (drop_dual η l) as [t0 |] eqn:e; [| discriminate].
      injection heq. intro hl. subst t.
      destruct (IH t0 eq_refl) as (l1 & μ & l2 & -> & -> & dμ).
      exists (ν :: l1), μ, l2. repeat split. exact dμ.
  Qed.

  Lemma drop_dual_none η l :
    drop_dual η l = None -> Forall (fun μ => ¬ dual μ η) l.
  Proof.
    induction l as [| ν l IH]; intro heq; [constructor |].
    simpl in heq. destruct (decide (dual ν η)) as [d | d]; [discriminate |].
    destruct (drop_dual η l) as [t0 |] eqn:e; [discriminate |].
    constructor; [exact d | exact (IH eq_refl)].
  Qed.

  (** Erase one feedback pair, if the trace contains one. *)
  Fixpoint drop_fb (s : trace A) : option (trace A) :=
    match s with
    | [] => None
    | η :: s' =>
        match (if decide (non_blocking η) then drop_dual η s' else None) with
        | Some t => Some t
        | None =>
            match drop_fb s' with
            | Some t => Some (η :: t)
            | None => None
            end
        end
    end.

  Lemma drop_fb_leq s : forall t,
    drop_fb s = Some t -> s ⊑ₜ t /\ S (S (length t)) = length s.
  Proof.
    induction s as [| η s IH]; intros t heq; [discriminate |].
    simpl in heq. destruct (decide (non_blocking η)) as [nb | nb].
    - destruct (drop_dual η s) as [t0 |] eqn:e.
      + injection heq. intro hl. subst t.
        eapply drop_dual_spec in e as (l1 & μ & l2 & -> & -> & d).
        split.
        * exact (trace_leq_feedback_mid [] l1 l2 η μ nb d).
        * simpl. rewrite !length_app'. simpl. lia.
      + destruct (drop_fb s) as [t1 |] eqn:e1; [| discriminate].
        injection heq. intro hl. subst t.
        destruct (IH t1 eq_refl) as (hle & hln).
        split; [exact (trace_leq_app_l [η] s t1 hle) | simpl; lia].
    - destruct (drop_fb s) as [t1 |] eqn:e1; [| discriminate].
      injection heq. intro hl. subst t.
      destruct (IH t1 eq_refl) as (hle & hln).
      split; [exact (trace_leq_app_l [η] s t1 hle) | simpl; lia].
  Qed.

  Lemma drop_fb_none s :
    drop_fb s = None ->
    forall s1 η s2 μ s3,
      s = s1 ++ η :: (s2 ++ μ :: s3) -> non_blocking η -> dual μ η -> False.
  Proof.
    induction s as [| x s IH]; intros heq s1 η s2 μ s3 hs nb d.
    - destruct s1; discriminate.
    - simpl in heq.
      destruct (decide (non_blocking x)) as [nbx | nbx]; simpl in heq.
      + destruct (drop_dual x s) as [t0 |] eqn:e; [discriminate |].
        destruct (drop_fb s) as [t1 |] eqn:e1; [discriminate |].
        destruct s1 as [| c s1]; simpl in hs; injection hs.
        * intros hs' hx. subst x. subst s.
          eapply drop_dual_none in e.
          eapply Forall_app_inv in e as (_ & e).
          eapply Forall_cons_1 in e as (e & _). exact (e d).
        * intros hs' _. exact (IH eq_refl s1 η s2 μ s3 hs' nb d).
      + destruct (drop_fb s) as [t1 |] eqn:e1; [discriminate |].
        destruct s1 as [| c s1]; simpl in hs; injection hs.
        * intros _ hx. subst x. contradiction.
        * intros hs' _. exact (IH eq_refl s1 η s2 μ s3 hs' nb d).
  Qed.

  Fixpoint fb_iter (n : nat) (s : trace A) : trace A :=
    match n with
    | 0 => s
    | S n => match drop_fb s with Some t => fb_iter n t | None => s end
    end.

  (** The simplified trace. *)
  Definition fbnf (s : trace A) : trace A := fb_iter (length s) s.

  Lemma fb_iter_leq n : forall s, s ⊑ₜ fb_iter n s /\ length (fb_iter n s) <= length s.
  Proof.
    induction n as [| n IH]; intro s; simpl.
    - split; [constructor | lia].
    - destruct (drop_fb s) as [t |] eqn:e.
      + eapply drop_fb_leq in e as (hle & hln).
        destruct (IH t) as (hle' & hl').
        split; [eapply tl_trans; eassumption | lia].
      + split; [constructor | lia].
  Qed.

  Lemma fb_iter_none n : forall s, length s <= n -> drop_fb (fb_iter n s) = None.
  Proof.
    induction n as [| n IH]; intros s hn; simpl.
    - destruct s as [| x s]; [reflexivity | simpl in hn; lia].
    - destruct (drop_fb s) as [t |] eqn:e.
      + eapply IH. eapply drop_fb_leq in e as (_ & hln). lia.
      + exact e.
  Qed.

  Theorem trace_leq_fbnf (s : trace A) : s ⊑ₜ fbnf s.
  Proof. exact (proj1 (fb_iter_leq (length s) s)). Qed.

  Theorem fbnf_length (s : trace A) : length (fbnf s) <= length s.
  Proof. exact (proj2 (fb_iter_leq (length s) s)). Qed.

  (** Nothing is left to simplify. *)
  Theorem fbnf_feedback_free (s s1 s2 s3 : trace A) (η μ : A) :
    fbnf s = s1 ++ η :: (s2 ++ μ :: s3) -> non_blocking η -> dual μ η -> False.
  Proof.
    eapply drop_fb_none. unfold fbnf. eapply fb_iter_none. lia.
  Qed.

  (** The normal form: the feedbacks are consumed, then the consecutive actions
      of a same class are collected into multisets. *)
  Definition fnf (s : trace A) : ntrace A := nform cls_tr (fbnf s).

  Lemma trace_leq_fnf (s : trace A) : s ⊑ₜ nlin (fnf s).
  Proof.
    eapply tl_trans; [eapply trace_leq_fbnf |].
    eapply trace_leq_of_tequiv, tequiv_nform.
  Qed.

End FeedbackNormalForm.

Section FeedbackNormalFormLts.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.

  Corollary wt_fbnf (p q : P) s : p ⟹[s] q -> p ⟹⋍[fbnf s] q.
  Proof. intro w. eapply wt_trace_leq; [eapply trace_leq_fbnf | exact w]. Qed.

  Corollary wt_fnf (p q : P) s : p ⟹[s] q -> p ⟹⋍[nlin (fnf s)] q.
  Proof. intro w. eapply wt_trace_leq; [eapply trace_leq_fnf | exact w]. Qed.

End FeedbackNormalFormLts.

(** ** The preorder and convergence

    [⊑ₜ] is sound for convergence too, but *contravariantly*: a weak transition
    is an existential statement, so making a trace easier to perform adds
    behaviours ([wt_trace_leq] goes from [s] to [t]); convergence is a
    universal statement over the states reachable along the trace, so it goes
    the other way. *)

Section TracePreorderConvergence.

  Context `{H : !ExtAction A}.
  Context `{@gLtsOba P A H gLtsEqP, !gLtsObaFW P A}.

  Lemma cnv_delay (p : P) (η α : A) s :
    non_blocking η -> p ⇓ α :: η :: s -> p ⇓ η :: α :: s.
  Proof.
    intros nb hcnv.
    assert (hterm : p ⤓) by (eapply cnv_terminate; exact hcnv).
    eapply cnv_act; [exact hterm |].
    intros q w1.
    eapply cnv_act.
    - eapply terminate_preserved_by_wt_non_blocking_action;
        [exact nb | exact hterm | exact w1].
    - intros t w2.
      assert (w3 : p ⟹[[η ; α]] t) by (eapply wt_push_left; eassumption).
      eapply push_wt_non_blocking_action in w3 as (t' & w4 & heq); [| exact nb].
      eapply cnv_preserved_by_eq; [exact heq | reflexivity |].
      eapply (cnv_wt_prefix [α ; η] s p); [exact hcnv | exact w4].
  Qed.

  Lemma cnv_anticipate (p : P) (μ α : A) s :
    exist_co_nba μ -> p ⇓ μ :: α :: s -> p ⇓ α :: μ :: s.
  Proof.
    intros (η & nb & duo) hcnv.
    assert (hterm : p ⤓) by (eapply cnv_terminate; exact hcnv).
    destruct (boomerang p η μ) as (t0 & Hb).
    destruct (Hb nb duo) as (l1 & l2).
    assert (h0 : t0 ⇓ α :: s).
    { eapply (cnv_preserved_by_wt_act (α :: s) p μ hcnv). eapply lts_to_wt, l1. }
    eapply cnv_act; [exact hterm |].
    intros q w1.
    eapply cnv_act.
    - destruct (delay_wt_non_blocking_action nb (mk_lts_eq l2) w1)
        as (t' & w2 & (t2 & hlt2 & heqt2)).
      assert (ht' : t' ⤓).
      { eapply (cnv_terminate t' s).
        exact (cnv_preserved_by_wt_act s t0 α h0 t' w2). }
      eapply (terminate_preserved_by_eq2 heqt2).
      exact (terminate_preserved_by_lts_non_blocking_action nb hlt2 ht').
    - intros r w2.
      destruct (wt_input_swap p r α μ (ex_intro _ η (conj nb duo))
                  (wt_push_left w1 w2)) as (t & w' & heq').
      eapply cnv_preserved_by_eq; [exact heq' | reflexivity |].
      eapply (cnv_wt_prefix [μ ; α] s p); [exact hcnv | exact w'].
  Qed.

  Lemma cnv_annhil_head (p : P) (η μ : A) s :
    non_blocking η -> dual μ η -> p ⇓ s -> p ⇓ η :: μ :: s.
  Proof.
    intros nb duo hcnv.
    assert (hterm : p ⤓) by (eapply cnv_terminate; exact hcnv).
    eapply cnv_act; [exact hterm |].
    intros q w1.
    eapply cnv_act.
    - eapply terminate_preserved_by_wt_non_blocking_action;
        [exact nb | exact hterm | exact w1].
    - intros t w2.
      assert (w3 : p ⟹[[η ; μ]] t) by (eapply wt_push_left; eassumption).
      eapply wt_annhil in w3 as (t' & w4 & heq); [| exact nb | exact duo].
      eapply cnv_preserved_by_eq; [exact heq | reflexivity |].
      eapply cnv_preserved_by_wt_nil; [exact hcnv | exact w4].
  Qed.

  Lemma cnv_drop_head (p : P) (η : A) s :
    non_blocking η -> p ⇓ s -> p ⇓ η :: s.
  Proof.
    intros nb hcnv.
    eapply cnv_act; [eapply cnv_terminate; exact hcnv |].
    intros q w. eapply cnv_preserved_by_wt_non_blocking_action; eassumption.
  Qed.

  (** All four rules only rewrite a factor, so a single context lemma suffices. *)
  Lemma cnv_ctx (p : P) s1 u v :
    (forall r : P, r ⇓ v -> r ⇓ u) -> p ⇓ s1 ++ v -> p ⇓ s1 ++ u.
  Proof.
    intros h hcnv. eapply cnv_jump.
    - eapply cnv_prefix. exact hcnv.
    - intros r w. eapply h. eapply cnv_wt_prefix; eassumption.
  Qed.

  Theorem cnv_trace_leq (p : P) s t : s ⊑ₜ t -> p ⇓ t -> p ⇓ s.
  Proof.
    intro hle. revert p.
    induction hle
      as [ s | s t u h1 IH1 h2 IH2 | s1 η α s2 nb | s1 α μ s2 i | s1 η μ s2 nb duo ];
      intros p hcnv.
    - exact hcnv.
    - eapply IH1, IH2, hcnv.
    - eapply cnv_ctx; [| exact hcnv]. intros r. now eapply cnv_delay.
    - eapply cnv_ctx; [| exact hcnv]. intros r. now eapply cnv_anticipate.
    - eapply (cnv_ctx p s1 (η :: μ :: s2) s2); [| exact hcnv].
      intros r. now eapply cnv_annhil_head.
  Qed.

  Theorem cnv_trace_pre (p : P) s t : s ≼ₜ t -> p ⇓ t -> p ⇓ s.
  Proof.
    intro hle. revert p.
    induction hle as [ s t hle | s t u h1 IH1 h2 IH2 | s1 η s2 nb ]; intros p hcnv.
    - eapply cnv_trace_leq; eassumption.
    - eapply IH1, IH2, hcnv.
    - eapply (cnv_ctx p s1 (η :: s2) s2); [| exact hcnv].
      intros r. now eapply cnv_drop_head.
  Qed.

End TracePreorderConvergence.

(** ** A feedback survives the normalisation

    A feedback pairs a non-blocking action with one of its co-actions, that is
    an action of class [CNB] with one of class [CIN].  They therefore always
    sit in two *different* blocks of the normal form, whereas the normalisation
    only permutes the actions *inside* a block.  So normalising can neither
    create nor destroy a feedback: whether a trace admits one is an invariant
    of [tequiv], hence of the normal form.

    Two consequences: the simplified trace stays feedback-free once normalised,
    and grouping the runs before consuming the feedbacks would not consume a
    single one more. *)

Section FeedbackInvariance.

  Context `{H : !ExtAction A}.

  (** *** Small facts about [Exists] *)

  Lemma Exists_cons_iff (Q : A -> Prop) x l : Exists Q (x :: l) <-> Q x \/ Exists Q l.
  Proof.
    split.
    - inversion 1; subst; [left; assumption | right; assumption].
    - intros [h | h]; [now constructor | now apply Exists_cons_tl].
  Qed.

  Lemma Exists_swap (Q : A -> Prop) l1 x y l2 :
    Exists Q (l1 ++ x :: y :: l2) <-> Exists Q (l1 ++ y :: x :: l2).
  Proof.
    induction l1 as [| c l1 IH]; simpl.
    - rewrite 4 Exists_cons_iff. tauto.
    - rewrite 2 Exists_cons_iff. tauto.
  Qed.

  Lemma Exists_mid (Q : A -> Prop) l1 y l2 : Q y -> Exists Q (l1 ++ y :: l2).
  Proof.
    intro h. induction l1 as [| c l1 IH]; simpl;
      [now constructor | now apply Exists_cons_tl].
  Qed.

  Lemma Exists_decomp (Q : A -> Prop) l :
    Exists Q l -> exists l1 y l2, l = l1 ++ y :: l2 /\ Q y.
  Proof.
    induction 1 as [x l hx | x l hl IH].
    - exists [], x, l. split; [reflexivity | exact hx].
    - destruct IH as (l1 & y & l2 & -> & hy).
      exists (x :: l1), y, l2. split; [reflexivity | exact hy].
  Qed.

  (** *** [has_fb u]: the trace [u] admits a feedback *)

  Definition dual_later (η : A) (l : trace A) : Prop := Exists (fun μ => dual μ η) l.

  Fixpoint has_fb (u : trace A) : Prop :=
    match u with
    | [] => False
    | x :: u' => (non_blocking x /\ dual_later x u') \/ has_fb u'
    end.

  Lemma has_fb_of_decomp (s1 : trace A) (η : A) s2 (μ : A) s3 :
    non_blocking η -> dual μ η -> has_fb (s1 ++ η :: (s2 ++ μ :: s3)).
  Proof.
    intros nb d. induction s1 as [| c s1 IH]; simpl.
    - left. split; [exact nb |]. unfold dual_later. now eapply Exists_mid.
    - right. exact IH.
  Qed.

  Lemma has_fb_decomp (u : trace A) :
    has_fb u ->
    exists s1 η s2 μ s3, u = s1 ++ η :: (s2 ++ μ :: s3) /\ non_blocking η /\ dual μ η.
  Proof.
    induction u as [| x u IH]; simpl; [contradiction |].
    intros [ (nb & hd) | h ].
    - eapply Exists_decomp in hd as (l1 & μ & l2 & -> & d).
      exists [], x, l1, μ, l2. repeat split; assumption.
    - destruct (IH h) as (s1 & η & s2 & μ & s3 & -> & nb & d).
      exists (x :: s1), η, s2, μ, s3. repeat split; assumption.
  Qed.

  (** *** Invariance *)

  Lemma nb_nb_not_dual (x y : A) : non_blocking x -> non_blocking y -> ¬ dual y x.
  Proof. intros nx ny d. exact (dual_blocks y x nx d ny). Qed.

  Lemma has_fb_swap (s1 : trace A) (x y : A) s2 :
    cls_tr x = cls_tr y -> cls_tr x ≠ COP ->
    has_fb (s1 ++ x :: y :: s2) -> has_fb (s1 ++ y :: x :: s2).
  Proof.
    intros heq hne. induction s1 as [| c s1 IH]; simpl.
    - destruct (cls_tr_same_class x y heq hne) as [ (nx & ny) | (ix & iy) ].
      + unfold dual_later. rewrite 2 Exists_cons_iff.
        intros [ (_ & [ dyx | hx ]) | [ (_ & hy) | h ] ].
        * exfalso. exact (nb_nb_not_dual x y nx ny dyx).
        * right. left. split; [exact nx | exact hx].
        * left. split; [exact ny | right; exact hy].
        * right. right. exact h.
      + assert (bx : ¬ non_blocking x) by (intro nx; exact (nb_not_exist_co_nba x nx ix)).
        assert (by_ : ¬ non_blocking y) by (intro ny; exact (nb_not_exist_co_nba y ny iy)).
        intros [ (nx & _) | [ (ny & _) | h ] ].
        * now exfalso.
        * now exfalso.
        * right. right. exact h.
    - unfold dual_later. rewrite (Exists_swap (fun μ => dual μ c) s1 x y s2).
      intros [ hc | h ]; [ left; exact hc | right; exact (IH h) ].
  Qed.

  Lemma has_fb_tequiv (s t : trace A) : tequiv cls_tr s t -> has_fb s -> has_fb t.
  Proof.
    induction 1 as [ s | s t u h1 IH1 h2 IH2 | s1 μ ν s2 heq hne ].
    - exact (fun h => h).
    - intro h. eapply IH2, IH1, h.
    - now eapply has_fb_swap.
  Qed.

  Corollary has_fb_nform (s t : trace A) :
    nform cls_tr s = nform cls_tr t -> has_fb s -> has_fb t.
  Proof. intro heq. eapply has_fb_tequiv, tequiv_of_nform, heq. Qed.

  (** *** Consequences *)

  (** The simplified trace admits no feedback, and neither does its normal
      form, however the runs are linearised. *)
  Corollary fbnf_no_fb (s : trace A) : ¬ has_fb (fbnf s).
  Proof.
    intro h. eapply has_fb_decomp in h as (s1 & η & s2 & μ & s3 & heq & nb & d).
    exact (fbnf_feedback_free s s1 s2 s3 η μ heq nb d).
  Qed.

  Corollary fnf_no_fb (s : trace A) : ¬ has_fb (nlin (fnf s)).
  Proof.
    intro h. eapply fbnf_no_fb.
    eapply has_fb_tequiv; [| exact h].
    eapply tequiv_sym, tequiv_nform.
  Qed.

  (** Grouping the runs first exposes no new feedback: the two orders of
      composition see exactly the same ones. *)
  Corollary has_fb_norm (s : trace A) : has_fb s <-> has_fb (nlin (nform cls_tr s)).
  Proof.
    split; intro h.
    - eapply has_fb_tequiv; [eapply tequiv_nform | exact h].
    - eapply has_fb_tequiv; [eapply tequiv_sym, tequiv_nform | exact h].
  Qed.

End FeedbackInvariance.

(** * [fnf] is idempotent

    A trace that carries no feedback is its own simplification, so the
    normalised traces are exactly the fixed points of [nlin ∘ fnf].  This is
    what makes the two readings of the preorder on simplified traces agree:
    quantifying over all traces on the left, or over the normalised ones on
    both sides (see [bhv_pre_ti_fnf_iff]). *)

Section FeedbackIdempotence.

  Context `{H : !ExtAction A}.

  Lemma has_fb_cons (x : A) (s : trace A) : has_fb s -> has_fb (x :: s).
  Proof. intro h. simpl. now right. Qed.

  (** [drop_fb] only ever fires on a real feedback. *)
  Lemma drop_fb_some (s : trace A) : forall t, drop_fb s = Some t -> has_fb s.
  Proof.
    induction s as [| x s IH]; intros t heq; [discriminate |].
    simpl in heq. destruct (decide (non_blocking x)) as [nb | nb].
    - destruct (drop_dual x s) as [t0 |] eqn:e.
      + eapply drop_dual_spec in e as (l1 & μ & l2 & -> & _ & d).
        exact (has_fb_of_decomp [] x l1 μ l2 nb d).
      + destruct (drop_fb s) as [t1 |] eqn:e1; [| discriminate].
        eapply has_fb_cons, (IH t1 eq_refl).
    - destruct (drop_fb s) as [t1 |] eqn:e1; [| discriminate].
      eapply has_fb_cons, (IH t1 eq_refl).
  Qed.

  Lemma fb_iter_id n (s : trace A) : drop_fb s = None -> fb_iter n s = s.
  Proof. intro h. destruct n; simpl; [reflexivity | now rewrite h]. Qed.

  Theorem fbnf_id (s : trace A) : ¬ has_fb s -> fbnf s = s.
  Proof.
    intro h. unfold fbnf. eapply fb_iter_id.
    destruct (drop_fb s) as [t |] eqn:e; [| reflexivity].
    exfalso. eapply h, (drop_fb_some s t e).
  Qed.

  Theorem fnf_idem (s : trace A) : nlin (fnf (nlin (fnf s))) = nlin (fnf s).
  Proof.
    unfold fnf at 1. rewrite (fbnf_id (nlin (fnf s)) (fnf_no_fb s)).
    unfold fnf. rewrite nform_nlin_nform. reflexivity.
  Qed.

End FeedbackIdempotence.
