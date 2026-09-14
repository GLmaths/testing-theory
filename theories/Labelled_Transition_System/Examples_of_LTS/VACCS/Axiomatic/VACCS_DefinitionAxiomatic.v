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

(** * An inequational proof system for [⊑ₘᵤₛₜᵢ] on VACCS

    Nine rules.  Every one has its semantic justification proved in
    [VACCS_Precongruence.v], [VACCS_Expansion.v] or [VACCS_ResNormalize.v]
    *before* being admitted here — this development has already been burnt
    twice by plausible-looking congruence rules that turned out to be
    false, once per calculus.

    ** What changes with respect to the VCCS system

    *Gone, because [gproc] has no output constructor.*  [ax_output],
    [ax_output_merge_*], [ax_output_distrib_*], [ax_share_out] and
    [ax_swap_out] have no VACCS counterpart.  An output is an atomic
    message [c!v•𝟘], never a guard, so it can neither be a summand nor
    carry a continuation — and with it goes the entire value-erasure
    problem that dominated VCCS's completeness proof.  Correspondingly,
    the expansion law has no synchronisation term: two guarded sums can
    never synchronise.

    *Gone, because it is UNSOUND here.*  [ax_choice_stable] — replacing a
    stable summand by another stable one.  See [VACCS_ChoiceProbes.v] for
    the machine-checked counterexample; the engine is the copycat
    [a?(a!x•𝟘) ≂ₘᵤₛₜᵢ 𝟘], which is invisible standalone but not under a
    choice, because committing to it discards the alternative.

    *New, in its place.*  [ax_choice_input]: a summand's *continuation*
    may be rewritten, its *guard* may not.  Together with [ax_choice_tau]
    that covers every guard shape VACCS has ([①] and [𝟘] carry no
    continuation), so the design principle sharpens from VCCS's "the
    rewrite must not change initial stability" to "the rewrite must not
    change the guard at all".

    *No [Static] side conditions anywhere.*  VCCS needed them on
    [ax_cgr], [ax_expansion_*] and [ax_res_normalize_*], to keep a
    derivation inside the [Static] fragment so that [ax_trans] could
    recover its middle term's [Static]-ness.  Here soundness needs no such
    invariant: the two *bridges* ([VACCS_Precongruence.v]) prove
    [‖]- and [ν]-precongruence with no hypothesis on the operands at all,
    and every other rule was already unconditional.  So [VACCS_SoundnessAx.v]
    proves [p ᴠᴀᴄᴄꜱ⊑ₐₓ q -> p ⊑ₘᵤₛₜᵢ q] outright. *)

From stdpp Require Import base gmultiset sets gmap.
From TestingTheory Require Import MultisetLTSConstruction.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Shift VACCS_Precongruence VACCS_Expansion VACCS_ResNormalize
  VACCS_Copycat VACCS_Absorb VACCS_Forwarder VACCS_Cond2 VACCS_Residues
  VACCS_GlbStable.

Section VACCS_DefinitionAxiomatic.

Context `{VP : VACCS_Parameters}.

(** The axiomatic preorder is written [p ᴠᴀᴄᴄꜱ⊑ₐₓ q], named like the semantic
    preorder it characterises, [p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q].  The token is reserved here
    and bound to the inductive by the [where] clause below, so the rules
    themselves read in the notation.  A [where]-bound notation is
    section-local like any other, so it is declared again, globally, at the
    end of this file. *)
Reserved Notation "p ᴠᴀᴄᴄꜱ⊑ₐₓ q" (at level 70).

Inductive ax_pre : proc -> proc -> Prop :=

(** *** Preorder and free equations *)

| ax_trans : forall p q r, p ᴠᴀᴄᴄꜱ⊑ₐₓ q -> q ᴠᴀᴄᴄꜱ⊑ₐₓ r -> p ᴠᴀᴄᴄꜱ⊑ₐₓ r
| ax_cgr : forall p q, p ≡* q -> p ᴠᴀᴄᴄꜱ⊑ₐₓ q

(** *** Congruence, one rule per operator

    [ax_par] and [ax_res] are sound by the two bridges — the context is
    moved into the test, and [p ⊑ₘᵤₛₜᵢ q] is applied at a *single* test.
    There is deliberately no rule for [+] beyond the two guard-preserving
    ones below. *)

| ax_par : forall p p' q q', p ᴠᴀᴄᴄꜱ⊑ₐₓ p' -> q ᴠᴀᴄᴄꜱ⊑ₐₓ q' -> (p ‖ q) ᴠᴀᴄᴄꜱ⊑ₐₓ (p' ‖ q')
| ax_res : forall p q, p ᴠᴀᴄᴄꜱ⊑ₐₓ q -> (ν p) ᴠᴀᴄᴄꜱ⊑ₐₓ (ν q)
(** *** Internal computation, and the greatest lower bound

    [⊕] is not primitive in this syntax; it is [𝛕•X + 𝛕•Y].  What projects
    out of it is not a law about sums at all but the general **τ-step**
    rule: a server's own internal move only ever decreases it, since
    [must]'s [pt] field hands the obligation straight to every
    τ-successor.  [ax_int_l] is its guarded-sum instance and is derived
    below, and [ax_int_r] follows by commutativity of [+].  Building
    *into* an internal choice is [ax_glb_tau] below, of which [ax_int_glb]
    is an instance.

    Stating it at the level of transitions rather than of guarded sums is
    what makes it usable on a **message beside a sum**, [(c!v•𝟘) ‖ g M],
    whose delivery τ is not the transition of any [gproc] — the shape the
    normal form [Ѵⁿ (msgs l ‖ g M)] actually produces.  For a [Static]
    process the premise quantifies over a finite, computable set of
    reducts, so nothing infinitary is smuggled in. *)

| ax_tau_step : forall p p', lts p τ p' -> p ᴠᴀᴄᴄꜱ⊑ₐₓ p'

(** *** Two processes with the same transitions

    [must] inspects a server only through its transitions, so two
    processes with the same transitions pass the same tests
    ([VACCS_Expansion.must_same_lts]).  The expansion law, the
    normalisation of a restriction over a guarded sum and the two laws
    identifying an [①] summand with a [𝟘] one are all instances, derived
    below. *)

| ax_same_lts : forall (p q : proc),
    (forall al z, lts p al z -> lts q al z) ->
    (forall al z, lts q al z -> lts p al z) ->
    p ᴠᴀᴄᴄꜱ⊑ₐₓ q

(** *** Below a guarded sum — two rules

    [p] is below a guarded sum [g M] as soon as
    - it is below every [𝛕]-branch (the [pt] field of [must] at the sum),
    - holding the received message, it is below every input continuation
      (the [com] field) — not "[p] offers the channel", which it need not
      ([c ? 𝟘 ⊑ₘᵤₛₜᵢ 𝟘]), and
    - the pair can always move (the [ex] field).

    The last condition is what distinguishes the two rules.

    [ax_glb_tau]: the sum has a [𝛕]-branch, so it moves on its own and
    [ex] is free.  Sound by [VACCS_Precongruence.must_i_glb_tau].

    [ax_glb_settle]: otherwise, [p] must never get stuck against the
    sum's silence.  Handed any bag of messages on channels the sum does
    not offer, it settles emitting only on the bag's own channels
    ([Settles]).  The quantification over bags is not decoration:
    [c ? 𝟘 ⊑ₘᵤₛₜᵢ 𝟘] holds, and the only way to see it is that [c ? 𝟘]
    swallows the [c]-messages it is handed.  Sound by
    [VACCS_GlbStable.must_i_glb_stable] when the sum is stable, and by
    [must_i_glb_tau] when it is not.

    The common form [ax_glb_sum], with the first premise a disjunction, is
    derived below; the usual way to discharge [ax_glb_settle]'s premise
    is [ax_below_gsum]. *)

| ax_glb_tau : forall (p : proc) (M : gproc),
    (exists X, In (𝛕 • X) (summands M)) ->
    (forall X, In (𝛕 • X) (summands M) -> p ᴠᴀᴄᴄꜱ⊑ₐₓ X) ->
    (forall c Q, In (c ? Q) (summands M) ->
       forall v, ((c ! v • 𝟘) ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ (Q^v)) ->
    p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M)

| ax_glb_settle : forall (p : proc) (M : gproc),
    (forall l : list TypeOfActions, (forall c v, In (c,v) l -> ~ offers M c) ->
       Settles (chans (bag l)) (p ▷ bag l)) ->
    (forall X, In (𝛕 • X) (summands M) -> p ᴠᴀᴄᴄꜱ⊑ₐₓ X) ->
    (forall c Q, In (c ? Q) (summands M) ->
       forall v, ((c ! v • 𝟘) ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ (Q^v)) ->
    p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M)

(** ** THE MESSAGE-LAYER POOLING RULE

    [ax_share_in] pools two branches of an internal choice at a shared
    **input guard**; this pools them at a shared **pending message**, and
    the message factors out of the choice.  Sound by
    [VACCS_Precongruence.must_i_share_msg_pre].

    It is not derivable: the premise is a guarded sum and the conclusion
    a parallel composition, [≡*] does not distribute [‖] over [+], and the
    expansion law does not apply — a message is not a [gproc].  The
    converse direction *is* derivable ([ax_int_glb] over
    [ax_par]+[ax_int_l]/[ax_int_r]), so the two sides are in fact
    must-equivalent. *)

| ax_share_msg : forall (c : ChannelData) (v : ValueData) (X Y : proc),
    (g ((𝛕 • (((c ! v • 𝟘) : proc) ‖ X))
             + (𝛕 • (((c ! v • 𝟘) : proc) ‖ Y))))
      ᴠᴀᴄᴄꜱ⊑ₐₓ (((c ! v • 𝟘) : proc) ‖ ((g ((𝛕 • X) + (𝛕 • Y))) : proc))
where "p ᴠᴀᴄᴄꜱ⊑ₐₓ q" := (ax_pre p q).


(** ** Derived rules

    Each is admissible from the rules above; they are recorded here
    rather than as constructors so that the rule set stays minimal. *)

Lemma ax_glb_sum : forall (p : proc) (M : gproc),
    ((exists X, In (𝛕 • X) (summands M))
     \/ (forall l : list TypeOfActions, (forall c v, In (c,v) l -> ~ offers M c) ->
           Settles (chans (bag l)) (p ▷ bag l))) ->
    (forall X, In (𝛕 • X) (summands M) -> p ᴠᴀᴄᴄꜱ⊑ₐₓ X) ->
    (forall c Q, In (c ? Q) (summands M) ->
       forall v, ((c ! v • 𝟘) ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ (Q^v)) ->
    p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M).
Proof.
  intros p M [H|H] Ht Hi; [ apply ax_glb_tau | apply ax_glb_settle ]; assumption.
Qed.

Lemma ax_int_glb : forall (p q1 q2 : proc),
  p ᴠᴀᴄᴄꜱ⊑ₐₓ q1 -> p ᴠᴀᴄᴄꜱ⊑ₐₓ q2 -> p ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((𝛕 • q1) + (𝛕 • q2))).
Proof.
  intros p q1 q2 H1 H2. apply ax_glb_tau.
  - exists q1. left. reflexivity.
  - intros X [HX|[HX|[]]]; injection HX as <-; assumption.
  - intros c Q [HX|[HX|[]]]; discriminate HX.
Qed.

Lemma ax_refl : forall p, p ᴠᴀᴄᴄꜱ⊑ₐₓ p.
Proof. intros p. apply ax_cgr. apply cgr_refl. Qed.

Lemma ax_cgr_sym : forall p q, p ≡* q -> q ᴠᴀᴄᴄꜱ⊑ₐₓ p.
Proof. intros p q H. apply ax_cgr. apply cgr_symm. exact H. Qed.

Lemma ax_nil_par : forall p, p ≡* ((g 𝟘 : proc) ‖ p).
Proof. intro p. etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ]. Qed.

(** ** Laws derived from [ax_same_lts] *)

Lemma ax_success_l : forall R, (g (① + R)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (𝟘 + R)).
Proof.
  intro R. apply ax_same_lts; intros al z Hl; inversion Hl; subst;
    try (match goal with HH : lts (g ①) _ _ |- _ => inversion HH end);
    try (match goal with HH : lts (g 𝟘) _ _ |- _ => inversion HH end);
    apply lts_choiceR; assumption.
Qed.

Lemma ax_success_r : forall R, (g (𝟘 + R)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (① + R)).
Proof.
  intro R. apply ax_same_lts; intros al z Hl; inversion Hl; subst;
    try (match goal with HH : lts (g ①) _ _ |- _ => inversion HH end);
    try (match goal with HH : lts (g 𝟘) _ _ |- _ => inversion HH end);
    apply lts_choiceR; assumption.
Qed.

Lemma ax_expansion_l : forall M N, (g M ‖ g N) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (ext M N + ext_r N M)).
Proof.
  intros M N. apply ax_same_lts; intros al z Hl.
  - apply lts_choice2_iff. apply expansion_lts_iff. exact Hl.
  - apply expansion_lts_iff. apply lts_choice2_iff. exact Hl.
Qed.

Lemma ax_expansion_r : forall M N, (g (ext M N + ext_r N M)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g M ‖ g N).
Proof.
  intros M N. apply ax_same_lts; intros al z Hl.
  - apply expansion_lts_iff. apply lts_choice2_iff. exact Hl.
  - apply lts_choice2_iff. apply expansion_lts_iff. exact Hl.
Qed.

Lemma ax_res_normalize_l : forall M, (ν (g M)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (resg M)).
Proof.
  intro M. apply ax_same_lts; intros al z Hl; apply resg_lts_iff; exact Hl.
Qed.

Lemma ax_res_normalize_r : forall M, (g (resg M)) ᴠᴀᴄᴄꜱ⊑ₐₓ (ν (g M)).
Proof.
  intro M. apply ax_same_lts; intros al z Hl; apply resg_lts_iff; exact Hl.
Qed.


(** ** Rules derived from [ax_glb_sum] and [ax_tau_step]

    A guarded sum with a [𝛕] is below [p] as soon as each of its
    transitions is reachable from [p] by internal steps (or, for a [τ],
    its target is already derivably above [p]): the [𝛕]-branches are
    [ax_tau_run]+[ax_tau_step], and an input branch is a delivery of the
    held message ([ax_deliver]).  Five former rules follow. *)

Lemma ax_tau_run : forall (p p' : proc), p ⟹[[]] p' -> p ᴠᴀᴄᴄꜱ⊑ₐₓ p'.
Proof.
  intros p p' Hw. remember (nil : trace (ExtAct TypeOfActions)) as s eqn:Hs.
  induction Hw as [x|s0 x q y Hl Hwt IH|mu s0 x q y Hl Hwt IH].
  - apply ax_refl.
  - eapply ax_trans; [ apply ax_tau_step; exact Hl | apply IH; exact Hs ].
  - discriminate Hs.
Qed.

Lemma ax_deliver : forall (p P' : proc) c v,
  lts p (ActExt (ActIn (c,v))) P' -> ((c ! v • 𝟘) ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ P'.
Proof.
  intros p P' c v Hl. eapply ax_trans.
  - apply ax_tau_step. eapply lts_comL; [ apply lts_output | exact Hl ].
  - apply ax_cgr_sym. apply ax_nil_par.
Qed.

(** ** The general "below a guarded sum" lemma

    [ax_glb_settle]'s premise, discharged by a single internal run of
    [p] to a state that is stable, silent, and only receives on channels
    the sum offers.  Six former rules follow from it. *)

Lemma ax_below_gsum : forall (p : proc) (M : gproc),
  ((exists X, In (𝛕 • X) (summands M)) \/
   (exists p1, p ⟹[[]] p1 /\ (forall z, ~ lts p1 τ z) /\
      (forall a z, ~ lts p1 (ActExt (ActOut a)) z) /\
      (forall c v z, lts p1 (ActExt (ActIn (c,v))) z -> offers M c))) ->
  (forall X, In (𝛕 • X) (summands M) -> p ᴠᴀᴄᴄꜱ⊑ₐₓ X) ->
  (forall c Q, In (c ? Q) (summands M) -> forall v, ((c ! v • 𝟘) ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ (Q^v)) ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M).
Proof.
  intros p M [Hex | (p1 & Hw & Hnt & Hno & Hin)] Ht Hi; apply ax_glb_sum; try assumption.
  - left; exact Hex.
  - right. intros l Hl. eapply Settles_wt; [ apply fw_wt_lift; exact Hw | ].
    apply Settles_here.
    + apply stable_of_no_step. apply fw_stable_iff. split; [ exact Hnt | ].
      intros (c,v) Ha q Hq. apply bag_elem in Ha. eapply Hl; [ exact Ha | ].
      eapply Hin. exact Hq.
    + intros d w r Hr. assert (Hy : exists y, (p1 ▷ bag l) ⟶[ActOut (d,w)] y) by (exists r; exact Hr).
      apply fw_emits_iff in Hy as [ (p' & Hp') | Hm ].
      * exfalso. eapply Hno. exact Hp'.
      * exists w. exact Hm.
Qed.

(** The same, with the premises read off the sum's transitions. *)
Lemma ax_below_gsum_lts : forall (p : proc) (M : gproc),
  ((exists z, lts (g M) τ z) \/
   (exists p1, p ⟹[[]] p1 /\ (forall z, ~ lts p1 τ z) /\
      (forall a z, ~ lts p1 (ActExt (ActOut a)) z) /\
      (forall c v z, lts p1 (ActExt (ActIn (c,v))) z -> offers M c))) ->
  (forall z, lts (g M) τ z -> p ᴠᴀᴄᴄꜱ⊑ₐₓ z) ->
  (forall c v z, lts (g M) (ActExt (ActIn (c,v))) z -> ((c ! v • 𝟘) ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ z) ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M).
Proof.
  intros p M Hex Ht Hi. apply ax_below_gsum.
  - destruct Hex as [ (z & Hz) | H ]; [ left; exists z; apply gsum_tau_summand; exact Hz | right; exact H ].
  - intros X HX. apply Ht. eapply summand_lts; [ exact HX | apply lts_tau ].
  - intros c Q HQ v. apply Hi. eapply summand_lts; [ exact HQ | apply lts_input ].
Qed.

Ltac inv_choice := repeat match goal with
  | HH : lts (g (_ + _)) _ _ |- _ => apply lts_choice2_iff in HH as [HH|HH]
  | HH : lts (g (_ ? _)) τ _ |- _ => inversion HH
  | HH : lts (g (𝛕 • _)) (ActExt _) _ |- _ => inversion HH
  end.

(** A copycat may be introduced — for a whole sum of copycat guards. *)
Lemma ax_ccat_r : forall M, gCopycats M -> (g 𝟘) ᴠᴀᴄᴄꜱ⊑ₐₓ (g M).
Proof.
  intros M HM. apply ax_below_gsum.
  - right. exists (g 𝟘). split; [ apply wt_nil | ].
    split; [ intros z Hz; inversion Hz | ]. split; [ intros a z Hz; inversion Hz | ].
    intros c v z Hz; inversion Hz.
  - intros X HX. exfalso. eapply gCopycats_no_tau; [ exact HM | ].
    eapply summand_lts; [ exact HX | apply lts_tau ].
  - intros c Q HQ v.
    destruct (gCopycats_lts M HM _ _ (summand_lts _ _ HQ _ _ (@lts_input _ c v Q))) as (c' & v' & E & ->).
    injection E as -> ->. apply ax_cgr. apply cgr_par_nil.
Qed.

(** A summand's continuation may be rewritten, its guard may not. *)
Lemma ax_choice_input : forall (c : ChannelData) (P Q : proc) (G : gproc),
  (forall v, (P^v) ᴠᴀᴄᴄꜱ⊑ₐₓ (Q^v)) -> (g ((c ? P) + G)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((c ? Q) + G)).
Proof.
  intros c P Q G H. apply ax_below_gsum_lts.
  - destruct (lts_dec (g G) τ) as [ Hno | (z & Hz) ]; [ right | left; exists z; apply lts_choiceR; exact Hz ].
    exists (g ((c ? P) + G)). split; [ apply wt_nil | ].
    split; [ intros z Hz; inv_choice; eapply Hno; eassumption | ].
    split; [ intros (d,w) z Hz; eapply gsum_no_out; exact Hz | ].
    intros d w z Hz. inv_choice.
    + inversion Hz; subst. exists w, (Q^w). apply lts_choiceL. apply lts_input.
    + exists w, z. apply lts_choiceR. exact Hz.
  - intros z Hz. inv_choice. apply ax_tau_step. apply lts_choiceR. exact Hz.
  - intros d v z Hz. inv_choice.
    + inversion Hz; subst. eapply ax_trans; [ apply ax_deliver; apply lts_choiceL; apply lts_input | apply H ].
    + apply ax_deliver. apply lts_choiceR. exact Hz.
Qed.

(** Prefix distributes over choice, in an arbitrary context [R]. *)
Lemma ax_input_distrib_l : forall (c : ChannelData) (P Q : proc) (R : gproc),
    (g (((c ? P) + (c ? Q)) + R)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + R)).
Proof.
  intros c P Q R. apply ax_below_gsum_lts.
  - destruct (lts_dec (g R) τ) as [ Hno | (z & Hz) ]; [ right | left; exists z; apply lts_choiceR; exact Hz ].
    exists (g (((c ? P) + (c ? Q)) + R)). split; [ apply wt_nil | ].
    split; [ intros z Hz; inv_choice; eapply Hno; eassumption | ].
    split; [ intros (d,w) z Hz; eapply gsum_no_out; exact Hz | ].
    intros d w z Hz. inv_choice.
    + inversion Hz; subst. exists w, ((g ((𝛕 • P) + (𝛕 • Q))) ^ w). apply lts_choiceL. apply lts_input.
    + inversion Hz; subst. exists w, ((g ((𝛕 • P) + (𝛕 • Q))) ^ w). apply lts_choiceL. apply lts_input.
    + exists w, z. apply lts_choiceR. exact Hz.
  - intros z Hz. inv_choice. apply ax_tau_step. apply lts_choiceR. exact Hz.
  - intros d v z Hz. inv_choice.
    + inversion Hz; subst. simpl. apply ax_int_glb.
      * apply ax_deliver. apply lts_choiceL. apply lts_choiceL. apply lts_input.
      * apply ax_deliver. apply lts_choiceL. apply lts_choiceR. apply lts_input.
    + apply ax_deliver. apply lts_choiceR. exact Hz.
Qed.

(** τ-separation of a mixed sum. *)
Lemma ax_tau_sep_l : forall (X Y : gproc),
    (g (X + (𝛕 • (g Y)))) ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((𝛕 • (g (X + Y))) + (𝛕 • (g Y)))).
Proof.
  intros X Y.
  assert (HtY : g (X + (𝛕 • (g Y))) ᴠᴀᴄᴄꜱ⊑ₐₓ g Y)
    by (apply ax_tau_step; apply lts_choiceR; apply lts_tau).
  assert (HS : g (X + (𝛕 • (g Y))) ᴠᴀᴄᴄꜱ⊑ₐₓ g (X + Y)).
  { apply ax_below_gsum_lts.
    - destruct (lts_dec (g (X + Y)) τ) as [ Hno | (z & Hz) ]; [ right | left; exists z; exact Hz ].
      exists (g Y). split; [ eapply wt_tau; [ apply lts_choiceR; apply lts_tau | apply wt_nil ] | ].
      split; [ intros z Hz; eapply Hno; apply lts_choiceR; exact Hz | ].
      split; [ intros (d,w) z Hz; eapply gsum_no_out; exact Hz | ].
      intros d w z Hz. exists w, z. apply lts_choiceR. exact Hz.
    - intros z Hz. inv_choice.
      + apply ax_tau_step. apply lts_choiceL. exact Hz.
      + eapply ax_trans; [ exact HtY | apply ax_tau_step; exact Hz ].
    - intros d v z Hz. inv_choice.
      + apply ax_deliver. apply lts_choiceL. exact Hz.
      + eapply ax_trans; [ apply ax_par; [ apply ax_refl | exact HtY ] | apply ax_deliver; exact Hz ]. }
  apply ax_below_gsum_lts.
  - left. exists (g (X + Y)). apply lts_choiceL. apply lts_tau.
  - intros z Hz. inv_choice; inversion Hz; subst; assumption.
  - intros d v z Hz. inv_choice.
Qed.

Lemma ax_below_gsum_steps : forall (p : proc) (M : gproc),
  (exists X, In (𝛕 • X) (summands M)) ->
  (forall al q, lts (g M) al q ->
     (exists p1, p ⟹[[]] p1 /\ lts p1 al q) \/ (al = τ /\ p ᴠᴀᴄᴄꜱ⊑ₐₓ q)) ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M).
Proof.
  intros p M Hex H. apply ax_glb_tau; [ exact Hex | | ].
  - intros X HX.
    destruct (H τ X (summand_lts _ _ HX _ _ lts_tau)) as [ (p1 & Hw & Hl) | (_ & Hb) ];
      [ | exact Hb ].
    eapply ax_trans; [ apply ax_tau_run; exact Hw | apply ax_tau_step; exact Hl ].
  - intros c Q HQ v.
    destruct (H _ _ (summand_lts _ _ HQ _ _ (@lts_input _ c v Q))) as [ (p1 & Hw & Hl) | (E & _) ];
      [ | discriminate E ].
    eapply ax_trans; [ apply ax_par; [ apply ax_refl | apply ax_tau_run; exact Hw ] | ].
    apply ax_deliver. exact Hl.
Qed.

(** τ makes you safe: a guarded sum with a [τ] whose transitions are
    among [p]'s is above [p], whatever [p]'s other branches do.  The
    general law for an arbitrary right-hand side is
    [VACCS_Precongruence.must_i_sub_tau]; every use in this development
    is at a guarded sum, which is the derivable case. *)
Lemma ax_sub_tau : forall (p : proc) (M : gproc),
    (forall al z, lts ((g M) : proc) al z -> lts p al z) ->
    (exists z, lts ((g M) : proc) τ z) ->
    p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M).
Proof.
  intros p M Hsub (z & Hz). apply ax_below_gsum_steps.
  - exists z. apply gsum_tau_summand. exact Hz.
  - intros al q Hl. left. exists p. split; [ apply wt_nil | apply Hsub; exact Hl ].
Qed.

Lemma ax_choice_tau : forall (p p' : proc) (gq : gproc),
    p ᴠᴀᴄᴄꜱ⊑ₐₓ p' -> (g ((𝛕 • p) + gq)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((𝛕 • p') + gq)).
Proof.
  intros p p' gq H. apply ax_below_gsum_steps.
  - exists p'. simpl. left. reflexivity.
  - intros al q Hl. inversion Hl; subst.
    + inversion H4; subst. right. split; [ reflexivity | ].
      eapply ax_trans; [ apply ax_tau_step; apply lts_choiceL; apply lts_tau | exact H ].
    + left. exists (g ((𝛕 • p) + gq)). split; [ apply wt_nil | apply lts_choiceR; exact H4 ].
Qed.

Lemma ax_tau_sep_r : forall (X Y : gproc),
    (g ((𝛕 • (g (X + Y))) + (𝛕 • (g Y)))) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (X + (𝛕 • (g Y)))).
Proof.
  intros X Y. apply ax_below_gsum_steps.
  - exists (g Y). simpl. apply in_or_app. right. left. reflexivity.
  - intros al q Hl. left. inversion Hl; subst.
    + exists (g (X + Y)). split; [ | apply lts_choiceL; exact H3 ].
      eapply wt_tau; [ apply lts_choiceL; apply lts_tau | apply wt_nil ].
    + inversion H3; subst. exists (g ((𝛕 • (g (X + Y))) + (𝛕 • (g Y)))).
      split; [ apply wt_nil | apply lts_choiceR; apply lts_tau ].
Qed.

Lemma ax_tau_flatten_l : forall (X Y : gproc),
    gAllTau Y -> (g (X + (𝛕 • (g Y)))) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (X + Y)).
Proof.
  intros X Y HY. apply ax_below_gsum_steps.
  - destruct (gAllTau_has_tau Y HY) as (r & Hr). exists r. simpl. apply in_or_app. right.
    apply gsum_tau_summand. exact Hr.
  - intros al q Hl. left. inversion Hl; subst.
    + exists (g (X + (𝛕 • (g Y)))). split; [ apply wt_nil | apply lts_choiceL; exact H3 ].
    + exists (g Y). split; [ | exact H3 ].
      eapply wt_tau; [ apply lts_choiceR; apply lts_tau | apply wt_nil ].
Qed.

Lemma ax_tau_flatten_r : forall (X Y : gproc),
    gAllTau Y -> (g (X + Y)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (X + (𝛕 • (g Y)))).
Proof.
  intros X Y HY. apply ax_below_gsum_steps.
  - exists (g Y). simpl. apply in_or_app. right. left. reflexivity.
  - intros al q Hl. inversion Hl; subst.
    + left. exists (g (X + Y)). split; [ apply wt_nil | apply lts_choiceL; exact H3 ].
    + inversion H3; subst. right. split; [ reflexivity | ].
      apply ax_below_gsum_steps.
      * destruct (gAllTau_has_tau Y HY) as (r & Hr). exists r. apply gsum_tau_summand. exact Hr.
      * intros al q Hq. left. exists (g (X + Y)). split; [ apply wt_nil | apply lts_choiceR; exact Hq ].
Qed.

Lemma ax_input : forall (c : ChannelData) (p q : proc),
  (forall v, (p^v) ᴠᴀᴄᴄꜱ⊑ₐₓ (q^v)) -> (g (c ? p)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (c ? q)).
Proof.
  intros c p q H.
  eapply ax_trans; [ apply ax_cgr; apply cgr_choice_nil_rev | ].
  eapply ax_trans; [ | apply ax_cgr; apply cgr_choice_nil ].
  apply ax_choice_input. exact H.
Qed.

(** The guarded-sum instance of [ax_tau_step]: an internal choice is
    below each of its branches. *)
Lemma ax_int_l : forall p q, (g ((𝛕 • p) + (𝛕 • q))) ᴠᴀᴄᴄꜱ⊑ₐₓ p.
Proof. intros p q. apply ax_tau_step. apply lts_choiceL. apply lts_tau. Qed.

Lemma ax_int_r : forall p q, (g ((𝛕 • p) + (𝛕 • q))) ᴠᴀᴄᴄꜱ⊑ₐₓ q.
Proof.
  intros p q. eapply ax_trans; [ | apply (ax_int_l q p) ].
  apply ax_cgr. apply cgr_choice_com.
Qed.

(** Convex closure of acceptance families. *)
Lemma ax_convex : forall (X Y Z : gproc),
    (g ((𝛕 • (g X)) + (𝛕 • (g ((X + Y) + Z))))) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (X + Y)).
Proof.
  intros X Y Z.
  assert (HA : g ((𝛕 • (g X)) + (𝛕 • (g ((X + Y) + Z)))) ᴠᴀᴄᴄꜱ⊑ₐₓ g X) by apply ax_int_l.
  assert (HB : g ((𝛕 • (g X)) + (𝛕 • (g ((X + Y) + Z)))) ᴠᴀᴄᴄꜱ⊑ₐₓ g ((X + Y) + Z)) by apply ax_int_r.
  apply ax_below_gsum_lts.
  - destruct (lts_dec (g (X + Y)) τ) as [ Hno | (z & Hz) ]; [ right | left; exists z; exact Hz ].
    exists (g X). split; [ eapply wt_tau; [ apply lts_choiceL; apply lts_tau | apply wt_nil ] | ].
    split; [ intros z Hz; eapply Hno; apply lts_choiceL; exact Hz | ].
    split; [ intros (d,w) z Hz; eapply gsum_no_out; exact Hz | ].
    intros d w z Hz. exists w, z. apply lts_choiceL. exact Hz.
  - intros z Hz. inv_choice.
    + eapply ax_trans; [ exact HA | apply ax_tau_step; exact Hz ].
    + eapply ax_trans; [ exact HB | apply ax_tau_step; apply lts_choiceL; apply lts_choiceR; exact Hz ].
  - intros d v z Hz. inv_choice.
    + eapply ax_trans; [ apply ax_par; [ apply ax_refl | exact HA ] | apply ax_deliver; exact Hz ].
    + eapply ax_trans; [ apply ax_par; [ apply ax_refl | exact HB ] | ].
      apply ax_deliver. apply lts_choiceL. apply lts_choiceR. exact Hz.
Qed.

(** Acceptance-tree uniformity: two branches pool their continuations at
    a shared input guard, keeping the first branch's ready set. *)
Lemma ax_share_in : forall (c : ChannelData) (P Q : proc) (X' Y' : gproc),
    (g ((𝛕 • (g ((c ? P) + X'))) + (𝛕 • (g ((c ? Q) + Y')))))
      ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + X')).
Proof.
  intros c P Q X' Y'.
  assert (HA : g ((𝛕 • (g ((c ? P) + X'))) + (𝛕 • (g ((c ? Q) + Y')))) ᴠᴀᴄᴄꜱ⊑ₐₓ g ((c ? P) + X')) by apply ax_int_l.
  assert (HB : g ((𝛕 • (g ((c ? P) + X'))) + (𝛕 • (g ((c ? Q) + Y')))) ᴠᴀᴄᴄꜱ⊑ₐₓ g ((c ? Q) + Y')) by apply ax_int_r.
  apply ax_below_gsum_lts.
  - destruct (lts_dec (g X') τ) as [ Hno | (z & Hz) ]; [ right | left; exists z; apply lts_choiceR; exact Hz ].
    exists (g ((c ? P) + X')). split; [ eapply wt_tau; [ apply lts_choiceL; apply lts_tau | apply wt_nil ] | ].
    split; [ intros z Hz; inv_choice; eapply Hno; eassumption | ].
    split; [ intros (d,w) z Hz; eapply gsum_no_out; exact Hz | ].
    intros d w z Hz. inv_choice.
    + inversion Hz; subst. exists w, ((g ((𝛕 • P) + (𝛕 • Q))) ^ w). apply lts_choiceL. apply lts_input.
    + exists w, z. apply lts_choiceR. exact Hz.
  - intros z Hz. inv_choice.
    eapply ax_trans; [ exact HA | apply ax_tau_step; apply lts_choiceR; exact Hz ].
  - intros d v z Hz. inv_choice.
    + inversion Hz; subst. simpl. apply ax_int_glb.
      * eapply ax_trans; [ apply ax_par; [ apply ax_refl | exact HA ] | ].
        apply ax_deliver. apply lts_choiceL. apply lts_input.
      * eapply ax_trans; [ apply ax_par; [ apply ax_refl | exact HB ] | ].
        apply ax_deliver. apply lts_choiceL. apply lts_input.
    + eapply ax_trans; [ apply ax_par; [ apply ax_refl | exact HA ] | ].
      apply ax_deliver. apply lts_choiceR. exact Hz.
Qed.

(** A [𝛕] prefix on its own: the context of [ax_choice_tau] is [𝟘], and
    [≡*] removes it on both sides. *)
Lemma ax_tau : forall p p', p ᴠᴀᴄᴄꜱ⊑ₐₓ p' -> (g (𝛕 • p)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (𝛕 • p')).
Proof.
  intros p p' H.
  eapply ax_trans; [ apply ax_cgr_sym; apply cgr_choice_nil | ].
  eapply ax_trans; [ apply (ax_choice_tau p p' 𝟘); exact H | ].
  apply ax_cgr. apply cgr_choice_nil.
Qed.

(** [Eval_Eq 0 E] is never [None] ([VACCS_Precongruence.Eval_Eq_0_not_none]),
    so a conditional is always structurally congruent to one of its
    branches and needs no rule of its own. *)
Lemma ax_if : forall E p p' q q', p ᴠᴀᴄᴄꜱ⊑ₐₓ p' -> q ᴠᴀᴄᴄꜱ⊑ₐₓ q' ->
  (If E Then p Else q) ᴠᴀᴄᴄꜱ⊑ₐₓ (If E Then p' Else q').
Proof.
  intros E p p' q q' Hp Hq.
  destruct (Eval_Eq 0 E) as [[|]|] eqn:HE;
    [ | | exfalso; eapply Eval_Eq_0_not_none; exact HE ].
  - eapply ax_trans; [ apply ax_cgr; apply cgr_if_true; exact HE | ].
    eapply ax_trans; [ exact Hp | ].
    apply ax_cgr_sym. apply cgr_if_true. exact HE.
  - eapply ax_trans; [ apply ax_cgr; apply cgr_if_false; exact HE | ].
    eapply ax_trans; [ exact Hq | ].
    apply ax_cgr_sym. apply cgr_if_false. exact HE.
Qed.

(** And the drop whose premise says **nothing** about the discarded
    continuation: an input guard sitting beside a [𝛕]-summand may always
    be removed, because the sum's own [τ] already discharges [ex] and
    every other field is contravariant. *)

Lemma ax_drop_tau : forall (c : ChannelData) (P : proc) (G : gproc),
  (exists z, lts ((g G) : proc) τ z) ->
  ((g ((c ? P) + G)) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g G) : proc).
Proof.
  intros c P G Htau. apply ax_sub_tau; [ | exact Htau ].
  intros al z Hz. apply lts_choiceR. exact Hz.
Qed.

End VACCS_DefinitionAxiomatic.

(** ** Notations for the axiomatic preorder

    [p ᴠᴀᴄᴄꜱ⊑ₐₓ q] and [p ᴠᴀᴄᴄꜱ≂ₐₓ q], after the semantic [p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q];
    VCCS has [p ᴠᴄᴄꜱ⊑ₐₓ q].  The calculus prefix is not decoration: the two
    developments each define their own [ax_pre], and notations are global,
    so an unprefixed token would clash as soon as one file imports both.

    They are declared here, *outside* the section: a [Notation] inside a
    [Section] is discharged at [End], which is why an earlier in-section
    notation was usable only within this file.  A turnstile form is not an
    option in these files: stdpp's [base] claims a bare [x ⊑ y] for
    [sqsubseteq], and a notation reusing that symbol parses its inner
    variable at level 200, swallowing the [⊑]. *)

Notation "p ᴠᴀᴄᴄꜱ⊑ₐₓ q" := (ax_pre p q) (at level 70).
Notation "p ᴠᴀᴄᴄꜱ≂ₐₓ q" := (p ᴠᴀᴄᴄꜱ⊑ₐₓ q /\ q ᴠᴀᴄᴄꜱ⊑ₐₓ p) (at level 70).
