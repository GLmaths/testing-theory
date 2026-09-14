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

(** * [Bad]: the summand-indexed harmlessness judgement

    [VACCS_Absorb.v]'s [Harmless] is sound but provably incomplete for the
    condition it approximates — "passes no τ-stuck, non-good, [S]-refusing
    client" — and the incompleteness is not incidental.  Unfolding [must]
    at such a client [u] (where [et] is vacuous, [u] being τ-stuck) gives,
    for a guarded sum [g M], exactly

        must (g M) u  ⟺  ex ∧ pt ∧ com

    with [ex] asking for a [𝛕]-summand or a channel [u] feeds, [pt] asking
    that *every* [𝛕]-continuation pass, and [com] that *every* input branch
    pass the residue.  So the condition is:

    - some [𝛕•p ∈ summands M] with [p] bad  ⟹  [g M] bad (through [pt]);
    - [M] stable  ⟹  bad iff *every* input branch is bad at [S ∪ {c}]
      (a client may feed one channel only, so each branch really is
      forced);
    - [M] with [𝛕]-summands but none bad  ⟹  **not** bad: the client [𝟘]
      is passed.

    [Harmless] demands *all* [𝛕]-branches where one suffices — hence its
    incompleteness.  Bolting a one-branch clause onto it breaks all four of
    its preservation lemmas, because an input transition may leave through
    a *different* summand.

    ** The fix: state the clauses over the LTS, not over the syntax

    Two clauses suffice, and they need no preservation lemmas at all:
    "one [τ]-successor is bad" (through [pt]) and "[τ]-stuck, every
    emittable channel already refused, every input residue bad at
    [S ∪ {c}]" (through [ex]).  Being LTS-indexed the judgement covers
    [‖] and [ν] for free, which the normal form [Ѵⁿ (msgs l ‖ g M)] needs
    and a syntactic version did not; the syntactic clauses are recovered
    as lemmas below.

    ** It is still NOT complete, and the reason is a quantifier alternation

    The semantic condition is "for **every** such client, **some** part of
    [p] fails it", whereas [bad_step] must name *one* [τ]-successor that
    fails them *all*.  Those differ: with [p := 𝛕•A + 𝛕•B] where [A] fails
    [u₁] but passes [u₂] and [B] fails [u₂] but passes [u₁], every client
    is failed by [p] (through [pt]) while neither [A] nor [B] is bad.  No
    inductive judgement of this shape can capture a ∀∃ alternation, so
    completeness — if it is wanted — has to come from restricting the
    processes the rule is applied to, not from adding clauses. *)

From Stdlib Require Import List.
From stdpp Require Import base sets gmap.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  VACCS_Static VACCS_Erasure VACCS_Precongruence VACCS_Expansion VACCS_ReadySet
  VACCS_Copycat VACCS_Absorb VACCS_DefinitionAxiomatic VACCS_SoundnessAx
  VACCS_Canonical VACCS_Matching VACCS_Forwarder VACCS_Residues VACCS_NormalForm
  VACCS_DerivedRules.

Section VACCS_Bad.

Context `{VP : VACCS_Parameters}.

(** ** Inverting a guarded sum's transitions to a summand *)



Lemma gStable_no_tau : forall (M : gproc), gStable M -> forall q, ~ lts (g M) τ q.
Proof.
  intros M HS q Hq. eapply stable_no_lts; [ apply gStable_iff; exact HS | exact Hq ].
Qed.

(** ** The syntactic clauses, recovered

    The three clauses of the first version are derivable, so nothing is
    lost by stating the judgement over the LTS. *)

Lemma bad_tau_summand : forall S (M : gproc) p,
  In (𝛕 • p) (summands M) -> Bad S p -> Bad S (g M).
Proof.
  intros S M p Hin HB. eapply bad_step; [ | exact HB ].
  eapply summand_lts; [ exact Hin | apply lts_tau ].
Qed.

Lemma bad_gstable : forall S (M : gproc), gStable M ->
  (forall c P, In (c ? P) (summands M) ->
     forall w, Bad (fun d => S d \/ d = c) (subst_in_proc 0 w P)) ->
  Bad S (g M).
Proof.
  intros S M HstM Hbr. apply bad_stuck.
  - apply gStable_no_tau. exact HstM.
  - intros c v p' Hl. exfalso. eapply gsum_no_out. exact Hl.
  - intros c v p' Hl. exists p'. split; [ exact Hl | ].
    destruct (gsum_in_summand M c v p' Hl) as (P & Hin & He).
    subst p'. apply Hbr. exact Hin.
Qed.

(** The clause the [exists] buys, and the reason it was weakened: a
    guarded sum is bad as soon as, **at each channel it guards, ONE of
    its guards has a bad continuation** — the siblings on that channel
    need not all be bad, because [must]'s [com] field owes them all and
    a single failure suffices. *)

Lemma bad_gstable_some : forall S (M : gproc), gStable M ->
  (forall c v p', lts ((g M) : proc) (ActExt (ActIn (c,v))) p' ->
     exists P, In ((c ? P) : gproc) (summands M)
            /\ Bad (fun d => S d \/ d = c) (subst_in_proc 0 v P)) ->
  Bad S (g M).
Proof.
  intros S M HstM Hbr. apply bad_stuck.
  - apply gStable_no_tau. exact HstM.
  - intros c v p' Hl. exfalso. eapply gsum_no_out. exact Hl.
  - intros c v p' Hl. destruct (Hbr c v p' Hl) as (P & Hin & HB).
    exists (subst_in_proc 0 v P). split; [ | exact HB ].
    eapply summand_lts; [ exact Hin | apply lts_input ].
Qed.

(** * Partial completeness: the output side of [bad_stuck] is FORCED

    [Bad] is not complete in general (the ∀∃ alternation above), but its
    *output* condition is: a [τ]-stuck process that can emit on a channel
    the client is not assumed to refuse always passes some client, so the
    condition [S c] is not a restriction the judgement imposes — it is
    exactly what the semantics dictates.

    The witness is the smallest possible probe, [c ? ①]: [τ]-stuck, not
    good, refusing nothing but [c], and it must-passes **any** [τ]-stuck
    process that emits on [c] — because whatever the process does, the
    probe's only move leads to [①]. *)

Lemma probe_not_good : forall c, ~ good_VACCS (g (c ? (g ①))).
Proof. intros c H. inversion H. Qed.

Lemma probe_no_tau : forall c q, ~ lts (g (c ? (g ①))) τ q.
Proof. intros c q H. inversion H. Qed.

Lemma must_any_probe : forall (p : proc) c,
  (forall q, ~ lts p τ q) ->
  (exists v p', lts p (ActExt (ActOut (c,v))) p') ->
  p must_pass (g (c ? (g ①))).
Proof.
  intros p c Hst (v & p' & Hl).
  apply m_step.
  - apply probe_not_good.
  - eexists. eapply (ParSync (ActOut (c,v)) (ActIn (c,v)));
      [ reflexivity | exact Hl | apply lts_input ].
  - intros q Hq. exfalso. eapply Hst. exact Hq.
  - intros t' Ht'. exfalso. eapply probe_no_tau. exact Ht'.
  - intros p'' t' mu1 mu2 Hd Hl1 Hl2.
    inversion Hl2; subst. apply m_now. simpl. apply good_success.
Qed.

Theorem bad_out_forced : forall (p : proc) (S : chset) c v p',
  (forall q, ~ lts p τ q) ->
  (forall u, (forall q, ~ lts u τ q) -> ~ good_VACCS u -> RefusesIn S u ->
     ~ (p must_pass u)) ->
  lts p (ActExt (ActOut (c,v))) p' -> ~ S c -> False.
Proof.
  intros p S c v p' Hst Hsem Hl Hnc.
  eapply (Hsem (g (c ? (g ①)))).
  - apply probe_no_tau.
  - apply probe_not_good.
  - intros d x q Hd Hlq. inversion Hlq; subst. apply Hnc. exact Hd.
  - apply must_any_probe; [ exact Hst | exists v, p'; exact Hl ].
Qed.

(** * At [S = ∅] the judgement's target IS an inequation

    [Bad] approximates the semantic predicate

      "p passes no client that is τ-stuck, not good, and refuses inputs
       on S"

    and [VACCS_DropProbes.v] shows that approximation cannot be made
    exact.  At the *empty* set, though, the predicate is not merely
    approximable — it **is** a [⊑ₘᵤₛₜᵢ] statement:

        p ⊑ₘᵤₛₜᵢ 𝟘   ⟺   p fails every τ-stuck, non-good client.

    Both directions are short, and the backward one explains why: [𝟘]'s
    only obligation against a client is its [ex] field, i.e. *the client
    must be able to move on its own* — and a client that cannot is
    exactly one the hypothesis says [p] fails.  Everything else is
    vacuous ([𝟘] has no transitions at all), and [et] is the induction.

    Two consequences worth keeping.  First, this is the cleanest reading
    of what [⊑ₘᵤₛₜᵢ 𝟘] means in an asynchronous calculus, and it makes
    facts like [ccat c ⊑ₘᵤₛₜᵢ 𝟘] one-liners from a τ-stuck analysis.
    Second, it locates precisely how much of the surplus-guard problem is
    an inequation: [must_i_restrict]'s premise at [S = T = ∅] is
    [g M ⊑ₘᵤₛₜᵢ g 𝟘], whereas at a non-empty [S] the extra "refuses
    inputs on S" clause restricts the client class and no fixed process
    plays the role [𝟘] plays here. *)

Lemma nil_fails_stuck : forall u, (forall q, ~ lts u τ q) -> ~ good_VACCS u ->
  ~ ((g 𝟘) must_pass u).
Proof.
  intros u Hst Hng Hm.
  inversion Hm as [Ho | Ho Hex Hpt Het Hcom]; subst; [contradiction |].
  destruct Hex as (z & Hz). inversion Hz; subst; unfold lts_step in *; simpl in *.
  - inversion l.
  - eapply Hst. exact l.
  - inversion l1.
Qed.

Theorem below_nil_iff : forall (p : proc),
  (p ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc))
  <-> (forall u : proc, (forall q : proc, ~ lts u τ q) -> ~ good_VACCS u -> ~ (p must_pass u)).
Proof.
  intro p. split.
  - intros Hle u Hst Hng Hm. eapply nil_fails_stuck; [ exact Hst | exact Hng | ].
    apply Hle. exact Hm.
  - intros H t Hm. remember p as p0 eqn:Heq. revert Heq. revert H.
    induction Hm; intros HB Heq.
    + apply m_now. assumption.
    + subst p0. apply m_step.
      * assumption.
      * assert (Htau : exists t', lts t τ t').
        { destruct (lts_dec t τ) as [Hno | Hyes].
          - exfalso. eapply (HB t Hno nh). apply m_step; assumption.
          - exact Hyes. }
        destruct Htau as (t' & Ht'). exists (((g 𝟘) : proc) ▷ t').
        apply ParRight. exact Ht'.
      * intros p' Hp'. inversion Hp'.
      * intros t' Ht'. eapply H0; [ exact Ht' | exact HB | reflexivity ].
      * intros p' t' mu1 mu2 Hd Hp' Ht'. inversion Hp'.
Qed.

(** The sound half, restated: a [Bad] process at [∅] really is below
    [𝟘] — so [Bad] is a *derivation system for one direction of*
    [⊑ₘᵤₛₜᵢ 𝟘], which is exactly the role it plays in the drop law. *)

Corollary Bad_below_nil : forall p,
  Bad (fun _ => False) p -> p ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof.
  intros p HB. apply below_nil_iff. intros u Hst Hng Hm.
  eapply Bad_sound; [ exact Hm | exact HB | exact Hst | exact Hng | ].
  intros c x q Hc. contradiction.
Qed.

(** * [⊑ₘᵤₛₜᵢ 𝟘] is closed under external choice — but not reflected by it

    A τ-stuck client can only make a *sum* move through one of its
    summands, and every obligation the sum then owes is that summand's
    own.  So a sum of two processes below [𝟘] is below [𝟘]:

      below_nil_choice : g M ⊑ₘᵤₛₜᵢ 𝟘 -> g N ⊑ₘᵤₛₜᵢ 𝟘 -> g (M + N) ⊑ₘᵤₛₜᵢ 𝟘

    via [choice_must_left], which says a τ-stuck client passed by a sum is
    passed by one of its summands.  (Stability of the *client* is what
    makes that true — with a client τ available, [ex] could be discharged
    without either summand contributing.)

    **The converse fails**, and that is the whole difficulty of the
    surplus-guard problem: [VACCS_DropProbes.v] exhibits [M] with
    [g M ⊑ₘᵤₛₜᵢ 𝟘] whose [a]-summand is *not* below [𝟘].  So the set of
    processes below [𝟘] is closed under [+] but is not generated by its
    "atoms", and a derivation cannot be assembled summand by summand.
    Together with the [Bad] incompleteness this pins the obstruction: the
    property is a *joint* one, and every local law records only a
    sufficient condition. *)

Lemma choice_must_left : forall (M N : gproc) (u : proc),
  (forall q, ~ lts u τ q) -> (g (M + N)) must_pass u ->
  (g M) must_pass u \/ (g N) must_pass u.
Proof.
  intros M N u Hst Hm.
  inversion Hm as [Ho | Ho Hex Hpt Het Hcom]; subst.
  - left. apply m_now. exact Ho.
  - destruct Hex as (z & Hz).
    assert (Hsplit : (exists z1, inter_step ((g M) ▷ u) τ z1)
                  \/ (exists z2, inter_step ((g N) ▷ u) τ z2)).
    { inversion Hz; subst; unfold lts_step in *; simpl in *.
      - inversion l; subst.
        + left. eexists. apply ParLeft. eassumption.
        + right. eexists. apply ParLeft. eassumption.
      - exfalso. eapply Hst. exact l.
      - inversion l1; subst.
        + left. eexists. eapply ParSync; [ exact eq | eassumption | exact l2 ].
        + right. eexists. eapply ParSync; [ exact eq | eassumption | exact l2 ]. }
    destruct Hsplit as [(z1 & Hz1) | (z2 & Hz2)].
    + left. apply m_step.
      * exact Ho.
      * exists z1. exact Hz1.
      * intros p' Hp'. apply Hpt. apply lts_choiceL. exact Hp'.
      * intros t' Ht'. exfalso. eapply Hst. exact Ht'.
      * intros p' t' mu1 mu2 Hd Hp' Ht'.
        eapply Hcom; [ exact Hd | apply lts_choiceL; exact Hp' | exact Ht' ].
    + right. apply m_step.
      * exact Ho.
      * exists z2. exact Hz2.
      * intros p' Hp'. apply Hpt. apply lts_choiceR. exact Hp'.
      * intros t' Ht'. exfalso. eapply Hst. exact Ht'.
      * intros p' t' mu1 mu2 Hd Hp' Ht'.
        eapply Hcom; [ exact Hd | apply lts_choiceR; exact Hp' | exact Ht' ].
Qed.

Theorem below_nil_choice : forall (M N : gproc),
  ((g M) ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc)) -> ((g N) ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc)) ->
  (g (M + N)) ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof.
  intros M N HM HN. apply below_nil_iff. intros u Hst Hng Hm.
  destruct (choice_must_left M N u Hst Hm) as [H1|H1].
  - eapply (proj1 (below_nil_iff (g M)) HM u Hst Hng H1).
  - eapply (proj1 (below_nil_iff (g N)) HN u Hst Hng H1).
Qed.

(** ** The two engines of the "dead guard" mechanism, at an arbitrary sum

    Both facts below were used repeatedly — in [Bad_sound], in
    [BadK_sound], and in every counterexample of `VACCS_DropProbes.v` —
    but only ever in an ad hoc two-summand form, re-proved on the spot.
    Stated at an arbitrary guarded sum they are an *inversion principle*
    for a τ-stuck non-good client: it must emit, and it must emit on a
    channel the sum guards *without* killing it.

    [stuck_out_residue] is the asynchronous fact underneath: an emitting
    client is [≡*] the message beside its residue
    ([TransitionShapeForOutputSimplified]), so the residue inherits
    τ-stuckness and non-goodness. *)

Lemma stuck_out_residue : forall (t : proc) (c0 : ChannelData) (v0 : ValueData) (b0 : proc),
  (forall q, ~ lts t τ q) -> ~ good_VACCS t -> lts t ((c0 ▷ v0)!) b0 ->
  (forall q, ~ lts b0 τ q) /\ ~ good_VACCS b0.
Proof.
  intros t c0 v0 b0 Hst Hng Hl.
  assert (Hsh : t ≡* ((c0 ! v0 • 𝟘) ‖ b0))
    by (eapply TransitionShapeForOutputSimplified; exact Hl).
  split.
  - intros q Hq.
    assert (Hsc : sc_then_lts t τ ((c0 ! v0 • 𝟘) ‖ q))
      by (exists ((c0 ! v0 • 𝟘) ‖ b0); split; [ exact Hsh | apply lts_parR; exact Hq ]).
    apply Congruence_Respects_Transition in Hsc.
    destruct Hsc as (r & Hr & _). eapply Hst. exact Hr.
  - intro Hgb. apply Hng.
    eapply good_preserved_by_cgr; [ | apply cgr_symm; exact Hsh ].
    apply good_par. right. exact Hgb.
Qed.

(** A *dead* guard — one whose continuation is [𝟘] — forbids the client
    to emit on its channel: the [com] field there would owe
    [𝟘 must_pass <residue>], and the residue is still τ-stuck and not
    good.  So a dead guard turns "I do not need this channel" into "I
    forbid this channel", which is exactly what makes the counterexamples
    of `VACCS_DropProbes.v` work. *)

Lemma gsum_dead_blocks : forall (M : gproc) (c : ChannelData) (u : proc) (z : ValueData) (u' : proc),
  In ((c ? ((g 𝟘) : proc)) : gproc) (summands M) ->
  (forall q, ~ lts u τ q) -> ~ good_VACCS u ->
  ((g M) : proc) must_pass u -> ~ lts u ((c ▷ z)!) u'.
Proof.
  intros M c u z u' Hin Hst Hng Hm Hl.
  inversion Hm; subst; [ contradiction | ].
  assert (Hg : lts ((g M) : proc) ((c ▷ z) ?) ((g 𝟘) : proc)).
  { eapply summand_lts; [ exact Hin | ].
    assert (E : ((g 𝟘) : proc) ^ z = ((g 𝟘) : proc)) by reflexivity.
    rewrite <- E at 2. apply lts_input. }
  assert (Hdual : dual (ActIn (c ▷ z)) (ActOut (c ▷ z))) by (simpl; reflexivity).
  pose proof (com _ _ _ _ Hdual Hg Hl) as Hd.
  destruct (stuck_out_residue u c z u' Hst Hng Hl) as (Hst' & Hng').
  eapply nil_fails_stuck; [ exact Hst' | exact Hng' | exact Hd ].
Qed.

(** Dually, the [ex] field forces the client to emit at all: a τ-stable
    guarded sum has no move of its own, and it can never emit
    ([gsum_no_out]), so the only available step of the pair is a
    synchronisation at one of its input guards. *)

Lemma gsum_forces_emit : forall (M : gproc) (u : proc),
  (forall q, ~ lts ((g M) : proc) τ q) ->
  (forall q, ~ lts u τ q) -> ~ good_VACCS u ->
  ((g M) : proc) must_pass u ->
  exists c P z u', In ((c ? P) : gproc) (summands M) /\ lts u ((c ▷ z)!) u'.
Proof.
  intros M u HstM Hst Hng Hm.
  inversion Hm; subst; [ contradiction | ].
  destruct ex as ((x1,x2) & Hs). inversion Hs; subst.
  - exfalso. eapply HstM; eassumption.
  - exfalso. eapply Hst; eassumption.
  - destruct μ1 as [[c1 z1]|[c1 z1]].
    + destruct (gsum_in_summand M c1 z1 x1 l1) as (P & Hin & _).
      destruct μ2 as [x|x]; simpl in eq; try contradiction. subst x.
      exists c1, P, z1, x2. split; [ exact Hin | exact l2 ].
    + exfalso. eapply gsum_no_out. exact l1.
Qed.

(** The two combined.  This is the inversion principle the analysis of a
    stable sum actually uses: a τ-stuck non-good client that the sum
    passes emits on a channel the sum guards, and that guard is *live*.
    Note it says nothing about the continuation — unlike [Bad] and
    [Harmless], which recurse into it and are provably incomplete. *)

Lemma stuck_client_emits_live : forall (M : gproc) (u : proc),
  (forall q, ~ lts ((g M) : proc) τ q) ->
  (forall q, ~ lts u τ q) -> ~ good_VACCS u ->
  ((g M) : proc) must_pass u ->
  exists c P z u', In ((c ? P) : gproc) (summands M)
                /\ ~ In ((c ? ((g 𝟘) : proc)) : gproc) (summands M)
                /\ lts u ((c ▷ z)!) u'.
Proof.
  intros M u HstM Hst Hng Hm.
  destruct (gsum_forces_emit M u HstM Hst Hng Hm) as (c & P & z & u' & Hin & Hl).
  exists c, P, z, u'. split; [ exact Hin | split; [ | exact Hl ] ].
  intro Hdead. eapply gsum_dead_blocks; eassumption.
Qed.

(** Immediate consequence, and the shape a *decidable* criterion for the
    empty-bag branch would have: if every channel the sum guards is also
    dead-guarded, no client can work at all. *)

Corollary below_nil_of_all_dead : forall (M : gproc),
  (forall q, ~ lts ((g M) : proc) τ q) ->
  (forall c P, In ((c ? P) : gproc) (summands M) ->
               In ((c ? ((g 𝟘) : proc)) : gproc) (summands M)) ->
  ((g M) : proc) ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof.
  intros M HstM Hall. apply below_nil_iff. intros u Hst Hng Hm.
  destruct (stuck_client_emits_live M u HstM Hst Hng Hm)
    as (c & P & z & u' & Hin & Hnd & _).
  apply Hnd. eapply Hall. exact Hin.
Qed.

(** ** The criterion is DECIDABLE

    [gdeadb c M] tests, structurally, whether [M] has a dead guard on [c];
    [all_deadb] tests the condition above over [gchans M].  Both are
    ordinary booleans, so [below_nil_of_all_deadb] can be applied after a
    plain [destruct (all_deadb M)] — which is the point.  The residual
    obstruction to closing the completeness disjunction is *classical*
    (see the plan file): the semantic case analysis needs excluded middle,
    and only a decidable criterion avoids it. *)

Fixpoint gdeadb (c : ChannelData) (M : gproc) : bool :=
match M with
| gpr_input d (g gpr_nil) => bool_decide (d = c)
| gpr_choice M1 M2 => gdeadb c M1 || gdeadb c M2
| _ => false
end.

Lemma gdeadb_spec : forall (M : gproc) (c : ChannelData),
  gdeadb c M = true -> In ((c ? ((g 𝟘) : proc)) : gproc) (summands M).
Proof.
  induction M as [ | | d P | P | M1 IH1 M2 IH2 ]; intros c H; simpl in H; try discriminate H.
  - destruct P as [ | | | | | | Y ]; try discriminate H.
    destruct Y; try discriminate H.
    apply bool_decide_eq_true in H. subst d. simpl. left. reflexivity.
  - simpl. apply in_or_app. apply orb_true_iff in H. destruct H as [H|H].
    + left. apply IH1. exact H.
    + right. apply IH2. exact H.
Qed.

Lemma gchans_summand : forall (M : gproc) c P,
  In ((c ? P) : gproc) (summands M) -> In c (gchans M).
Proof.
  induction M as [ | | d Q | Q | M1 IH1 M2 IH2 ]; intros c P Hin; simpl in Hin.
  - destruct Hin as [H|[]]; discriminate H.
  - destruct Hin as [H|[]]; discriminate H.
  - destruct Hin as [H|[]]. injection H as H1 H2. subst. simpl. left. reflexivity.
  - destruct Hin as [H|[]]; discriminate H.
  - apply in_app_or in Hin. simpl. apply in_or_app.
    destruct Hin as [H|H]; [ left; eapply IH1 | right; eapply IH2 ]; eassumption.
Qed.

Definition all_deadb (M : gproc) : bool := forallb (fun c => gdeadb c M) (gchans M).

Corollary below_nil_of_all_deadb : forall (M : gproc),
  (forall q, ~ lts ((g M) : proc) τ q) -> all_deadb M = true ->
  ((g M) : proc) ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof.
  intros M HstM Hb. apply below_nil_of_all_dead; [ exact HstM | ].
  intros c P Hin. apply gdeadb_spec.
  unfold all_deadb in Hb. rewrite forallb_forall in Hb.
  apply Hb. eapply gchans_summand. exact Hin.
Qed.

(** ** The witness that motivated weakening [bad_stuck]

    [(c ? K) + (c ? 𝟘)], with [K] arbitrary, is below [𝟘]: the client is
    forced to emit on [c] ([gsum_forces_emit]), and the dead **sibling**
    guard then kills it ([gsum_dead_blocks]).

    The *first* version of [bad_stuck] could not certify it — it demanded
    that **every** [c]-residue be bad, and [K] need not be.  That was too
    strong: [must]'s [com] field owes all the residues at a channel at
    once, so a single failing one already refutes it.  With the [exists]
    form the instance is an ordinary [Bad], through [bad_gstable_some] —
    so the sibling-sensitivity that [Harmless]/[Bad]'s per-branch reading
    could not express is now *inside* the judgement. *)

Lemma sibling_dead_stable : forall (c1 : ChannelData) (K : proc) q,
  ~ lts ((g ((c1 ? K) + (c1 ? ((g 𝟘) : proc)))) : proc) τ q.
Proof.
  intros c1 K q H.
  inversion H; subst;
  match goal with H2 : lts (g (_ ? _)) τ _ |- _ => inversion H2 end.
Qed.

Lemma sibling_dead_below_nil : forall (c1 : ChannelData) (K : proc),
  ((g ((c1 ? K) + (c1 ? ((g 𝟘) : proc)))) : proc) ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof.
  intros c1 K. apply below_nil_of_all_dead.
  - apply sibling_dead_stable.
  - intros c P Hin. simpl in Hin.
    destruct Hin as [H|[H|[]]]; injection H as H1 H2; subst;
      simpl; right; left; reflexivity.
Qed.

Lemma sibling_dead_Bad : forall (S : chset) (c1 : ChannelData) (K : proc),
  Bad S ((g ((c1 ? K) + (c1 ? ((g 𝟘) : proc)))) : proc).
Proof.
  intros S c1 K. apply bad_gstable_some.
  - simpl. split; exact I.
  - intros c v p' Hl. exists ((g 𝟘) : proc).
    assert (Hc : c1 = c).
    { inversion Hl; subst;
        match goal with H : lts (g (_ ? _)) _ _ |- _ => inversion H end;
        reflexivity. }
    subst c1. split; [ simpl; right; left; reflexivity | apply bad_nil_any ].
Qed.

(** The negative half, in general form: a live message is never [Bad] at
    a set that misses its channel.  It is what shows the *per-branch*
    reading could not have worked — [(c ? K) + (c ? 𝟘)] with [K] a
    message on a third channel is below [𝟘], yet [K] itself is not
    [Bad] at any set the client is known to refuse. *)

Lemma msg_not_Bad : forall (S : chset) (d : Channel) (y : Value),
  ~ S (cst d) -> ~ Bad S (((cst d) ! (cst y) • 𝟘) : proc).
Proof.
  intros S d y Hne HB. inversion HB; subst.
  - match goal with H : lts _ τ _ |- _ => inversion H end.
  - apply Hne.
    match goal with H : forall _ _ _, lts _ (ActExt (ActOut _)) _ -> _ |- _ =>
      eapply H end.
    apply lts_output.
Qed.

(** ** …and the RULE gets strictly stronger

    [ax_input_drop] discards an input summand whose continuation is
    [Bad].  With the sibling clause a *nested* sum qualifies, and the old
    per-branch clause provably could not license it: it would have asked
    for [Bad {c,d} K], which [msg_not_Bad] refutes as soon as [K] emits
    on a third channel. *)

Theorem ax_nested_sibling_drop : forall (c d : ChannelData) (K : proc) (G : gproc),
  Static K -> gStatic G ->
  ((g ((c ? ((g ((d ? K) + (d ? ((g 𝟘) : proc)))) : proc)) + G)) : proc)
    ᴠᴀᴄᴄꜱ⊑ₐₓ ((g G) : proc).
Proof.
  intros c d K G HK HG.
  apply ax_input_drop; [ repeat constructor; assumption | ].
  intro v. simpl. apply sibling_dead_Bad.
Qed.

(** ** …and a drop that NO certificate can license

    [ax_drop_tau] removes an input guard beside a [𝛕]-summand with a
    premise that says nothing about the discarded continuation.  The
    certificate-based rules cannot: [ax_input_drop] would need
    [Bad {c} K], refuted by [msg_not_Bad] as soon as [K] emits on another
    channel, and [ax_restrict] requires the sum to be **stable**, which it
    is not.  So the two families are complementary — a certificate for the
    stable case, a free ride for the unstable one. *)

Theorem ax_tau_beside_drop : forall (c : ChannelData) (K : proc),
  ((g ((c ? K) + (𝛕 • ((g 𝟘) : proc)))) : proc)
    ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (𝛕 • ((g 𝟘) : proc))) : proc).
Proof.
  intros c K. apply ax_drop_tau. exists ((g 𝟘) : proc). apply lts_tau.
Qed.

Lemma tau_beside_not_bad : forall (c : ChannelData) (d : Channel) (y : Value),
  ~ (fun x => x = c) (cst d) ->
  ~ Bad (fun x => x = c) (((cst d) ! (cst y) • 𝟘) : proc).
Proof. intros c d y. apply msg_not_Bad. Qed.

(** ** The same defect was in [BadK], and fixing it makes the instance
       DERIVABLE, not merely true

    [bk_kill] carried the same universal clause, and had to be weakened
    the same way — but not to an [exists]: [BadK_sound] inducts on the
    **judgement**, and Coq generates no induction hypothesis for a
    recursive occurrence under an [exists].  The clause therefore names
    the choice by a **function** [f : ValueData -> proc], so the
    recursive occurrence sits under an ordinary [forall].  Nothing
    classical is smuggled in: [f] is supplied by whoever builds the
    derivation.

    The payoff is a *derivation*, through [ax_restrict] at [M' := 𝟘] —
    where before only the semantic [sibling_dead_below_nil] was
    available. *)

Lemma badk_nil_any : forall S D, BadK S D ((g 𝟘) : proc).
Proof.
  intros S D. apply bk_stuck;
    [ intros q Hq | intros d x q Hq | intros d x q Hq ]; inversion Hq.
Qed.

Lemma sibling_dead_BadK : forall (c1 : ChannelData) (K : proc) (S D : chset),
  BadK S D ((g ((c1 ? K) + (c1 ? ((g 𝟘) : proc)))) : proc).
Proof.
  intros c1 K S D.
  eapply (bk_kill _ _ c1 _ (fun _ => ((g 𝟘) : proc))).
  - intro x. apply lts_choiceR.
    assert (E : ((g 𝟘) : proc) ^ x = ((g 𝟘) : proc)) by reflexivity.
    rewrite <- E at 2. apply lts_input.
  - intro x. apply badk_nil_any.
  - apply bk_stuck.
    + apply sibling_dead_stable.
    + intros d x q Hq. exfalso. eapply gsum_no_out. exact Hq.
    + intros d x q Hq. right.
      inversion Hq; subst;
        match goal with H : lts (g (_ ? _)) _ _ |- _ => inversion H end;
        reflexivity.
Qed.

Theorem ax_sibling_dead_below_nil : forall (c1 : ChannelData) (K : proc),
  Static K ->
  ((g ((c1 ? K) + (c1 ? ((g 𝟘) : proc)))) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g 𝟘) : proc).
Proof.
  intros c1 K HK. apply ax_restrict.
  - repeat constructor; assumption.
  - repeat constructor.
  - intros al q Hq. exfalso. inversion Hq.
  - apply sibling_dead_stable.
  - apply sibling_dead_BadK.
Qed.

(** And the decidable criterion of [below_nil_of_all_deadb] is now a
    *decidable fragment of [Bad]* rather than something beside it: with
    the [exists] clause, "every guarded channel is also dead-guarded"
    certifies [Bad] at any set.  The direct proof through
    [stuck_client_emits_live] is kept because it is what makes the
    criterion checkable by a plain [destruct] on a boolean; this lemma
    records that the two agree. *)

Lemma bad_of_all_dead : forall S (M : gproc), gStable M ->
  (forall c P, In ((c ? P) : gproc) (summands M) ->
               In ((c ? ((g 𝟘) : proc)) : gproc) (summands M)) ->
  Bad S ((g M) : proc).
Proof.
  intros S M HstM Hall. apply bad_gstable_some; [ exact HstM | ].
  intros c v p' Hl. destruct (gsum_in_summand M c v p' Hl) as (P & Hin & _).
  exists ((g 𝟘) : proc). split; [ apply Hall with (P := P); exact Hin | apply bad_nil_any ].
Qed.

(** ** Message rigidity, at an arbitrary channel

    `VACCS_DropProbes.v` proves [𝟘 ⋢ₘᵤₛₜᵢ (a!v•𝟘)] at the constant
    channel its own section fixes.  The argument is generic, and the
    general form is what the descent analysis of `VACCS_Matching.v`
    actually needs — it is the reason a **swallowing** guard does not
    license the descent, where a **returning** one does.

    The probe is the smallest possible: [𝛕•① + c?𝟘] succeeds on its own
    (its [𝛕] reaches [①]), so [𝟘] passes it; the message does not,
    because its [com] at [c] leaves [𝟘] facing [𝟘], with nothing left to
    move.  Absorbing a message is therefore **observable** — which is the
    half of message rigidity that is easy to forget. *)

Definition TSg (c : ChannelData) : proc :=
  g ((𝛕 • ((g ①) : proc)) + (c ? ((g 𝟘) : proc))).

Lemma TSg_not_good : forall c, ~ good_VACCS (TSg c).
Proof.
  intros c Hg. unfold TSg in Hg. inversion Hg; subst.
  match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
Qed.

Lemma nil_passes_TSg : forall c, ((g 𝟘) : proc) must_pass (TSg c).
Proof.
  intro c. apply m_step.
  - apply TSg_not_good.
  - exists (((g 𝟘) : proc) ▷ ((g ①) : proc)). apply ParRight.
    unfold TSg. apply lts_choiceL. apply lts_tau.
  - intros p' Hp'. inversion Hp'.
  - intros t' Ht'. unfold TSg in Ht'. inversion Ht'; subst.
    + inversion H3; subst. apply m_now. simpl. constructor.
    + inversion H3.
  - intros p' t' mu1 mu2 Hd Hp' Ht'. inversion Hp'.
Qed.

Lemma msg_fails_TSg : forall (c : ChannelData) (v : ValueData),
  ~ (((c ! v • 𝟘) : proc) must_pass (TSg c)).
Proof.
  intros c v Hm. inversion Hm; subst.
  - eapply TSg_not_good. eassumption.
  - assert (Hbad : ((g 𝟘) : proc) must_pass ((g 𝟘) : proc)).
    { match goal with Hc : forall _ _ _ _, _ |- _ =>
        eapply (Hc ((g 𝟘) : proc) ((g 𝟘) : proc) (ActOut (c,v)) (ActIn (c,v)))
      end.
      - simpl. reflexivity.
      - apply lts_output.
      - unfold TSg. apply lts_choiceR.
        assert (E : ((g 𝟘) : proc) ^ v = ((g 𝟘) : proc)) by reflexivity.
        rewrite <- E at 2. apply lts_input. }
    eapply nil_fails_stuck; [ | | exact Hbad ].
    + intros q Hq. inversion Hq.
    + intro Hg. inversion Hg.
Qed.

Theorem nil_not_below_msg_gen : forall (c : ChannelData) (v : ValueData),
  ~ (((g 𝟘) : proc) ⊑ₘᵤₛₜᵢ ((c ! v • 𝟘) : proc)).
Proof.
  intros c v Hle. eapply msg_fails_TSg. apply Hle. apply nil_passes_TSg.
Qed.

(** At both sets empty, [BadK] certifies an inequation of the theory —
    the same reading [below_nil_iff] gives, now with a judgement strong
    enough to reach `VACCS_DropProbes.v`'s counterexample, which [Bad]
    provably cannot. *)

Corollary BadK_below_nil : forall p,
  BadK (fun _ => False) (fun _ => False) p -> p ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof.
  intros p HB. apply below_nil_iff. intros u Hst Hng Hm.
  eapply BadK_sound; [ exact HB | exact Hm | exact Hst | exact Hng | | ].
  - intros c x q Hc. contradiction.
  - intros c Hc. contradiction.
Qed.

(** ** An unstable left configuration need NOT have the right's bag

    [VACCS_NormalForm.bags_agree] forces the two message bags to be equal,
    but only when the **left configuration is τ-stable**.  That hypothesis
    is not slack: written with [VACCS_NormalForm.msgs], the left-hand side
    below is [msgs [(c,v)] ‖ g (c ? 𝟘)] and the right-hand side is
    [msgs [] ‖ g 𝟘] (up to [≡*]) — so a *one-message* bag sits below an
    *empty* one.

    The reason is exactly the instability: the pending message is consumed
    by the guard rather than emitted, so no trace ever exposes it, and the
    whole configuration is below [𝟘] by [below_nil_iff] — its only [τ]
    lands on a process with no transitions at all, which fails every
    τ-stuck non-good client.

    Consequence for the completeness assembly: matching the two normal
    forms' bags, like Phase A, is available only for a stable left.  Both
    are the *same* gap, and this fixes its shape: for an unstable left the
    configuration-comparison format [Ѵⁿ (msgs l ‖ ·)] versus
    [Ѵⁿ (msgs l ‖ ·)] — same [n], same [l] — is simply not attainable. *)

Lemma unstable_delivery_below_nil : forall (c : ChannelData) (v : ValueData),
  ((((c ! v • 𝟘) : proc) ‖ ((g 𝟘) : proc)) ‖ g (c ? ((g 𝟘) : proc)))
    ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof.
  intros c v. apply below_nil_iff. intros u Hst Hng Hm.
  inversion Hm; subst; [ contradiction | ].
  assert (Hstep : lts ((((c ! v • 𝟘) : proc) ‖ ((g 𝟘) : proc)) ‖ g (c ? ((g 𝟘) : proc))) τ
                      ((((g 𝟘) : proc) ‖ ((g 𝟘) : proc))
                       ‖ (subst_in_proc 0 v ((g 𝟘) : proc))))
    by (eapply lts_comL; [ apply lts_parL; apply lts_output | apply lts_input ]).
  simpl in Hstep.
  pose proof (pt _ Hstep) as Hd.
  apply (nil_fails_stuck u Hst Hng).
  assert (Hc : ((((g 𝟘) : proc) ‖ ((g 𝟘) : proc)) ‖ ((g 𝟘) : proc)) ≡* ((g 𝟘) : proc))
    by (etransitivity; [ apply cgr_par_nil | apply cgr_par_nil ]).
  apply (proj2 (must_i_cgr _ _ Hc)). exact Hd.
Qed.

(** …and yet this instance **is** derivable — by [ax_tau_step], stepping to
    the delivery's target, which here is [≡*]-equal to the right-hand side.

    So the unstable case is not uniformly out of reach: what is out of
    reach is the *configuration-comparison format*, not the inequation.
    The route that does work on it, [ax_tau_step] + [ax_trans], is
    available exactly when **some** τ-successor is itself below the
    right-hand side — and that is not implied by [p ⊑ₘᵤₛₜᵢ q] (a τ-reduct
    passes strictly more tests), which is the same ∀∃ alternation that has
    defeated every other attack on this gap. *)
Lemma ax_unstable_delivery_below_nil : forall (c : ChannelData) (v : ValueData),
  ((((c ! v • 𝟘) : proc) ‖ ((g 𝟘) : proc)) ‖ g (c ? ((g 𝟘) : proc)))
    ᴠᴀᴄᴄꜱ⊑ₐₓ ((g 𝟘) : proc).
Proof.
  intros c v.
  assert (Hstep : lts ((((c ! v • 𝟘) : proc) ‖ ((g 𝟘) : proc)) ‖ g (c ? ((g 𝟘) : proc))) τ
                      ((((g 𝟘) : proc) ‖ ((g 𝟘) : proc))
                       ‖ (subst_in_proc 0 v ((g 𝟘) : proc))))
    by (eapply lts_comL; [ apply lts_parL; apply lts_output | apply lts_input ]).
  simpl in Hstep.
  eapply ax_trans; [ apply ax_tau_step; exact Hstep | ].
  apply ax_cgr. etransitivity; [ apply cgr_par_nil | apply cgr_par_nil ].
Qed.

(** ** [𝟘] is NOT below an arbitrary guarded sum — a dead guard suffices

    [VACCS_Copycat.must_i_nil_below_copycats] gives [𝟘 ⊑ₘᵤₛₜᵢ g M] for a
    sum of **copycats**, and that is what discharges the source-only
    disjunct of [VACCS_Matching.CfgDisjunctionSource] on that class.  The
    hypothesis is not slack: already the one-summand **dead** guard
    [c ? 𝟘] is not above [𝟘].

    The probe is the smallest possible.  [TD c v] is a pending message
    beside a client-side guard that turns it into success:

        TD := (c ! v • 𝟘) ‖ (c ? ①)

    [𝟘] passes it — the client's own synchronisation reaches [①] — while
    [c ? 𝟘] **steals the message** and leaves the client with nothing to
    do: after the [com] at [c] the residue is [𝟘 ‖ (c ? ①)], which is
    τ-stuck and not good, so [nil_fails_stuck] applies.

    So absorbing a message is observable from *both* sides: the other
    half is [nil_not_below_msg_gen] (a message cannot be added), this one
    says a guard that swallows one cannot be added either.  Together they
    say why the [K ⊑ₘᵤₛₜᵢ g M] premise of the source disjunct genuinely
    needs the copycat structure — returning the message — and not merely
    "the residue does nothing". *)

Definition TD (c : ChannelData) (v : ValueData) : proc :=
  ((c ! v • 𝟘) : proc) ‖ ((g (c ? ((g ①) : proc))) : proc).

Lemma TD_not_good : forall c v, ~ good_VACCS (TD c v).
Proof.
  intros c v Hg. unfold TD in Hg. inversion Hg; subst.
  match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
Qed.

Lemma TD_tau_inv : forall c v t',
  lts (TD c v) τ t' -> t' = (((g 𝟘) : proc) ‖ ((g ①) : proc)).
Proof.
  intros c v t' Hl. unfold TD in Hl. inversion Hl; subst.
  - match goal with H : lts (g (_ ? _)) _ _ |- _ => inversion H; subst end.
    match goal with H : lts (_ ! _ • 𝟘) _ _ |- _ => inversion H; subst end.
    reflexivity.
  - match goal with H : lts (g (_ ? _)) (ActExt (ActOut _)) _ |- _ => inversion H end.
  - match goal with H : lts (_ ! _ • 𝟘) τ _ |- _ => inversion H end.
  - match goal with H : lts (g (_ ? _)) τ _ |- _ => inversion H end.
Qed.

Lemma nil_passes_TD : forall c v, ((g 𝟘) : proc) must_pass (TD c v).
Proof.
  intros c v. apply m_step.
  - apply TD_not_good.
  - exists (((g 𝟘) : proc) ▷ (((g 𝟘) : proc) ‖ ((g ①) : proc))).
    apply ParRight. unfold TD.
    eapply lts_comL; [ apply lts_output | ].
    assert (E : ((g ①) : proc) ^ v = ((g ①) : proc)) by reflexivity.
    rewrite <- E at 2. apply lts_input.
  - intros p' Hp'. inversion Hp'.
  - intros t' Ht'. rewrite (TD_tau_inv c v t' Ht').
    apply m_now. apply good_par. right. constructor.
  - intros p' t' mu1 mu2 Hd Hp' Ht'. inversion Hp'.
Qed.

(** Le refus vaut dès qu'**un sommant** est mort : [must]'s [com] doit les
    résidus d'un canal *tous à la fois*, donc le sommant mort suffit à le
    faire échouer, quels que soient ses frères.  [summand_lts] relève sa
    transition à la somme entière. *)

Lemma dead_summand_fails_TD : forall (M : gproc) (c : ChannelData) (v : ValueData),
  In ((c ? ((g 𝟘) : proc)) : gproc) (summands M) ->
  ~ (((g M) : proc) must_pass (TD c v)).
Proof.
  intros M c v Hin Hm.
  assert (Hsrv : lts ((g M) : proc) (ActExt (ActIn (c,v))) ((g 𝟘) : proc)).
  { eapply summand_lts; [ exact Hin | ].
    assert (E : ((g 𝟘) : proc) ^ v = ((g 𝟘) : proc)) by reflexivity.
    rewrite <- E at 2. apply lts_input. }
  inversion Hm; subst.
  - eapply TD_not_good. eassumption.
  - assert (Hbad : ((g 𝟘) : proc) must_pass
                     (((g 𝟘) : proc) ‖ ((g (c ? ((g ①) : proc))) : proc))).
    { match goal with Hc : forall _ _ _ _, _ |- _ =>
        eapply (Hc ((g 𝟘) : proc)
                   (((g 𝟘) : proc) ‖ ((g (c ? ((g ①) : proc))) : proc))
                   (ActIn (c,v)) (ActOut (c,v)))
      end.
      - simpl. reflexivity.
      - exact Hsrv.
      - unfold TD. apply lts_parL. apply lts_output. }
    eapply nil_fails_stuck; [ | | exact Hbad ].
    + intros q Hq. inversion Hq; subst.
      * match goal with H : lts ((g 𝟘) : proc) (ActExt _) _ |- _ => inversion H end.
      * match goal with H : lts ((g 𝟘) : proc) (ActExt _) _ |- _ => inversion H end.
      * match goal with H : lts ((g 𝟘) : proc) τ _ |- _ => inversion H end.
      * match goal with H : lts (g (_ ? _)) τ _ |- _ => inversion H end.
    + intro Hg. inversion Hg; subst.
      match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
Qed.

(** **Une seule garde morte suffit** : la classe copycat de
    [must_i_nil_below_copycats] ne peut donc pas être relâchée en
    « contient au moins un copycat » — un sommant mort quelque part dans
    la somme réfute déjà [𝟘 ⊑ₘᵤₛₜᵢ g M]. *)

Theorem nil_not_below_dead_summand : forall (M : gproc) (c : ChannelData) (v : ValueData),
  In ((c ? ((g 𝟘) : proc)) : gproc) (summands M) ->
  ~ (((g 𝟘) : proc) ⊑ₘᵤₛₜᵢ ((g M) : proc)).
Proof.
  intros M c v Hin Hle.
  apply (dead_summand_fails_TD M c v Hin). apply Hle. apply nil_passes_TD.
Qed.

Corollary nil_not_below_dead_guard : forall (c : ChannelData) (v : ValueData),
  ~ (((g 𝟘) : proc) ⊑ₘᵤₛₜᵢ ((g (c ? ((g 𝟘) : proc))) : proc)).
Proof.
  intros c v. apply (nil_not_below_dead_summand (c ? ((g 𝟘) : proc)) c v).
  simpl. left. reflexivity.
Qed.

(** ** …et les branches [𝛕] d'une somme NE SE LAISSENT PAS mettre en commun
       vers le bas

    [VACCS_Matching.left_ichoice_below] met le choix interne des
    τ-successeurs **sous** le processus — mais sous l'hypothèse qu'il n'a
    **aucune transition externe**.  Cette hypothèse n'est pas du gras, et
    voici pourquoi : une garde d'entrée porte une obligation [com] que le
    choix interne n'a pas, donc le choix passe *plus* de tests, et
    l'inclusion tombe dans ce sens-là.

    Le témoin est minimal — un [𝛕]-sommant et une garde **morte** — et il
    se ramène à [nil_not_below_dead_summand] : le seul τ-successeur est
    [𝟘], le choix interne à un membre lui est [≂ₘᵤₛₜᵢ]-égal, et la garde
    morte réfute [𝟘 ⊑ₘᵤₛₜᵢ g M].

    Conséquence pour la loi manquante : **elle ne peut pas être « mettre
    en commun les τ-branches »**.  [ax_share_msg] réussit sur les
    branches [𝛕] d'une *configuration* parce que le sac, qui porte les
    offres externes, est factorisé hors du choix ; ici les offres
    externes sont des **gardes**, et rien ne les factorise.  La loi
    cherchée doit donc traiter les délivrances **sans jeter les offres
    externes**. *)

Definition PoolM (c : ChannelData) : gproc :=
  (𝛕 • ((g (𝟘 : gproc)) : proc)) + (c ? ((g (𝟘 : gproc)) : proc)).

Lemma PoolM_tau : forall c, lts ((g (PoolM c)) : proc) τ ((g (𝟘 : gproc)) : proc).
Proof. intros c. unfold PoolM. apply lts_choiceL. apply lts_tau. Qed.

Lemma PoolM_tau_uniq : forall c z,
  lts ((g (PoolM c)) : proc) τ z -> z = ((g (𝟘 : gproc)) : proc).
Proof.
  intros c z Hz. unfold PoolM in Hz.
  inversion Hz; subst.
  - inversion H3; subst. reflexivity.
  - inversion H3.
Qed.

Lemma nil_eq_ichoice_nil :
  (((g (𝟘 : gproc)) : proc) ⊑ₘᵤₛₜᵢ ((g (ichoice [((g (𝟘 : gproc)) : proc)])) : proc)).
Proof.
  apply soundness_ax. apply ax_ichoice_glb; [ discriminate | ].
  intros p Hp. simpl in Hp. destruct Hp as [Heq | []]. subst p. apply ax_refl.
Qed.

Theorem tau_branches_not_poolable : forall (c : ChannelData) (v : ValueData),
     lts ((g (PoolM c)) : proc) τ ((g (𝟘 : gproc)) : proc)
  /\ (forall z, lts ((g (PoolM c)) : proc) τ z -> z = ((g (𝟘 : gproc)) : proc))
  /\ ~ (((g (ichoice [((g (𝟘 : gproc)) : proc)])) : proc)
          ⊑ₘᵤₛₜᵢ ((g (PoolM c)) : proc)).
Proof.
  intros c v. split; [ apply PoolM_tau | split; [ apply PoolM_tau_uniq | ]].
  intros Hle.
  apply (nil_not_below_dead_summand (PoolM c) c v).
  - unfold PoolM. simpl. right. left. reflexivity.
  - intros t Ht. apply Hle. apply nil_eq_ichoice_nil. exact Ht.
Qed.

(* ===================================================================== *)


(** [SelfRet M] : une garde de [M] a une continuation qui **peut émettre
    sur la voie de cette garde même**.  C'est exactement la négation du
    critère de [cfg_local_of_no_return], et c'est décidable : par
    [gsum_in_summand] la condition ne porte que sur les **sommants**, en
    nombre fini, et [ochans_subst] la rend indépendante de la valeur
    reçue. *)

Definition SelfRet (M : gproc) : Prop :=
  exists c v P', lts ((g M) : proc) (ActExt (ActIn (c,v))) P' /\ In c (ochans P').


(** ** La disjonction se scinde en DEUX obligations complémentaires

    **Rectification.**  Une première version demandait le *second*
    disjoint dès que le critère échoue — c'est-à-dire aussi quand [M]
    porte un [𝛕]-sommant.  Cette prémisse est **fausse**, et
    [selfret_case_premise_is_false] l'exhibe : avec [M := 𝛕 • 𝟘] la
    configuration a bien un [τ], mais [M] n'a **aucune garde d'entrée**,
    donc le second disjoint — qui réclame une délivrance — est
    insatisfiable.  La réduction était vacue.

    La bonne forme sépare les deux cas décidables, et ils sont
    complémentaires :

    - [M] porte un [𝛕]-sommant → il faut le **premier** disjoint,
      c'est-à-dire l'annulation du sac.  Noter que le contre-exemple
      connu à l'annulation ([VACCS_Matching.bagsem_does_not_descend],
      sur [MCert]) **ne s'applique pas ici** : [MCert] est τ-stable ;
    - [M] est τ-stable et une continuation peut rendre le message de sa
      propre garde ([SelfRet]) → il faut le **second** ;
    - [M] est τ-stable et aucune ne le peut → [cfg_local_of_no_return]
      donne le premier, sans rien demander.

    L'analyse de cas est constructive ([lts_dec], [selfret_dec]). *)

Lemma selfret_case_premise_is_false : forall (c : ChannelData) (v : ValueData),
  ~ (forall (l : list TypeOfActions) (M N : gproc), gStatic M -> gStatic N ->
       (SelfRet M \/ (exists z, lts ((g M) : proc) τ z)) ->
       (exists z, (((g M) : proc) ▷ bag l) ⟶ z) ->
       ((msgs l ‖ ((g M) : proc)) ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
       (exists c0 v0 l0 Mc,
          Permutation l ((c0,v0) :: l0)
          /\ lts ((g M) : proc) (ActExt (ActIn (c0,v0))) Mc
          /\ Mc ⊑ₘᵤₛₜᵢ (((c0 ! v0 • 𝟘) : proc) ‖ ((g N) : proc)))).
Proof.
  intros c v H.
  assert (Hst : gStatic ((𝛕 • ((g (𝟘 : gproc)) : proc)) : gproc))
    by (repeat constructor).
  assert (Htau : exists z, lts ((g ((𝛕 • ((g (𝟘 : gproc)) : proc)) : gproc)) : proc) τ z)
    by (exists ((g (𝟘 : gproc)) : proc); apply lts_tau).
  assert (Hcfg : exists z,
    (((g ((𝛕 • ((g (𝟘 : gproc)) : proc)) : gproc)) : proc) ▷ bag [(c ▷ v)]) ⟶ z).
  { exists (((g (𝟘 : gproc)) : proc) ▷ bag [(c ▷ v)]).
    apply fw_tau_left. apply lts_tau. }
  assert (Hsem : (msgs [(c ▷ v)] ‖ ((g ((𝛕 • ((g (𝟘 : gproc)) : proc)) : gproc)) : proc))
                   ⊑ₘᵤₛₜᵢ (msgs [(c ▷ v)] ‖ ((g (𝟘 : gproc)) : proc))).
  { apply must_i_par_compat_r. apply soundness_ax.
    apply ax_tau_step with (p' := ((g (𝟘 : gproc)) : proc)). apply lts_tau. }
  destruct (H [(c ▷ v)] ((𝛕 • ((g (𝟘 : gproc)) : proc)) : gproc) (𝟘 : gproc)
              Hst ltac:(constructor) (or_intror Htau) Hcfg Hsem)
    as (c0 & v0 & l0 & Mc & Hp & Hin & Hb).
  inversion Hin.
Qed.



(* ===================================================================== *)
(** * LE CRITÈRE RAFFINÉ : SEULES LES GARDES SUR LES CANAUX DU SAC COMPTENT

    [SelfRet] est *suffisant* pour que le sac ne s'annule pas, jamais
    nécessaire : [VACCS_DropProbes.MSelf] est [SelfRet] par une garde sur
    un canal **absent du sac**, et son sac s'annule pourtant.  Le critère
    regardait les mauvaises gardes.

    La correction s'appuie sur
    [VACCS_NormalForm.fw_conservation_bounded] : le long d'une trace sans
    entrée, **tout ce que le processus consomme venait du sac initial**,
    donc la première entrée du run projeté — la seule que l'inversion
    consulte — porte sur un canal du sac.

    [SelfRetBag l M] est donc [SelfRet] restreint aux canaux de [l], et
    il est décidable pour la même raison : la condition ne porte que sur
    les **sommants**, en nombre fini, et [ochans_subst] la rend
    indépendante de la valeur reçue. *)

Definition SelfRetOn (c : ChannelData) (a : gproc) : Prop :=
  exists P, a = (c ? P) /\ In c (ochans P).


Definition SelfRetBag (l : list TypeOfActions) (M : gproc) : Prop :=
  exists c v, In (c,v) l /\ Exists (SelfRetOn c) (summands M).


(** Il est bien **plus faible** que [SelfRet] — inclusion prouvée
    ci-dessous, stricte par [VACCS_DropProbes.MSelf_not_selfretbag]. *)

Lemma selfretbag_selfret : forall l M, SelfRetBag l M -> SelfRet M.
Proof.
  intros l M (c & v & Hin & Hex).
  apply Exists_exists in Hex. destruct Hex as (aa & Hina & (P & Heq & Hoc)).
  subst aa. apply list_elem_of_In in Hina.
  exists c, v, (P ^ v). split.
  - eapply summand_lts; [ exact Hina | apply lts_input ].
  - rewrite ochans_subst. exact Hoc.
Qed.



(** ** ★ LES DEUX CRITÈRES RELATIFS AU SAC, RÉUNIS EN UNE DICHOTOMIE

    Deux routes ferment l'annulation du sac, et elles sont
    **incomparables** :

    - [cfg_derivable_or_selfretbag] — la somme gauche est τ-stable et
      aucune de ses gardes **sur une voie du sac** ne rend son message
      ([SelfRetBag]).  Les émissions sont permises ;
    - [VACCS_Matching.msgs_cancel_no_output_bag] — la somme gauche
      n'émet sur **aucune voie du sac**.  Les [𝛕]-sommants sont permis.

    La seconde entraîne la négation de [SelfRetBag] (une garde
    auto-rendante sur [c] met [c] dans [ochans] de la somme), mais pas
    l'inverse : une somme τ-stable peut fort bien émettre sur une voie
    du sac ([VACCS_DropProbes.MCert]).

    Les deux tests étant décidables, on les enchaîne et l'on n'exhibe
    que le **résidu** : une somme qui, *à la fois*, porte un
    [𝛕]-sommant ou une garde auto-rendante, **et** peut émettre sur une
    voie du sac. *)

Lemma gochans_summand_in : forall (M a : gproc) (c : ChannelData),
  In a (summands M) -> In c (gochans a) -> In c (gochans M).
Proof.
  induction M as [ | | d P | p | M1 IH1 M2 IH2 ]; intros a c Hin Hc; simpl in *;
    try (destruct Hin as [He|[]]; subst a; exact Hc).
  apply in_app_or in Hin as [H|H]; apply in_or_app;
    [ left; eapply IH1 | right; eapply IH2 ]; eassumption.
Qed.

Definition MeetsBag (l : list TypeOfActions) (M : gproc) : Prop :=
  exists c vv, In (c,vv) l /\ In c (ochans ((g M) : proc)).

(** Une garde auto-rendante sur une voie du sac met cette voie dans
    l'empreinte d'émission de la somme : [SelfRetBag] est donc un cas
    particulier de [MeetsBag], ce qui simplifie l'énoncé du résidu. *)

Lemma selfretbag_meets : forall l M, SelfRetBag l M -> MeetsBag l M.
Proof.
  intros l M (c & vv & Hin & Hex).
  apply Exists_exists in Hex as (aa & Hina & (P & Heq & Hoc)).
  exists c, vv. split; [ exact Hin | ].
  apply list_elem_of_In in Hina.
  simpl. eapply gochans_summand_in; [ exact Hina | ].
  subst aa. simpl. exact Hoc.
Qed.












(** ** …et le refus SURVIT AU SAC

    [VACCS_Matching.CfgDisjunctionSourceBag] affaiblit la prémisse du
    disjoint source en [msgs l ‖ K ⊑ₘᵤₛₜᵢ msgs l ‖ g M] — relativisée au
    sac, donc strictement plus faible faute d'annulation.  On pourrait
    espérer qu'une garde morte y devienne inoffensive : sous le sac, ce
    qu'elle avale est justement un message que la configuration porte.

    **C'est faux dès que sa voie n'est pas dans le sac.**  Le même probe
    [TD d w] sépare, à ceci près que le rôle des deux composantes
    s'inverse : c'est le message *du client* qui donne au client son
    [τ] (donc le champ [ex] de la gauche), et la garde morte le vole.
    Ce qui reste — [msgs l ‖ 𝟘] face à [𝟘 ‖ (d ? ①)] — est bloqué, la
    seule action du client étant une entrée sur [d] et le sac n'ayant
    aucun message dessus.

    La condition [d ∉ chans l] est nécessaire, et elle dit exactement où
    est la marge : une garde morte **sur une voie du sac** est bien
    inoffensive (son résidu garde le sac intact), une garde morte sur une
    voie étrangère ne l'est pas. *)

Lemma bag_nil_no_tau : forall (l : list TypeOfActions) q,
  ~ lts (msgs l ‖ ((g 𝟘) : proc)) τ q.
Proof.
  intros l q H. inversion H; subst.
  - match goal with H2 : lts ((g 𝟘) : proc) (ActExt _) _ |- _ => inversion H2 end.
  - eapply msgs_no_input. eassumption.
  - eapply msgs_no_tau. eassumption.
  - match goal with H2 : lts ((g 𝟘) : proc) τ _ |- _ => inversion H2 end.
Qed.

Lemma bag_nil_out_inv : forall (l : list TypeOfActions) c v q,
  lts (msgs l ‖ ((g 𝟘) : proc)) (ActExt (ActOut (c,v))) q -> In (c,v) l.
Proof.
  intros l c v q H. inversion H; subst.
  - match goal with H2 : lts (msgs l) _ _ |- _ =>
      apply msgs_lts_inv in H2 as (c0 & v0 & l' & He & Hp & _) end.
    injection He as He1 He2. subst.
    rewrite Hp. simpl. left. reflexivity.
  - match goal with H2 : lts ((g 𝟘) : proc) _ _ |- _ => inversion H2 end.
Qed.

Lemma bag_nil_ext_inv : forall (l : list TypeOfActions) mu q,
  lts (msgs l ‖ ((g 𝟘) : proc)) (ActExt mu) q -> exists c v, mu = ActOut (c,v).
Proof.
  intros l mu q H. inversion H; subst.
  - match goal with H2 : lts (msgs l) _ _ |- _ =>
      apply msgs_lts_inv in H2 as (c0 & v0 & l' & He & _ & _) end.
    exists c0, v0. exact He.
  - match goal with H2 : lts ((g 𝟘) : proc) _ _ |- _ => inversion H2 end.
Qed.

Lemma bag_stuck_fails : forall (l : list TypeOfActions) (d : ChannelData),
  (forall v, ~ In (d,v) l) ->
  ~ ((msgs l ‖ ((g 𝟘) : proc)) must_pass
       (((g 𝟘) : proc) ‖ ((g (d ? ((g ①) : proc))) : proc))).
Proof.
  intros l d Hnin Hm. inversion Hm; subst.
  - match goal with Hg : good_VACCS _ |- _ =>
      inversion Hg; subst;
      match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end
    end.
  - match goal with He : exists _, _ |- _ => destruct He as (x & Hx) end.
    inversion Hx; subst.
    + eapply bag_nil_no_tau; eassumption.
    + inversion l0; subst;
        match goal with
        | H : lts ((g 𝟘) : proc) _ _ |- _ => inversion H
        | H : lts (g (_ ? _)) τ _ |- _ => inversion H
        end.
    + inversion l2; subst.
      * match goal with H : lts ((g 𝟘) : proc) _ _ |- _ => inversion H end.
      * match goal with H : lts (g (_ ? _)) _ _ |- _ => inversion H; subst end.
        destruct μ1 as [a1|a1]; simpl in eq; try contradiction.
        subst a1. eapply Hnin. eapply bag_nil_out_inv. exact l1.
Qed.

Lemma TD_in_good : forall (d : ChannelData) (w : ValueData) c v t',
  lts (TD d w) (ActExt (ActIn (c,v))) t' -> good_VACCS t'.
Proof.
  intros d w c v t' H. unfold TD in H. inversion H; subst.
  - match goal with H2 : lts (_ ! _ • 𝟘) _ _ |- _ => inversion H2 end.
  - match goal with H2 : lts (g (_ ? _)) _ _ |- _ => inversion H2; subst end.
    apply good_par. right. simpl. constructor.
Qed.

Lemma bag_passes_TD : forall (l : list TypeOfActions) (d : ChannelData) (w : ValueData),
  (msgs l ‖ ((g 𝟘) : proc)) must_pass (TD d w).
Proof.
  intros l d w. apply m_step.
  - apply TD_not_good.
  - exists ((msgs l ‖ ((g 𝟘) : proc)) ▷ (((g 𝟘) : proc) ‖ ((g ①) : proc))).
    apply ParRight. unfold TD.
    eapply lts_comL; [ apply lts_output | ].
    assert (E : ((g ①) : proc) ^ w = ((g ①) : proc)) by reflexivity.
    rewrite <- E at 2. apply lts_input.
  - intros p' Hp'. exfalso. eapply bag_nil_no_tau; eassumption.
  - intros t' Ht'. rewrite (TD_tau_inv d w t' Ht').
    apply m_now. apply good_par. right. constructor.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    destruct (bag_nil_ext_inv l mu1 p' Hp') as (c & v & Emu). subst mu1.
    destruct mu2 as [a2|a2]; simpl in Hd; try contradiction. subst a2.
    apply m_now. eapply TD_in_good. exact Ht'.
Qed.

Lemma dead_summand_bag_fails_TD : forall (l : list TypeOfActions) (M : gproc)
                                         (d : ChannelData) (w : ValueData),
  In ((d ? ((g 𝟘) : proc)) : gproc) (summands M) ->
  (forall v, ~ In (d,v) l) ->
  ~ ((msgs l ‖ ((g M) : proc)) must_pass (TD d w)).
Proof.
  intros l M d w Hin Hnin Hm.
  assert (Hsrv : lts (msgs l ‖ ((g M) : proc)) (ActExt (ActIn (d,w)))
                     (msgs l ‖ ((g 𝟘) : proc))).
  { apply lts_parR. eapply summand_lts; [ exact Hin | ].
    assert (E : ((g 𝟘) : proc) ^ w = ((g 𝟘) : proc)) by reflexivity.
    rewrite <- E at 2. apply lts_input. }
  inversion Hm; subst.
  - eapply TD_not_good. eassumption.
  - assert (Hbad : (msgs l ‖ ((g 𝟘) : proc)) must_pass
                     (((g 𝟘) : proc) ‖ ((g (d ? ((g ①) : proc))) : proc))).
    { match goal with Hc : forall _ _ _ _, _ |- _ =>
        eapply (Hc (msgs l ‖ ((g 𝟘) : proc))
                   (((g 𝟘) : proc) ‖ ((g (d ? ((g ①) : proc))) : proc))
                   (ActIn (d,w)) (ActOut (d,w)))
      end.
      - simpl. reflexivity.
      - exact Hsrv.
      - unfold TD. apply lts_parL. apply lts_output. }
    eapply bag_stuck_fails; [ exact Hnin | exact Hbad ].
Qed.

(** ** UN PROCESSUS QUI N'ÉMET JAMAIS EST SOUS [𝟘]

    Généralisation substantielle de [below_nil_of_all_dead], qui exige que
    **toute** garde ait une sœur morte sur sa voie : ici il suffit que le
    terme ne puisse jamais émettre, ce que [ochans] mesure syntaxiquement.
    [c ? (d ? 𝟘)] est couvert, [c ? 𝟘 + d ? (e!y•𝟘)] ne l'est pas — et de
    fait cette dernière n'est pas sous [𝟘] au sac vide.

    Deux lignes : [VACCS_Absorb.no_output_Bad] certifie [Bad ∅ p] à
    partir du critère, et [Bad_below_nil] conclut.  Une première rédaction
    refaisait ici l'induction sur [size] à la main — inutile, [Bad_sound]
    la fait déjà une fois pour toutes.

    C'est aussi le pendant sémantique du critère de
    [VACCS_Matching.drain_forced_no_output] : la même hypothèse
    [ochans p = []] y fait s'annuler le sac, ici elle place le terme sous
    [𝟘]. *)

Theorem no_output_below_nil : forall (p : proc),
  Static p -> ochans p = [] -> p ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof.
  intros p Hst Hoc. apply Bad_below_nil. apply no_output_Bad; assumption.
Qed.

Theorem nil_not_below_dead_summand_bag :
  forall (l : list TypeOfActions) (M : gproc) (d : ChannelData) (w : ValueData),
  In ((d ? ((g 𝟘) : proc)) : gproc) (summands M) ->
  (forall v, ~ In (d,v) l) ->
  ~ ((msgs l ‖ ((g 𝟘) : proc)) ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g M) : proc))).
Proof.
  intros l M d w Hin Hnin Hle.
  apply (dead_summand_bag_fails_TD l M d w Hin Hnin).
  apply Hle. apply bag_passes_TD.
Qed.

(* ------------------------------------------------------------------ *)
(*  LE POOLING FAIT PASSER LE CRITÈRE D'ANNULATION                     *)
(*                                                                    *)
(*  [cfg_derivable_of_disjoint] ferme le cas dès que la somme gauche   *)
(*  n'émet sur aucune voie du sac — c'est la négation de [MeetsBag],   *)
(*  l'unique condition qui reste dans [HardResidue] au cas [n = n1 =   *)
(*  0].                                                               *)
(*                                                                    *)
(*  Or [ax_share_msgs_ichoice] et sa réciproque font du pooling une    *)
(*  ÉQUIVALENCE dérivable, donc l'hypothèse sémantique se transporte   *)
(*  — et le critère est alors évalué sur la forme POOLÉE, où les       *)
(*  messages sont sortis du choix et ne comptent plus dans [ochans].   *)
(*                                                                    *)
(*  [pool_criterion_fails_unpooled] ci-dessous montre que ce n'est pas *)
(*  du confort : sur la forme dépliée le critère est TOUJOURS faux dès *)
(*  que le sac est non vide, chaque branche portant une copie du sac.  *)
(*  Le pooling est donc la seule façon d'y arriver.                   *)
(*                                                                    *)
(*  C'est exactement la situation de [VACCS_DropProbes.OCp], dont      *)
(*  [ax_OCp_below_msg] est fermé par [ax_share_msg] et par rien        *)
(*  d'autre : les deux descentes y sont machine-réfutées               *)
(*  ([out_choice_is_false], [no_drain_witness_for_OCp]).              *)




Lemma ochans_msgs_in : forall l c u, In (c,u) l -> In c (ochans (msgs l)).
Proof.
  induction l as [|cv l IH]; intros c u Hin; [ contradiction | ].
  destruct Hin as [Heq | Hin].
  - subst cv. simpl. left. reflexivity.
  - simpl. right. eapply IH. exact Hin.
Qed.

Lemma gochans_ichoice_mem : forall (L : list proc) (x : proc) c,
  In x L -> In c (ochans x) -> In c (gochans (ichoice L)).
Proof.
  induction L as [|y L IH]; intros x c Hx Hc; [ contradiction | ].
  destruct L as [|z L'].
  - destruct Hx as [<- | []]. simpl. apply in_or_app. left. exact Hc.
  - destruct Hx as [<- | Hx].
    + simpl. apply in_or_app. left. exact Hc.
    + simpl. apply in_or_app. right. eapply IH; [ exact Hx | exact Hc ].
Qed.

(** Le critère est TOUJOURS faux sur la forme dépliée : chaque branche
    porte une copie du sac, donc [ochans] contient toutes ses voies.
    [cfg_derivable_of_disjoint] ne peut donc jamais s'y appliquer
    directement — le pooling est indispensable. *)
Lemma pool_criterion_fails_unpooled :
  forall (l : list TypeOfActions) (L : list proc) c u,
    L <> nil -> In (c,u) l ->
    In c (ochans ((g (ichoice (map (fun x => msgs l ‖ x) L))) : proc)).
Proof.
  intros l L c u Hne Hin.
  destruct L as [|y L]; [ contradiction | ].
  eapply (gochans_ichoice_mem _ (msgs l ‖ y)).
  - simpl. left. reflexivity.
  - simpl. apply in_or_app. left. eapply ochans_msgs_in. exact Hin.
Qed.

(* ------------------------------------------------------------------ *)
(*  LE RECONNAISSEUR : extraire les messages en tête d'une branche      *)
(*                                                                    *)
(*  [cfg_branch_msgs_cancel] demande la forme                          *)
(*  [⊕ᵢ (msgs lb ‖ xᵢ)].  [peel_msgs] la reconnaît : il descend dans   *)
(*  les [‖] et collecte les messages atomiques, laissant le reste.     *)
(*  Le test « toutes les branches donnent le même [lb], à     *)
(*  permutation près » est alors                                       *)
(*  purement syntaxique.                                              *)
(* ------------------------------------------------------------------ *)

Fixpoint peel_msgs (p : proc) : list TypeOfActions * proc :=
match p with
| P ‖ Q => let r1 := peel_msgs P in
           let r2 := peel_msgs Q in
           (fst r1 ++ fst r2, snd r1 ‖ snd r2)
| c ! v • 𝟘 => ([(c,v)], ((g (𝟘 : gproc)) : proc))
| _ => ([], p)
end.





(** Contrôle : le reconnaisseur se déclenche exactement sur la forme des
    branches de [VACCS_DropProbes.OCp] — un message à côté d'une somme
    gardée — et par simple calcul. *)
Lemma peel_msg_par : forall (c : ChannelData) (v : ValueData) (M : gproc),
  fst (peel_msgs (((c ! v • 𝟘) : proc) ‖ ((g M) : proc))) = [(c,v)]
  /\ snd (peel_msgs (((c ! v • 𝟘) : proc) ‖ ((g M) : proc)))
     = (((g (𝟘 : gproc)) : proc) ‖ ((g M) : proc)).
Proof. intros. split; reflexivity. Qed.


(* ------------------------------------------------------------------ *)
(*  LA SCISSION [l ≡ₚ l1 ++ lb] N'EST PAS FORCÉE PAR LA SÉMANTIQUE     *)
(*                                                                    *)
(*  C'est la dernière hypothèse du pont dont on pouvait espérer        *)
(*  qu'elle découle de [⊑ₘᵤₛₜᵢ].  Elle n'en découle pas, et le témoin  *)
(*  est celui du dépôt : [bag_incl_fails_without_mute].               *)
(*                                                                    *)
(*  Le mécanisme : [peel_msgs] ne voit que les messages DÉJÀ EN        *)
(*  PARALLÈLE en tête d'une branche.  Ici la branche est une somme     *)
(*  gardée [g (𝛕 • (c!v•𝟘))] — le message est derrière un [𝛕] de plus  *)
(*  — donc [lb = []], alors que la cible porte bien [(c,v)] dans son   *)
(*  sac.  Ce que la gauche finit par ÉMETTRE excède ce que             *)
(*  l'extracteur en lit syntaxiquement.                                *)
(*                                                                    *)
(*  Donc [Permutation l (l1 ++ lb)] est une CONDITION LATÉRALE du      *)
(*  fragment — décidable, au même titre que [untrappedB] ou            *)
(*  [SelfRetBag] ailleurs — et non un fait dérivable.  Ne pas chercher *)
(*  à la prouver.                                                      *)
(* ------------------------------------------------------------------ *)

Theorem branch_bag_scission_not_forced : forall (c : ChannelData) (v : ValueData),
  let Bs := [ ((g (𝛕 • ((c ! v • 𝟘) : proc))) : proc) ] in
  Bs <> nil
  /\ Forall (fun b => Permutation (fst (peel_msgs b)) (@nil TypeOfActions)) Bs
  /\ (msgs (@nil TypeOfActions) ‖ ((g (ichoice Bs)) : proc))
       ⊑ₘᵤₛₜᵢ (msgs [(c,v)] ‖ ((g (𝟘 : gproc)) : proc))
  /\ ~ Permutation [(c,v)] ((@nil TypeOfActions) ++ (@nil TypeOfActions)).
Proof.
  intros c v Bs. subst Bs. split; [ discriminate | ].
  split; [ constructor; [ apply Permutation_refl | constructor ] | ].
  split.
  - intros t Ht.
    apply (proj1 (bag_incl_fails_without_mute c v)).
    eapply must_i_tau_below; [ | exact Ht ].
    apply lts_parR. apply lts_ichoice. simpl. left. reflexivity.
  - intro Hp. apply Permutation_length in Hp. simpl in Hp. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(*  LA PREMIÈRE LOI τ DE MILNER — [𝛕 • X ≂ X], SÉMANTIQUE ET DÉRIVABLE  *)
(*                                                                    *)
(*  [VACCS_Residues.v] définit le singleton de [ichoice] comme         *)
(*  [𝛕•p + 𝛕•p] plutôt que [𝛕•p] précisément pour CONTOURNER cette     *)
(*  loi, notée là-bas comme « pas manifestement dérivable : aucune     *)
(*  règle n'a une garde [𝛕] isolée d'un côté ou de l'autre ».  La      *)
(*  question n'avait jamais été tranchée.  Elle l'est : la loi vaut,   *)
(*  et elle est dérivable.                                            *)
(*                                                                    *)
(*  Sémantiquement, le sens non trivial est [X ⊑ 𝛕 • X] : le champ     *)
(*  [ex] de la garde est gratuit (son propre τ), son [com] est vide    *)
(*  (une garde [𝛕] n'a aucune transition externe), et son [pt] réclame *)
(*  exactement l'hypothèse — que l'on RECONSTRUIT sur place par        *)
(*  [apply m_step; assumption], l'induction l'ayant destructurée.     *)
(*                                                                    *)
(*  Dérivationnellement, aucune règle ne suffit seule : [ax_ichoice_glb] *)
(*  fait entrer dans la forme DUPLIQUÉE [𝛕•X + 𝛕•X], et c'est          *)
(*  [ax_sub_tau] — « un état qui peut toujours bouger seul ne doit     *)
(*  rien au client » — qui écrase le sommant en trop.                  *)
(* ------------------------------------------------------------------ *)

Lemma must_i_tau_prefix_r : forall (X : proc),
  X ⊑ₘᵤₛₜᵢ ((g ((𝛕 • X) : gproc)) : proc).
Proof.
  intros X t Ht.
  induction Ht as [ p t Hgood | p t nh ex pt IHpt et IHet com IHcom ].
  - apply m_now. assumption.
  - apply m_step.
    + exact nh.
    + exists (p, t). apply ParLeft. apply lts_tau.
    + intros p' Hp'. inversion Hp'; subst. apply m_step; assumption.
    + exact IHet.
    + intros p' t' mu1 mu2 Hd Hp' Ht'. inversion Hp'.
Qed.

Lemma must_i_tau_prefix_l : forall (X : proc),
  ((g ((𝛕 • X) : gproc)) : proc) ⊑ₘᵤₛₜᵢ X.
Proof. intros X. apply must_i_tau_below. apply lts_tau. Qed.

Lemma ax_tau_prefix_l : forall (X : proc), ((g ((𝛕 • X) : gproc)) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ X.
Proof. intros X. apply ax_tau_step. apply lts_tau. Qed.

Lemma ax_tau_prefix_r : forall (X : proc), X ᴠᴀᴄᴄꜱ⊑ₐₓ ((g ((𝛕 • X) : gproc)) : proc).
Proof.
  intros X.
  eapply ax_trans.
  - apply (ax_ichoice_glb [X]); [ discriminate | ].
    intros y Hy. destruct Hy as [<- | []]. apply ax_refl.
  - simpl. apply ax_sub_tau.
    + intros al z Hz. inversion Hz; subst; apply lts_choiceL; assumption.
    + exists X. apply lts_tau.
Qed.

(** La loi, dans les deux lectures. *)
Theorem tau_prefix_law : forall (X : proc),
  (((g ((𝛕 • X) : gproc)) : proc) ⊑ₘᵤₛₜᵢ X)
  /\ (X ⊑ₘᵤₛₜᵢ ((g ((𝛕 • X) : gproc)) : proc))
  /\ ((g ((𝛕 • X) : gproc)) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ X
  /\ X ᴠᴀᴄᴄꜱ⊑ₐₓ ((g ((𝛕 • X) : gproc)) : proc).
Proof.
  intro X. split; [ apply must_i_tau_prefix_l | ].
  split; [ apply must_i_tau_prefix_r | ].
  split; [ apply ax_tau_prefix_l | apply ax_tau_prefix_r ].
Qed.

(* ------------------------------------------------------------------ *)
(*  EFFACER LES [𝛕] EN TÊTE — et le contre-exemple précédent tombe      *)
(*                                                                    *)
(*  [branch_bag_scission_not_forced] repose sur une branche            *)
(*  [g (𝛕 • (c!v•𝟘))] dont [peel_msgs] ne voit RIEN, le message étant  *)
(*  derrière un [𝛕].  La première loi τ efface ce [𝛕] dans les DEUX    *)
(*  sens, donc la sémantique le traverse et l'extracteur retrouve le   *)
(*  message.                                                          *)
(* ------------------------------------------------------------------ *)

Fixpoint strip_taus (p : proc) : proc :=
match p with
| g M => match M with
         | gpr_tau X => strip_taus X
         | _ => p
         end
| _ => p
end.




(** Monotonie du choix interne : [ax_ichoice_glb] pour entrer,
    [ax_ichoice_below] pour sortir.  Aucune congruence de somme n'est
    nécessaire — c'est ce qui rend l'énoncé si court malgré
    l'unsoundness de [ax_choice_stable]. *)
Lemma ichoice_ax_mono : forall (L1 L2 : list proc),
  L2 <> nil ->
  (forall b, In b L2 -> exists a, In a L1 /\ a ᴠᴀᴄᴄꜱ⊑ₐₓ b) ->
  ((g (ichoice L1)) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (ichoice L2)) : proc).
Proof.
  intros L1 L2 Hne H.
  apply ax_ichoice_glb; [ exact Hne | ].
  intros y Hy. destruct (H y Hy) as (a & Ha & Hab).
  eapply ax_trans; [ apply ax_ichoice_below; exact Ha | exact Hab ].
Qed.




(** Le contrôle : sur la branche même de [branch_bag_scission_not_forced],
    l'extracteur ne voit rien, et il voit le message après effacement. *)
Lemma strip_repairs_the_counterexample : forall (c : ChannelData) (v : ValueData),
  fst (peel_msgs ((g ((𝛕 • ((c ! v • 𝟘) : proc)) : gproc)) : proc)) = []
  /\ fst (peel_msgs (strip_taus ((g ((𝛕 • ((c ! v • 𝟘) : proc)) : gproc)) : proc)))
     = [(c,v)].
Proof. intros. split; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  IDEMPOTENCE DE LA SOMME GARDÉE, ET LA TROISIÈME LOI τ DE MILNER    *)
(*                                                                    *)
(*  [g (X + X) ≂ g X] : les deux sommes ont LES MÊMES transitions,     *)
(*  mais aucune règle ne conclut de cela seul.  Deux règles s'en       *)
(*  chargent, et elles sont COMPLÉMENTAIRES — le partage se fait par   *)
(*  [lts_dec], exactement comme dans [ax_dup_ctx] :                    *)
(*                                                                    *)
(*    [ax_sub_tau]       si la somme réduite a un τ  (rien à payer)    *)
(*    [ax_restrict_keep] si elle est τ-stable        (aucun canal perdu)*)
(*                                                                    *)
(*  Puis [X + 𝛕•(g X) ≂ X] — la troisième loi τ de Milner, que le      *)
(*  dossier notait valide en CCS sans l'avoir jamais énoncée ici.      *)
(*  Sa dérivation enchaîne quatre règles et CONSOMME la première loi   *)
(*  ([ax_tau_prefix_l]) :                                             *)
(*                                                                    *)
(*    ax_tau_sep_l   X + 𝛕•(g X)  ⊑  𝛕•(g (X+X)) + 𝛕•(g X)             *)
(*    ax_choice_tau  …             ⊑  𝛕•(g X)     + 𝛕•(g X)   (idem.)  *)
(*    ax_sub_tau     …             ⊑  𝛕•(g X)                 (dup.)   *)
(*    ax_tau_prefix  …             ⊑  g X                     (1ʳᵉ loi)*)
(*                                                                    *)
(*  et le retour par [ax_int_glb] + [ax_tau_sep_r].                    *)
(* ------------------------------------------------------------------ *)

Lemma ax_dup_sum_l : forall (X : gproc), gStatic X ->
  ((g (X + X)) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g X) : proc).
Proof.
  intros X HX.
  destruct (lts_dec ((g X) : proc) τ) as [Hno | [z Hz]].
  - apply ax_restrict_keep.
    + constructor; assumption.
    + assumption.
    + intros al q Hq. apply lts_choiceL. exact Hq.
    + intros c v p Hp. inversion Hp; subst; eauto.
    + intros p Hp. inversion Hp; subst; eapply Hno; eassumption.
  - apply ax_sub_tau.
    + intros al z0 Hz0. apply lts_choiceL. exact Hz0.
    + exists z. exact Hz.
Qed.

Lemma ax_dup_sum_r : forall (X : gproc), gStatic X ->
  ((g X) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (X + X)) : proc).
Proof.
  intros X HX.
  destruct (lts_dec ((g (X + X)) : proc) τ) as [Hno | [z Hz]].
  - apply ax_restrict_keep.
    + assumption.
    + constructor; assumption.
    + intros al q Hq. inversion Hq; subst; assumption.
    + intros c v p Hp. exists v, p. apply lts_choiceL. exact Hp.
    + intros p Hp. eapply Hno. apply lts_choiceL. exact Hp.
  - apply ax_sub_tau.
    + intros al z0 Hz0. inversion Hz0; subst; assumption.
    + exists z. exact Hz.
Qed.

Lemma ax_tau3_l : forall (X : gproc), gStatic X ->
  ((g (X + (𝛕 • ((g X) : proc)))) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g X) : proc).
Proof.
  intros X HX.
  eapply ax_trans; [ apply (ax_tau_sep_l X X) | ].
  eapply ax_trans; [ apply ax_choice_tau; apply ax_dup_sum_l; exact HX | ].
  eapply ax_trans; [ | apply ax_tau_prefix_l ].
  apply ax_sub_tau.
  - intros al z Hz. inversion Hz; subst; apply lts_choiceL; assumption.
  - exists ((g X) : proc). apply lts_tau.
Qed.

Lemma ax_tau3_r : forall (X : gproc), gStatic X ->
  ((g X) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (X + (𝛕 • ((g X) : proc)))) : proc).
Proof.
  intros X HX.
  eapply ax_trans; [ | apply (ax_tau_sep_r X X) ].
  apply ax_int_glb.
  - apply ax_dup_sum_r. exact HX.
  - apply ax_refl.
Qed.

(** La troisième loi, dans les deux lectures. *)
Theorem tau_third_law : forall (X : gproc), gStatic X ->
  ((g (X + (𝛕 • ((g X) : proc)))) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g X) : proc)
  /\ ((g X) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (X + (𝛕 • ((g X) : proc)))) : proc)
  /\ ((g (X + (𝛕 • ((g X) : proc)))) : proc) ⊑ₘᵤₛₜᵢ ((g X) : proc)
  /\ ((g X) : proc) ⊑ₘᵤₛₜᵢ ((g (X + (𝛕 • ((g X) : proc)))) : proc).
Proof.
  intros X HX.
  split; [ apply ax_tau3_l; exact HX | ].
  split; [ apply ax_tau3_r; exact HX | ].
  split; apply soundness_ax; [ apply ax_tau3_l | apply ax_tau3_r ]; exact HX.
Qed.

(* ------------------------------------------------------------------ *)
(*  LA TROISIÈME LOI CLASSIQUE : [α.τ.P = α.P] SOUS UNE GARDE D'ENTRÉE *)
(*                                                                    *)
(*  Trois lignes, parce que [ax_input] est la RÈGLE OMÉGA : elle       *)
(*  consomme la première loi τ à chaque valeur reçue, et la           *)
(*  substitution traverse la garde [𝛕] sans rien faire                *)
(*  ([subst_tau_guard], par calcul) — un [𝛕] ne lie aucune valeur.     *)
(* ------------------------------------------------------------------ *)

Lemma subst_tau_guard : forall (P : proc) (v : ValueData),
  ((g ((𝛕 • P) : gproc)) : proc) ^ v = ((g ((𝛕 • (P ^ v)) : gproc)) : proc).
Proof. intros. reflexivity. Qed.

Lemma ax_tau_under_input_l : forall (c : ChannelData) (P : proc),
  ((g (c ? ((g ((𝛕 • P) : gproc)) : proc))) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (c ? P)) : proc).
Proof.
  intros c P. apply ax_input. intro v.
  rewrite subst_tau_guard. apply ax_tau_prefix_l.
Qed.

Lemma ax_tau_under_input_r : forall (c : ChannelData) (P : proc),
  ((g (c ? P)) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (c ? ((g ((𝛕 • P) : gproc)) : proc))) : proc).
Proof.
  intros c P. apply ax_input. intro v.
  rewrite subst_tau_guard. apply ax_tau_prefix_r.
Qed.

(** ** Les trois lois τ valides de Milner, pour VACCS

    Rassemblées, parce que l'encodage [⊕ := 𝛕•X + 𝛕•Y] de ce dépôt les
    rendait toutes trois douteuses — [VACCS_Residues.v] contourne la
    première par la duplication du singleton de [ichoice].

      τ.P        = P
      α.τ.P      = α.P        (ici : garde d'entrée ; il n'y a pas de
                               garde de sortie en VACCS)
      P + τ.P    = τ.P

    La loi INVALIDE de la famille, [τ.P + Q = P + Q], a son
    contre-exemple au dépôt : [VACCS_ChoiceProbes], et côté VCCS c'est
    la raison du retrait d'[ax_choice]. *)
Theorem milner_tau_laws :
  forall (c : ChannelData) (P : proc) (X : gproc), gStatic X ->
    (((g ((𝛕 • P) : gproc)) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ P
     /\ P ᴠᴀᴄᴄꜱ⊑ₐₓ ((g ((𝛕 • P) : gproc)) : proc))
 /\ (((g (c ? ((g ((𝛕 • P) : gproc)) : proc))) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (c ? P)) : proc)
     /\ ((g (c ? P)) : proc)
          ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (c ? ((g ((𝛕 • P) : gproc)) : proc))) : proc))
 /\ (((g (X + (𝛕 • ((g X) : proc)))) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g X) : proc)
     /\ ((g X) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (X + (𝛕 • ((g X) : proc)))) : proc)).
Proof.
  intros c P X HX.
  split; [ split; [ apply ax_tau_prefix_l | apply ax_tau_prefix_r ] | ].
  split; [ split; [ apply ax_tau_under_input_l | apply ax_tau_under_input_r ] | ].
  split; [ apply ax_tau3_l; exact HX | apply ax_tau3_r; exact HX ].
Qed.

(* ------------------------------------------------------------------ *)
(*  DEUX ROUTES NEUVES VERS [HardResidue], TOUTES DEUX FERMÉES         *)
(*                                                                    *)
(*  ROUTE 1 — « donner un τ à la cible ».  La cible du résidu est      *)
(*  τ-STABLE, donc [ax_glb_weak] (dont la 5ᵉ prémisse est justement le *)
(*  choix interne des résidus d'émission, que la sémantique fournit    *)
(*  par [ichoice_residues_below]) ne s'y applique pas.  La première    *)
(*  loi τ semble débloquer : [q ≂ g (𝛕 • q)], donc on peut remplacer   *)
(*  la cible par une cible qui A un τ.                                *)
(*                                                                    *)
(*  [tau_wrap_glb_is_circular] montre que c'est VIDE : l'unique        *)
(*  τ-successeur de [g (𝛕 • q)] est [q] lui-même, donc la prémisse τ   *)
(*  d'[ax_glb_weak] EST le but de départ, ni plus ni moins.            *)
(*                                                                    *)
(*  ROUTE 2 — « récurrence sur la taille du MEMBRE GAUCHE ».  Les      *)
(*  descentes de gauche ([ax_below_cfg_descend_wreturn],               *)
(*  [ax_cfg_replay_balanced]) font décroître la gauche en laissant la  *)
(*  cible intacte, donc une mesure lexicographique (droite, gauche)    *)
(*  semble praticable.  Elle ne l'est pas : par                        *)
(*  [cfg_replay_tau_run] ces descentes sont des τ-RUNS de la           *)
(*  configuration, donc elles MONTENT dans le préordre                 *)
(*  ([must_i_tau_below]) — l'hypothèse sémantique ne se transporte pas *)
(*  sur l'état descendu.                                              *)
(*                                                                    *)
(*  LE LIEN, sous sa forme la plus nue : toute descente à gauche       *)
(*  monte ; toute descente à droite exige que la gauche s'aligne       *)
(*  ([OutChoice], réfuté par [out_choice_is_false] ; le certificat de  *)
(*  pose, réfuté par [CertAll_is_false]).                             *)
(* ------------------------------------------------------------------ *)

Lemma tau_wrap_tau_inv : forall (q z : proc),
  lts ((g ((𝛕 • q) : gproc)) : proc) τ z -> z = q.
Proof. intros q z Hz. inversion Hz; subst; reflexivity. Qed.

(** La prémisse τ d'[ax_glb_weak] sur une cible [g (𝛕 • q)] est
    ÉQUIVALENTE au but [p ᴠᴀᴄᴄꜱ⊑ₐₓ q] : dans les deux sens. *)
Theorem tau_wrap_glb_is_circular :
  forall (q : proc),
    (exists z, lts ((g ((𝛕 • q) : gproc)) : proc) τ z)
    /\ (forall (p : proc),
          (forall z, lts ((g ((𝛕 • q) : gproc)) : proc) τ z -> p ᴠᴀᴄᴄꜱ⊑ₐₓ z)
          -> p ᴠᴀᴄᴄꜱ⊑ₐₓ q)
    /\ (forall (p : proc), p ᴠᴀᴄᴄꜱ⊑ₐₓ q ->
          (forall z, lts ((g ((𝛕 • q) : gproc)) : proc) τ z -> p ᴠᴀᴄᴄꜱ⊑ₐₓ z)).
Proof.
  intro q. split; [ exists q; apply lts_tau | ].
  split.
  - intros p H. apply H. apply lts_tau.
  - intros p H z Hz. rewrite (tau_wrap_tau_inv q z Hz). exact H.
Qed.

End VACCS_Bad.
