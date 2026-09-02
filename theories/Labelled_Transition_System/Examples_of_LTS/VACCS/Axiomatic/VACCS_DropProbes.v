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

(** * Canonicity does not make the drop rule's premise derivable

    [VACCS_Bad.v]'s judgement approximates the premise
    [must_i_input_drop_bad] needs:

      [SemBad S p] := "p passes no client that is τ-stuck, not good, and
                       refuses inputs on S".

    An earlier plan entry expected canonicity — at most one guard per
    channel, [VACCS_Canonical.canonical] — to make [Bad]'s [bad_stuck]
    input clause *forced*, i.e. to give

      [SemBad S (g M)  ⟹  ∀ input reduct p' on c, SemBad (S ∪ {c}) p'].

    **That is false, and this file is the counterexample.**  Canonicity
    fixes one gap and a second, independent one remains.

    With three distinct channels [a], [b], [e]:

        PP := b ? (e!y•𝟘)          MM := (a ? PP) + (b ? 𝟘)
        UU := (b!w•𝟘) ‖ (e ? ①)

    [MM] is [gStatic], τ-stable and **canonical** (two guards, distinct
    channels).  Then [MM_bad] : [g MM] passes *no* τ-stuck non-good
    client at all — yet [PP_passes_UU] : its [a]-continuation [PP] passes
    [UU], which is τ-stuck, not good, and refuses inputs on [{a}].

    **The mechanism.**  The natural probe for the inversion is
    [(a!v•𝟘) ‖ UU].  Every field of [must (g MM) ((a!v•𝟘) ‖ UU)] goes
    through except [com], and [com] splits two ways: the message is taken
    by the [a]-guard — the case *canonicity* pins down, and it holds
    here — or **the client emits on [MM]'s other channel [b]**, where the
    [b]-guard's own obligation [𝟘 must_pass _] fails against a deadlocked
    residue.  So the sum fails the probe *through a different guard than
    the one being inverted*, and the continuation learns nothing.

    **Why no judgement of this shape can be complete.**  [must (g M) u] is
    a conjunction over branches, so [¬ must] is a disjunction, and the
    semantic condition quantifies [∀u ∃branch].  An inductive judgement
    must name the branch before seeing the client.  The plan file records
    the same alternation over τ-branches ([𝛕•A + 𝛕•B]); this is the
    version over *guards*, and canonicity removes the alternation only
    *within* one channel, never *across* channels.

    **Consequence.**  It sharpens the "restrict, do not drop" finding
    ([VACCS_Absorb.must_i_restrict]): here [b ? 𝟘] is droppable on its own
    (a [𝟘] continuation is harmless at any set) while [a ? PP] is not —
    and it is the [b]-guard that kills every client.  Removing the easy
    one first destroys the fact that justified removing them at all, so
    surplus guards have to go **jointly**, which is exactly
    [must_i_restrict]'s shape — and that lemma's premise is the very
    inequation completeness is trying to derive. *)

From Stdlib Require Import List Permutation Lia.
From Stdlib.Program Require Import Equality.
From stdpp Require Import base gmultiset.
From TestingTheory Require Import InputOutputActions ActTau Must VACCS_Must_Characterization
  gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB ParallelLTSConstruction
  InteractionBetweenLts Testing_Predicate DefinitionAS VACCS VACCS_Good VACCS_Instance
  Convergence WeakTransitions Subset_Act MultisetLTSConstruction Termination
  VACCS_Static VACCS_Erasure VACCS_Precongruence VACCS_Expansion VACCS_ResNormalize
  VACCS_Copycat VACCS_Absorb VACCS_DefinitionAxiomatic VACCS_SoundnessAx
  VACCS_NormalForm VACCS_Canonical VACCS_ReadySet VACCS_Bad VACCS_Forwarder VACCS_Cond2
  VACCS_Descent VACCS_Matching.
Import ListNotations.

Section VACCS_DropProbes.

Context `{VP : VACCS_Parameters}.
Context {a b e : Channel} {v w y : Value}.
Context {nab : a <> b} {nae : a <> e} {nbe : b <> e}.

(** ** The processes *)

Definition Ke : proc := (cst e) ! (cst y) • 𝟘.
Definition PP : proc := g ((cst b) ? Ke).
Definition MM : gproc := ((cst a) ? PP) + ((cst b) ? (g 𝟘)).
Definition UU : proc := ((cst b) ! (cst w) • 𝟘) ‖ (g ((cst e) ? (g ①))).

(** Same inversion tactic as [VACCS_ChoiceProbes.v]: invert every [lts]
    whose subject has a concrete head, then close on the channel
    disequalities.  The leading [unfold lts_step] is needed because
    [must]'s own fields are stated with the [gLts] notation. *)

Ltac blast3 :=
  unfold lts_step in *; simpl in *;
  repeat match goal with
  | H : lts (_ ‖ _) _ _ |- _ => inversion H; subst; clear H
  | H : lts (_ ! _ • 𝟘) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g (_ + _)) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g (_ ? _)) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g 𝟘) _ _ |- _ => inversion H
  | H : lts (g ①) _ _ |- _ => inversion H
  end; simpl in *; try congruence; try contradiction.

Lemma dual_io : forall (x : TypeOfActions), dual (ActIn x) (ActOut x).
Proof. intros x. simpl. reflexivity. Qed.

(** ** [MM] really is canonical, and stable

    Note the [decide]: [destruct (decide ...)] does **not** rewrite the
    goal's own [if decide _] here (the instance elaborates differently),
    so the exact instance has to be grabbed out of the goal. *)

Lemma MM_canonical : canonical MM.
Proof.
  unfold canonical, MM. simpl.
  match goal with |- context[@decide ?P ?d] => destruct (@decide P d) as [He|He] end.
  - exfalso. injection He as He. congruence.
  - reflexivity.
Qed.

Lemma MM_no_tau : forall q, ~ lts (g MM) τ q.
Proof. intros q Hl. unfold MM in Hl. blast3. Qed.

(** ** The client [UU] *)

Lemma UU_no_tau : forall q, ~ lts UU τ q.
Proof. intros q Hl. unfold UU in Hl. blast3. Qed.

Lemma UU_not_good : ~ good_VACCS UU.
Proof.
  intro H. unfold UU in H. inversion H; subst.
  match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
Qed.

Lemma UU_refuses_a : forall x q, ~ lts UU ((cst a ▷ x)?) q.
Proof. intros x q Hl. unfold UU in Hl. blast3. Qed.

(** ** The continuation passes it

    [PP] takes the [b]-message and answers on [e], where [①] is waiting.
    So [PP] is *not* [SemBad {a}]. *)

Lemma PP_passes_UU : PP must_pass UU.
Proof.
  apply m_step.
  - apply UU_not_good.
  - exists (Ke ▷ ((g 𝟘) ‖ (g ((cst e) ? (g ①))))).
    eapply ParSync; [ apply dual_io | | ].
    + unfold PP. assert (E : Ke ^ (cst w) = Ke) by reflexivity.
      rewrite <- E at 2. apply lts_input.
    + unfold UU. apply lts_parL. apply lts_output.
  - intros p' Hp'. unfold PP in Hp'. blast3.
  - intros t' Ht'. exfalso. eapply UU_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold PP in Hp'. unfold UU in Ht'. blast3.
    apply m_step.
    + intro Hg. inversion Hg; subst.
      match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
    + exists ((g 𝟘) ▷ ((g 𝟘) ‖ (g ①))).
      eapply ParSync; [ apply dual_out_in | apply lts_output | ].
      apply lts_parR.
      assert (E : ((g ①) : proc) ^ (cst y) = g ①) by reflexivity.
      rewrite <- E. apply lts_input.
    + intros p' Hp'. blast3.
    + intros t' Ht'. blast3.
    + intros p' t' mu1' mu2' Hd2 Hp' Ht'. blast3.
      apply m_now. apply good_par. right. apply good_success.
Qed.

(** ** Residues of an output

    Both facts are the ones [Bad_sound]/[Harmless_sound] use, isolated
    here: an emitting client is [≡*] the message beside its residue
    ([TransitionShapeForOutputSimplified] — asynchrony), so the residue
    inherits τ-stuckness and non-goodness, and its own outputs lift back
    to the whole. *)

Lemma out_residue : forall t c0 v0 b0,
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

Lemma out_lift : forall t c0 v0 b0 c1 x q,
  lts t ((c0 ▷ v0)!) b0 -> lts b0 ((c1 ▷ x)!) q ->
  exists r, lts t ((c1 ▷ x)!) r.
Proof.
  intros t c0 v0 b0 c1 x q Hl Hq.
  assert (Hsh : t ≡* ((c0 ! v0 • 𝟘) ‖ b0))
    by (eapply TransitionShapeForOutputSimplified; exact Hl).
  assert (Hsc : sc_then_lts t ((c1 ▷ x)!) ((c0 ! v0 • 𝟘) ‖ q))
    by (exists ((c0 ! v0 • 𝟘) ‖ b0); split; [ exact Hsh | apply lts_parR; exact Hq ]).
  apply Congruence_Respects_Transition in Hsc.
  destruct Hsc as (r & Hr & _). exists r. exact Hr.
Qed.

(** ** The sum is bad at the empty set

    First: a client [g MM] passes can never emit on [b].  The [b]-guard's
    continuation is [𝟘], so [com] there demands [𝟘 must_pass r] with [r]
    τ-stuck and not good — impossible. *)

Lemma MM_no_b_out : forall t, (forall q, ~ lts t τ q) -> ~ good_VACCS t ->
  (g MM) must_pass t -> forall x q, ~ lts t ((cst b ▷ x)!) q.
Proof.
  intros t Hst Hng Hm x q Hl.
  inversion Hm as [Ho | Ho Hex Hpt Het Hcom]; subst; [contradiction |].
  assert (Hnil : (g 𝟘) must_pass q).
  { eapply (Hcom _ _ (ActIn (cst b, x)) (ActOut (cst b, x))).
    - apply dual_io.
    - unfold MM. apply lts_choiceR.
      assert (E : ((g 𝟘) : proc) ^ x = g 𝟘) by reflexivity.
      rewrite <- E. apply lts_input.
    - exact Hl. }
  destruct (out_residue t (cst b) x q Hst Hng Hl) as (Hq1 & Hq2).
  inversion Hnil as [Ho2 | Ho2 Hex2 Hpt2 Het2 Hcom2]; subst; [contradiction |].
  destruct Hex2 as (z & Hz). inversion Hz; subst; unfold lts_step in *; simpl in *.
  - inversion l.
  - eapply Hq1. exact l.
  - inversion l1.
Qed.

(** And then: [ex] forces the client to emit on [a] or [b]; [b] is out by
    the above, and after the [a]-synchronisation [PP]'s own [ex] needs the
    client to emit on [b] after all. *)

Lemma MM_bad : forall t, (forall q, ~ lts t τ q) -> ~ good_VACCS t ->
  ~ ((g MM) must_pass t).
Proof.
  intros t Hst Hng Hm.
  pose proof (MM_no_b_out t Hst Hng Hm) as Hnb.
  inversion Hm as [Ho | Ho Hex Hpt Het Hcom]; subst; [contradiction |].
  destruct Hex as (z & Hz). inversion Hz; subst; unfold lts_step in *; simpl in *.
  - eapply MM_no_tau. exact l.
  - eapply Hst. exact l.
  - destruct μ1 as [[c1 v1]|[c1 v1]]; [ | exfalso; eapply gsum_no_out; exact l1 ].
    destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; try (exfalso; exact eq).
    inversion eq; subst.
    assert (Hobl : a2 must_pass b2)
      by (eapply (Hcom _ _ (ActIn (c2, v2)) (ActOut (c2, v2)));
          [ apply dual_io | exact l1 | exact l2 ]).
    unfold MM in l1. inversion l1; subst.
    + inversion H3; subst.
      destruct (out_residue t (cst a) v2 b2 Hst Hng l2) as (Hb1 & Hb2).
      inversion Hobl as [Ho2 | Ho2 Hex2 Hpt2 Het2 Hcom2]; subst; [contradiction |].
      destruct Hex2 as (z2 & Hz2). inversion Hz2; subst; unfold lts_step in *; simpl in *.
      * inversion l.
      * eapply Hb1. eassumption.
      * destruct μ1 as [[d1 x1]|[d1 x1]]; [ | exfalso; inversion l0 ].
        destruct μ2 as [[d2 x2]|[d2 x2]]; simpl in eq0; try (exfalso; exact eq0).
        inversion eq0; subst.
        inversion l0; subst.
        destruct (out_lift t (cst a) v2 b2 (cst b) x2 b0 l2 l3) as (r & Hr).
        eapply Hnb. exact Hr.
    + inversion H3; subst. eapply Hnb. exact l2.
Qed.

Lemma MM_lts_a : lts (g MM) ((cst a ▷ cst v)?) PP.
Proof.
  unfold MM. apply lts_choiceL.
  assert (E : PP ^ (cst v) = PP) by reflexivity.
  rewrite <- E at 2. apply lts_input.
Qed.

(** ** The negative result

    The refuted statement is exactly [bad_stuck]'s input clause, read as
    an inversion principle: it is what a completeness proof for
    [VACCS_Bad.Bad] would have to establish, and what the canonicity
    detour was meant to supply.  Note how much is granted and still does
    not help — the process is a τ-stable guarded sum, canonical, with
    [𝟘] and a single output as its continuations. *)

Theorem bad_input_clause_is_not_forced :
  ~ (forall (p : proc) (S : chset),
       (forall q, ~ lts p τ q) ->
       (forall u, (forall q, ~ lts u τ q) -> ~ good_VACCS u -> RefusesIn S u ->
          ~ (p must_pass u)) ->
       forall c0 v0 p', lts p ((c0 ▷ v0)?) p' ->
         forall u, (forall q, ~ lts u τ q) -> ~ good_VACCS u ->
            RefusesIn (fun d => S d \/ d = c0) u -> ~ (p' must_pass u)).
Proof.
  intro Hrule.
  assert (Hsum : forall u, (forall q, ~ lts u τ q) -> ~ good_VACCS u ->
                   RefusesIn (fun _ : ChannelData => False) u -> ~ ((g MM) must_pass u)).
  { intros u Hst Hng _. apply MM_bad; assumption. }
  assert (Href : RefusesIn (fun d => (fun _ : ChannelData => False) d \/ d = cst a) UU).
  { intros c0 x q [Hc|Hc]; [ contradiction | subst c0 ]. apply UU_refuses_a. }
  eapply (Hrule (g MM) (fun _ : ChannelData => False) MM_no_tau Hsum
                (cst a) (cst v) PP MM_lts_a UU UU_no_tau UU_not_good Href).
  exact PP_passes_UU.
Qed.

(** ** …and the inequation it witnesses

    [VACCS_Bad.below_nil_iff] turns [MM_bad] into a genuine inequation of
    the theory.  So this is not a curiosity about a predicate: it is a
    **true inequation between [Static] processes** whose only obvious
    derivation route provably passes through a *false* intermediate.

    `ax_input_drop` discards the [b]-summand at once ([𝟘] is harmless at
    any set), leaving the goal [⊢ g (a ? PP) ⊑ g 𝟘] — and that is not
    merely underivable, it is **unsound**: [PP_passes_UU] plus
    [below_nil_iff] give [g (a ? PP) ⋢ₘᵤₛₜᵢ g 𝟘].  The two guards have to
    go together, which is [must_i_restrict]'s shape and not any rule's.

    Whether the 24-rule system derives [⊢ g MM ⊑ g 𝟘] by some other route
    is open; showing it does not would need an invariant over
    derivations, in the style of the [ax_choice] unsoundness argument but
    harder, and is not attempted. *)

Theorem MM_below_nil : (g MM) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof. apply below_nil_iff. exact MM_bad. Qed.

Definition TT2 : proc := ((cst a) ! (cst v) • 𝟘) ‖ UU.

Lemma TT2_no_tau : forall q, ~ lts TT2 τ q.
Proof. intros q Hq. unfold TT2, UU in Hq. blast3. Qed.

Lemma TT2_not_good : ~ good_VACCS TT2.
Proof.
  intro Hg. unfold TT2 in Hg. inversion Hg; subst.
  match goal with H : _ \/ _ |- _ => destruct H as [H|H]; [ inversion H | ] end.
  apply UU_not_good. assumption.
Qed.

Lemma a_guard_passes_TT2 : (g ((cst a) ? PP)) must_pass TT2.
Proof.
  apply m_step.
  - apply TT2_not_good.
  - exists (PP ▷ ((g 𝟘) ‖ UU)).
    eapply ParSync; [ apply dual_io | | ].
    + assert (E : PP ^ (cst v) = PP) by reflexivity.
      rewrite <- E at 2. apply lts_input.
    + unfold TT2. apply lts_parL. apply lts_output.
  - intros p' Hp'. blast3.
  - intros t' Ht'. exfalso. eapply TT2_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    inversion Hp'; subst.
    unfold TT2 in Ht'. inversion Ht'; subst.
    + inversion H3; subst.
      assert (E : PP ^ v0 = PP) by reflexivity. rewrite E.
      eapply must_eq_client; [ | apply PP_passes_UU ].
      etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ].
    + exfalso. unfold UU in H3. blast3.
Qed.

Theorem a_guard_not_below_nil : ~ ((g ((cst a) ? PP)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc)).
Proof.
  intro Hle. rewrite below_nil_iff in Hle.
  eapply Hle; [ apply TT2_no_tau | apply TT2_not_good | apply a_guard_passes_TT2 ].
Qed.

(** ** The drop-rule family provably cannot remove this guard

    [ax_input_drop] and its up-to form [ax_input_drop_upto] are the only
    rules that discard a summand, and both ask for a target [Q] with
    [⊢ P^v ⊑ Q^v] and [Q^v] harmless.  **No such [Q] exists here**, and
    the reason is one line: the semantic predicate is *downward closed*
    along [⊑ₘᵤₛₜᵢ], so a harmless [Q] above [PP] would make [PP] harmless —
    and [PP_passes_UU] says it is not.

    So the failure is not that the judgement [Harmless]/[Bad] is too
    weak: it is that **the target does not exist**, whatever judgement is
    used to certify it.  Removing this guard needs a rule of a different
    shape — one that removes several summands jointly, which is
    [VACCS_Absorb.must_i_restrict]'s form and whose premise is the very
    inequation completeness is trying to derive. *)

Lemma UU_refuses : RefusesIn (fun d => d = cst a) UU.
Proof. intros c0 x q Hc. subst c0. apply UU_refuses_a. Qed.

Theorem no_drop_target_for_a :
  ~ (exists Q : proc, (PP ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ Q) /\
       (forall u : proc, (forall q : proc, ~ lts u τ q) -> ~ good_VACCS u ->
          RefusesIn (fun d => d = cst a) u -> ~ (Q must_pass u))).
Proof.
  intros (Q & Hle & HQ).
  eapply (HQ UU UU_no_tau UU_not_good UU_refuses).
  apply Hle. exact PP_passes_UU.
Qed.

Corollary no_Harmless_target :
  ~ (exists Q : proc, (PP ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ Q) /\ Harmless (fun d => d = cst a) Q).
Proof.
  intros (Q & Hle & HH). apply no_drop_target_for_a. exists Q. split; [ exact Hle | ].
  intros u Hst Hng Href Hm. eapply Harmless_sound; eassumption.
Qed.

Corollary no_Bad_target :
  ~ (exists Q : proc, (PP ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ Q) /\ Bad (fun d => d = cst a) Q).
Proof.
  intros (Q & Hle & HB). apply no_drop_target_for_a. exists Q. split; [ exact Hle | ].
  intros u Hst Hng Href Hm. eapply Bad_sound; eassumption.
Qed.

(** ** …and [BadK] DOES certify it

    Where [Bad] provably cannot ([no_Bad_target] above), the killer-set
    judgement of [VACCS_Bad.v] succeeds, and the derivation reads exactly
    like the informal argument:

    - [bk_kill] at [b]: [MM] has a [b]-guard, its continuation is [𝟘] and
      is bad at any set — so a client that emits on [b] is killed;
    - hence the rest may assume the client is silent on [b].  [bk_kill]
      at [a]: [MM]'s [a]-continuation is [PP = b ? (e!y•𝟘)], whose only
      guard is on [b] — a channel now in [D] — so [bk_stuck] applies,
      [ex] having nothing to fire on;
    - and finally [MM] itself, with both its channels in [D].

    This is precisely the cooperation the earlier judgements could not
    record: the [a]-guard is harmless *because* the [b]-guard already
    killed every client that could have fed it. *)

Lemma nil_BadK : forall S D, BadK S D (g 𝟘).
Proof.
  intros S D. apply bk_stuck.
  - intros q Hq. inversion Hq.
  - intros c0 x p' Hl. inversion Hl.
  - intros c0 x p' Hl. inversion Hl.
Qed.

Lemma PP_BadK : forall S (D : chset), D (cst b) -> BadK S D PP.
Proof.
  intros S D HD. unfold PP. apply bk_stuck.
  - intros q Hq. blast3.
  - intros c0 x p' Hl. blast3.
  - intros c0 x p' Hl. inversion Hl; subst. exact HD.
Qed.

Theorem MM_BadK : BadK (fun _ => False) (fun _ => False) (g MM).
Proof.
  eapply (bk_kill _ _ (cst b) _ (fun _ => ((g 𝟘) : proc))).
  - intro x. unfold MM. apply lts_choiceR.
    assert (E : ((g 𝟘) : proc) ^ x = g 𝟘) by reflexivity.
    rewrite <- E. apply lts_input.
  - intro x. apply nil_BadK.
  - eapply (bk_kill _ _ (cst a) _ (fun _ => PP)).
    + intro x. unfold MM. apply lts_choiceL.
      assert (E : PP ^ x = PP) by reflexivity.
      rewrite <- E at 2. apply lts_input.
    + intro x. apply PP_BadK. right. reflexivity.
    + apply bk_stuck.
      * apply MM_no_tau.
      * intros c0 x p' Hl. exfalso. eapply gsum_no_out. exact Hl.
      * intros c0 x p' Hl. unfold MM in Hl. inversion Hl; subst.
        -- inversion H3; subst. right. reflexivity.
        -- inversion H3; subst. left. right. reflexivity.
Qed.

(** The inequation, recovered from the judgement alone. *)
Corollary MM_below_nil_via_BadK : (g MM) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof. apply BadK_below_nil. exact MM_BadK. Qed.

(** ** THE INEQUATION IS NOW DERIVABLE

    [MM_below_nil] is the inequation whose derivation was blocked: every
    route through the drop laws provably fails ([no_drop_target_for_a]),
    and the copycat-mirror route is circular.  With [ax_restrict] — whose
    premise is the [BadK] derivation above rather than the goal — it is
    two lines.

    The three premises: [g 𝟘] has no transitions at all, so the sub-sum
    condition is vacuous; [g MM] is stable; and [MM_BadK] certifies it,
    transported to [offers 𝟘] by [BadK_mono]. *)

Theorem MM_derivable : ax_pre (g MM) ((g 𝟘) : proc).
Proof.
  apply ax_restrict.
  - intros al q Hl. inversion Hl.
  - apply MM_no_tau.
  - eapply BadK_mono; [ exact MM_BadK | intros c0 [] | intros c0 [] ].
Qed.

(** …and it really is the same inequation: soundness hands back the
    semantic fact, matching [MM_below_nil] proved directly. *)
Corollary MM_derivable_sound : (g MM) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof. apply soundness_ax. exact MM_derivable. Qed.

(** * A second probe: `grestrict` is the wrong restriction target

    The matching argument discharges its [gGuardsIn] side condition by
    restricting the left-hand sum to the channels the right-hand side
    offers ([VACCS_Absorb.grestrict]).  That is unsound, and this is the
    half of the reason that can be machine-checked.

    Take

        MC := a ? (b ? (e!y•𝟘))          MC' := b ? (a ? (e!y•𝟘))

    Both want the *same two messages* and answer on [e]; messages are
    asynchronous, so the order in which they are consumed ought to be
    invisible — i.e. [a ? (b ? P) ≂ₘᵤₛₜᵢ b ? (a ? P)].  That law is not
    proved here (it is worth proving in its own right), but if it holds
    then [g MC ⊑ₘᵤₛₜᵢ g MC'] while
    [offers MC = {a}] and [offers MC' = {b}] are **disjoint**, so
    [grestrict MC' MC = 𝟘].

    And [g MC ⋢ₘᵤₛₜᵢ g 𝟘] — that is [MC_not_below_nil] below, proved: the
    client [(a!v•𝟘) ‖ (b!w•𝟘) ‖ (e ? ①)] is τ-stuck and not good, and
    [MC] passes it by taking both messages and answering on [e].

    So restricting to the target's channels can drop guards that are
    genuinely needed; what a target reaches through a *different channel
    order* is invisible to that criterion.  Note this does not touch
    [ax_restrict], whose premise is a [BadK] derivation and which simply
    cannot be applied here. *)

Definition MC : gproc := (cst a) ? (g ((cst b) ? ((cst e) ! (cst y) • 𝟘))).
Definition TT3 : proc :=
  ((cst a) ! (cst v) • 𝟘) ‖ (((cst b) ! (cst w) • 𝟘) ‖ (g ((cst e) ? (g ①)))).

Lemma TT3_no_tau : forall q, ~ lts TT3 τ q.
Proof. intros q Hq. unfold TT3 in Hq. blast3. Qed.

Lemma TT3_not_good : ~ good_VACCS TT3.
Proof.
  intro Hg. unfold TT3 in Hg. inversion Hg; subst.
  match goal with H : _ \/ _ |- _ => destruct H as [H|H]; [ inversion H | ] end.
  inversion H0; subst.
  match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
Qed.

Lemma level3 : ((cst e) ! (cst y) • 𝟘) must_pass ((g 𝟘) ‖ ((g 𝟘) ‖ (g ((cst e) ? (g ①))))).
Proof.
  apply m_step.
  - intro Hg. inversion Hg; subst.
    match goal with H : _ \/ _ |- _ => destruct H as [H|H]; [ inversion H | ] end.
    inversion H0; subst.
    match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
  - exists ((g 𝟘) ▷ ((g 𝟘) ‖ ((g 𝟘) ‖ (g ①)))).
    eapply ParSync; [ apply dual_out_in | apply lts_output | ].
    apply lts_parR. apply lts_parR.
    assert (E : ((g ①) : proc) ^ (cst y) = g ①) by reflexivity.
    rewrite <- E. apply lts_input.
  - intros p' Hp'. blast3.
  - intros t' Ht'. blast3.
  - intros p' t' mu1 mu2 Hd Hp' Ht'. blast3.
    apply m_now. apply good_par. right. apply good_par. right. apply good_success.
Qed.

Lemma level2b : (g ((cst b) ? ((cst e) ! (cst y) • 𝟘)))
                  must_pass ((g 𝟘) ‖ (((cst b) ! (cst w) • 𝟘) ‖ (g ((cst e) ? (g ①))))).
Proof.
  apply m_step.
  - intro Hg. inversion Hg; subst.
    match goal with H : _ \/ _ |- _ => destruct H as [H|H]; [ inversion H | ] end.
    inversion H0; subst.
    match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
  - exists (((cst e) ! (cst y) • 𝟘) ▷ ((g 𝟘) ‖ ((g 𝟘) ‖ (g ((cst e) ? (g ①)))))).
    eapply ParSync; [ apply dual_io | | ].
    + assert (E : ((cst e) ! (cst y) • 𝟘) ^ (cst w) = (cst e) ! (cst y) • 𝟘) by reflexivity.
      rewrite <- E at 2. apply lts_input.
    + apply lts_parR. apply lts_parL. apply lts_output.
  - intros p' Hp'. blast3.
  - intros t' Ht'. blast3.
  - intros p' t' mu1 mu2 Hd Hp' Ht'. blast3.
    exact level3.
Qed.

Theorem MC_passes_TT3 : (g MC) must_pass TT3.
Proof.
  apply m_step.
  - apply TT3_not_good.
  - exists ((g ((cst b) ? ((cst e) ! (cst y) • 𝟘)))
              ▷ ((g 𝟘) ‖ (((cst b) ! (cst w) • 𝟘) ‖ (g ((cst e) ? (g ①)))))).
    eapply ParSync; [ apply dual_io | | ].
    + unfold MC.
      assert (E : ((g ((cst b) ? ((cst e) ! (cst y) • 𝟘))) : proc) ^ (cst v)
                  = g ((cst b) ? ((cst e) ! (cst y) • 𝟘))) by reflexivity.
      rewrite <- E at 2. apply lts_input.
    + unfold TT3. apply lts_parL. apply lts_output.
  - intros p' Hp'. unfold MC in Hp'. blast3.
  - intros t' Ht'. exfalso. eapply TT3_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'. unfold MC in Hp'. unfold TT3 in Ht'. blast3.
    exact level2b.
Qed.

Theorem MC_not_below_nil : ~ ((g MC) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc)).
Proof.
  intro Hle. rewrite below_nil_iff in Hle.
  eapply Hle; [ apply TT3_no_tau | apply TT3_not_good | apply MC_passes_TT3 ].
Qed.

(** ** A PENDING MESSAGE IS RIGID: it can be neither dropped nor added

    [VACCS_NormalForm.msgs_buffer_iff] says a syntactic message bag is
    the forwarder's buffer.  These two probes say the bag is *observable*
    — a configuration [msgs l ‖ p] is comparable to [msgs l' ‖ q] only
    when the two bags genuinely account for each other, never by
    forgetting or inventing a message.

    Recall [ctx_pre p q] is [∀ t, p must_pass t -> q must_pass t]: [p ⊑ q]
    means every test [p] passes, [q] passes.

    - **Not droppable** ([msg_not_below_nil]): the probe [SINK := a ? ①]
      is τ-stuck and not good, and [a!v•𝟘] passes it — it hands the
      message over and the client succeeds — while [𝟘] fails it, having
      nothing to offer ([nil_fails_stuck]).
    - **Not addable** ([nil_not_below_msg]): the probe
      [TSINK := 𝛕•① + a?𝟘] is passed by [𝟘] (its own [𝛕] reaches [①]),
      and failed by [a!v•𝟘] — the message is absorbed by the [a]-branch,
      leaving [𝟘] against [𝟘].

    So the message layer of the normal form cannot be normalised away,
    and the two bags cannot be aligned by any rule that changes one of
    them alone: [ax_par] is the only congruence for [‖], and it needs the
    two bags related by [⊑] already, which the probes forbid unless they
    match. *)

Definition MSG : proc := (cst a) ! (cst v) • 𝟘.
Definition SINK : proc := g ((cst a) ? (g ①)).
Definition TSINK : proc := g ((𝛕 • (g ①)) + ((cst a) ? (g 𝟘))).

Lemma SINK_no_tau : forall q, ~ lts SINK τ q.
Proof. intros q Hq. unfold SINK in Hq. blast3. Qed.

Lemma SINK_not_good : ~ good_VACCS SINK.
Proof. intro Hg. unfold SINK in Hg. inversion Hg. Qed.

Lemma MSG_passes_SINK : MSG must_pass SINK.
Proof.
  apply m_step.
  - apply SINK_not_good.
  - unfold MSG, SINK. eexists.
    eapply (ParSync (ActOut (cst a, cst v)) (ActIn (cst a, cst v)));
      [ simpl; reflexivity | apply lts_output | apply lts_input ].
  - intros p' Hp'. unfold MSG in Hp'. blast3.
  - intros t' Ht'. exfalso. eapply SINK_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold MSG in Hp'. inversion Hp'; subst.
    unfold SINK in Ht'. inversion Ht'; subst.
    apply m_now. simpl. constructor.
Qed.

Theorem msg_not_below_nil : ~ (MSG ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc)).
Proof.
  intro Hle. rewrite below_nil_iff in Hle.
  eapply Hle; [ apply SINK_no_tau | apply SINK_not_good | apply MSG_passes_SINK ].
Qed.

Lemma TSINK_not_good : ~ good_VACCS TSINK.
Proof. intro Hg. unfold TSINK in Hg. inversion Hg; subst.
  match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end. Qed.

Lemma TSINK_tau : lts TSINK τ ((g ①) : proc).
Proof. unfold TSINK. apply lts_choiceL. apply lts_tau. Qed.

Lemma nil_passes_TSINK : ((g 𝟘) : proc) must_pass TSINK.
Proof.
  apply m_step.
  - apply TSINK_not_good.
  - eexists. apply ParRight. apply TSINK_tau.
  - intros p' Hp'. blast3.
  - intros t' Ht'. unfold TSINK in Ht'. inversion Ht'; subst.
    + inversion H3; subst. apply m_now. simpl. constructor.
    + inversion H3.
  - intros p' t' mu1 mu2 Hd Hp' Ht'. blast3.
Qed.

Lemma MSG_fails_TSINK : ~ (MSG must_pass TSINK).
Proof.
  intro Hm. inversion Hm; subst.
  - apply TSINK_not_good. assumption.
  - match goal with Hc : forall _ _ _ _, _ |- _ =>
      assert (Hbad : ((g 𝟘) : proc) must_pass ((g 𝟘) : proc))
    end.
    { match goal with Hc : forall _ _ _ _, _ |- _ =>
        eapply (Hc ((g 𝟘) : proc) ((g 𝟘) : proc)
                   (ActOut (cst a, cst v)) (ActIn (cst a, cst v)))
      end.
      - simpl. reflexivity.
      - unfold MSG. apply lts_output.
      - unfold TSINK. apply lts_choiceR.
        assert (E : ((g 𝟘) : proc) ^ (cst v) = ((g 𝟘) : proc)) by reflexivity.
        rewrite <- E at 2. apply lts_input. }
    eapply nil_fails_stuck; [ | | exact Hbad ].
    + intros q Hq. blast3.
    + intro Hg. inversion Hg.
Qed.

Theorem nil_not_below_msg : ~ (((g 𝟘) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ MSG).
Proof.
  intro Hle. apply MSG_fails_TSINK. apply Hle. apply nil_passes_TSINK.
Qed.

(** * The τ-successor cannot always be chosen

    [ax_tau_step] lets a derivation move *up* to a τ-successor, and that is
    the one route that handles an **unstable** left-hand side (see
    [VACCS_Bad.ax_unstable_delivery_below_nil]).  It works exactly when
    *some* successor is itself below the right-hand side.  It is not a
    general route:

        P1 := (b ? Ke) + (a ? 𝟘)        Ke := e!y•𝟘
        P2 := (a ? Ke) + (b ? 𝟘)
        PC := 𝛕•(g P1) + 𝛕•(g P2)

    [PC ⊑ₘᵤₛₜᵢ 𝟘] while **neither** of its two τ-successors is.

    Why it works, and why the obvious attempt does not.  Each [Pi] helps
    one client — [P1] takes a [b]-message and answers on [e], so it passes
    the τ-stuck non-good [UU] — hence neither is below [𝟘].  But no client
    is helped by *both*, because of the **dead guard**: an input guard
    with continuation [𝟘] converts "I do not need channel [x]" into "I
    forbid the client to offer [x]" ([dead_guard_blocks]), while [ex]
    forces the client to offer one of the two channels
    ([guard_forces_emit]).  So [P1] passing [u] forces [u] to emit on [b]
    and not on [a], and [P2] forces the exact opposite.  Since [must]'s
    [pt] field demands *all* τ-successors pass, [PC] fails every τ-stuck
    non-good client, which by [VACCS_Bad.below_nil_iff] is exactly
    [PC ⊑ₘᵤₛₜᵢ 𝟘].

    Without the dead guards the two successors are independent and the
    union client [(b!w•𝟘) ‖ (a!w•𝟘) ‖ (e?①)] is passed by both — so [PC]
    passes it too and is *not* below [𝟘].  That is what makes the dead
    guard the load-bearing part of the construction. *)

Lemma dead_guard_blocks : forall (c1 c2 : ChannelData) (X : proc) (u : proc)
    (z : ValueData) (u' : proc),
  (forall q : proc, ~ lts u τ q) -> ~ good_VACCS u ->
  (g ((c1 ? X) + (c2 ? ((g 𝟘) : proc)))) must_pass u ->
  ~ lts u ((c2 ▷ z) !) u'.
Proof.
  intros c1 c2 X u z u' Hst Hng Hm Hl.
  inversion Hm; subst; [ contradiction | ].
  assert (Hg : lts (g ((c1 ? X) + (c2 ? ((g 𝟘) : proc)))) ((c2 ▷ z) ?) ((g 𝟘) : proc)).
  { apply lts_choiceR.
    assert (E : ((g 𝟘) : proc) ^ z = ((g 𝟘) : proc)) by reflexivity.
    rewrite <- E at 2. apply lts_input. }
  assert (Hdual : dual (ActIn (c2 ▷ z)) (ActOut (c2 ▷ z))) by (simpl; reflexivity).
  pose proof (com _ _ _ _ Hdual Hg Hl) as Hd.
  destruct (out_residue u c2 z u' Hst Hng Hl) as (Hst' & Hng').
  eapply nil_fails_stuck; [ exact Hst' | exact Hng' | exact Hd ].
Qed.

Lemma guard_forces_emit : forall (c1 c2 : ChannelData) (X Y : proc) (u : proc),
  (forall q : proc, ~ lts u τ q) -> ~ good_VACCS u ->
  (g ((c1 ? X) + (c2 ? Y))) must_pass u ->
  (exists z u', lts u ((c1 ▷ z) !) u') \/ (exists z u', lts u ((c2 ▷ z) !) u').
Proof.
  intros c1 c2 X Y u Hst Hng Hm.
  inversion Hm; subst; [ contradiction | ].
  destruct ex as ((x1,x2) & Hs). inversion Hs; subst.
  - exfalso. inversion l; subst. all: inversion H3.
  - exfalso. eapply Hst; eassumption.
  - inversion l1; subst.
    + inversion H3; subst.
      destruct μ2 as [x|x]; simpl in eq; try contradiction. subst x.
      left. exists v0, x2. exact l2.
    + inversion H3; subst.
      destruct μ2 as [x|x]; simpl in eq; try contradiction. subst x.
      right. exists v0, x2. exact l2.
Qed.

Definition P1 : gproc := ((cst b) ? Ke) + ((cst a) ? ((g 𝟘) : proc)).
Definition P2 : gproc := ((cst a) ? Ke) + ((cst b) ? ((g 𝟘) : proc)).
Definition UU2 : proc := ((cst a) ! (cst w) • 𝟘) ‖ (g ((cst e) ? (g ①))).
Definition PC : gproc := (𝛕 • ((g P1) : proc)) + (𝛕 • ((g P2) : proc)).

Lemma P1_passes_UU : ((g P1) : proc) must_pass UU.
Proof.
  apply m_step.
  - apply UU_not_good.
  - exists (Ke ▷ ((g 𝟘) ‖ (g ((cst e) ? (g ①))))).
    eapply ParSync; [ apply dual_io | | ].
    + unfold P1. apply lts_choiceL.
      assert (E : Ke ^ (cst w) = Ke) by reflexivity.
      rewrite <- E at 2. apply lts_input.
    + unfold UU. apply lts_parL. apply lts_output.
  - intros p' Hp'. unfold P1 in Hp'. blast3.
  - intros t' Ht'. exfalso. eapply UU_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold P1 in Hp'. unfold UU in Ht'. blast3.
    apply m_step.
    + intro Hg. inversion Hg; subst.
      match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
    + exists ((g 𝟘) ▷ ((g 𝟘) ‖ (g ①))).
      eapply ParSync; [ apply dual_out_in | apply lts_output | ].
      apply lts_parR.
      assert (E : ((g ①) : proc) ^ (cst y) = g ①) by reflexivity.
      rewrite <- E. apply lts_input.
    + intros p' Hp'. blast3.
    + intros t' Ht'. blast3.
    + intros p' t' mu1' mu2' Hd2 Hp' Ht'. blast3.
      apply m_now. apply good_par. right. apply good_success.
Qed.

Lemma UU2_no_tau : forall q, ~ lts UU2 τ q.
Proof. intros q Hl. unfold UU2 in Hl. blast3. Qed.

Lemma UU2_not_good : ~ good_VACCS UU2.
Proof.
  intro H. unfold UU2 in H. inversion H; subst.
  match goal with H0 : _ \/ _ |- _ => destruct H0 as [H0|H0]; inversion H0 end.
Qed.

Lemma P2_passes_UU2 : ((g P2) : proc) must_pass UU2.
Proof.
  apply m_step.
  - apply UU2_not_good.
  - exists (Ke ▷ ((g 𝟘) ‖ (g ((cst e) ? (g ①))))).
    eapply ParSync; [ apply dual_io | | ].
    + unfold P2. apply lts_choiceL.
      assert (E : Ke ^ (cst w) = Ke) by reflexivity.
      rewrite <- E at 2. apply lts_input.
    + unfold UU2. apply lts_parL. apply lts_output.
  - intros p' Hp'. unfold P2 in Hp'. blast3.
  - intros t' Ht'. exfalso. eapply UU2_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold P2 in Hp'. unfold UU2 in Ht'. blast3.
    apply m_step.
    + intro Hg. inversion Hg; subst.
      match goal with H0 : _ \/ _ |- _ => destruct H0 as [H0|H0]; inversion H0 end.
    + exists ((g 𝟘) ▷ ((g 𝟘) ‖ (g ①))).
      eapply ParSync; [ apply dual_out_in | apply lts_output | ].
      apply lts_parR.
      assert (E : ((g ①) : proc) ^ (cst y) = g ①) by reflexivity.
      rewrite <- E. apply lts_input.
    + intros p' Hp'. blast3.
    + intros t' Ht'. blast3.
    + intros p' t' mu1' mu2' Hd2 Hp' Ht'. blast3.
      apply m_now. apply good_par. right. apply good_success.
Qed.

Lemma P1_not_below_nil : ~ (((g P1) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc)).
Proof.
  intro H. apply (proj1 (below_nil_iff _) H UU UU_no_tau UU_not_good).
  apply P1_passes_UU.
Qed.

Lemma P2_not_below_nil : ~ (((g P2) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc)).
Proof.
  intro H. apply (proj1 (below_nil_iff _) H UU2 UU2_no_tau UU2_not_good).
  apply P2_passes_UU2.
Qed.

Lemma PC_below_nil : ((g PC) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof.
  apply below_nil_iff. intros u Hst Hng Hm.
  inversion Hm; subst; [ contradiction | ].
  assert (H1 : ((g P1) : proc) must_pass u)
    by (apply pt; unfold PC; apply lts_choiceL; apply lts_tau).
  assert (H2 : ((g P2) : proc) must_pass u)
    by (apply pt; unfold PC; apply lts_choiceR; apply lts_tau).
  unfold P1 in H1. unfold P2 in H2.
  destruct (guard_forces_emit (cst b) (cst a) Ke ((g 𝟘) : proc) u Hst Hng H1)
    as [(z & u' & Hl) | (z & u' & Hl)].
  - exact (dead_guard_blocks (cst a) (cst b) Ke u z u' Hst Hng H2 Hl).
  - exact (dead_guard_blocks (cst b) (cst a) Ke u z u' Hst Hng H1 Hl).
Qed.

Theorem tau_successor_cannot_be_chosen :
  (((g PC) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc))
  /\ (forall p', lts ((g PC) : proc) τ p' -> ~ (p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc))).
Proof.
  split; [ apply PC_below_nil | ].
  intros p' Hl. unfold PC in Hl. inversion Hl; subst.
  - inversion H3; subst. apply P1_not_below_nil.
  - inversion H3; subst. apply P2_not_below_nil.
Qed.

(** …and yet [⊢ g PC ⊑ g 𝟘] IS derivable — by [ax_share_in]

    The negative result above says no *single* τ-successor works.  It does
    not say the inequation is out of reach, and it is not: the rule that
    reaches it is the one designed for exactly this shape, namely
    [ax_share_in], which consumes **both** branches of an internal choice
    at once and pools their continuations at a shared channel.

    The derivation is five steps.  Commute [P2]'s summands so both
    branches lead with a [b]-guard; [ax_share_in] pools the two
    [b]-continuations into [Ke ⊕ 𝟘] and keeps the *first* branch's residue
    [a ? 𝟘]; [ax_choice_input] rewrites that continuation to [𝟘] by
    [ax_int_r]; then [ax_input_drop] removes the [b]-guard and, after one
    [ax_cgr], the [a]-guard, both because [𝟘] is [Harmless].

    So the moral is not that the system is incomplete here, but that the
    left-hand rule the unstable case needs is a **branch-pooling** one —
    `ax_share_in`'s shape — rather than a branch-selecting one
    ([ax_tau_step]).  Whether the existing pooling rules suffice in
    general is exactly the remaining open question. *)

Lemma ax_PC_below_nil : ax_pre ((g PC) : proc) ((g 𝟘) : proc).
Proof.
  unfold PC, P1, P2.
  eapply ax_trans.
  { apply ax_cgr. apply cgr_fullchoice; [ reflexivity | ].
    apply cgr_tau. apply cgr_choice_com. }
  eapply ax_trans; [ apply (ax_share_in (cst b) Ke ((g 𝟘) : proc)
                                        ((cst a) ? ((g 𝟘) : proc))
                                        ((cst a) ? Ke)) | ].
  eapply ax_trans.
  { apply (ax_choice_input (cst b) ((g ((𝛕 • Ke) + (𝛕 • ((g 𝟘) : proc)))) : proc)
                           ((g 𝟘) : proc) ((cst a) ? ((g 𝟘) : proc))).
    intro v0. simpl. apply ax_int_r. }
  eapply ax_trans.
  { apply (ax_input_drop (cst b) ((g 𝟘) : proc) ((cst a) ? ((g 𝟘) : proc))).
    intro v0. simpl. apply bad_nil_any. }
  eapply ax_trans; [ apply ax_cgr_sym; apply cgr_choice_nil | ].
  apply (ax_input_drop (cst a) ((g 𝟘) : proc) 𝟘).
  intro v0. simpl. apply bad_nil_any.
Qed.

(** * A τ on the RIGHT also breaks bag matching

    [VACCS_NormalForm.bags_agree] forces the two message bags equal under
    two hypotheses: the left configuration is τ-stable, and the right's
    sum has no τ.  The first was shown necessary by
    [VACCS_Bad.unstable_delivery_below_nil].  The second is necessary too:

    read as configurations, the left below is [msgs [(c,z)] ‖ g 𝟘] (up to
    [≡*]) and the right is [msgs [] ‖ g (𝛕 • (c!z•𝟘))] — bags [[(c,z)]]
    and [[]].  The inequation holds because a `𝛕` makes [ex] free: the
    right-hand side satisfies its own [ex] with its internal step, so it
    passes *more* tests than the plain message does, and the message it
    will emit only has to appear after that step.

    Consequence for the completeness assembly: bag matching cannot be
    postponed until after the right's τ-layer has been peeled
    ([ax_below_gsum_bag]), because that driver already compares two
    configurations at a **common** bag — yet it also cannot be done
    before, because [bags_agree] needs the τ-layer gone.  That is a second,
    independent place where the unstable case bites. *)

Lemma msg_below_tau_msg : forall (c : ChannelData) (z : ValueData),
  ((c ! z • 𝟘) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g (𝛕 • ((c ! z • 𝟘) : proc))).
Proof.
  intros c z t Hm.
  remember ((c ! z • 𝟘) : proc) as S eqn:HS.
  revert HS. induction Hm as [ S t Ho | S t Ho Hex Hpt IHpt Het IHet Hcom IHcom ];
    intro HS; subst.
  - now apply m_now.
  - apply m_step.
    + exact Ho.
    + exists (((c ! z • 𝟘) : proc) ▷ t). eapply ParLeft. apply lts_tau.
    + intros x Hx. inversion Hx; subst. apply m_step; assumption.
    + intros t' Ht'. eapply IHet; [ exact Ht' | reflexivity ].
    + intros x t' mu1 mu2 Hd Hx Ht'. inversion Hx.
Qed.


(** * THE CERTIFICATE OF PHASE A IS FALSE — [CertAll] refuted

    [VACCS_Matching.CertAll] reduces the whole matching argument to one
    statement: the left process, handed any buffer the right refuses,
    settles without emitting outside it.  It is **false**, and the
    counterexample is small:

      M := (a ? (a ! x • 𝟘)) + (b ? (e ! y • 𝟘))     N := 𝟘
      l := [(a,v)]                                    K := {(b,w)}

    - **The hypothesis holds.**  [msgs l ‖ g M] has a τ — delivering
      [a!v] into the copycat — and that τ **commits** the guarded choice,
      throwing the [b] summand away.  Its target is
      [(𝟘 ‖ 𝟘) ‖ (a!v•𝟘) ≡* msgs l ‖ g 𝟘], the right-hand side itself, so
      [must_i_tau_below] gives the inequation outright.
    - **The mirror is stable at [K]**: [N = 𝟘] has no guard, so the
      mirror is [𝟘] and refuses everything.
    - **And the certificate fails.**  [(g M ▷ K)] is *not* stable — [K]
      carries [(b,w)] and [M] guards [b] — and its only τ delivers it,
      committing the choice the other way and reaching [(e!y•𝟘 ▷ ∅)],
      which is stable and emits on [e ∉ chans K].  That is the only
      stable state reachable, so [Settles (chans K) (g M ▷ K)] is false.

    What makes it work is exactly what [VACCS_ChoiceProbes] first
    isolated: **guarded choice commits**.  The τ that makes the
    hypothesis true (deliver [a]) and the τ that makes the certificate
    false (deliver [b]) are *incompatible* — each discards the other's
    guard.  The certificate, which speaks of the buffer [K] alone, sees
    only the second; the hypothesis, which speaks of the bag [l], sees
    only the first.

    So [ax_phaseA_direct] cannot be discharged in general: its premise is
    false at the intended instances, not merely out of reach.  Note that
    **Phase A itself remains true here** — the inequation is derivable in
    one [ax_tau_step] — so it is the *route* through a settling
    simulation that falls, not the statement. *)

Definition MCert : gproc :=
  ((cst a) ? ((cst a) ! (bvar 0) • 𝟘)) + ((cst b) ? (cst e ! cst y • 𝟘)).
Definition KCert : MO (ExtAct TypeOfActions) := {[+ ActOut (cst b ▷ cst w) +]}.

Lemma MCert_no_tau : forall z, ~ lts (g MCert) τ z.
Proof. intros z Hz. unfold MCert in Hz. inversion Hz; subst; inversion H3. Qed.

Lemma MCert_in_inv : forall c0 v0 p', lts (g MCert) (ActExt (ActIn (c0,v0))) p' ->
  (c0 = cst a /\ p' = ((cst a) ! v0 • 𝟘)) \/ (c0 = cst b /\ p' = (cst e ! cst y • 𝟘)).
Proof.
  intros c0 v0 p' Hl. unfold MCert in Hl. inversion Hl; subst.
  - inversion H3; subst. left. split; reflexivity.
  - inversion H3; subst. right. split; reflexivity.
Qed.

Lemma MCert_step_inv : forall x, ((g MCert) ▷ KCert) ⟶ x ->
  x = ((cst e ! cst y • 𝟘) ▷ (∅ : MO (ExtAct TypeOfActions))).
Proof.
  intros x Hx.
  apply fw_tau_shape in Hx as [ (p' & Hp' & Ex) | (a0 & p' & m' & Hm & Hin & Ex) ].
  - exfalso. eapply MCert_no_tau. exact Hp'.
  - assert (Ha0 : ActOut a0 ∈ KCert).
    { rewrite Hm. apply gmultiset_elem_of_disj_union. left.
      apply gmultiset_elem_of_singleton. reflexivity. }
    unfold KCert in Ha0. apply gmultiset_elem_of_singleton in Ha0.
    injection Ha0 as Ha0. subst a0.
    assert (Em : m' = (∅ : MO (ExtAct TypeOfActions))).
    { eapply gmultiset_disj_union_inj_1. unfold KCert in Hm.
      rewrite gmultiset_disj_union_right_id. symmetry. exact Hm. }
    subst m'.
    destruct (MCert_in_inv _ _ _ Hin) as [ (Ec & Ep) | (Ec & Ep) ].
    + exfalso. injection Ec as Ec. apply nab. symmetry. exact Ec.
    + subst p'. exact Ex.
Qed.

Lemma MCert_deliver :
  ((g MCert) ▷ KCert) ⟶ ((cst e ! cst y • 𝟘) ▷ (∅ : MO (ExtAct TypeOfActions))).
Proof.
  assert (EK : KCert = {[+ ActOut (cst b ▷ cst w) +]} ⊎ (∅ : MO (ExtAct TypeOfActions))).
  { unfold KCert. symmetry. apply gmultiset_disj_union_right_id. }
  rewrite EK. apply fw_tau_deliver. apply lts_choiceR.
  assert (E : (cst e ! cst y • 𝟘 : proc) = ((cst e ! cst y • 𝟘) ^ (cst w))) by reflexivity.
  rewrite E at 2. apply lts_input.
Qed.

Lemma MCert_msg_stable : ((cst e ! cst y • 𝟘) ▷ (∅ : MO (ExtAct TypeOfActions))) ↛.
Proof.
  apply stable_of_no_step. apply fw_stable_iff. split.
  - intros z Hz. inversion Hz.
  - intros a0 Hin. exfalso. eapply gmultiset_not_elem_of_empty. exact Hin.
Qed.

Theorem MCert_not_settles : ~ Settles (chans KCert) ((g MCert) ▷ KCert).
Proof.
  intros (z & Hw & Hst & Hem).
  assert (Ez : z = ((cst e ! cst y • 𝟘) ▷ (∅ : MO (ExtAct TypeOfActions)))).
  { inversion Hw; subst.
    - exfalso. eapply no_step_of_stable; [ exact Hst | apply MCert_deliver ].
    - assert (Ey : q = ((cst e ! cst y • 𝟘) ▷ (∅ : MO (ExtAct TypeOfActions))))
        by (apply MCert_step_inv; assumption).
      subst q. eapply wt_nil_stable_fw; [ apply MCert_msg_stable | assumption ]. }
  subst z.
  assert (Hd : chans KCert (cst e)).
  { eapply Hem. instantiate (1 := (g 𝟘 ▷ (∅ : MO (ExtAct TypeOfActions)))).
    apply fw_ext_left. apply lts_output. }
  destruct Hd as (w' & Hw').
  unfold KCert in Hw'. apply gmultiset_elem_of_singleton in Hw'.
  injection Hw' as E1 E2. apply nbe. symmetry. exact E1.
Qed.

Lemma MCert_below :
  (msgs [(cst a ▷ cst v)] ‖ g MCert) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs [(cst a ▷ cst v)] ‖ g 𝟘).
Proof.
  assert (Hstep : lts (msgs [(cst a ▷ cst v)] ‖ g MCert) τ
                      (((g 𝟘) ‖ (g 𝟘)) ‖ ((cst a) ! cst v • 𝟘))).
  { simpl. eapply lts_comL.
    - apply lts_parL. apply lts_output.
    - apply lts_choiceL.
      assert (E : ((cst a) ! cst v • 𝟘 : proc) = (((cst a) ! (bvar 0) • 𝟘) ^ (cst v)))
        by reflexivity.
      rewrite E. apply lts_input. }
  assert (Hc : (((g 𝟘) ‖ (g 𝟘)) ‖ ((cst a) ! cst v • 𝟘))
                 ≡* (msgs [(cst a ▷ cst v)] ‖ (g 𝟘))).
  { simpl.
    etransitivity; [ apply cgr_par_com | ].
    etransitivity; [ apply cgr_fullpar; [ reflexivity | apply cgr_par_nil ] | ].
    etransitivity; [ apply cgr_par_nil | ].
    symmetry. etransitivity; [ apply cgr_par_nil | apply cgr_par_nil ]. }
  intros t Hm.
  apply (proj2 (must_i_cgr _ _ Hc)).
  eapply must_i_tau_below; [ exact Hstep | exact Hm ].
Qed.


Theorem CertAll_is_false : ~ CertAll.
Proof.
  intro H. apply MCert_not_settles.
  eapply (H MCert 𝟘 [(cst a ▷ cst v)]).
  - repeat constructor.
  - constructor.
  - intros z Hz. inversion Hz.
  - apply MCert_below.
  - intros x Hx. unfold KCert in Hx.
    apply gmultiset_elem_of_singleton in Hx. subst x.
    exists (cst b ▷ cst w). reflexivity.
  - apply stable_of_no_step. apply fw_stable_iff. simpl. split.
    + intros z Hz. inversion Hz.
    + intros a0 Hin q Hq. inversion Hq.
Qed.


(** * …AND CHOOSING A DELIVERY DOES NOT WORK EITHER

    With the settling route refuted, the natural remaining move for an
    unstable configuration is [ax_tau_step]: descend to a **delivery**
    successor and recurse.  [tau_successor_cannot_be_chosen] does not
    forbid it — that counterexample is a guarded sum with [𝛕]-summands,
    not a configuration.  This one is.

      MD   := (a ? P1) + (a ? P2)          PCfg := msgs [(a,v)] ‖ g MD

    One pending message, two guards on its channel: delivering it is the
    configuration's only τ, and it can go **either way**.  The two
    successors are [P1] and [P2] of the earlier probe — the pair whose
    demands are contradictory because each carries a *dead guard* on the
    channel the other needs.

    - [PCfg ⊑ₘᵤₛₜᵢ 𝟘]: a τ-stuck non-good client passed by [PCfg] would,
      through [must]'s [pt] field, be passed by **both** successors, and
      [must_i_tau_choice_join] would then make [PC] pass it — which
      [PC_below_nil] forbids.
    - and **neither successor is below [𝟘]** ([P1_not_below_nil],
      [P2_not_below_nil]).

    So the answer to "is some delivery successor still below the target?"
    is **no**, and the mechanism is the one this development keeps
    meeting: guarded choice **commits**, so the two deliveries are
    incompatible, and the semantics only ever constrains their
    conjunction. *)

Definition MD : gproc := ((cst a) ? ((g P1) : proc)) + ((cst a) ? ((g P2) : proc)).
Definition PCfg : proc := msgs [(cst a ▷ cst v)] ‖ g MD.

Lemma MD_no_tau : forall z, ~ lts (g MD) τ z.
Proof. intros z Hz. unfold MD in Hz. inversion Hz; subst; inversion H3. Qed.

Lemma PCfg_step_inv : forall x, lts PCfg τ x ->
  x = (((g 𝟘) ‖ (g 𝟘)) ‖ ((g P1) : proc))
  \/ x = (((g 𝟘) ‖ (g 𝟘)) ‖ ((g P2) : proc)).
Proof.
  intros x Hx. unfold PCfg in Hx. inversion Hx; subst.
  - unfold MD in H2. inversion H2; subst.
    + inversion H5; subst. left. inversion H1; subst.
      * inversion H6; subst. reflexivity.
      * exfalso. inversion H6.
    + inversion H5; subst. right. inversion H1; subst.
      * inversion H6; subst. reflexivity.
      * exfalso. inversion H6.
  - exfalso. inversion H2; subst; inversion H5.
  - exfalso. inversion H3; subst.
    + inversion H2.
    + inversion H1.
    + inversion H4.
    + inversion H4.
  - exfalso. eapply MD_no_tau. eassumption.
Qed.

Lemma PCfg_deliver1 : lts PCfg τ (((g 𝟘) ‖ (g 𝟘)) ‖ ((g P1) : proc)).
Proof.
  unfold PCfg, MD. simpl. eapply lts_comL.
  - apply lts_parL. apply lts_output.
  - apply lts_choiceL.
    assert (E : ((g P1) : proc) = (((g P1) : proc) ^ (cst v))) by reflexivity.
    rewrite E. apply lts_input.
Qed.

Lemma PCfg_deliver2 : lts PCfg τ (((g 𝟘) ‖ (g 𝟘)) ‖ ((g P2) : proc)).
Proof.
  unfold PCfg, MD. simpl. eapply lts_comL.
  - apply lts_parL. apply lts_output.
  - apply lts_choiceR.
    assert (E : ((g P2) : proc) = (((g P2) : proc) ^ (cst v))) by reflexivity.
    rewrite E. apply lts_input.
Qed.

Lemma nilnil_cgr : forall (P : proc), (((g 𝟘) ‖ (g 𝟘)) ‖ P) ≡* P.
Proof.
  intro P.
  etransitivity; [ apply cgr_fullpar; [ apply cgr_par_nil | reflexivity ] | ].
  etransitivity; [ apply cgr_par_com | apply cgr_par_nil ].
Qed.

Lemma PCfg_below_nil : PCfg ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof.
  apply below_nil_iff. intros u Hst Hng Hm.
  inversion Hm as [Hg | Hnh Hex Hpt Het Hcom]; subst; [ contradiction | ].
  assert (Hm1 : ((g P1) : proc) must_pass u).
  { apply (proj2 (must_i_cgr _ _ (nilnil_cgr ((g P1) : proc)))).
    apply Hpt. apply PCfg_deliver1. }
  assert (Hm2 : ((g P2) : proc) must_pass u).
  { apply (proj2 (must_i_cgr _ _ (nilnil_cgr ((g P2) : proc)))).
    apply Hpt. apply PCfg_deliver2. }
  eapply (proj1 (below_nil_iff _) PC_below_nil u Hst Hng).
  apply must_i_tau_choice_join; assumption.
Qed.

Theorem delivery_successor_cannot_be_chosen :
  (PCfg ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc))
  /\ (forall p', lts PCfg τ p' -> ~ (p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc))).
Proof.
  split; [ apply PCfg_below_nil | ].
  intros p' Hp' Hsub.
  destruct (PCfg_step_inv p' Hp') as [E|E]; subst p'.
  - apply P1_not_below_nil. intros t Hm.
    apply Hsub. apply (proj1 (must_i_cgr _ _ (nilnil_cgr ((g P1) : proc)))). exact Hm.
  - apply P2_not_below_nil. intros t Hm.
    apply Hsub. apply (proj1 (must_i_cgr _ _ (nilnil_cgr ((g P2) : proc)))). exact Hm.
Qed.


(** * …BUT CANONICALISATION REPAIRS IT

    The counterexample above is an artefact of **non-canonicity**: [MD]
    has *two* guards on the same channel, which is exactly what
    [VACCS_Canonical.canonicalize] removes.  Merge them with
    [ax_input_distrib_l] and the picture changes completely:

      MDc := a ? (P1 ⊕ P2)        PCfgC := msgs [(a,v)] ‖ g MDc

    - the merge is **derivable**: [⊢ PCfg ⊑ PCfgC] ([ax_PCfg_merge]);
    - the delivery is now **deterministic** ([PCfgC_step_inv]) — one
      guard, one successor;
    - and that successor **is** below the target, because it is
      [P1 ⊕ P2 = PC] itself, which [PC_below_nil] settles.

    So on a canonical sum, "choose a delivery successor" is not a choice
    at all, and the obstruction that
    [delivery_successor_cannot_be_chosen] exhibits disappears.  That is
    what [canonicalize] is *for*: it was proved for [Bad]'s sake, and it
    turns out to be what makes the delivery step deterministic too.

    What this does **not** settle is a bag with several messages on
    *different* channels: those deliveries cannot be merged, since
    [ax_input_distrib_l] only merges guards on the same channel.  That is
    the remaining shape to investigate. *)

Definition MDc : gproc := (cst a) ? ((g PC) : proc).
Definition PCfgC : proc := msgs [(cst a ▷ cst v)] ‖ g MDc.

Lemma ax_PCfg_merge : ax_pre PCfg PCfgC.
Proof.
  unfold PCfg, PCfgC. apply ax_par; [ apply ax_refl | ].
  eapply ax_trans; [ apply ax_cgr; apply cgr_choice_nil_rev | ].
  eapply ax_trans; [ apply (ax_input_distrib_l (cst a) ((g P1) : proc) ((g P2) : proc) 𝟘) | ].
  apply ax_cgr. apply cgr_choice_nil.
Qed.

Lemma PCfgC_step_inv : forall x, lts PCfgC τ x ->
  x = (((g 𝟘) ‖ (g 𝟘)) ‖ ((g PC) : proc)).
Proof.
  intros x Hx. unfold PCfgC, MDc in Hx. inversion Hx; subst.
  - inversion H2; subst. inversion H1; subst.
    + inversion H5; subst. reflexivity.
    + exfalso. inversion H5.
  - exfalso. inversion H2; subst; inversion H5.
  - exfalso. inversion H3; subst.
    + inversion H2.
    + inversion H1.
    + inversion H4.
    + inversion H4.
  - exfalso. inversion H3.
Qed.

Theorem canonical_delivery_is_deterministic_and_works :
  ax_pre PCfg PCfgC
  /\ (forall p', lts PCfgC τ p' -> p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc)).
Proof.
  split; [ apply ax_PCfg_merge | ].
  intros p' Hp'. rewrite (PCfgC_step_inv p' Hp').
  intros t Hm.
  apply PC_below_nil.
  apply (proj2 (must_i_cgr _ _ (nilnil_cgr ((g PC) : proc)))). exact Hm.
Qed.

(** ** `CfgDisjunction` sur cette instance : c'est le disjoint DESCENTE

    [VACCS_Matching.CfgDisjunction] demande, pour une configuration
    gauche instable sous sa cible, que **l'un des deux** disjoints tienne.
    Ici le disjoint « sac vide » est **faux** — [g MCert] passe le client
    τ-bloqué non bon [(b!w•𝟘) ‖ (e?①)] par sa branche [b], que [g 𝟘]
    rate — et c'est précisément ce qui a fait tomber [CertAll].  Mais la
    délivrance dans le copycat donne un successeur [≂ₘᵤₛₜᵢ] la cible,
    donc le **disjoint descente** tient. *)

Theorem cfg_disjunction_at_MCert :
  (((g MCert) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc))
  \/ (exists p', lts (msgs [(cst a ▷ cst v)] ‖ ((g MCert) : proc)) τ p'
        /\ p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs [(cst a ▷ cst v)] ‖ ((g 𝟘) : proc))).
Proof.
  right.
  exists (((g 𝟘) ‖ (g 𝟘)) ‖ ((cst a) ! cst v • 𝟘)). split.
  - simpl. eapply lts_comL.
    + apply lts_parL. apply lts_output.
    + apply lts_choiceL.
      assert (E : ((cst a) ! cst v • 𝟘 : proc) = (((cst a) ! (bvar 0) • 𝟘) ^ (cst v)))
        by reflexivity.
      rewrite E. apply lts_input.
  - assert (Hc : (((g 𝟘) ‖ (g 𝟘)) ‖ ((cst a) ! cst v • 𝟘))
                   ≡* (msgs [(cst a ▷ cst v)] ‖ (g 𝟘))).
    { simpl.
      etransitivity; [ apply cgr_par_com | ].
      etransitivity; [ apply cgr_fullpar; [ reflexivity | apply cgr_par_nil ] | ].
      etransitivity; [ apply cgr_par_nil | ].
      symmetry. etransitivity; [ apply cgr_par_nil | apply cgr_par_nil ]. }
    exact (proj2 (must_i_cgr _ _ Hc)).
Qed.

(** * …et la famille « SOURCE-ONLY » de la disjonction est FAUSSE

    [VACCS_Matching.CfgDisjunctionSource] et sa version relativisée au sac
    [CfgDisjunctionSourceBag] remplacent le second disjoint de
    [CfgDisjunction] — « un τ-successeur est sous la **cible** » — par une
    condition qui ne mentionne que la **source**.  Elles impliquent donc
    [CfgDisjunction], et l'une d'elles suffirait.

    **Aucune des deux ne tient**, et [MCert] est le contre-exemple.

    La clef est la lecture suivante : [msgs l0 ‖ Mc ≡* msgs l ‖ K] (le
    message est de retour dans le sac) et [msgs l0 ‖ Mc] est un
    τ-successeur de [msgs l ‖ g M].  Le disjoint source dit donc
    exactement « **un pas interne est réversible** » — le successeur est
    *au-dessus* de la source, [must_i_tau_below] donnant toujours l'autre
    sens.  Sur [MCert] :

    - le disjoint « sac vide » est faux : [MCert_not_below_nil], via le
      client [UCert := (b!w•𝟘) ‖ (e ? ①)], τ-bloqué et non bon, que
      [g MCert] passe (il prend [b] et répond sur [e]) ;
    - l'unique délivrance donne [Mc = a!v•𝟘], qui rend le message avec
      [K = 𝟘], donc le disjoint réclame
      [msgs l ‖ 𝟘 ⊑ₘᵤₛₜᵢ msgs l ‖ g MCert] — réfuté par [TCert].

    [TCert := (b!w•𝟘) ‖ (a ? (𝛕•① + (e ? 𝟘)))] sépare pour la raison qui
    court dans tout ce fichier : la garde **sœur** sur une voie étrangère
    au sac.  À gauche, [msgs l ‖ 𝟘 ≂ (a!v•𝟘)] passe — son [com] en [a]
    laisse [𝟘] face à un client qui réussit tout seul par son [𝛕].  À
    droite, le [com] en [b] réveille [e!y•𝟘], le [e ? 𝟘] du client
    l'absorbe, et il ne reste que [𝟘] face à [𝟘].

    C'est le même mécanisme que [VACCS_Bad.nil_not_below_dead_summand] :
    ajouter [g M] à côté du sac n'est pas gratuit dès que [M] peut
    absorber une voie que le sac ne porte pas.

    **Ce que cela ne réfute pas** : [CfgDisjunction] et
    [CfgDisjunctionLocal], dont les disjoints mentionnent la cible — sur
    [MCert] le successeur *est* [≡*] la cible, donc ils tiennent
    ([cfg_disjunction_at_MCert]).  Seules les formes source-only tombent,
    et [VACCS_Matching.cfg_source_disjunct_at_copycats] reste correct : il
    dit que la classe copycat satisfait ce disjoint, pas que tout le monde
    le fait. *)

(** ** Le client qui réfute le disjoint « sac vide » *)

Definition UCert : proc :=
  (((cst b) ! (cst w) • 𝟘) : proc) ‖ ((g ((cst e) ? ((g ①) : proc))) : proc).

Lemma UCert_not_good : ~ good_VACCS UCert.
Proof.
  intro Hg. unfold UCert in Hg. inversion Hg; subst.
  match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
Qed.

Lemma UCert_no_tau : forall z, ~ lts UCert τ z.
Proof.
  intros z H. unfold UCert in H. inversion H; subst.
  - match goal with H2 : lts (g (_ ? _)) (ActExt (ActIn _)) _ |- _ =>
      inversion H2; subst end.
    match goal with H3 : lts (_ ! _ • 𝟘) _ _ |- _ => inversion H3; subst end.
    apply nbe. reflexivity.
  - match goal with H2 : lts (g (_ ? _)) (ActExt (ActOut _)) _ |- _ => inversion H2 end.
  - match goal with H2 : lts (_ ! _ • 𝟘) τ _ |- _ => inversion H2 end.
  - match goal with H2 : lts (g (_ ? _)) τ _ |- _ => inversion H2 end.
Qed.

Lemma UCert_out_inv : forall c0 v0 t',
  lts UCert (ActExt (ActOut (c0,v0))) t' ->
  c0 = cst b /\ v0 = cst w
  /\ t' = (((g 𝟘) : proc) ‖ ((g ((cst e) ? ((g ①) : proc))) : proc)).
Proof.
  intros c0 v0 t' H. unfold UCert in H. inversion H; subst.
  - match goal with H2 : lts (_ ! _ • 𝟘) _ _ |- _ => inversion H2; subst end.
    repeat split.
  - match goal with H2 : lts (g (_ ? _)) _ _ |- _ => inversion H2 end.
Qed.

Lemma emsg_passes_esink :
  (((cst e) ! (cst y) • 𝟘) : proc) must_pass
    (((g 𝟘) : proc) ‖ ((g ((cst e) ? ((g ①) : proc))) : proc)).
Proof.
  apply m_step.
  - intro Hg. inversion Hg; subst.
    match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
  - exists (((g 𝟘) : proc) ▷ (((g 𝟘) : proc) ‖ ((g ①) : proc))).
    eapply (ParSync (ActOut (cst e, cst y)) (ActIn (cst e, cst y))).
    + simpl. reflexivity.
    + apply lts_output.
    + apply lts_parR.
      assert (E : ((g ①) : proc) = ((g ①) : proc) ^ (cst y)) by reflexivity.
      rewrite E at 2. apply lts_input.
  - intros p' Hp'. inversion Hp'.
  - intros t' Ht'. exfalso. inversion Ht'; subst.
    + match goal with H2 : lts ((g 𝟘) : proc) _ _ |- _ => inversion H2 end.
    + match goal with H2 : lts ((g 𝟘) : proc) _ _ |- _ => inversion H2 end.
    + match goal with H2 : lts ((g 𝟘) : proc) τ _ |- _ => inversion H2 end.
    + match goal with H2 : lts (g (_ ? _)) τ _ |- _ => inversion H2 end.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    inversion Hp'; subst.
    destruct mu2 as [a2|a2]; simpl in Hd; try contradiction. subst a2.
    apply m_now. inversion Ht'; subst.
    + match goal with H2 : lts ((g 𝟘) : proc) _ _ |- _ => inversion H2 end.
    + match goal with H2 : lts (g (_ ? _)) _ _ |- _ => inversion H2; subst end.
      apply good_par. right. simpl. constructor.
Qed.

Lemma MCert_passes_UCert : ((g MCert) : proc) must_pass UCert.
Proof.
  apply m_step.
  - apply UCert_not_good.
  - exists ((((cst e) ! (cst y) • 𝟘) : proc)
             ▷ (((g 𝟘) : proc) ‖ ((g ((cst e) ? ((g ①) : proc))) : proc))).
    eapply (ParSync (ActIn (cst b, cst w)) (ActOut (cst b, cst w))).
    + simpl. reflexivity.
    + unfold MCert. apply lts_choiceR.
      assert (E : (((cst e) ! (cst y) • 𝟘) : proc)
                = (((cst e) ! (cst y) • 𝟘) : proc) ^ (cst w)) by reflexivity.
      rewrite E at 2. apply lts_input.
    + unfold UCert. apply lts_parL. apply lts_output.
  - intros p' Hp'. exfalso. eapply MCert_no_tau. exact Hp'.
  - intros t' Ht'. exfalso. eapply UCert_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    destruct mu2 as [a2|a2].
    + destruct mu1 as [a1|a1]; simpl in Hd; try contradiction.
      exfalso. destruct a1 as (c1,v1).
      unfold MCert in Hp'. inversion Hp'; subst;
        match goal with H : lts (g (_ ? _)) (ActExt (ActOut _)) _ |- _ => inversion H end.
    + destruct mu1 as [a1|a1]; simpl in Hd; try contradiction. subst a1.
      destruct a2 as (c2,v2).
      destruct (UCert_out_inv _ _ _ Ht') as (Ec & Ev & Et). subst c2 v2 t'.
      destruct (MCert_in_inv _ _ _ Hp') as [ (Ec & Ep) | (Ec & Ep) ].
      * exfalso. injection Ec as Ec. apply nab. symmetry. exact Ec.
      * subst p'. apply emsg_passes_esink.
Qed.

Theorem MCert_not_below_nil : ~ (((g MCert) : proc) ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc)).
Proof.
  intro Hle.
  apply (proj1 (below_nil_iff ((g MCert) : proc)) Hle UCert).
  - apply UCert_no_tau.
  - apply UCert_not_good.
  - apply MCert_passes_UCert.
Qed.

(* ===================================================================== *)
(** * DEUX RÉFUTATIONS : LE CAS [𝛕]-SOMMANT

    Le découpage décidable de [VACCS_Bad] renvoyait d'abord le cas
    « [M] porte un [𝛕]-sommant » vers l'**annulation du sac** (le premier
    disjoint).  C'est faux, et la localisation de la disjonction l'est
    aussi.  Les deux témoins sont [MCert] augmenté d'un [𝛕]-sommant. *)

(** ** (1) Un [𝛕]-sommant n'entraîne pas l'annulation du sac

    [MTau] est [MCert] plus une branche [𝛕] vers lui-même.  Sa **branche
    de délivrance** épingle la configuration sur la cible — le message
    est rendu tel quel — donc l'inéquation de configuration est
    gratuite ; mais le [𝛕] rend le champ [ex] libre au niveau nu, si bien
    que la somme passe [UCert] et n'est pas sous [𝟘].

    Noter que le contre-exemple connu à l'annulation ([MCert] lui-même)
    ne couvrait **pas** ce cas : [MCert] est τ-stable. *)

Definition MTau : gproc := MCert + (𝛕 • ((g MCert) : proc)).

Lemma MTau_tau_inv : forall z, lts ((g MTau) : proc) τ z -> z = ((g MCert) : proc).
Proof.
  intros z Hz. unfold MTau in Hz. inversion Hz; subst.
  - exfalso. eapply MCert_no_tau. exact H3.
  - inversion H3; subst. reflexivity.
Qed.

Lemma MTau_in_inv : forall c0 v0 p',
  lts ((g MTau) : proc) (ActExt (ActIn (c0,v0))) p' ->
  (c0 = cst a /\ p' = ((cst a) ! v0 • 𝟘)) \/ (c0 = cst b /\ p' = (cst e ! cst y • 𝟘)).
Proof.
  intros c0 v0 p' Hl. unfold MTau in Hl. inversion Hl; subst.
  - apply MCert_in_inv. exact H3.
  - inversion H3.
Qed.

Lemma MTau_passes_UCert : ((g MTau) : proc) must_pass UCert.
Proof.
  apply m_step.
  - apply UCert_not_good.
  - exists (((g MCert) : proc) ▷ UCert).
    apply ParLeft. unfold MTau. apply lts_choiceR. apply lts_tau.
  - intros p' Hp'. apply MTau_tau_inv in Hp'. subst p'. apply MCert_passes_UCert.
  - intros t' Ht'. exfalso. eapply UCert_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    destruct mu2 as [a2|a2].
    + destruct mu1 as [a1|a1]; simpl in Hd; try contradiction.
      exfalso. destruct a1 as (c1,v1). eapply gsum_no_out. exact Hp'.
    + destruct mu1 as [a1|a1]; simpl in Hd; try contradiction. subst a1.
      destruct a2 as (c2,v2).
      destruct (UCert_out_inv _ _ _ Ht') as (Ec & Ev & Et). subst c2 v2 t'.
      destruct (MTau_in_inv _ _ _ Hp') as [ (Ec & Ep) | (Ec & Ep) ].
      * exfalso. injection Ec as Ec. apply nab. symmetry. exact Ec.
      * subst p'. apply emsg_passes_esink.
Qed.

Theorem MTau_not_below_nil : ~ (((g MTau) : proc) ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc)).
Proof.
  intro Hle.
  apply (proj1 (below_nil_iff ((g MTau) : proc)) Hle UCert).
  - apply UCert_no_tau.
  - apply UCert_not_good.
  - apply MTau_passes_UCert.
Qed.

Lemma MTau_below :
  (msgs [(cst a ▷ cst v)] ‖ ((g MTau) : proc))
    ⊑ₘᵤₛₜᵢ (msgs [(cst a ▷ cst v)] ‖ ((g 𝟘) : proc)).
Proof.
  assert (Hstep : lts (msgs [(cst a ▷ cst v)] ‖ ((g MTau) : proc)) τ
                      (((g 𝟘) ‖ (g 𝟘)) ‖ ((cst a) ! cst v • 𝟘))).
  { simpl. eapply lts_comL.
    - apply lts_parL. apply lts_output.
    - unfold MTau. apply lts_choiceL. unfold MCert. apply lts_choiceL.
      assert (E : ((cst a) ! cst v • 𝟘 : proc) = (((cst a) ! (bvar 0) • 𝟘) ^ (cst v)))
        by reflexivity.
      rewrite E. apply lts_input. }
  assert (Hc : (((g 𝟘) ‖ (g 𝟘)) ‖ ((cst a) ! cst v • 𝟘))
                 ≡* (msgs [(cst a ▷ cst v)] ‖ (g 𝟘))).
  { simpl.
    etransitivity; [ apply cgr_par_com | ].
    etransitivity; [ apply cgr_fullpar; [ reflexivity | apply cgr_par_nil ] | ].
    etransitivity; [ apply cgr_par_nil | ].
    symmetry. etransitivity; [ apply cgr_par_nil | apply cgr_par_nil ]. }
  intros t Hm.
  apply (proj2 (must_i_cgr _ _ Hc)).
  eapply must_i_tau_below; [ exact Hstep | exact Hm ].
Qed.

Theorem tau_summand_cancellation_is_false :
  ~ (forall (l : list TypeOfActions) (M N : gproc), gStatic M -> gStatic N ->
       (exists z, lts ((g M) : proc) τ z) ->
       (exists z, (((g M) : proc) ▷ bag l) ⟶ z) ->
       ((msgs l ‖ ((g M) : proc)) ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
       ((g M) : proc) ⊑ₘᵤₛₜᵢ ((g N) : proc)).
Proof.
  intro H. apply MTau_not_below_nil.
  apply (H [(cst a ▷ cst v)] MTau 𝟘).
  - unfold MTau, MCert. repeat constructor.
  - constructor.
  - exists ((g MCert) : proc). unfold MTau. apply lts_choiceR. apply lts_tau.
  - exists (((g MCert) : proc) ▷ bag [(cst a ▷ cst v)]). apply fw_tau_left.
    unfold MTau. apply lts_choiceR. apply lts_tau.
  - apply MTau_below.
Qed.

(** ** (2) …et [CfgDisjunctionLocal] elle-même est FAUSSE

    [MFalse] remplace la garde copycat de [MCert] par une garde
    **morte**, et garde la branche [𝛕].  Alors :

    - le premier disjoint échoue — [g MFalse] passe [UCert] par sa
      branche [𝛕], et [g 𝟘] ne le passe pas ;
    - le second aussi — l'unique délivrance mène à [𝟘], et
      [nil_not_below_msg_gen] dit qu'un [𝟘] n'est pas sous un message ;
    - et pourtant l'inéquation de configuration **tient**, portée par la
      branche [𝛕] et [MCert_below].

    C'est donc la **localisation** qui est trop forte : [CfgDisjunction],
    dont le second disjoint quantifie sur les τ-successeurs de la
    *configuration*, attrape cette branche.  La forme corrigée est
    [VACCS_Matching.CfgDisjunctionLocal3]. *)

Definition MFalse : gproc :=
  ((cst a) ? ((g 𝟘) : proc)) + (𝛕 • ((g MCert) : proc)).

Lemma MFalse_tau_inv : forall z, lts ((g MFalse) : proc) τ z -> z = ((g MCert) : proc).
Proof.
  intros z Hz. unfold MFalse in Hz. inversion Hz; subst.
  - inversion H3.
  - inversion H3; subst. reflexivity.
Qed.

Lemma MFalse_in_inv : forall c0 v0 p',
  lts ((g MFalse) : proc) (ActExt (ActIn (c0,v0))) p' ->
  c0 = cst a /\ p' = ((g 𝟘) : proc).
Proof.
  intros c0 v0 p' Hl. unfold MFalse in Hl. inversion Hl; subst.
  - inversion H3; subst. split; reflexivity.
  - inversion H3.
Qed.

Lemma MFalse_passes_UCert : ((g MFalse) : proc) must_pass UCert.
Proof.
  apply m_step.
  - apply UCert_not_good.
  - exists (((g MCert) : proc) ▷ UCert).
    apply ParLeft. unfold MFalse. apply lts_choiceR. apply lts_tau.
  - intros p' Hp'. apply MFalse_tau_inv in Hp'. subst p'. apply MCert_passes_UCert.
  - intros t' Ht'. exfalso. eapply UCert_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    destruct mu2 as [a2|a2].
    + destruct mu1 as [a1|a1]; simpl in Hd; try contradiction.
      exfalso. destruct a1 as (c1,v1). eapply gsum_no_out. exact Hp'.
    + destruct mu1 as [a1|a1]; simpl in Hd; try contradiction. subst a1.
      destruct a2 as (c2,v2).
      destruct (UCert_out_inv _ _ _ Ht') as (Ec & Ev & Et). subst c2 v2 t'.
      destruct (MFalse_in_inv _ _ _ Hp') as (Ec & Ep).
      exfalso. injection Ec as Ec. apply nab. symmetry. exact Ec.
Qed.

Theorem MFalse_not_below_nil : ~ (((g MFalse) : proc) ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc)).
Proof.
  intro Hle.
  apply (proj1 (below_nil_iff ((g MFalse) : proc)) Hle UCert).
  - apply UCert_no_tau.
  - apply UCert_not_good.
  - apply MFalse_passes_UCert.
Qed.

Lemma MFalse_below :
  (msgs [(cst a ▷ cst v)] ‖ ((g MFalse) : proc))
    ⊑ₘᵤₛₜᵢ (msgs [(cst a ▷ cst v)] ‖ ((g 𝟘) : proc)).
Proof.
  intros t Hm.
  apply MCert_below.
  eapply must_i_tau_below; [ | exact Hm ].
  apply lts_parR. unfold MFalse. apply lts_choiceR. apply lts_tau.
Qed.

Theorem CfgDisjunctionLocal_is_false : ~ CfgDisjunctionLocal.
Proof.
  intro H.
  destruct (H [(cst a ▷ cst v)] MFalse 𝟘
              ltac:(unfold MFalse, MCert; repeat constructor)
              ltac:(constructor)
              ltac:(eexists; apply fw_tau_left; unfold MFalse;
                    apply lts_choiceR; apply lts_tau)
              MFalse_below)
    as [Ha | (c0 & v0 & l0 & Mc & Hp & Hin & Hb)].
  - apply MFalse_not_below_nil. exact Ha.
  - destruct (MFalse_in_inv _ _ _ Hin) as (Ec & Ep). subst Mc.
    apply Permutation_length_1_inv in Hp. injection Hp as Hp1 Hp2.
    subst c0 v0.
    assert (Hc : (((cst a ! cst v • 𝟘) : proc) ‖ ((g 𝟘) : proc))
                   ≡* ((cst a ! cst v • 𝟘) : proc)) by apply cgr_par_nil.
    apply (nil_not_below_msg_gen (cst a) (cst v)).
    intros t Ht. apply (proj2 (must_i_cgr _ _ Hc)). apply Hb. exact Ht.
Qed.

(** ** (3) …et le TROISIÈME disjoint ne se laisse pas imposer non plus

    La forme corrigée [CfgDisjunctionLocal3] ajoute le disjoint (C) — une
    branche [𝛕] de la somme qui, sous le sac, est sous la cible.  Il
    serait tentant d'y renvoyer *tout* le cas « [g M] porte un
    [𝛕]-sommant ».  C'est faux, et le témoin est [PC], déjà au dossier :
    ses deux branches ont des exigences contradictoires, donc **aucune**
    n'est sous [𝟘] ([tau_successor_cannot_be_chosen]) alors que leur
    conjonction l'est ([PC_below_nil]).

    Ici c'est le disjoint (A) qui porte l'inéquation. *)

Theorem tau_branch_below_is_false :
  ~ (forall (l : list TypeOfActions) (M N : gproc), gStatic M -> gStatic N ->
       (exists z, lts ((g M) : proc) τ z) ->
       (exists z, (((g M) : proc) ▷ bag l) ⟶ z) ->
       ((msgs l ‖ ((g M) : proc)) ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
       (exists K, lts ((g M) : proc) τ K
          /\ (msgs l ‖ K) ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc)))).
Proof.
  intro H.
  assert (Htau : exists z, lts ((g PC) : proc) τ z).
  { exists ((g P1) : proc). unfold PC. apply lts_choiceL. apply lts_tau. }
  assert (Hsem : (msgs [] ‖ ((g PC) : proc)) ⊑ₘᵤₛₜᵢ (msgs [] ‖ ((g 𝟘) : proc))).
  { apply must_i_par_compat_r. apply PC_below_nil. }
  destruct (H [] PC 𝟘
              ltac:(unfold PC, P1, P2, Ke; repeat constructor)
              ltac:(constructor) Htau
              ltac:(destruct Htau as (z & Hz); exists (z ▷ bag []);
                    apply fw_tau_left; exact Hz)
              Hsem)
    as (K & Hk & Hb).
  apply (proj2 tau_successor_cannot_be_chosen K Hk).
  assert (Hc1 : (K : proc) ≡* (((g 𝟘) : proc) ‖ K))
    by (symmetry; apply cgr_nil_par_l).
  assert (Hc2 : (((g 𝟘) : proc) ‖ ((g 𝟘) : proc)) ≡* ((g 𝟘) : proc))
    by apply cgr_par_nil.
  intros t Ht.
  apply (proj2 (must_i_cgr _ _ Hc2)).
  apply Hb.
  apply (proj2 (must_i_cgr _ _ Hc1)). exact Ht.
Qed.

(** ** Contrôle : la forme CORRIGÉE survit aux six témoins

    [CfgDisjunctionLocal] avait été prise pour cible plusieurs sessions
    sans avoir jamais été instanciée sur un [𝛕]-sommant.  Pour ne pas
    répéter l'erreur, [VACCS_Matching.CfgDisjunctionLocal3] est vérifiée
    sur les six témoins connus :

    | témoin | disjoint |
    |---|---|
    | [𝛕 • 𝟘], [PC] | (A) — [PC_below_nil] |
    | [MCert], [MTau] | (B) |
    | [MFalse] | (C) |
    | [XProbe] | (A) — [cfg_disjunction_at_XProbe] |

    Les deux cas neufs sont ci-dessous ; les autres sont déjà au dossier
    ([cfg_disjunction_local_at_MCert], [cfg_disjunction_at_XProbe]). *)

Lemma cfg_local3_at_MFalse :
  exists K, lts ((g MFalse) : proc) τ K
    /\ (msgs [(cst a ▷ cst v)] ‖ K)
         ⊑ₘᵤₛₜᵢ (msgs [(cst a ▷ cst v)] ‖ ((g 𝟘) : proc)).
Proof.
  exists ((g MCert) : proc). split.
  - unfold MFalse. apply lts_choiceR. apply lts_tau.
  - apply MCert_below.
Qed.

Lemma cfg_local3_at_MTau :
  exists c v0 l0 Mc,
    Permutation [(cst a ▷ cst v)] ((c,v0) :: l0)
    /\ lts ((g MTau) : proc) (ActExt (ActIn (c,v0))) Mc
    /\ Mc ⊑ₘᵤₛₜᵢ (((c ! v0 • 𝟘) : proc) ‖ ((g 𝟘) : proc)).
Proof.
  exists (cst a), (cst v), [], ((cst a) ! (cst v) • 𝟘).
  split; [ reflexivity | split ].
  - unfold MTau. apply lts_choiceL. unfold MCert. apply lts_choiceL.
    assert (E : ((cst a) ! cst v • 𝟘 : proc) = (((cst a) ! (bvar 0) • 𝟘) ^ (cst v)))
      by reflexivity.
    rewrite E. apply lts_input.
  - assert (Hc : (((cst a ! cst v • 𝟘) : proc) ‖ ((g 𝟘) : proc))
                   ≡* ((cst a ! cst v • 𝟘) : proc)) by apply cgr_par_nil.
    intros t Ht. apply (proj1 (must_i_cgr _ _ Hc)). exact Ht.
Qed.

(** ** …et les deux branches de la dichotomie décidable sont atteintes

    [VACCS_Bad.cfg_derivable_or_selfret] tranche par [SelfRet].  Les deux
    issues se produisent, sur deux sommes du dossier :

    - [MCert] **rend** le message de sa garde [a] (sa continuation est le
      copycat), donc [SelfRet] — et de fait son sac ne s'annule pas
      ([VACCS_Matching.bagsem_does_not_descend]) ;
    - [MM] ne le rend pas : ses deux continuations n'émettent que sur
      [e], ou rien.  Son sac s'annule donc **à tout [l] et toute cible**.

    Le critère n'est donc ni trivialement vrai ni trivialement faux, et
    il sépare précisément les deux comportements. *)

Lemma MM_not_selfret : ~ SelfRet MM.
Proof.
  intros (c & v0 & P' & Hl & Hin).
  destruct (gsum_in_summand _ c v0 P' Hl) as (P & Hins & Heq). subst P'.
  rewrite ochans_subst in Hin.
  unfold MM in Hins. simpl in Hins.
  destruct Hins as [Heq | [Heq | []]]; injection Heq as Hc Hp; subst;
    simpl in Hin.
  - destruct Hin as [H|[]]. injection H as H. congruence.
  - contradiction.
Qed.

Lemma MCert_selfret : SelfRet MCert.
Proof.
  exists (cst a), (cst v), ((cst a) ! (cst v) • 𝟘). split.
  - unfold MCert. apply lts_choiceL.
    assert (E : ((cst a) ! cst v • 𝟘 : proc) = (((cst a) ! (bvar 0) • 𝟘) ^ (cst v)))
      by reflexivity.
    rewrite E. apply lts_input.
  - simpl. left. reflexivity.
Qed.

(** ** (4) …et la TROISIÈME obligation tombe aussi — le critère regarde
       les mauvaises gardes

    Des trois obligations du découpage, celle-ci — « [g M] τ-stable et
    [SelfRet M] ⟹ une délivrance convient » — avait survécu aux six
    témoins.  Elle est fausse, et la raison est nette : **[SelfRet M] ne
    dit pas que la garde qui reçoit le message rend ce message**.  Le
    témoin met la garde auto-rendante sur un canal **absent du sac** :

      MSelf := ((b ? (b ! x • 𝟘)) + (b ? 𝟘)) + (a ? 𝟘)     sac [(a,v)]

    - [SelfRet MSelf] ✓ par la garde [b] (continuation copycat) ;
    - [g MSelf] est τ-stable ✓ ;
    - l'hypothèse tient, et **gratuitement** : chaque canal gardé a une
      garde morte, donc [below_nil_of_all_dead] donne
      [g MSelf ⊑ₘᵤₛₜᵢ 𝟘], que [must_i_par_compat_r] relève sous le sac ;
    - mais la seule délivrance est celle du message [a], dont la
      continuation est [𝟘] — et [nil_not_below_msg_gen] interdit
      [𝟘 ⊑ₘᵤₛₜᵢ (a!v•𝟘)].

    **Piste que cela ouvre** : [SelfRet] est *suffisant* pour que le sac
    ne s'annule pas, jamais nécessaire ([MSelf] l'illustre).  Le critère
    naturel serait sa version **relative au sac** — « une garde sur un
    canal *du sac* rend son message » — et [MSelf] y est correctement
    classé (sa garde [a] ne rend rien).  Non tenté ; noter que
    [no_regen_of_own_channel], sur lequel repose l'annulation, quantifie
    pour l'instant sur **tous** les canaux. *)

Definition MSelf : gproc :=
  (((cst b) ? ((cst b) ! (bvar 0) • 𝟘)) + ((cst b) ? ((g 𝟘) : proc)))
  + ((cst a) ? ((g 𝟘) : proc)).

Lemma MSelf_no_tau : forall z, ~ lts ((g MSelf) : proc) τ z.
Proof.
  intros z Hz. unfold MSelf in Hz.
  inversion Hz; subst; [ inversion H3; subst; inversion H4 | inversion H3 ].
Qed.

Lemma MSelf_selfret : SelfRet MSelf.
Proof.
  exists (cst b), (cst v), ((cst b) ! (cst v) • 𝟘). split.
  - unfold MSelf. apply lts_choiceL. apply lts_choiceL.
    assert (E : ((cst b) ! cst v • 𝟘 : proc) = (((cst b) ! (bvar 0) • 𝟘) ^ (cst v)))
      by reflexivity.
    rewrite E. apply lts_input.
  - simpl. left. reflexivity.
Qed.

Lemma MSelf_below_nil : ((g MSelf) : proc) ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc).
Proof.
  apply below_nil_of_all_dead; [ apply MSelf_no_tau | ].
  intros c P Hin. unfold MSelf in *. simpl in *.
  destruct Hin as [H|[H|[H|[]]]]; injection H as Hc Hp; subst; auto.
Qed.

Lemma MSelf_in_a_inv : forall v0 Mc,
  lts ((g MSelf) : proc) (ActExt (ActIn (cst a, v0))) Mc -> Mc = ((g 𝟘) : proc).
Proof.
  intros v0 Mc Hl.
  destruct (gsum_in_summand _ _ v0 Mc Hl) as (P & Hins & Heq). subst Mc.
  unfold MSelf in Hins. simpl in Hins.
  destruct Hins as [H|[H|[H|[]]]].
  - exfalso. injection H as Hc Hp. apply nab. symmetry. exact Hc.
  - exfalso. injection H as Hc Hp. apply nab. symmetry. exact Hc.
  - injection H as Hp. subst P. reflexivity.
Qed.

Lemma MSelf_cfg_tau :
  exists z, (((g MSelf) : proc) ▷ bag [(cst a ▷ cst v)]) ⟶ z.
Proof.
  exists (((g 𝟘) : proc) ▷ (∅ : MO (ExtAct TypeOfActions))).
  simpl. apply fw_tau_deliver.
  unfold MSelf. apply lts_choiceR.
  assert (E : ((g 𝟘) : proc) = (((g 𝟘) : proc) ^ (cst v))) by reflexivity.
  rewrite E at 2. apply lts_input.
Qed.

Theorem selfret_descent_is_false :
  ~ (forall (l : list TypeOfActions) (M N : gproc), gStatic M -> gStatic N ->
       SelfRet M ->
       (forall z, ~ lts ((g M) : proc) τ z) ->
       (exists z, (((g M) : proc) ▷ bag l) ⟶ z) ->
       ((msgs l ‖ ((g M) : proc)) ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
       (exists c v0 l0 Mc,
          Permutation l ((c,v0) :: l0)
          /\ lts ((g M) : proc) (ActExt (ActIn (c,v0))) Mc
          /\ Mc ⊑ₘᵤₛₜᵢ (((c ! v0 • 𝟘) : proc) ‖ ((g N) : proc)))).
Proof.
  intro H.
  destruct (H [(cst a ▷ cst v)] MSelf 𝟘
              ltac:(unfold MSelf; repeat constructor)
              ltac:(constructor)
              MSelf_selfret MSelf_no_tau MSelf_cfg_tau
              ltac:(apply must_i_par_compat_r; apply MSelf_below_nil))
    as (c0 & v0 & l0 & Mc & Hp & Hin & Hb).
  apply Permutation_length_1_inv in Hp. injection Hp as Hp1 Hp2. subst c0 v0.
  rewrite (MSelf_in_a_inv _ _ Hin) in Hb.
  assert (Hc : (((cst a ! cst v • 𝟘) : proc) ‖ ((g 𝟘) : proc))
                 ≡* ((cst a ! cst v • 𝟘) : proc)) by apply cgr_par_nil.
  apply (nil_not_below_msg_gen (cst a) (cst v)).
  intros t Ht. apply (proj2 (must_i_cgr _ _ Hc)). apply Hb. exact Ht.
Qed.

(** ** …et le critère RAFFINÉ classe [MSelf] correctement

    [VACCS_Bad.SelfRetBag] ne regarde que les gardes sur les **canaux du
    sac**.  [MSelf] y échappe — sa garde auto-rendante est sur [b], hors
    du sac — donc [VACCS_Bad.cfg_no_selfretbag_cancels] lui donne
    l'annulation, que [MSelf_below_nil] confirme indépendamment.

    Avec [VACCS_Bad.selfretbag_selfret] (l'inclusion), cela rend
    l'inclusion **stricte** : le cas clos de la dichotomie est
    strictement plus grand qu'avec [SelfRet]. *)

Lemma MSelf_not_selfretbag : ~ SelfRetBag [(cst a ▷ cst v)] MSelf.
Proof.
  intros (c & v0 & Hin & Hex).
  simpl in Hin. destruct Hin as [Heq|[]]. injection Heq as Hc Hv. subst c v0.
  apply Exists_exists in Hex. destruct Hex as (aa & Hina & (P & Heq & Hoc)).
  subst aa. unfold MSelf in Hina. simpl in Hina.
  destruct Hina as [H|[H|[H|[]]]].
  - injection H as Hc Hp. congruence.
  - injection H as Hc Hp. congruence.
  - injection H as Hp. subst P. simpl in Hoc. contradiction.
Qed.

(** ** …et les deux branches de [VACCS_Bad.cfg_derivable_or_hard] sont
    atteintes

    [MCert] tombe dans le **résidu** — sa garde sur [a] rend le message
    du sac ; [MSelf] est traité par l'*autre* route, celle du critère
    d'émission ([VACCS_Bad.cfg_derivable_of_disjoint]), sans qu'aucune
    τ-stabilité ne soit consultée : sa seule voie d'émission est [b], et
    le sac est sur [a].

    C'est une seconde raison, indépendante de
    [MSelf_not_selfretbag], pour laquelle [MSelf] est du côté clos. *)

Lemma MCert_selfretbag : SelfRetBag [(cst a ▷ cst v)] MCert.
Proof.
  exists (cst a), (cst v). split; [ left; reflexivity | ].
  unfold MCert. simpl. left.
  exists ((cst a) ! (bvar 0) • 𝟘). split; [ reflexivity | ].
  simpl. left. reflexivity.
Qed.

(** …et pourtant [MCert] est dérivablement sous le **sac nu**, par la
    descente à travers sa garde copycat
    ([VACCS_Matching.cfg_copycat_guard_below_bag]) : le message revient
    aussitôt et le choix gardé, en s'engageant, jette la garde sur [b].

    C'est la contrepartie **dérivationnelle** de [MCert_below], qui
    n'était jusqu'ici établi que sémantiquement — et c'est le premier
    théorème du développement qui couvre génériquement le témoin de la
    branche [SelfRetBag] du résidu. *)

Lemma ax_MCert_bag_below_nil :
  ax_pre ((msgs [(cst a ▷ cst v)]) ‖ ((g MCert) : proc))
         ((msgs [(cst a ▷ cst v)]) ‖ ((g (𝟘 : gproc)) : proc)).
Proof.
  eapply (cfg_copycat_guard_below_bag _ [] (cst a) (cst v) _
            [((cst b) ? ((cst e) ! (cst y) • 𝟘))]).
  - reflexivity.
  - unfold MCert, ccatg. reflexivity.
Qed.


Lemma MSelf_disjoint_from_bag : forall c' u',
  In (c',u') [(cst a ▷ cst v)] -> ~ In c' (ochans ((g MSelf) : proc)).
Proof.
  intros c' u' Hin Hoc. simpl in Hin. destruct Hin as [He|[]].
  injection He as He1 He2. subst c' u'.
  simpl in Hoc. destruct Hoc as [He|[]]. congruence.
Qed.



(** ** Bilan : la disjonction ne se DÉCOUPE pas par un critère syntaxique

    Trois tentatives successives de scinder
    [VACCS_Matching.CfgDisjunctionLocal3] en obligations à **un seul**
    disjoint, chacune réfutée par un petit terme :

    | classe visée | disjoint imposé | témoin |
    |---|---|---|
    | [SelfRet M] ∨ [g M] a un [τ] | (B) | [𝛕 • 𝟘] ([VACCS_Bad.selfret_case_premise_is_false]) |
    | [g M] a un [τ] | (A) | [MTau] ([tau_summand_cancellation_is_false]) |
    | [g M] a un [τ] | (C) | [PC] |
    | [g M] τ-stable, [SelfRet M] | (B) | [MSelf] |

    Et la raison est structurelle : à l'intérieur de la classe « [g M]
    porte un [𝛕]-sommant », les quatre témoins se répartissent sur
    **trois** disjoints différents —

    - [𝛕 • 𝟘] et [PC] : seul (A) ;
    - [MFalse] : seul (C) ;
    - [MTau] : (B) et (C), pas (A).

    Distinguer [PC] de [MFalse] demanderait de savoir si *une* branche
    est sous la cible — c'est-à-dire (C) lui-même.  **Le choix du
    disjoint dépend donc de la sémantique et non de la forme**, ce qui
    explique que le caractère classique de la disjonction ne soit pas un
    artefact d'énoncé : elle n'est pas décidable par inspection de [M].

    Corollaire de méthode : cesser de chercher un découpage syntaxique.
    Ce qu'il faut est soit une **règle** qui consomme la conjonction des
    branches (analogue à gauche de [ax_glb_tau], absent — cf.
    [VACCS_Matching.cfg_tau_species]), soit un tout autre angle. *)


(** ** Le client qui réfute le disjoint « source » *)

Definition QCert : gproc := (𝛕 • ((g ①) : proc)) + ((cst e) ? ((g 𝟘) : proc)).
Definition TCert2 : proc := (((cst b) ! (cst w) • 𝟘) : proc) ‖ ((g QCert) : proc).
Definition TCert : proc :=
  (((cst b) ! (cst w) • 𝟘) : proc)
  ‖ ((g ((cst a) ? ((g QCert) : proc))) : proc).

Lemma TCert_not_good : ~ good_VACCS TCert.
Proof.
  intro Hg. unfold TCert in Hg. inversion Hg; subst.
  match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
Qed.

Lemma TCert_no_tau : forall z, ~ lts TCert τ z.
Proof.
  intros z H. unfold TCert in H. inversion H; subst.
  - match goal with H2 : lts (g (_ ? _)) (ActExt (ActIn _)) _ |- _ =>
      inversion H2; subst end.
    match goal with H3 : lts (_ ! _ • 𝟘) _ _ |- _ => inversion H3; subst end.
    apply nab. reflexivity.
  - match goal with H2 : lts (g (_ ? _)) (ActExt (ActOut _)) _ |- _ => inversion H2 end.
  - match goal with H2 : lts (_ ! _ • 𝟘) τ _ |- _ => inversion H2 end.
  - match goal with H2 : lts (g (_ ? _)) τ _ |- _ => inversion H2 end.
Qed.

Lemma TCert2_not_good : ~ good_VACCS TCert2.
Proof.
  intro Hg. unfold TCert2, QCert in Hg. inversion Hg; subst.
  match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H; subst end.
  match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
Qed.

Lemma TCert2_tau_inv : forall z, lts TCert2 τ z ->
  z = ((((cst b) ! (cst w) • 𝟘) : proc) ‖ ((g ①) : proc)).
Proof.
  intros z H. unfold TCert2, QCert in H. inversion H; subst.
  - match goal with H2 : lts (g (_ + _)) (ActExt (ActIn _)) _ |- _ =>
      inversion H2; subst end.
    + match goal with H3 : lts (g (𝛕 • _)) _ _ |- _ => inversion H3 end.
    + match goal with H3 : lts (g (_ ? _)) _ _ |- _ => inversion H3; subst end.
      match goal with H4 : lts (_ ! _ • 𝟘) _ _ |- _ => inversion H4; subst end.
      exfalso. apply nbe. reflexivity.
  - match goal with H2 : lts (g (_ + _)) (ActExt (ActOut _)) _ |- _ =>
      inversion H2; subst end;
    match goal with H3 : lts (g _) (ActExt (ActOut _)) _ |- _ => inversion H3 end.
  - match goal with H2 : lts (_ ! _ • 𝟘) τ _ |- _ => inversion H2 end.
  - match goal with H2 : lts (g (_ + _)) τ _ |- _ => inversion H2; subst end.
    + match goal with H3 : lts (g (𝛕 • _)) τ _ |- _ => inversion H3; subst end.
      reflexivity.
    + match goal with H3 : lts (g (_ ? _)) τ _ |- _ => inversion H3 end.
Qed.

Lemma nil_passes_TCert2 : ((g 𝟘) : proc) must_pass TCert2.
Proof.
  apply m_step.
  - apply TCert2_not_good.
  - exists (((g 𝟘) : proc) ▷ ((((cst b) ! (cst w) • 𝟘) : proc) ‖ ((g ①) : proc))).
    apply ParRight. unfold TCert2, QCert.
    apply lts_parR. apply lts_choiceL. apply lts_tau.
  - intros p' Hp'. inversion Hp'.
  - intros t' Ht'. rewrite (TCert2_tau_inv t' Ht').
    apply m_now. apply good_par. right. constructor.
  - intros p' t' mu1 mu2 Hd Hp' Ht'. inversion Hp'.
Qed.

Lemma TCert_in_inv : forall c0 v0 t', lts TCert (ActExt (ActIn (c0,v0))) t' ->
  c0 = cst a /\ t' = TCert2.
Proof.
  intros c0 v0 t' H. unfold TCert in H. inversion H; subst.
  - match goal with H2 : lts (_ ! _ • 𝟘) _ _ |- _ => inversion H2 end.
  - match goal with H2 : lts (g (_ ? _)) _ _ |- _ => inversion H2; subst end.
    split; reflexivity.
Qed.

Lemma Amsg_passes_TCert : (((cst a) ! (cst v) • 𝟘) : proc) must_pass TCert.
Proof.
  apply m_step.
  - apply TCert_not_good.
  - exists (((g 𝟘) : proc) ▷ TCert2).
    eapply (ParSync (ActOut (cst a, cst v)) (ActIn (cst a, cst v))).
    + simpl. reflexivity.
    + apply lts_output.
    + unfold TCert, TCert2. apply lts_parR.
      assert (E : ((g QCert) : proc) = ((g QCert) : proc) ^ (cst v)) by reflexivity.
      rewrite E at 2. apply lts_input.
  - intros p' Hp'. inversion Hp'.
  - intros t' Ht'. exfalso. eapply TCert_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    inversion Hp'; subst.
    destruct mu2 as [a2|a2]; simpl in Hd; try contradiction. subst a2.
    destruct (TCert_in_inv _ _ _ Ht') as (_ & Et'). subst t'.
    apply nil_passes_TCert2.
Qed.

Lemma nilpar_no_lts : forall al q,
  ~ lts (((g 𝟘) : proc) ‖ ((g 𝟘) : proc)) al q.
Proof.
  intros al q H. inversion H; subst;
    match goal with H2 : lts ((g 𝟘) : proc) _ _ |- _ => inversion H2 end.
Qed.

Lemma nilnil_fails_nilnil :
  ~ ((((g 𝟘) : proc) ‖ ((g 𝟘) : proc)) must_pass
       (((g 𝟘) : proc) ‖ ((g 𝟘) : proc))).
Proof.
  intro Hm. inversion Hm; subst.
  - match goal with Hg : good_VACCS _ |- _ =>
      inversion Hg; subst;
      match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end end.
  - match goal with He : exists _, _ |- _ => destruct He as (x & Hx) end.
    inversion Hx; subst; eapply nilpar_no_lts; eassumption.
Qed.

Lemma emsg_fails_QCert :
  ~ ((((g 𝟘) : proc) ‖ (((cst e) ! (cst y) • 𝟘) : proc)) must_pass
       (((g 𝟘) : proc) ‖ ((g QCert) : proc))).
Proof.
  intro Hm. inversion Hm; subst.
  - match goal with Hg : good_VACCS _ |- _ =>
      inversion Hg; subst;
      match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H; subst end end.
    match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
  - apply nilnil_fails_nilnil.
    match goal with Hc : forall _ _ _ _, _ |- _ =>
      eapply (Hc (((g 𝟘) : proc) ‖ ((g 𝟘) : proc))
                 (((g 𝟘) : proc) ‖ ((g 𝟘) : proc))
                 (ActOut (cst e, cst y)) (ActIn (cst e, cst y)))
    end.
    + simpl. reflexivity.
    + apply lts_parR. apply lts_output.
    + unfold QCert. apply lts_parR. apply lts_choiceR.
      assert (E : ((g 𝟘) : proc) = ((g 𝟘) : proc) ^ (cst y)) by reflexivity.
      rewrite E at 2. apply lts_input.
Qed.

Lemma aemsg_fails_aQCert :
  ~ (((((cst a) ! (cst v) • 𝟘) : proc) ‖ (((cst e) ! (cst y) • 𝟘) : proc)) must_pass
       (((g 𝟘) : proc) ‖ ((g ((cst a) ? ((g QCert) : proc))) : proc))).
Proof.
  intro Hm. inversion Hm; subst.
  - match goal with Hg : good_VACCS _ |- _ =>
      inversion Hg; subst;
      match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end end.
  - apply emsg_fails_QCert.
    match goal with Hc : forall _ _ _ _, _ |- _ =>
      eapply (Hc (((g 𝟘) : proc) ‖ (((cst e) ! (cst y) • 𝟘) : proc))
                 (((g 𝟘) : proc) ‖ ((g QCert) : proc))
                 (ActOut (cst a, cst v)) (ActIn (cst a, cst v)))
    end.
    + simpl. reflexivity.
    + apply lts_parL. apply lts_output.
    + apply lts_parR.
      assert (E : ((g QCert) : proc) = ((g QCert) : proc) ^ (cst v)) by reflexivity.
      rewrite E at 2. apply lts_input.
Qed.

Lemma BCert_fails_TCert :
  ~ ((((((cst a) ! (cst v) • 𝟘)) : proc) ‖ ((g MCert) : proc)) must_pass TCert).
Proof.
  intro Hm. inversion Hm; subst.
  - eapply TCert_not_good. eassumption.
  - apply aemsg_fails_aQCert.
    match goal with Hc : forall _ _ _ _, _ |- _ =>
      eapply (Hc ((((cst a) ! (cst v) • 𝟘) : proc) ‖ (((cst e) ! (cst y) • 𝟘) : proc))
                 (((g 𝟘) : proc) ‖ ((g ((cst a) ? ((g QCert) : proc))) : proc))
                 (ActIn (cst b, cst w)) (ActOut (cst b, cst w)))
    end.
    + simpl. reflexivity.
    + unfold MCert. apply lts_parR. apply lts_choiceR.
      assert (E : (((cst e) ! (cst y) • 𝟘) : proc)
                = (((cst e) ! (cst y) • 𝟘) : proc) ^ (cst w)) by reflexivity.
      rewrite E at 2. apply lts_input.
    + unfold TCert. apply lts_parL. apply lts_output.
Qed.

Theorem MCert_succ_not_below_source :
  ~ ((msgs [(cst a ▷ cst v)] ‖ ((g 𝟘) : proc))
       ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs [(cst a ▷ cst v)] ‖ ((g MCert) : proc))).
Proof.
  intro Hle. apply BCert_fails_TCert.
  assert (Hc2 : (msgs [(cst a ▷ cst v)] ‖ ((g MCert) : proc))
                ≡* ((((cst a) ! (cst v) • 𝟘) : proc) ‖ ((g MCert) : proc))).
  { simpl. apply cgr_fullpar; [ apply cgr_par_nil | reflexivity ]. }
  apply (proj2 (must_i_cgr _ _ Hc2)).
  apply Hle.
  assert (Hc1 : (((cst a) ! (cst v) • 𝟘) : proc)
                ≡* (msgs [(cst a ▷ cst v)] ‖ ((g 𝟘) : proc))).
  { simpl. symmetry. etransitivity; [ apply cgr_par_nil | apply cgr_par_nil ]. }
  apply (proj2 (must_i_cgr _ _ Hc1)).
  apply Amsg_passes_TCert.
Qed.

(** ** Les deux disjonctions source-only sont réfutées *)

Theorem cfg_disjunction_source_bag_is_false : ~ CfgDisjunctionSourceBag.
Proof.
  intro H.
  destruct (H [(cst a ▷ cst v)] MCert 𝟘)
    as [Hempty | (c0 & v0 & l0 & Mc & K & Hp & Hin & Hout & HK)].
  - unfold MCert. repeat constructor.
  - repeat constructor.
  - exists ((((cst a) ! (cst v) • 𝟘) : proc) ▷ (∅ : MO (ExtAct TypeOfActions))).
    simpl. apply fw_tau_deliver. unfold MCert. apply lts_choiceL.
    assert (E : (((cst a) ! (cst v) • 𝟘) : proc)
              = (((cst a) ! (bvar 0) • 𝟘) : proc) ^ (cst v)) by reflexivity.
    rewrite E. apply lts_input.
  - apply MCert_below.
  - apply MCert_not_below_nil. exact Hempty.
  - apply Permutation_length_1_inv in Hp.
    injection Hp as Hp1 Hp2 Hp3. subst c0 v0 l0.
    destruct (MCert_in_inv _ _ _ Hin) as [ (Ec & Ep) | (Ec & Ep) ].
    + subst Mc. inversion Hout; subst.
      apply MCert_succ_not_below_source. exact HK.
    + exfalso. injection Ec as Ec. apply nab. exact Ec.
Qed.

Corollary cfg_disjunction_source_is_false : ~ CfgDisjunctionSource.
Proof.
  intro H. apply cfg_disjunction_source_bag_is_false.
  apply cfg_source_bag_of_source. exact H.
Qed.

(** ** …tandis que [CfgDisjunctionLocal], elle, TIENT sur cette instance

    C'est le point de la réfutation ci-dessus : ce qui tombe est la
    suppression de la cible, pas la disjonction.  Ici le disjoint local
    est satisfait par la garde copycat — elle rend le message, et le
    résidu [𝟘] est sous la cible [𝟘] par réflexivité
    ([VACCS_Matching.local_disjunct_of_returning]). *)

Theorem cfg_disjunction_local_at_MCert :
  (((g MCert) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc))
  \/ (exists c0 v0 l0 Mc,
        Permutation [(cst a ▷ cst v)] ((c0,v0) :: l0)
        /\ lts ((g MCert) : proc) (ActExt (ActIn (c0,v0))) Mc
        /\ Mc ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((((c0 ! v0 • 𝟘)) : proc) ‖ ((g 𝟘) : proc))).
Proof.
  right. exists (cst a), (cst v), [], ((((cst a) ! (cst v) • 𝟘)) : proc).
  split; [ reflexivity | split ].
  - unfold MCert. apply lts_choiceL.
    assert (E : (((cst a) ! (cst v) • 𝟘) : proc)
              = (((cst a) ! (bvar 0) • 𝟘) : proc) ^ (cst v)) by reflexivity.
    rewrite E. apply lts_input.
  - eapply local_disjunct_of_returning; [ apply lts_output | ].
    intros t Hm. exact Hm.
Qed.

(** ** LE PRÉORDRE RELATIVISÉ NE DESCEND PAS AUX SOUS-SACS

    [msgs_below_tests] lit [msgs l ‖ p ⊑ₘᵤₛₜᵢ msgs l ‖ q] comme
    « [p ⊑ₘᵤₛₜᵢ q] **restreint aux tests qui portent le sac** ».  À un
    sous-sac la classe de tests est **plus grande** (un test portant [l]
    est un test portant [l'] avec le reste du sac poussé dans [e]), donc
    la relativisation y est **plus forte** — et l'implication ne descend
    pas.

    C'est exactement pourquoi [BagSem], que toute la couche [_bag]
    réclame, ne découle pas de son instance au sac courant : la même
    paire [MCert] qui sert de témoin partout ailleurs le montre ici sous
    sa forme la plus courte. *)

Theorem bagsem_does_not_descend :
  ((msgs [(cst a ▷ cst v)] ‖ ((g MCert) : proc))
     ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs [(cst a ▷ cst v)] ‖ ((g 𝟘) : proc)))
  /\ ~ ((msgs (@nil TypeOfActions) ‖ ((g MCert) : proc))
          ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs (@nil TypeOfActions) ‖ ((g 𝟘) : proc))).
Proof.
  split; [ apply MCert_below | ].
  intro H. apply MCert_not_below_nil.
  intros t Ht.
  apply (proj2 (must_i_cgr _ _ (cgr_nil_par_l ((g 𝟘) : proc)))).
  apply H.
  apply (proj1 (must_i_cgr _ _ (cgr_nil_par_l ((g MCert) : proc)))).
  exact Ht.
Qed.


(** ** ★ AJOUTER UNE SOMME À GARDE COPYCAT N'EST PAS INOFFENSIF — SOUS LE SAC

    [VACCS_Matching.cfg_derivable_of_copycats] exige que **tous** les
    sommants soient des copycats.  La tentation est de n'en peler que
    quelques-uns et de laisser un reste ; il faudrait pour cela que
    l'ajout d'un sommant copycat soit invisible, ce que
    [VACCS_ChoiceProbes.choice_stable_congruence_is_unsound] réfute — mais
    **au niveau nu**.  Or le dossier consigne deux fois qu'un effet du sac
    ne doit pas être affirmé sans sonde : le sac change les résidus.

    Voici donc la réfutation **sous le sac**, sur [MCert] lui-même : le
    sac porte [(a,v)], la garde sur [a] est un copycat, la garde sur [b]
    ne l'est pas, et ajouter la somme au sac fait **perdre** un test.

    Le mécanisme est celui de [VACCS_ChoiceProbes] : le client émet sur
    [b], la garde [b] de [MCert] **vole** ce message et répond sur [e],
    que le client absorbe par une garde morte — après quoi plus rien ne
    bouge.  Le sac seul, lui, n'a aucune garde et laisse le client
    réussir tout seul. *)

Definition ECont : proc := ((cst e) ! (cst y) • 𝟘).
Definition Pcc : proc := (((cst b) ! (cst w) • 𝟘)) ‖ (TSg (cst e)).
Definition TCC : proc := ((g ((cst a) ? Pcc)) : proc).

Lemma nilnil_static : Static (((g (𝟘 : gproc)) : proc) ‖ ((g (𝟘 : gproc)) : proc)).
Proof. repeat constructor. Qed.

Lemma nil_not_good : ~ good_VACCS ((g (𝟘 : gproc)) : proc).
Proof. intro H. inversion H. Qed.

Lemma out_not_good : forall (c : ChannelData) (u : ValueData),
  ~ good_VACCS ((c ! u • 𝟘) : proc).
Proof. intros c u H. inversion H. Qed.

Lemma nil_TSg_not_good :
  ~ good_VACCS (((g (𝟘 : gproc)) : proc) ‖ (TSg (cst e))).
Proof.
  intro Hg. inversion Hg; subst.
  match goal with H : _ \/ _ |- _ => destruct H end;
    [ eapply nil_not_good; eassumption | eapply TSg_not_good; eassumption ].
Qed.

(** Le cœur : une fois le message [b] volé et la réponse [e] absorbée,
    il ne reste que [𝟘] face à [𝟘]. *)

Lemma e_sync_fails :
  ~ ((((g (𝟘 : gproc)) : proc) ‖ ECont) must_pass
       (((g (𝟘 : gproc)) : proc) ‖ (TSg (cst e)))).
Proof.
  intro Hm. inversion Hm; subst.
  { exfalso. eapply nil_TSg_not_good; eassumption. }
  assert (Hbad : (((g (𝟘 : gproc)) : proc) ‖ ((g (𝟘 : gproc)) : proc)) must_pass
               (((g (𝟘 : gproc)) : proc) ‖ (subst_in_proc 0 (cst y) ((g (𝟘 : gproc)) : proc)))).
  { eapply com with (μ1 := ActOut (cst e, cst y)) (μ2 := ActIn (cst e, cst y)).
    - simpl. reflexivity.
    - apply lts_parR. unfold ECont. apply lts_output.
    - apply lts_parR. unfold TSg. apply lts_choiceR. apply lts_input. }
  simpl in Hbad.
  assert (Hbad2 : (((g (𝟘 : gproc)) : proc) ‖ ((g (𝟘 : gproc)) : proc)) must_pass
                  ((g (𝟘 : gproc)) : proc)).
  { eapply must_eq_client; [ apply cgr_par_nil | exact Hbad ]. }
  eapply no_client_nil; [ apply nilnil_static | exact Hbad2 ].
Qed.

Lemma Pcc_not_good : ~ good_VACCS Pcc.
Proof.
  intro Hg. unfold Pcc in Hg. inversion Hg; subst.
  match goal with H : _ \/ _ |- _ => destruct H end;
    [ eapply out_not_good; eassumption | eapply TSg_not_good; eassumption ].
Qed.

Lemma Pcc_tau_inv : forall t', lts Pcc τ t' ->
  t' = (((cst b) ! (cst w) • 𝟘) ‖ ((g (① : gproc)) : proc)).
Proof.
  intros t' Ht. unfold Pcc, TSg in Ht.
  inversion Ht; subst;
    repeat match goal with
    | H : lts ((cst b ! cst w • 𝟘) : proc) τ _ |- _ => inversion H
    | H : lts ((cst b ! cst w • 𝟘) : proc) (ActExt (ActIn _)) _ |- _ => inversion H
    | H : lts ((cst b ! cst w • 𝟘) : proc) (ActExt (ActOut _)) _ |- _ =>
        inversion H; subst; clear H
    | H : lts ((g (_ + _)) : proc) _ _ |- _ => inversion H; subst; clear H
    | H : lts ((𝛕 • _) : proc) (ActExt _) _ |- _ => inversion H
    | H : lts ((𝛕 • _) : proc) τ _ |- _ => inversion H; subst; clear H
    | H : lts ((cst e ? _) : proc) τ _ |- _ => inversion H
    | H : lts ((cst e ? _) : proc) (ActExt (ActIn _)) _ |- _ =>
        inversion H; subst; clear H
    end;
    try reflexivity; try congruence.
  all: inversion H4; subst; try reflexivity; try congruence.
Qed.

(** Le sac seul passe le client : il n'a aucune garde, donc aucun [com] à
    honorer, et le client réussit par son propre [𝛕]. *)

Lemma must_nil_Pcc : ((g (𝟘 : gproc)) : proc) must_pass Pcc.
Proof.
  apply m_step.
  - apply Pcc_not_good.
  - exists (((g (𝟘 : gproc)) : proc) ▷ (((cst b) ! (cst w) • 𝟘) ‖ ((g (① : gproc)) : proc))).
    apply ParRight. unfold Pcc. apply lts_parR. unfold TSg.
    apply lts_choiceL. apply lts_tau.
  - intros p' Hp'. exfalso. eapply nil_no_lts; exact Hp'.
  - intros t' Ht'. rewrite (Pcc_tau_inv t' Ht'). apply m_now.
    constructor. right. constructor.
  - intros p' t' mu1 mu2 Hd Hp' Ht'. exfalso. eapply nil_no_lts; exact Hp'.
Qed.

(** …et la somme ajoutée le fait échouer, par sa garde sur [b]. *)

Lemma b_sync_fails :
  ~ ((((g (𝟘 : gproc)) : proc) ‖ ((g MCert) : proc)) must_pass Pcc).
Proof.
  intro Hm. inversion Hm; subst.
  { exfalso. eapply Pcc_not_good; eassumption. }
  assert (Hbad : (((g (𝟘 : gproc)) : proc)
                    ‖ (subst_in_proc 0 (cst w) (((cst e) ! (cst y) • 𝟘) : proc)))
                 must_pass (((g (𝟘 : gproc)) : proc) ‖ (TSg (cst e)))).
  { eapply com with (μ1 := ActIn (cst b, cst w)) (μ2 := ActOut (cst b, cst w)).
    - simpl. reflexivity.
    - apply lts_parR. unfold MCert. apply lts_choiceR. apply lts_input.
    - unfold Pcc. apply lts_parL. apply lts_output. }
  simpl in Hbad. eapply e_sync_fails. unfold ECont. exact Hbad.
Qed.

Lemma subst_Pcc : forall X, subst_in_proc 0 X Pcc = Pcc.
Proof. intro X. unfold Pcc, TSg. reflexivity. Qed.

Lemma TCC_not_good : ~ good_VACCS TCC.
Proof. intro H. unfold TCC in H. inversion H. Qed.

Lemma msg_passes_TCC : (((cst a) ! (cst v) • 𝟘) : proc) must_pass TCC.
Proof.
  apply m_step.
  - apply TCC_not_good.
  - exists (((g (𝟘 : gproc)) : proc) ▷ (subst_in_proc 0 (cst v) Pcc)).
    eapply ParSync with (μ1 := ActOut (cst a, cst v)) (μ2 := ActIn (cst a, cst v)).
    + simpl. reflexivity.
    + apply lts_output.
    + unfold TCC. apply lts_input.
  - intros p' Hp'. inversion Hp'.
  - intros t' Ht'. exfalso. unfold TCC in Ht'. inversion Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    inversion Hp'; subst. unfold TCC in Ht'. inversion Ht'; subst.
    rewrite subst_Pcc. apply must_nil_Pcc.
Qed.

Lemma msg_MCert_fails_TCC :
  ~ (((((cst a) ! (cst v) • 𝟘) : proc) ‖ ((g MCert) : proc)) must_pass TCC).
Proof.
  intro Hm. inversion Hm; subst.
  { exfalso. eapply TCC_not_good; eassumption. }
  assert (Hbad : (((g (𝟘 : gproc)) : proc) ‖ ((g MCert) : proc))
                 must_pass (subst_in_proc 0 (cst v) Pcc)).
  { eapply com with (μ1 := ActOut (cst a, cst v)) (μ2 := ActIn (cst a, cst v)).
    - simpl. reflexivity.
    - apply lts_parL. apply lts_output.
    - unfold TCC. apply lts_input. }
  rewrite subst_Pcc in Hbad. eapply b_sync_fails. exact Hbad.
Qed.

Theorem copycat_summand_not_harmless :
  ~ ((msgs [(cst a ▷ cst v)])
       ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((msgs [(cst a ▷ cst v)]) ‖ ((g MCert) : proc))).
Proof.
  intro Hpre.
  assert (Hcgr : (msgs [(cst a ▷ cst v)]) ≡* (((cst a) ! (cst v) • 𝟘) : proc)).
  { simpl. apply cgr_par_nil. }
  assert (H1 : (msgs [(cst a ▷ cst v)]) must_pass TCC).
  { apply (proj1 (must_i_cgr _ _ Hcgr)). apply msg_passes_TCC. }
  pose proof (Hpre TCC H1) as H2.
  eapply msg_MCert_fails_TCC.
  assert (Hcgr2 : ((msgs [(cst a ▷ cst v)]) ‖ ((g MCert) : proc))
                  ≡* ((((cst a) ! (cst v) • 𝟘) : proc) ‖ ((g MCert) : proc))).
  { apply cgr_fullpar; [ exact Hcgr | apply cgr_refl ]. }
  apply (proj2 (must_i_cgr _ _ Hcgr2)). exact H2.
Qed.

(** ** ★★ [VACCS_Matching.OutChoice] EST FAUX

    Le résidu se ramène ([ax_below_cfg_of_out_choice]) au **choix** d'un
    résidu d'émission faible du membre gauche : si l'un d'eux est sous
    le résidu de la cible, la comparaison se poursuit à un sac
    strictement plus petit.  Ce choix n'est **pas** fourni par la
    sémantique, et le témoin est la paire contradictoire [P1]/[P2]
    portée à côté d'un message.

      MsgC := oc ! v • 𝟘
      OCp  := 𝛕•(MsgC ‖ P1)  +  𝛕•(MsgC ‖ P2)

    - [OCp] est **sous** la configuration cible [msgs [(oc,v)] ‖ 𝟘] :
      c'est [ax_share_msg] — le message se factorise hors du choix
      interne — suivi de [PC_below_nil] et de la précongruence de [‖].
      Autrement dit, ce sont exactement les deux lois de mise en commun
      du développement qui rendent l'inéquation vraie ;
    - ses **seuls** résidus d'émission faible sont [P1] et [P2]
      ([OCp_wt_nil_inv] : un τ engage l'une des deux branches, après
      quoi rien ne bouge plus), et aucun des deux n'est sous [𝟘]
      ([P1_not_below_nil], [P2_not_below_nil]).

    C'est la même alternation ∀∃ que partout ailleurs — l'intersection
    des tests de [P1] et [P2] est incluse dans celle de [𝟘] sans
    qu'aucune des deux ne le soit — mais lue cette fois sur des
    **résidus d'émission**, ce que les contre-exemples antérieurs
    ([tau_successor_cannot_be_chosen], [no_delivery_is_reversible])
    ne couvraient pas.

    Noter enfin que l'instance **est dérivable** ([ax_OCp_below_msg]) :
    ce n'est pas un témoin d'incomplétude, c'est la réfutation d'une
    *route*.  Et la route qui marche est celle de [ax_share_msg], donc
    la mise en commun, pas la descente. *)

Context {oc : Channel} {noca : oc <> a} {nocb : oc <> b}.

Definition MsgC : proc := (cst oc) ! (cst v) • 𝟘.
Definition OCp : gproc :=
  (𝛕 • (MsgC ‖ ((g P1) : proc))) + (𝛕 • (MsgC ‖ ((g P2) : proc))).

Lemma OCp_below_msg :
  ((g OCp) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (MsgC ‖ ((g (𝟘 : gproc)) : proc)).
Proof.
  intros t Ht.
  apply (must_i_par_compat_r MsgC ((g PC) : proc) ((g (𝟘 : gproc)) : proc)).
  - apply PC_below_nil.
  - apply (soundness_ax _ _ (ax_share_msg (cst oc) (cst v)
             ((g P1) : proc) ((g P2) : proc))).
    exact Ht.
Qed.

Lemma MsgP1_no_tau : forall z, ~ lts (MsgC ‖ ((g P1) : proc)) τ z.
Proof. intros z Hz. unfold MsgC, P1 in Hz. blast3. Qed.

Lemma MsgP2_no_tau : forall z, ~ lts (MsgC ‖ ((g P2) : proc)) τ z.
Proof. intros z Hz. unfold MsgC, P2 in Hz. blast3. Qed.

Lemma OCp_tau_inv : forall z, lts ((g OCp) : proc) τ z ->
  z = (MsgC ‖ ((g P1) : proc)) \/ z = (MsgC ‖ ((g P2) : proc)).
Proof.
  intros z Hz. unfold OCp in Hz.
  inversion Hz; subst.
  - inversion H3; subst. left. reflexivity.
  - inversion H3; subst. right. reflexivity.
Qed.

Lemma OCp_no_ext : forall mu z, ~ lts ((g OCp) : proc) (ActExt mu) z.
Proof.
  intros mu z Hz. unfold OCp in Hz.
  inversion Hz; subst; inversion H3.
Qed.

Lemma OCp_wt_nil_inv : forall p1, ((g OCp) : proc) ⟹[[]] p1 ->
  p1 = ((g OCp) : proc)
  \/ p1 = (MsgC ‖ ((g P1) : proc))
  \/ p1 = (MsgC ‖ ((g P2) : proc)).
Proof.
  intros p1 Hw.
  inversion Hw; subst.
  - left. reflexivity.
  - destruct (OCp_tau_inv _ l) as [Hy|Hy]; subst.
    + right. left. eapply wt_nil_stable; [ | exact w0 ].
      apply no_lts_stable. intros zz Hzz. eapply MsgP1_no_tau. exact Hzz.
    + right. right. eapply wt_nil_stable; [ | exact w0 ].
      apply no_lts_stable. intros zz Hzz. eapply MsgP2_no_tau. exact Hzz.
Qed.

Lemma OCp_static : Static ((g OCp) : proc).
Proof. unfold OCp, MsgC, P1, P2, Ke. repeat constructor. Qed.

Lemma msgC_cgr : (MsgC ‖ ((g (𝟘 : gproc)) : proc))
  ≡* (msgs [((cst oc), (cst v))] ‖ ((g (𝟘 : gproc)) : proc)).
Proof.
  simpl. transitivity (MsgC ‖ (((g (𝟘 : gproc)) : proc) ‖ ((g (𝟘 : gproc)) : proc))).
  - apply cgr_fullpar; [ apply cgr_refl | apply cgr_par_nil_rev ].
  - unfold MsgC. symmetry. apply cgr_par_assoc.
Qed.

Lemma NilP1_no_tau : forall z, ~ lts (((g (𝟘 : gproc)) : proc) ‖ ((g P1) : proc)) τ z.
Proof. intros z Hz. unfold P1 in Hz. blast3. Qed.

Lemma NilP2_no_tau : forall z, ~ lts (((g (𝟘 : gproc)) : proc) ‖ ((g P2) : proc)) τ z.
Proof. intros z Hz. unfold P2 in Hz. blast3. Qed.

Lemma NilPi_not_below_nil : forall (X : gproc),
  ~ (((g X) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g (𝟘 : gproc)) : proc)) ->
  ~ ((((g (𝟘 : gproc)) : proc) ‖ ((g X) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g (𝟘 : gproc)) : proc)).
Proof.
  intros X HX Hpre. apply HX. intros t Ht.
  apply Hpre.
  assert (Hn : (((g (𝟘 : gproc)) : proc) ‖ ((g X) : proc)) ≡* ((g X) : proc)).
  { transitivity (((g X) : proc) ‖ ((g (𝟘 : gproc)) : proc)).
    - apply cgr_par_com.
    - apply cgr_par_nil. }
  apply (proj1 (must_i_cgr _ _ Hn)). exact Ht.
Qed.

(** La sémantique de l'instance, et l'inversion de ses résidus
    d'émission : un [τ] engage l'une des deux branches, après quoi il ne
    reste qu'une émission, donc les résidus sont **exactement** [𝟘 ‖ P1]
    et [𝟘 ‖ P2]. *)

Lemma OCp_below_cfg :
  ((g OCp) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ
    (msgs [((cst oc), (cst v))] ‖ ((g (𝟘 : gproc)) : proc)).
Proof.
  intros t Ht.
  apply (proj2 (must_i_cgr _ _ msgC_cgr)).
  apply OCp_below_msg. exact Ht.
Qed.

Lemma OCp_out_residue_inv : forall p1 p'',
  ((g OCp) : proc) ⟹[[]] p1 ->
  lts p1 (ActExt (ActOut ((cst oc), (cst v)))) p'' ->
  p'' = (((g (𝟘 : gproc)) : proc) ‖ ((g P1) : proc))
  \/ p'' = (((g (𝟘 : gproc)) : proc) ‖ ((g P2) : proc)).
Proof.
  intros p1 p'' Hrun Hout.
  destruct (OCp_wt_nil_inv _ Hrun) as [Hp1|[Hp1|Hp1]]; subst.
  - exfalso. eapply OCp_no_ext. exact Hout.
  - left. unfold MsgC, P1 in Hout. inversion Hout; subst.
    2: { inversion H3; subst; inversion H4. }
    inversion H3; subst. reflexivity.
  - right. unfold MsgC, P2 in Hout. inversion Hout; subst.
    2: { inversion H3; subst; inversion H4. }
    inversion H3; subst. reflexivity.
Qed.

Theorem OCp_no_good_out_residue : forall p1 p'',
  ((g OCp) : proc) ⟹[[]] p1 ->
  lts p1 (ActExt (ActOut ((cst oc), (cst v)))) p'' ->
  ~ (p'' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs [] ‖ ((g (𝟘 : gproc)) : proc))).
Proof.
  intros p1 p'' Hrun Hout Hres.
  destruct (OCp_out_residue_inv p1 p'' Hrun Hout) as [Hq|Hq]; subst.
  - eapply NilPi_not_below_nil; [ apply P1_not_below_nil | ].
    intros t Ht.
    assert (Hnil : (((g (𝟘 : gproc)) : proc) ‖ ((g (𝟘 : gproc)) : proc))
                     ≡* ((g (𝟘 : gproc)) : proc)) by apply cgr_par_nil.
    apply (proj2 (must_i_cgr _ _ Hnil)). simpl in Hres. apply Hres. exact Ht.
  - eapply NilPi_not_below_nil; [ apply P2_not_below_nil | ].
    intros t Ht.
    assert (Hnil : (((g (𝟘 : gproc)) : proc) ‖ ((g (𝟘 : gproc)) : proc))
                     ≡* ((g (𝟘 : gproc)) : proc)) by apply cgr_par_nil.
    apply (proj2 (must_i_cgr _ _ Hnil)). simpl in Hres. apply Hres. exact Ht.
Qed.

Theorem out_choice_is_false : ~ OutChoice.
Proof.
  intros HC.
  destruct (HC ((g OCp) : proc) [((cst oc), (cst v))] [] (cst oc) (cst v)
               (𝟘 : gproc) OCp_static ltac:(constructor) (Permutation_refl _)
               OCp_below_cfg)
    as (p1 & p'' & Hrun & Hout & Hres).
  eapply OCp_no_good_out_residue; [ exact Hrun | exact Hout | exact Hres ].
Qed.

(** Le contrôle : l'inéquation est bel et bien **dérivable**, par la
    mise en commun.  Ce n'est donc pas un témoin d'incomplétude — c'est
    la réfutation de la route « descendre par un résidu d'émission ». *)

Lemma ax_OCp_below_msg :
  ax_pre ((g OCp) : proc)
         (msgs [((cst oc), (cst v))] ‖ ((g (𝟘 : gproc)) : proc)).
Proof.
  eapply ax_trans;
    [ apply (ax_share_msg (cst oc) (cst v) ((g P1) : proc) ((g P2) : proc)) | ].
  eapply ax_trans.
  - apply (ax_par MsgC MsgC ((g PC) : proc) ((g (𝟘 : gproc)) : proc));
      [ apply ax_refl | apply ax_PC_below_nil ].
  - apply ax_cgr. apply msgC_cgr.
Qed.

(** ** …ET AUCUN TÉMOIN DE VIDANGE NE MARCHE NON PLUS

    [VACCS_Matching.residue_reduces_to_bare] ramène le résidu à une
    comparaison **nue** : le rejeu produit un [qq] τ-stable non émetteur
    et il suffirait que [⊢ qq ⊑ g M].  Ce [qq] est le témoin que
    [bhv_pre_cond2] rend à la **trace de vidange** — et il est
    existentiel, donc on ne le choisit pas.

    Sur [OCp] la question se pose au plus simple : la trace de vidange
    est [[oc!]], et les états qu'elle atteint sont *exactement*
    [𝟘 ‖ P1] et [𝟘 ‖ P2] ([OCp_drain_inv] : le premier pas ne peut être
    qu'un [τ] — [OCp_no_ext] — après quoi la branche est engagée et rien
    ne bouge plus qu'une émission).  Aucun des deux n'est sous [𝟘].

    Donc l'hypothèse de [residue_reduces_to_bare] n'est pas
    **atteignable** ici, bien que l'inéquation soit dérivable
    ([ax_OCp_below_msg]).  Le témoin qui réfute le choix d'un résidu
    d'émission réfute donc aussi le choix d'un témoin de vidange, et par
    le même mécanisme : [P1] et [P2] ont des exigences contradictoires,
    donc leur *conjonction* est sous [𝟘] sans qu'aucun ne le soit. *)

Lemma OCp_drain_inv : forall q,
  ((g OCp) : proc) ⟹[[ActOut ((cst oc), (cst v))]] q ->
  q = (((g (𝟘 : gproc)) : proc) ‖ ((g P1) : proc))
  \/ q = (((g (𝟘 : gproc)) : proc) ‖ ((g P2) : proc)).
Proof.
  intros q Hw.
  inversion Hw; subst.
  - destruct (OCp_tau_inv _ l) as [Hy|Hy]; subst.
    + inversion w0; subst.
      * exfalso. eapply MsgP1_no_tau. eassumption.
      * left. unfold MsgC, P1 in l0. inversion l0; subst.
        2: { inversion H3; subst; inversion H4. }
        inversion H3; subst.
        eapply wt_nil_stable; [ | eassumption ].
        apply no_lts_stable. intros zz Hzz. eapply NilP1_no_tau. exact Hzz.
    + inversion w0; subst.
      * exfalso. eapply MsgP2_no_tau. eassumption.
      * right. unfold MsgC, P2 in l0. inversion l0; subst.
        2: { inversion H3; subst; inversion H4. }
        inversion H3; subst.
        eapply wt_nil_stable; [ | eassumption ].
        apply no_lts_stable. intros zz Hzz. eapply NilP2_no_tau. exact Hzz.
  - exfalso. eapply OCp_no_ext. eassumption.
Qed.

Theorem no_drain_witness_for_OCp : forall q,
  ((g OCp) : proc) ⟹[[ActOut ((cst oc), (cst v))]] q ->
  ~ (q ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g (𝟘 : gproc)) : proc)).
Proof.
  intros q Hw. destruct (OCp_drain_inv q Hw) as [Hq|Hq]; subst.
  - apply NilPi_not_below_nil. apply P1_not_below_nil.
  - apply NilPi_not_below_nil. apply P2_not_below_nil.
Qed.

(** ** ★ LE TÉMOIN, EN UN SEUL ÉNONCÉ

    [OCp] réfute les **deux** routes « choisir un témoin » de ce
    développement, et il est en même temps **dérivable** — donc ce n'est
    pas un témoin d'incomplétude mais la délimitation de deux stratégies.

    La route qui marche est [ax_share_msg] : le message se factorise
    hors du choix interne, et [PC_below_nil] fait le reste.  C'est la
    **mise en commun**, pas la descente. *)

Theorem OCp_refutes_the_choices :
     ((g OCp) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ
       (msgs [((cst oc), (cst v))] ‖ ((g (𝟘 : gproc)) : proc))
  /\ ax_pre ((g OCp) : proc)
       (msgs [((cst oc), (cst v))] ‖ ((g (𝟘 : gproc)) : proc))
  /\ (forall p1 p'', ((g OCp) : proc) ⟹[[]] p1 ->
        lts p1 (ActExt (ActOut ((cst oc), (cst v)))) p'' ->
        ~ (p'' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs [] ‖ ((g (𝟘 : gproc)) : proc))))
  /\ (forall q, ((g OCp) : proc) ⟹[[ActOut ((cst oc), (cst v))]] q ->
        ~ (q ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g (𝟘 : gproc)) : proc))).
Proof.
  split; [ exact OCp_below_cfg | ].
  split; [ exact ax_OCp_below_msg | ].
  split; [ exact OCp_no_good_out_residue | exact no_drain_witness_for_OCp ].
Qed.

End VACCS_DropProbes.


(** * La branche régénérante de la dichotomie est FAUSSE

    L'énoncé visé par plusieurs sessions —

        (msgs l ‖ g M) ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)  ∧  M régénère (c,v)
          ⟹  (msgs l0 ‖ Mc) ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)

    — ne tient pas.  Le contre-exemple tient en quatre canaux :

        MR := (ra ? ((ra ! ru • 𝟘) ‖ (rc ? Kr)))  +  (rb ? (rb ! rw • 𝟘))
        lr := [(ra,ru); (rb,rw)]     N := 𝟘        Kr := re ! ry • 𝟘
        TRr := (rc ! rz • 𝟘) ‖ (re ? ①)

    Les **deux** gardes régénèrent — chacune ré-émet le message qu'elle
    consomme — et les deux successeurs de délivrance sont, à [≡*] près,
    [msgs lr ‖ (rc ? Kr)] et [msgs lr].

    - **L'hypothèse tient, et gratuitement** : [must_i_tau_below] sur la
      délivrance de [rb] donne [PR ⊑ₘᵤₛₜᵢ SBr], et [SBr ≡* msgs lr].
      Aucun raisonnement [must] n'est requis ([PR_below_msgs]).
    - **[SAr] passe [TRr]** ([SAr_passes_TRr]) : le client est τ-bloqué et
      non bon ; [SAr] prend son message [rc], la continuation répond sur
      [re], le client devient bon.
    - **[msgs lr] rate [TRr]** ([msgs_fails_TRr]) : un sac émet sur
      [ra],[rb] et n'écoute rien ; le client émet sur [rc] et n'écoute que
      [re].  Aucun pas dans la paire, donc le champ [ex] échoue.

    Le mécanisme est celui déjà isolé deux fois ici
    ([tau_successor_cannot_be_chosen],
    [delivery_successor_cannot_be_chosen]) : **le choix gardé commet**,
    donc les deux délivrances sont incompatibles et la sémantique ne
    contraint jamais que leur *conjonction* (champ [pt]), jamais chaque
    successeur séparément.

    Ce qui reste vrai, et qui explique pourquoi ces résultats ne se
    généralisent pas : dans la classe copycat les résidus sont [𝟘], donc
    tous les successeurs sont [≂ₘᵤₛₜᵢ] entre eux et [pt] ne contraint
    rien — c'est [VACCS_Matching.copycat_delivery_below_target].  Dès
    qu'un résidu fait autre chose ([rc ? Kr] ci-dessus contre [𝟘]), les
    successeurs divergent et rien ne les relie. *)

Section VACCS_RegenProbe.

Context `{VP : VACCS_Parameters}.
Context {ra rb rc re : Channel} {ru rw rz ry : Value}.
Context {nac : ra <> rc} {nae : ra <> re} {nbc : rb <> rc} {nbe : rb <> re}
        {nce : rc <> re}.

Definition Kr : proc := (cst re) ! (cst ry) • 𝟘.
Definition PAr : proc := ((cst ra) ! (cst ru) • 𝟘) ‖ (g ((cst rc) ? Kr)).
Definition PBr : proc := (cst rb) ! (cst rw) • 𝟘.
Definition MR : gproc := ((cst ra) ? PAr) + ((cst rb) ? PBr).
Definition lr : list TypeOfActions := [(cst ra ▷ cst ru); (cst rb ▷ cst rw)].
Definition PR : proc := (msgs lr) ‖ (g MR).

(** Les deux successeurs de délivrance, écrits littéralement pour que les
    pas [lts] soient des applications directes des constructeurs. *)
Definition SAr : proc :=
  ((𝟘 : proc) ‖ ((((cst rb) ! (cst rw) • 𝟘)) ‖ (𝟘 : proc))) ‖ PAr.
Definition SBr : proc :=
  ((((cst ra) ! (cst ru) • 𝟘)) ‖ ((𝟘 : proc) ‖ (𝟘 : proc))) ‖ PBr.
Definition TRr : proc := ((cst rc) ! (cst rz) • 𝟘) ‖ (g ((cst re) ? (g ①))).

Ltac blastR :=
  unfold lts_step in *; simpl in *;
  repeat match goal with
  | H : lts (_ ‖ _) _ _ |- _ => inversion H; subst; clear H
  | H : lts (_ ! _ • 𝟘) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g (_ + _)) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g (_ ? _)) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g 𝟘) _ _ |- _ => inversion H
  | H : lts (g ①) _ _ |- _ => inversion H
  end; simpl in *; try congruence; try contradiction.

Lemma dual_io_r : forall (x : TypeOfActions), dual (ActIn x) (ActOut x).
Proof. intros x. simpl. reflexivity. Qed.
Lemma dual_oi_r : forall (x : TypeOfActions), dual (ActOut x) (ActIn x).
Proof. intros x. simpl. reflexivity. Qed.

Lemma PR_tau_a : lts PR τ SAr.
Proof.
  unfold PR, SAr, MR, lr. eapply lts_comL.
  - simpl. apply lts_parL. apply lts_output.
  - apply lts_choiceL.
    assert (E : PAr ^ (cst ru) = PAr) by reflexivity.
    rewrite <- E at 2. apply lts_input.
Qed.

Lemma PR_tau_b : lts PR τ SBr.
Proof.
  unfold PR, SBr, MR, lr. eapply lts_comL.
  - simpl. apply lts_parR. apply lts_parL. apply lts_output.
  - apply lts_choiceR.
    assert (E : PBr ^ (cst rw) = PBr) by reflexivity.
    rewrite <- E at 2. apply lts_input.
Qed.

Lemma SBr_cgr : SBr ≡* (msgs lr).
Proof.
  unfold SBr, lr, PBr. simpl.
  transitivity (((cst ra ! cst ru • 𝟘) ‖ (𝟘 : proc)) ‖ (cst rb ! cst rw • 𝟘)).
  { apply cgr_fullpar; [ apply cgr_fullpar; [ reflexivity | apply cgr_par_nil ]
                       | reflexivity ]. }
  transitivity ((cst ra ! cst ru • 𝟘) ‖ (cst rb ! cst rw • 𝟘)).
  { apply cgr_fullpar; [ apply cgr_par_nil | reflexivity ]. }
  apply cgr_fullpar; [ reflexivity | apply cgr_par_nil_rev ].
Qed.

(** [SAr] est bien la configuration [msgs l0 ‖ Mc] de l'énoncé. *)
Lemma SAr_cgr : SAr ≡* ((msgs [(cst rb ▷ cst rw)]) ‖ PAr).
Proof.
  unfold SAr. simpl. apply cgr_fullpar; [ | reflexivity ].
  apply cgr_symm. apply ax_nil_par.
Qed.

(** L'hypothèse, gratuitement : un τ du serveur est déjà un pas [⊑ₘᵤₛₜᵢ]. *)
Lemma PR_below_msgs : PR ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs lr).
Proof.
  intros t Hm.
  apply (proj2 (must_i_cgr _ _ SBr_cgr) t).
  exact (must_i_tau_below PR SBr PR_tau_b t Hm).
Qed.

Lemma TRr_no_tau : forall q, ~ lts TRr τ q.
Proof. intros q Hq. unfold TRr in Hq. blastR. Qed.

Lemma TRr_not_good : ~ good_VACCS TRr.
Proof.
  intro Hg. unfold TRr in Hg. inversion Hg; subst.
  destruct H0 as [H|H]; inversion H.
Qed.

(** L'état atteint après la synchronisation sur [rc] : le serveur y émet
    sur [re], que le client écoute. *)
Definition InnerT : proc := (𝟘 : proc) ‖ (g ((cst re) ? (g ①))).
Definition InnerS : proc :=
  ((𝟘 : proc) ‖ ((((cst rb) ! (cst rw) • 𝟘)) ‖ (𝟘 : proc)))
    ‖ (((cst ra) ! (cst ru) • 𝟘) ‖ Kr).

Lemma InnerT_no_tau : forall q, ~ lts InnerT τ q.
Proof. intros q Hq. unfold InnerT in Hq. blastR. Qed.

Lemma InnerT_not_good : ~ good_VACCS InnerT.
Proof.
  intro Hg. unfold InnerT in Hg. inversion Hg; subst.
  destruct H0 as [H|H]; inversion H.
Qed.

Lemma InnerS_no_tau : forall q, ~ lts InnerS τ q.
Proof. intros q Hq. unfold InnerS, Kr in Hq. blastR. Qed.

Lemma inner_passes : InnerS must_pass InnerT.
Proof.
  apply m_step.
  - apply InnerT_not_good.
  - exists (((((𝟘 : proc) ‖ ((((cst rb) ! (cst rw) • 𝟘)) ‖ (𝟘 : proc)))
               ‖ (((cst ra) ! (cst ru) • 𝟘) ‖ (𝟘 : proc))))
              ▷ ((𝟘 : proc) ‖ ((g ①) : proc))).
    eapply ParSync.
    + apply dual_oi_r.
    + unfold InnerS, Kr. apply lts_parR. apply lts_parR. apply lts_output.
    + unfold InnerT. apply lts_parR.
      assert (E : ((g ①) : proc) ^ (cst ry) = ((g ①) : proc)) by reflexivity.
      rewrite <- E at 2. apply lts_input.
  - intros p' Hp'. exfalso. eapply InnerS_no_tau. exact Hp'.
  - intros t' Ht'. exfalso. eapply InnerT_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold InnerT in Ht'. inversion Ht'; subst.
    + exfalso. blastR.
    + inversion H3; subst.
      apply m_now. simpl. apply good_par. right. apply good_success.
Qed.

Lemma SAr_no_tau : forall q, ~ lts SAr τ q.
Proof. intros q Hq. unfold SAr, PAr, Kr in Hq. blastR. Qed.

Lemma SAr_passes_TRr : SAr must_pass TRr.
Proof.
  apply m_step.
  - apply TRr_not_good.
  - exists (InnerS ▷ InnerT). eapply ParSync.
    + apply dual_io_r.
    + unfold SAr, PAr, InnerS. apply lts_parR. apply lts_parR.
      assert (E : Kr ^ (cst rz) = Kr) by reflexivity.
      rewrite <- E at 2. apply lts_input.
    + unfold TRr, InnerT. apply lts_parL. apply lts_output.
  - intros p' Hp'. exfalso. eapply SAr_no_tau. exact Hp'.
  - intros t' Ht'. exfalso. eapply TRr_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold TRr in Ht'. inversion Ht'; subst.
    + inversion H3; subst.
      destruct mu1 as [x1|x1]; simpl in Hd; try contradiction. subst x1.
      unfold SAr, PAr in Hp'. blastR. exact inner_passes.
    + inversion H3; subst.
      apply m_now. apply good_par. right. apply good_success.
Qed.

Lemma msgs_fails_TRr : ~ ((msgs lr) must_pass TRr).
Proof.
  intro Hm. inversion Hm; subst.
  - apply TRr_not_good. assumption.
  - match goal with
    | H : exists _ : proc * proc, _ |- _ => destruct H as [[s1 t1] Hstep]
    end.
    unfold lr, TRr in Hstep. inversion Hstep; subst.
    all: blastR.
Qed.

Theorem regenerating_successor_can_fail :
  (PR ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs lr))
  /\ lts ((g MR) : proc) ((cst ra ▷ cst ru) ?) PAr
  /\ lts PR τ SAr
  /\ lts PAr ((cst ra ▷ cst ru) !) ((𝟘 : proc) ‖ (g ((cst rc) ? Kr)))
  /\ SAr ≡* ((msgs [(cst rb ▷ cst rw)]) ‖ PAr)
  /\ ~ (SAr ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs lr)).
Proof.
  repeat split.
  - exact PR_below_msgs.
  - unfold MR. apply lts_choiceL.
    assert (E : PAr ^ (cst ru) = PAr) by reflexivity.
    rewrite <- E at 2. apply lts_input.
  - exact PR_tau_a.
  - unfold PAr. apply lts_parL. apply lts_output.
  - exact SAr_cgr.
  - intro H. apply msgs_fails_TRr. apply H. exact SAr_passes_TRr.
Qed.

(** ** CORRECTION DE LECTURE : cette sonde ne réfute PAS la disjonction

    [regenerating_successor_can_fail] dit que **le successeur [ra] échoue**,
    pas qu'aucun successeur ne marche — et c'est une distinction qui a été
    confondue une fois dans les notes de conception.  Le successeur [rb],
    lui, convient : [SBr ≡* msgs lr].

    Les deux disjoints de [VACCS_Matching.CfgDisjunction] sont donc
    évalués ici, et le second tient :

    - **(A) sac vide** — [g MR ⊑ₘᵤₛₜᵢ g 𝟘] est **FAUX**.  Le client
      [UR := (ra!ru•𝟘) ‖ TRr] est τ-bloqué et non bon, et [g MR] le
      passe : la garde [ra] prend le message, sa continuation [PAr]
      re-émet sur [ra] (que le client refuse) **et** écoute [rc], que
      [TRr] fournit ; la réponse part alors sur [re], que [TRr] écoute,
      et le client devient bon.  C'est exactement la continuation « rend
      le message *et fait autre chose* » qui distingue cette sonde du
      copycat.
    - **(B) descente** — un successeur convient, via la délivrance de
      [rb].

    L'hypothèse [ra <> rb] est nécessaire et n'est pas dans le contexte
    de la section : sans elle la garde [rb] pourrait aussi tirer sur le
    message [ra] et l'obligation [com] changerait. *)

Definition PInner : proc := ((cst ra) ! (cst ru) • 𝟘) ‖ Kr.
Definition CTInner : proc := (𝟘 : proc) ‖ ((𝟘 : proc) ‖ (g ((cst re) ? (g ①)))).
Definition CTr : proc := (𝟘 : proc) ‖ TRr.
Definition UR : proc := ((cst ra) ! (cst ru) • 𝟘) ‖ TRr.

Lemma CTInner_no_tau : forall q, ~ lts CTInner τ q.
Proof. intros q Hq. unfold CTInner in Hq. blastR. Qed.

Lemma CTInner_not_good : ~ good_VACCS CTInner.
Proof.
  intro Hg. unfold CTInner in Hg. inversion Hg; subst.
  destruct H0 as [H|H]; [ inversion H | ].
  inversion H; subst. destruct H1 as [H'|H']; inversion H'.
Qed.

Lemma PInner_no_tau : forall q, ~ lts PInner τ q.
Proof. intros q Hq. unfold PInner, Kr in Hq. blastR. Qed.

Lemma CTr_no_tau : forall q, ~ lts CTr τ q.
Proof. intros q Hq. unfold CTr, TRr in Hq. blastR. Qed.

Lemma CTr_not_good : ~ good_VACCS CTr.
Proof.
  intro Hg. unfold CTr, TRr in Hg. inversion Hg; subst.
  destruct H0 as [H|H]; [ inversion H | ].
  inversion H; subst. destruct H1 as [H'|H']; inversion H'.
Qed.

Lemma pinner_passes : PInner must_pass CTInner.
Proof.
  apply m_step.
  - apply CTInner_not_good.
  - exists (((((cst ra) ! (cst ru) • 𝟘)) ‖ (𝟘 : proc))
              ▷ ((𝟘 : proc) ‖ ((𝟘 : proc) ‖ ((g ①) : proc)))).
    eapply ParSync.
    + apply dual_oi_r.
    + unfold PInner, Kr. apply lts_parR. apply lts_output.
    + unfold CTInner. apply lts_parR. apply lts_parR.
      assert (E : ((g ①) : proc) ^ (cst ry) = ((g ①) : proc)) by reflexivity.
      rewrite <- E at 2. apply lts_input.
  - intros p' Hp'. exfalso. eapply PInner_no_tau. exact Hp'.
  - intros t' Ht'. exfalso. eapply CTInner_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold CTInner in Ht'. inversion Ht'; subst.
    + exfalso. blastR.
    + inversion H3; subst.
      * exfalso. blastR.
      * inversion H4; subst.
        apply m_now. apply good_par. right. apply good_par. right. apply good_success.
Qed.

Lemma PAr_no_tau : forall q, ~ lts PAr τ q.
Proof. intros q Hq. unfold PAr, Kr in Hq. blastR. Qed.

Lemma PAr_passes_CTr : PAr must_pass CTr.
Proof.
  apply m_step.
  - apply CTr_not_good.
  - exists (PInner ▷ CTInner). eapply ParSync.
    + apply dual_io_r.
    + unfold PAr, PInner. apply lts_parR.
      assert (E : Kr ^ (cst rz) = Kr) by reflexivity.
      rewrite <- E at 2. apply lts_input.
    + unfold CTr, TRr, CTInner. apply lts_parR. apply lts_parL. apply lts_output.
  - intros p' Hp'. exfalso. eapply PAr_no_tau. exact Hp'.
  - intros t' Ht'. exfalso. eapply CTr_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold CTr, TRr in Ht'. inversion Ht'; subst.
    + exfalso. blastR.
    + inversion H3; subst.
      * inversion H4; subst.
        destruct mu1 as [x1|x1]; simpl in Hd; try contradiction. subst x1.
        unfold PAr in Hp'. blastR. exact pinner_passes.
      * inversion H4; subst.
        apply m_now. apply good_par. right. apply good_par. right. apply good_success.
Qed.

Lemma UR_no_tau : forall q, ~ lts UR τ q.
Proof. intros q Hq. unfold UR, TRr in Hq. blastR. Qed.

Lemma UR_not_good : ~ good_VACCS UR.
Proof.
  intro Hg. unfold UR, TRr in Hg. inversion Hg; subst.
  destruct H0 as [H|H]; [ inversion H | ].
  inversion H; subst. destruct H1 as [H'|H']; inversion H'.
Qed.

Lemma MR_no_tau : forall q, ~ lts ((g MR) : proc) τ q.
Proof. intros q Hq. unfold MR in Hq. blastR. Qed.

Lemma MR_passes_UR : ra <> rb -> ((g MR) : proc) must_pass UR.
Proof.
  intro Hab. apply m_step.
  - apply UR_not_good.
  - exists (PAr ▷ CTr). eapply ParSync.
    + apply dual_io_r.
    + unfold MR. apply lts_choiceL.
      assert (E : PAr ^ (cst ru) = PAr) by reflexivity.
      rewrite <- E at 2. apply lts_input.
    + unfold UR, CTr. apply lts_parL. apply lts_output.
  - intros p' Hp'. exfalso. eapply MR_no_tau. exact Hp'.
  - intros t' Ht'. exfalso. eapply UR_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold UR, TRr in Ht'. inversion Ht'; subst.
    + inversion H3; subst.
      destruct mu1 as [x1|x1]; simpl in Hd; try contradiction. subst x1.
      unfold MR in Hp'. blastR. exact PAr_passes_CTr.
    + inversion H3; subst.
      * inversion H4; subst.
        destruct mu1 as [x1|x1]; simpl in Hd; try contradiction. subst x1.
        exfalso. unfold MR in Hp'. blastR.
      * inversion H4; subst.
        exfalso. unfold MR in Hp'. blastR.
Qed.

Theorem regen_empty_bag_fails : ra <> rb ->
  ~ (((g MR) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc)).
Proof.
  intros Hab Hle. rewrite below_nil_iff in Hle.
  eapply Hle; [ apply UR_no_tau | apply UR_not_good | apply MR_passes_UR; exact Hab ].
Qed.

Theorem regen_probe_satisfies_disjunction : ra <> rb ->
  (PR ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs lr))
  /\ ~ (((g MR) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc))
  /\ (exists p', lts PR τ p' /\ p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs lr)).
Proof.
  intro Hab. split; [ exact PR_below_msgs | split ].
  - apply regen_empty_bag_fails. exact Hab.
  - exists SBr. split; [ exact PR_tau_b | ].
    exact (proj2 (must_i_cgr _ _ SBr_cgr)).
Qed.

(** ** …mais Phase A, elle, tient — et se dérive en trois coups

    Il faut séparer deux choses que le contre-exemple ci-dessus pourrait
    laisser confondre.  Ce qu'il réfute est la **descente** : le
    successeur de délivrance n'est pas sous la cible.  Il ne dit rien
    contre [VACCS_Matching.PhaseA_config], qui est l'unique hypothèse
    dont dépendent [ax_below_stable_sum_cfg] et [ax_below_NF_cfg] — et
    ici Phase A est non seulement vraie mais **dérivable**, par la
    délivrance de l'*autre* message.

    Même situation qu'au contre-exemple précédent
    ([CertAll_is_false]) : là aussi Phase A tient et se dérive en un
    [ax_tau_step], et c'est le *certificat de pose* qui est faux.

    Donc les deux résultats négatifs de ce fichier ferment deux **routes
    vers** Phase A (la simulation de pose rigide, la descente vers un
    successeur), et laissent l'énoncé lui-même intact.  C'est lui, et
    lui seul, qui reste à prouver. *)

Lemma phaseA_holds_on_regen_probe :
  ax_pre PR ((msgs lr) ‖ ((g (mirrorN ((g MR) : proc) 𝟘)) : proc)).
Proof.
  simpl.
  eapply ax_trans; [ apply ax_tau_step; exact PR_tau_b | ].
  eapply ax_trans; [ apply ax_cgr; exact SBr_cgr | ].
  apply ax_cgr. apply cgr_par_nil_rev.
Qed.

(** …et ici encore [CfgDisjunctionLocal] tient, par l'**autre** garde :
    [rb] rend exactement le message qu'elle consomme, avec résidu [𝟘].
    C'est la même leçon que celle du tableau des instances : ce que
    [regenerating_successor_can_fail] réfute est le choix d'un successeur
    *désigné*, pas l'existence d'un bon. *)

Theorem cfg_disjunction_local_at_MR :
  (((g MR) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc))
  \/ (exists c0 v0 l0 Mc,
        Permutation lr ((c0,v0) :: l0)
        /\ lts ((g MR) : proc) (ActExt (ActIn (c0,v0))) Mc
        /\ Mc ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((((c0 ! v0 • 𝟘)) : proc) ‖ ((g 𝟘) : proc))).
Proof.
  right. exists (cst rb), (cst rw), [(cst ra ▷ cst ru)], PBr.
  split; [ | split ].
  - unfold lr. apply perm_swap.
  - unfold MR. apply lts_choiceR.
    assert (E : PBr = PBr ^ (cst rw)) by reflexivity.
    rewrite E at 2. apply lts_input.
  - unfold PBr. eapply local_disjunct_of_returning; [ apply lts_output | ].
    intros t Hm. exact Hm.
Qed.

End VACCS_RegenProbe.

(** * AUCUNE délivrance n'est réversible — même pour une somme CANONIQUE

    `must_i_delivery_reversible` et `copycat_delivery_below_target`
    ([VACCS_Matching.v]) donnent les deux cas où la délivrance *est*
    réversible ; et l'espoir restant pour la récursion de
    [PhaseA_config] était que la **canonicité** suffise à ce qu'*une* des
    délivrances le soit.  Elle ne suffit pas.

    Le mécanisme est celui de [tau_successor_cannot_be_chosen], transposé
    des `𝛕`-sommants aux **délivrances** : deux **gardes mortes
    croisées**.

        XKe := xe ! xy • 𝟘
        XA  := (xc ? XKe) + (xd ? 𝟘)      XB  := (xd ? XKe) + (xc ? 𝟘)
        XM  := (xa ? XA)  + (xb ? XB)     xl  := [(xa,xu); (xb,xw)]
        XP  := msgs xl ‖ g XM

    [XM] est **canonique** — une garde par canal, [xa] ≠ [xb] — et [XA],
    [XB] aussi.  La garde morte de [XA] est sur le canal dont [XB] a
    besoin, et réciproquement.  Les deux successeurs de délivrance sont
    donc *incompatibles* :

    - [XSA] passe [XTa := (xc!xz•𝟘) ‖ (xe ? ①)] — il prend [xc], la
      continuation répond sur [xe] — et [XSB] le **rate** : sa garde
      morte sur [xc] force [𝟘] à passer un résidu τ-bloqué non bon.
    - symétriquement avec [XTb] et [xd].

    Comme le champ [pt] de [must] exige que **tous** les τ-successeurs
    passent, [XP] rate [XTa] (à cause de [XSB]) et rate [XTb] (à cause de
    [XSA]).  Donc ni [XSA] ni [XSB] n'est [⊑ₘᵤₛₜᵢ]-sous [XP], alors que
    [XP] est sous les deux ([must_i_tau_below]) :

        no_delivery_is_reversible :
          XP ⟶τ XSA  ∧  XP ⟶τ XSB
          ∧ XP ⊑ₘᵤₛₜᵢ XSA  ∧  XP ⊑ₘᵤₛₜᵢ XSB
          ∧ ¬ (XSA ⊑ₘᵤₛₜᵢ XP)  ∧  ¬ (XSB ⊑ₘᵤₛₜᵢ XP)

    **Conséquence.**  La récursion « descendre vers un successeur » ne
    peut pas être rendue déterministe par [canonicalize] : la canonicité
    supprime l'ambiguïté *au sein d'un canal*
    ([canonical_delivery_is_deterministic_and_works]), pas
    l'incompatibilité *entre* canaux.  Toute preuve de [PhaseA_config]
    devra donc consommer la **conjonction** que le champ [pt] fournit —
    l'analogue à gauche de [ax_glb_tau] — et un tel analogue n'existe pas
    aujourd'hui, parce que les délivrances viennent du *sac* et non de
    `𝛕`-sommants. *)

Section VACCS_XProbe.

Context `{VP : VACCS_Parameters}.
Context {xa xb xc xd xe : Channel} {xu xw xz xy : Value}.
Context {xab : xa <> xb} {xac : xa <> xc} {xad : xa <> xd} {xae : xa <> xe}
        {xbc : xb <> xc} {xbd : xb <> xd} {xbe : xb <> xe}
        {xcd : xc <> xd} {xce : xc <> xe} {xde : xd <> xe}.

Definition XKe : proc := (cst xe) ! (cst xy) • 𝟘.
Definition XA : gproc := ((cst xc) ? XKe) + ((cst xd) ? ((g 𝟘) : proc)).
Definition XB : gproc := ((cst xd) ? XKe) + ((cst xc) ? ((g 𝟘) : proc)).
Definition XM : gproc := ((cst xa) ? ((g XA) : proc)) + ((cst xb) ? ((g XB) : proc)).
Definition xl : list TypeOfActions := [(cst xa ▷ cst xu); (cst xb ▷ cst xw)].
Definition XP : proc := (msgs xl) ‖ (g XM).
Definition XSA : proc :=
  ((𝟘 : proc) ‖ ((((cst xb) ! (cst xw) • 𝟘)) ‖ (𝟘 : proc))) ‖ ((g XA) : proc).
Definition XSB : proc :=
  ((((cst xa) ! (cst xu) • 𝟘)) ‖ ((𝟘 : proc) ‖ (𝟘 : proc))) ‖ ((g XB) : proc).
Definition XTa : proc := ((cst xc) ! (cst xz) • 𝟘) ‖ (g ((cst xe) ? (g ①))).
Definition XTb : proc := ((cst xd) ! (cst xz) • 𝟘) ‖ (g ((cst xe) ? (g ①))).

Ltac blastX :=
  unfold lts_step in *; simpl in *;
  repeat match goal with
  | H : lts (_ ‖ _) _ _ |- _ => inversion H; subst; clear H
  | H : lts (_ ! _ • 𝟘) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g (_ + _)) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g (_ ? _)) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g 𝟘) _ _ |- _ => inversion H
  | H : lts (g ①) _ _ |- _ => inversion H
  end; simpl in *; try congruence; try contradiction.

Lemma dual_io_x : forall (x : TypeOfActions), dual (ActIn x) (ActOut x).
Proof. intros x. simpl. reflexivity. Qed.
Lemma dual_oi_x : forall (x : TypeOfActions), dual (ActOut x) (ActIn x).
Proof. intros x. simpl. reflexivity. Qed.

Lemma XP_tau_a : lts XP τ XSA.
Proof.
  unfold XP, XSA, XM, xl. eapply lts_comL.
  - simpl. apply lts_parL. apply lts_output.
  - apply lts_choiceL.
    assert (E : ((g XA) : proc) ^ (cst xu) = ((g XA) : proc)) by reflexivity.
    rewrite <- E at 2. apply lts_input.
Qed.

Lemma XP_tau_b : lts XP τ XSB.
Proof.
  unfold XP, XSB, XM, xl. eapply lts_comL.
  - simpl. apply lts_parR. apply lts_parL. apply lts_output.
  - apply lts_choiceR.
    assert (E : ((g XB) : proc) ^ (cst xw) = ((g XB) : proc)) by reflexivity.
    rewrite <- E at 2. apply lts_input.
Qed.

Definition XIt : proc := (𝟘 : proc) ‖ (g ((cst xe) ? (g ①))).
Definition XIa : proc :=
  ((𝟘 : proc) ‖ ((((cst xb) ! (cst xw) • 𝟘)) ‖ (𝟘 : proc))) ‖ XKe.
Definition XIb : proc :=
  ((((cst xa) ! (cst xu) • 𝟘)) ‖ ((𝟘 : proc) ‖ (𝟘 : proc))) ‖ XKe.
Definition XRb : proc :=
  ((((cst xa) ! (cst xu) • 𝟘)) ‖ ((𝟘 : proc) ‖ (𝟘 : proc))) ‖ ((g 𝟘) : proc).
Definition XRa : proc :=
  ((𝟘 : proc) ‖ ((((cst xb) ! (cst xw) • 𝟘)) ‖ (𝟘 : proc))) ‖ ((g 𝟘) : proc).

Lemma XIt_no_tau : forall q, ~ lts XIt τ q.
Proof. intros q Hq. unfold XIt in Hq. blastX. Qed.

Lemma XIt_not_good : ~ good_VACCS XIt.
Proof. intro Hg. unfold XIt in Hg. inversion Hg; subst. destruct H0 as [H|H]; inversion H. Qed.

Lemma XIa_no_tau : forall q, ~ lts XIa τ q.
Proof. intros q Hq. unfold XIa, XKe in Hq. blastX. Qed.

Lemma XIb_no_tau : forall q, ~ lts XIb τ q.
Proof. intros q Hq. unfold XIb, XKe in Hq. blastX. Qed.

Lemma XIa_passes : XIa must_pass XIt.
Proof.
  apply m_step.
  - apply XIt_not_good.
  - exists ((((𝟘 : proc) ‖ ((((cst xb) ! (cst xw) • 𝟘)) ‖ (𝟘 : proc))) ‖ (𝟘 : proc))
              ▷ ((𝟘 : proc) ‖ ((g ①) : proc))).
    eapply ParSync.
    + apply dual_oi_x.
    + unfold XIa, XKe. apply lts_parR. apply lts_output.
    + unfold XIt. apply lts_parR.
      assert (E : ((g ①) : proc) ^ (cst xy) = ((g ①) : proc)) by reflexivity.
      rewrite <- E at 2. apply lts_input.
  - intros p' Hp'. exfalso. eapply XIa_no_tau. exact Hp'.
  - intros t' Ht'. exfalso. eapply XIt_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold XIt in Ht'. inversion Ht'; subst.
    + exfalso. blastX.
    + inversion H3; subst. apply m_now. simpl. apply good_par. right. apply good_success.
Qed.

Lemma XIb_passes : XIb must_pass XIt.
Proof.
  apply m_step.
  - apply XIt_not_good.
  - exists (((((cst xa) ! (cst xu) • 𝟘) ‖ ((𝟘 : proc) ‖ (𝟘 : proc))) ‖ (𝟘 : proc))
              ▷ ((𝟘 : proc) ‖ ((g ①) : proc))).
    eapply ParSync.
    + apply dual_oi_x.
    + unfold XIb, XKe. apply lts_parR. apply lts_output.
    + unfold XIt. apply lts_parR.
      assert (E : ((g ①) : proc) ^ (cst xy) = ((g ①) : proc)) by reflexivity.
      rewrite <- E at 2. apply lts_input.
  - intros p' Hp'. exfalso. eapply XIb_no_tau. exact Hp'.
  - intros t' Ht'. exfalso. eapply XIt_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold XIt in Ht'. inversion Ht'; subst.
    + exfalso. blastX.
    + inversion H3; subst. apply m_now. simpl. apply good_par. right. apply good_success.
Qed.

Lemma XTa_no_tau : forall q, ~ lts XTa τ q.
Proof. intros q Hq. unfold XTa in Hq. blastX. Qed.
Lemma XTb_no_tau : forall q, ~ lts XTb τ q.
Proof. intros q Hq. unfold XTb in Hq. blastX. Qed.
Lemma XTa_not_good : ~ good_VACCS XTa.
Proof. intro Hg. unfold XTa in Hg. inversion Hg; subst. destruct H0 as [H|H]; inversion H. Qed.
Lemma XTb_not_good : ~ good_VACCS XTb.
Proof. intro Hg. unfold XTb in Hg. inversion Hg; subst. destruct H0 as [H|H]; inversion H. Qed.
Lemma XSA_no_tau : forall q, ~ lts XSA τ q.
Proof. intros q Hq. unfold XSA, XA, XKe in Hq. blastX. Qed.
Lemma XSB_no_tau : forall q, ~ lts XSB τ q.
Proof. intros q Hq. unfold XSB, XB, XKe in Hq. blastX. Qed.

(** Les deux résidus des **gardes mortes** : plus rien ne peut bouger. *)
Lemma XRb_fails_XIt : ~ (XRb must_pass XIt).
Proof.
  intro Hm. inversion Hm; subst.
  - apply XIt_not_good. assumption.
  - match goal with H : exists _ : proc * proc, _ |- _ => destruct H as [[s1 t1] Hstep] end.
    unfold XRb, XIt in Hstep. inversion Hstep; subst; blastX.
Qed.

Lemma XRa_fails_XIt : ~ (XRa must_pass XIt).
Proof.
  intro Hm. inversion Hm; subst.
  - apply XIt_not_good. assumption.
  - match goal with H : exists _ : proc * proc, _ |- _ => destruct H as [[s1 t1] Hstep] end.
    unfold XRa, XIt in Hstep. inversion Hstep; subst; blastX.
Qed.

Lemma XSB_fails_XTa : ~ (XSB must_pass XTa).
Proof.
  intro Hm. inversion Hm; subst.
  - apply XTa_not_good. assumption.
  - apply XRb_fails_XIt.
    match goal with H : forall _ _ _ _, _ |- _ =>
      apply (H XRb XIt (ActIn (cst xc ▷ cst xz)) (ActOut (cst xc ▷ cst xz))) end.
    + apply dual_io_x.
    + unfold XSB, XRb, XB. apply lts_parR. apply lts_choiceR.
      assert (E : ((g 𝟘) : proc) ^ (cst xz) = ((g 𝟘) : proc)) by reflexivity.
      rewrite <- E at 2. apply lts_input.
    + unfold XTa, XIt. apply lts_parL. apply lts_output.
Qed.

Lemma XSA_fails_XTb : ~ (XSA must_pass XTb).
Proof.
  intro Hm. inversion Hm; subst.
  - apply XTb_not_good. assumption.
  - apply XRa_fails_XIt.
    match goal with H : forall _ _ _ _, _ |- _ =>
      apply (H XRa XIt (ActIn (cst xd ▷ cst xz)) (ActOut (cst xd ▷ cst xz))) end.
    + apply dual_io_x.
    + unfold XSA, XRa, XA. apply lts_parR. apply lts_choiceR.
      assert (E : ((g 𝟘) : proc) ^ (cst xz) = ((g 𝟘) : proc)) by reflexivity.
      rewrite <- E at 2. apply lts_input.
    + unfold XTb, XIt. apply lts_parL. apply lts_output.
Qed.

Lemma XSA_passes_XTa : XSA must_pass XTa.
Proof.
  apply m_step.
  - apply XTa_not_good.
  - exists (XIa ▷ XIt). eapply ParSync.
    + apply dual_io_x.
    + unfold XSA, XIa, XA. apply lts_parR. apply lts_choiceL.
      assert (E : XKe ^ (cst xz) = XKe) by reflexivity.
      rewrite <- E at 2. apply lts_input.
    + unfold XTa, XIt. apply lts_parL. apply lts_output.
  - intros p' Hp'. exfalso. eapply XSA_no_tau. exact Hp'.
  - intros t' Ht'. exfalso. eapply XTa_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold XTa in Ht'. inversion Ht'; subst.
    + inversion H3; subst.
      destruct mu1 as [x1|x1]; simpl in Hd; try contradiction. subst x1.
      unfold XSA, XA in Hp'. blastX. exact XIa_passes.
    + inversion H3; subst. apply m_now. apply good_par. right. apply good_success.
Qed.

Lemma XSB_passes_XTb : XSB must_pass XTb.
Proof.
  apply m_step.
  - apply XTb_not_good.
  - exists (XIb ▷ XIt). eapply ParSync.
    + apply dual_io_x.
    + unfold XSB, XIb, XB. apply lts_parR. apply lts_choiceL.
      assert (E : XKe ^ (cst xz) = XKe) by reflexivity.
      rewrite <- E at 2. apply lts_input.
    + unfold XTb, XIt. apply lts_parL. apply lts_output.
  - intros p' Hp'. exfalso. eapply XSB_no_tau. exact Hp'.
  - intros t' Ht'. exfalso. eapply XTb_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold XTb in Ht'. inversion Ht'; subst.
    + inversion H3; subst.
      destruct mu1 as [x1|x1]; simpl in Hd; try contradiction. subst x1.
      unfold XSB, XB in Hp'. blastX. exact XIb_passes.
    + inversion H3; subst. apply m_now. apply good_par. right. apply good_success.
Qed.

(** C'est le champ [pt] qui fait tout le travail : il exige que **tous**
    les τ-successeurs passent, donc l'un qui rate suffit. *)
Lemma XP_fails_XTa : ~ (XP must_pass XTa).
Proof.
  intro Hm. inversion Hm; subst.
  - apply XTa_not_good. assumption.
  - apply XSB_fails_XTa. apply (pt XSB XP_tau_b).
Qed.

Lemma XP_fails_XTb : ~ (XP must_pass XTb).
Proof.
  intro Hm. inversion Hm; subst.
  - apply XTb_not_good. assumption.
  - apply XSA_fails_XTb. apply (pt XSA XP_tau_a).
Qed.

Theorem no_delivery_is_reversible :
  lts XP τ XSA /\ lts XP τ XSB
  /\ (XP ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ XSA) /\ (XP ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ XSB)
  /\ ~ (XSA ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ XP) /\ ~ (XSB ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ XP).
Proof.
  repeat split.
  - exact XP_tau_a.
  - exact XP_tau_b.
  - exact (must_i_tau_below XP XSA XP_tau_a).
  - exact (must_i_tau_below XP XSB XP_tau_b).
  - intro H. apply XP_fails_XTa. apply H. exact XSA_passes_XTa.
  - intro H. apply XP_fails_XTb. apply H. exact XSB_passes_XTb.
Qed.

(** ** LA « DESCENTE » N'EST PAS LA RÈGLE MANQUANTE — elle est FAUSSE

    Des deux formes candidates pour la règle qui traiterait
    [VACCS_Matching.CfgUnstableLeft], celle-ci se réfute d'un coup :

        si la gauche a un τ et qu'elle est sous la cible,
        alors *un* de ses τ-successeurs est sous la cible

    Prendre la cible **égale à la gauche** : l'hypothèse devient la
    réflexivité, et [no_delivery_is_reversible] dit qu'aucun des deux
    successeurs n'est sous [XP].  L'inversion [XP_tau_inv] montre qu'il
    n'y en a pas d'autres.

    Noter que l'inéquation, elle, est parfaitement dérivable ici — par
    [ax_refl].  Ce qui est réfuté est la *stratégie* « descendre », pas
    l'énoncé de complétude. *)

Lemma XP_static : Static XP.
Proof.
  unfold XP. constructor; [ apply msgs_Static | ].
  apply static_g. unfold XM, XA, XB, XKe. repeat constructor.
Qed.

Lemma XP_tau_inv : forall p', lts XP τ p' -> p' = XSA \/ p' = XSB.
Proof.
  intros p' Hl. unfold XP, XM, xl in Hl. simpl in Hl.
  inversion Hl; subst;
    repeat match goal with
    | H : lts (_ ‖ _) _ _ |- _ => inversion H; subst; clear H
    | H : lts (_ ! _ • 𝟘) _ _ |- _ => inversion H; subst; clear H
    | H : lts (g (_ + _)) _ _ |- _ => inversion H; subst; clear H
    | H : lts (g (_ ? _)) _ _ |- _ => inversion H; subst; clear H
    | H : lts (g 𝟘) _ _ |- _ => inversion H
    end; simpl in *; try congruence;
    try (left; unfold XSA, XA; reflexivity);
    try (right; unfold XSB, XB; reflexivity).
Qed.

Theorem cfg_descent_is_false :
  ~ (forall (p q : proc), Static p -> Static q ->
       (exists z, lts p τ z) -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
       exists p', lts p τ p' /\ p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q).
Proof.
  intro H.
  destruct no_delivery_is_reversible as (Ha & Hb & _ & _ & HnA & HnB).
  destruct (H XP XP XP_static XP_static (ex_intro _ _ Ha) (fun t Hm => Hm))
    as (p' & Hstep & Hle).
  destruct (XP_tau_inv p' Hstep) as [E | E]; subst p'.
  - apply HnA. exact Hle.
  - apply HnB. exact Hle.
Qed.

(** ** `CfgDisjunction` sur cette instance : c'est le disjoint SAC VIDE

    Ici c'est l'inverse de [cfg_disjunction_at_MCert] : le disjoint
    **descente** est faux ([no_delivery_is_reversible] : aucun des deux
    successeurs n'est sous [XP], et [XP_tau_inv] dit qu'il n'y en a pas
    d'autres), mais la cible **est** la gauche, donc l'inéquation au sac
    vide vaut par réflexivité et le **disjoint sac vide** tient.

    Les deux instances se complètent donc exactement : chacune réfute un
    disjoint et vérifie l'autre. *)

Theorem cfg_disjunction_at_XProbe :
  (((g XM) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g XM) : proc))
  /\ ~ (exists p', lts XP τ p' /\ p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ XP).
Proof.
  split.
  - intros t Hm. exact Hm.
  - intros (p' & Hstep & Hle).
    destruct no_delivery_is_reversible as (_ & _ & _ & _ & HnA & HnB).
    destruct (XP_tau_inv p' Hstep) as [E | E]; subst p'.
    + apply HnA. exact Hle.
    + apply HnB. exact Hle.
Qed.

(** Et sur la troisième instance, [CfgDisjunctionLocal] tient par son
    **premier** disjoint — la cible étant la gauche elle-même, l'inéquation
    au sac vide est la réflexivité.

    Les trois instances machine-vérifiées du fichier valident donc la forme
    survivante : [MCert] et [MR] par le disjoint local (une garde rend son
    message), [XProbe] par le disjoint « sac vide ».  C'est exactement le
    test que la famille source-only ne passe pas. *)

Theorem cfg_disjunction_local_at_XProbe :
  (((g XM) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g XM) : proc))
  \/ (exists c0 v0 l0 Mc,
        Permutation xl ((c0,v0) :: l0)
        /\ lts ((g XM) : proc) (ActExt (ActIn (c0,v0))) Mc
        /\ Mc ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((((c0 ! v0 • 𝟘)) : proc) ‖ ((g XM) : proc))).
Proof.
  left. intros t Hm. exact Hm.
Qed.

(** ** Le critère décidable route CETTE instance vers le PREMIER disjoint

    [VACCS_Bad.cfg_local_split] scinde
    [VACCS_Matching.CfgDisjunctionLocal] à une seule implication, sous
    une hypothèse décidable : la somme nue a-t-elle un [τ], et une de ses
    continuations peut-elle émettre sur la voie de sa propre garde ?

    Contrôle sur l'instance la plus dure du dossier — celle dont
    [no_delivery_is_reversible] et [cfg_descent_is_false] réfutent
    justement la descente.  Le critère y **réussit** : [g XM] est
    τ-stable (aucun [𝛕]-sommant) et aucune continuation ne rend le
    message de sa garde (les deux continuations n'émettent que sur
    [xe]).  Le cas est donc envoyé sur le **premier** disjoint, où il est
    effectivement vrai ([cfg_disjunction_at_XProbe]).

    C'est ce que la réduction demande : là où la descente est
    machine-réfutée, le critère ne l'essaie pas. *)

Lemma XProbe_meets_criterion :
  (forall z, ~ lts ((g XM) : proc) τ z) /\ ~ SelfRet XM.
Proof.
  split.
  - intros z Hz. unfold XM in Hz.
    inversion Hz; subst; inversion H3.
  - intros (c & v & P' & Hl & Hin).
    destruct (gsum_in_summand XM c v P' Hl) as (P & Hins & Heq). subst P'.
    rewrite ochans_subst in Hin.
    unfold XM in Hins. simpl in Hins.
    destruct Hins as [Heq | [Heq | []]]; injection Heq; intros; subst;
      simpl in Hin; destruct Hin as [Heq2 | []]; injection Heq2; intros;
      congruence.
Qed.

End VACCS_XProbe.

(** * THE LEFT-HAND RESTRICTION IS NOT AN ARTEFACT — [MuteSem] EXCLUDES
      A THREE-LINE PROCESS

    [VACCS_EquivalenceAx]'s completeness needs the left in [MuteSem]:
    [⊢]-below a *mute* configuration [msgs l ‖ g M] (no continuation of
    any guard can emit) that is [⊑ₘᵤₛₜᵢ]-above it.  This section
    machine-checks that the restriction bites already at

        PL := a ? (b ! v • 𝟘)          (a ≠ b)

    — a guard whose continuation emits on **another** channel.

    The argument.  A mute configuration can only ever emit what its bag
    held from the start: its sum emits nothing ([gsum_no_out]) and no
    continuation can either ([ochans (g M) = []]).  So against the
    τ-stuck, non-good client

        TL := (a ! v • 𝟘) ‖ (b ? ①)

    it is [Bad] at its own emitted channels ([ochans_sub_Bad]), hence
    fails TL as soon as [b] is not among them ([Bad_sound]) — while [PL]
    *passes* TL: it takes the [a]-message and answers on [b], which the
    probe accepts.

    What is left informal is the complementary case, a bag that already
    carries a [b]-message: such a configuration emits [b] straight away
    and [b ? ①] separates it from [PL], which emits nothing until it has
    received.  (Formalising that half needs a *positive* [must] against a
    configuration with deliveries available, which [must_any_probe] does
    not cover — it asks for a τ-stuck server.)

    Note what this does and does not show.  It delimits **[MuteSem]**,
    i.e. the route this development takes; it does *not* say completeness
    fails for [PL] — only that no mute configuration certifies it. *)

Section VACCS_MuteLimit.

Context `{VP : VACCS_Parameters}.
Context {ma mb : Channel} {mvv : Value}.
Context {mab : ma <> mb}.

Definition PL : proc := g (((cst ma) ? (((cst mb) ! (cst mvv) • 𝟘) : proc)) : gproc).
Definition TP : proc := g (((cst mb) ? ((g (① : gproc)) : proc)) : gproc).
Definition TL : proc := (((cst ma) ! (cst mvv) • 𝟘) : proc) ‖ TP.

Lemma TL_not_good : ~ good_VACCS TL.
Proof.
  intro H. inversion H; subst; inversion H1.
  - inversion H0.
  - inversion H0.
Qed.

Lemma TL_no_tau : forall z, ~ lts TL τ z.
Proof.
  intros z H. inversion H; subst.
  - inversion H2; subst. inversion H3; subst. symmetry in H5. contradiction.
  - inversion H2.
  - inversion H4.
  - inversion H4.
Qed.

Lemma inner_must :
  ((cst mb) ! (cst mvv) • 𝟘) must_pass (((g (𝟘 : gproc)) : proc) ‖ TP).
Proof.
  eapply must_eq_client with (t := TP).
  - symmetry. etransitivity; [ apply cgr_par_com | apply cgr_par_nil ].
  - apply must_any_probe.
    + intros q Hq. inversion Hq.
    + exists (cst mvv), ((g (𝟘 : gproc)) : proc). apply lts_output.
Qed.

Lemma PL_passes_TL : PL must_pass TL.
Proof.
  apply m_step.
  - apply TL_not_good.
  - assert (Hcl : lts TL (ActExt (ActOut ((cst ma) ▷ (cst mvv))))
                      (((g (𝟘 : gproc)) : proc) ‖ TP)).
    { apply lts_parL. apply lts_output. }
    assert (Hsv : lts PL (ActExt (ActIn ((cst ma) ▷ (cst mvv))))
                      (subst_in_proc 0 (cst mvv) (((cst mb) ! (cst mvv) • 𝟘) : proc)))
      by apply lts_input.
    eexists. eapply (ParSync (ActIn ((cst ma) ▷ (cst mvv)))
                             (ActOut ((cst ma) ▷ (cst mvv)))).
    + reflexivity.
    + exact Hsv.
    + exact Hcl.
  - intros p' Hp'. inversion Hp'.
  - intros t' Ht'. exfalso. eapply TL_no_tau. exact Ht'.
  - intros mu1 mu2 p' t' Hdual Hp' Ht'. inversion Hp'; subst.
    destruct t' as [a2|a2]; simpl in Hdual; try contradiction.
    subst a2. inversion Ht'; subst.
    + inversion H3; subst. simpl. apply inner_must.
    + inversion H3.
Qed.

Lemma ochans_msgs_l : forall (l : list TypeOfActions), ochans (msgs l) = map fst l.
Proof.
  induction l as [|a l IH]; simpl; [ reflexivity | ].
  destruct a as (c,v). simpl. rewrite IH. reflexivity.
Qed.

Theorem mute_cfg_not_above_PL : forall (l : list TypeOfActions) (M : gproc),
  gStatic M -> ochans ((g M) : proc) = [] ->
  ~ In (cst mb) (map fst l) ->
  ~ (PL ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g M) : proc))).
Proof.
  intros l M HM Hoc Hnd Hpre.
  assert (Hm : (msgs l ‖ ((g M) : proc)) must_pass TL)
    by (apply Hpre; apply PL_passes_TL).
  assert (Hoch : ochans (msgs l ‖ ((g M) : proc)) = map fst l).
  { simpl. rewrite ochans_msgs_l. simpl in Hoc. rewrite Hoc. apply app_nil_r. }
  eapply (Bad_sound _ TL Hm (fun d => In d (ochans (msgs l ‖ ((g M) : proc))))).
  - apply ochans_sub_Bad.
    + constructor; [ apply msgs_Static | apply static_g; exact HM ].
    + intros d Hd. exact Hd.
  - apply TL_no_tau.
  - apply TL_not_good.
  - intros c0 v0 q Hc0 Hl. rewrite Hoch in Hc0. apply Hnd.
    inversion Hl; subst.
    + inversion H3.
    + inversion H3; subst. exact Hc0.
Qed.


(** ** The complementary half: a bag that already carries an [mb]-message

    [mute_cfg_not_above_PL] covers the bags carrying no [mb]-message.
    The other bags are settled here, and the plan's estimate of the cost
    was too pessimistic: it expected a **positive** [must] fact against a
    configuration with available deliveries — something
    [VACCS_Matching.must_any_probe] does not cover, since it needs a
    τ-stuck server.  None is needed.

    [VACCS_Matching.below_preserves_no_weak_out] already says that "never
    emitting weakly on [c]" travels **up** the preorder, and the two
    sides sit on opposite sides of it: a configuration holding an
    [mb]-message emits on [mb] **at once**, while [PL] cannot emit at all
    before it has received.

    Together with [mute_cfg_not_above_PL] this covers *every* bag: no
    configuration with a mute sum is ever above [PL]. *)

Lemma PL_static : Static PL.
Proof. unfold PL. apply static_g. constructor. constructor. Qed.

Lemma PL_no_weak_out : NoWeakOut (cst mb) PL.
Proof.
  intros p1 Hw w r Hl.
  assert (Hst : PL ↛).
  { apply no_lts_stable. intros q Hq. unfold PL in Hq. inversion Hq. }
  apply (wt_nil_stable PL p1 Hst) in Hw. subst p1.
  unfold PL in Hl. inversion Hl.
Qed.

Theorem cfg_with_msg_not_above_PL : forall l M w l0,
  gStatic M ->
  Permutation l ((cst mb ▷ w) :: l0) ->
  ~ (PL ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g M) : proc))).
Proof.
  intros l M w l0 HM Hperm Hpre.
  destruct (cfg_out_of_perm l l0 (cst mb) w ((g M) : proc) Hperm) as (r & Hout & _).
  assert (Hnw : NoWeakOut (cst mb) (msgs l ‖ ((g M) : proc))).
  { eapply below_preserves_no_weak_out; try eassumption.
    - apply PL_static.
    - constructor; [ apply msgs_Static | apply static_g; exact HM ].
    - apply PL_no_weak_out. }
  eapply (Hnw (msgs l ‖ ((g M) : proc))); [ | exact Hout ].
  apply wt_nil.
Qed.
End VACCS_MuteLimit.

(* ===================================================================== *)
(** * [Bad] IS NOT CLOSED UNDER PARALLEL COMPOSITION

    [VACCS_Absorb.Harmless] has a compositional clause for [‖]
    ([hm_par]); [VACCS_Absorb.Bad] has none, and the plan notes recorded
    that gap as "probably provable, never attempted".  It is **not**
    provable: this section refutes it.

    The mechanism is the output clause of [bad_stuck].  It constrains
    only the **channel** of an emission, never the state left behind —
    [Harmless] does have that preservation lemma ([hm_out_step]), [Bad]
    cannot.  So a process may be [Bad] while its output residue is not,
    and a partner that **consumes** that emission forces the pair through
    exactly that residue.

    Four distinct channels; [BPsum] is the summand that escapes on [pf]:

        BPsum := (pc ? 𝟘) + (pe ? (pf!pw•𝟘))
        BPp   := (pc!pv•𝟘) ‖ (pd ? BPsum)          BPq := pc ? 𝟘
        S     := {pc}

    [BPp] is [Bad S] — it is τ-stable, its only output is on [pc ∈ S],
    and its only input (on [pd]) leads to [(pc!pv•𝟘) ‖ BPsum], which is
    [Bad] because the message and [BPsum]'s [pc]-branch **synchronise**
    into [𝟘 ‖ 𝟘].  [BPq] is [Bad S] trivially.

    But [BPp ‖ BPq] has exactly **one** τ — the message goes to [BPq]
    instead — and after it the [pc]-branch of [BPsum] is no longer fed,
    so the only way on is [pd] then [pe], which emits on [pf ∉ S].

    Note this is not merely an incompleteness of [Bad]: the pair really
    does pass the τ-stuck, non-good, [S]-refusing client
    [(pd!·•𝟘) ‖ (pe!·•𝟘) ‖ (pf ? ①)], so it is not semantically bad
    either.  (That direction is not formalised here — [Bad_sound] makes
    it redundant for the point being made.) *)

Section VACCS_BadPar.

Context `{VP : VACCS_Parameters}.
Context {pc pd pe pf : Channel} {pv pw : Value}.
Context {pcd : pc <> pd} {pce : pc <> pe} {pcf : pc <> pf}
        {pde : pd <> pe} {pdf : pd <> pf} {pef : pe <> pf}.

Definition BPsum : gproc :=
  ((cst pc) ? ((g 𝟘) : proc)) + ((cst pe) ? ((cst pf) ! (cst pw) • 𝟘)).
Definition BPguard : proc := (g ((cst pd) ? ((g BPsum) : proc))) : proc.
Definition BPp : proc := ((cst pc) ! (cst pv) • 𝟘) ‖ BPguard.
Definition BPq : proc := (g ((cst pc) ? ((g 𝟘) : proc))) : proc.
Definition BPS : chset := fun x => x = cst pc.

Ltac blastBP :=
  unfold lts_step in *; simpl in *;
  repeat match goal with
  | H : lts (_ ‖ _) _ _ |- _ => inversion H; subst; clear H
  | H : lts (_ ! _ • 𝟘) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g (_ + _)) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g (_ ? _)) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g 𝟘) _ _ |- _ => inversion H
  | H : lts (g ①) _ _ |- _ => inversion H
  | H : cst _ = cst _ |- _ => inversion H; subst; clear H
  end; try congruence.

(** A τ-stable process emitting outside [S] is not [Bad S] — the only
    clause available is [bad_stuck], whose output field demands [S c]. *)
Lemma not_bad_out : forall (S : chset) p c v p',
  (forall z, ~ lts p τ z) ->
  lts p (ActExt (ActOut (c,v))) p' -> ~ S c -> ~ Bad S p.
Proof.
  intros S p c v p' Hnt Hout HS HB.
  destruct HB as [ S0 p0 p1 Hl _ | S0 p0 Hst Ho Hi ].
  - eapply Hnt; exact Hl.
  - apply HS. eapply Ho; exact Hout.
Qed.

(** ** The positive half *)

Lemma BPp_no_tau : forall z, ~ lts BPp τ z.
Proof. intros z Hz. unfold BPp, BPguard in Hz. blastBP. Qed.

Lemma bad_nilpar : forall (S : chset), Bad S (((g 𝟘) : proc) ‖ ((g 𝟘) : proc)).
Proof.
  intro S. apply bad_stuck;
    [ intros z Hz | intros d x z Hz | intros d x z Hz ]; blastBP.
Qed.

Lemma BPmid_bad : forall (S : chset),
  Bad S (((cst pc) ! (cst pv) • 𝟘) ‖ ((g BPsum) : proc)).
Proof.
  intro S. eapply bad_step.
  - eapply lts_comL; [ apply lts_output | apply lts_choiceL; apply lts_input ].
  - apply bad_nilpar.
Qed.

Lemma BPp_in_inv : forall d x z, lts BPp (ActExt (ActIn (d,x))) z ->
  d = cst pd /\ z = (((cst pc) ! (cst pv) • 𝟘) ‖ ((g BPsum) : proc)).
Proof.
  intros d x z Hz. unfold BPp, BPguard in Hz.
  inversion Hz; subst.
  - inversion H3.
  - inversion H3; subst. split; [ reflexivity | simpl; reflexivity ].
Qed.

Lemma BPp_bad : Bad BPS BPp.
Proof.
  apply bad_stuck.
  - apply BPp_no_tau.
  - intros d x z Hz. unfold BPp, BPguard in Hz. unfold BPS.
    inversion Hz; subst.
    + inversion H3; subst. reflexivity.
    + inversion H3.
  - intros d x z Hz.
    destruct (BPp_in_inv d x z Hz) as (Hd & _). subst d.
    exists (((cst pc) ! (cst pv) • 𝟘) ‖ ((g BPsum) : proc)). split.
    + unfold BPp, BPguard. apply lts_parR.
      assert (Hs : ((g BPsum) : proc) = subst_in_proc 0 x ((g BPsum) : proc))
        by (simpl; reflexivity).
      rewrite Hs at 2. apply lts_input.
    + apply BPmid_bad.
Qed.

Lemma BPq_bad : Bad BPS BPq.
Proof.
  apply bad_stuck.
  - intros z Hz. unfold BPq in Hz. inversion Hz.
  - intros d x z Hz. unfold BPq in Hz. inversion Hz.
  - intros d x z Hz. exists z. split; [ exact Hz | ].
    unfold BPq in Hz. inversion Hz; subst. apply bad_nil_any.
Qed.

(** ** The negative half

    Three nested states, each refuted by the one below it.  [BPz3] emits
    on [pf] and is τ-stable, so [not_bad_out] applies; [BPz2] must go
    through it on [pe]; [BPz1] must go through [BPz2] on [pd]. *)

Definition BPz3 : proc :=
  (((g 𝟘) : proc) ‖ ((cst pf) ! (cst pw) • 𝟘)) ‖ ((g 𝟘) : proc).
Definition BPz2 : proc :=
  (((g 𝟘) : proc) ‖ ((g BPsum) : proc)) ‖ ((g 𝟘) : proc).
Definition BPz1 : proc :=
  (((g 𝟘) : proc) ‖ ((g ((cst pd) ? ((g BPsum) : proc))) : proc)) ‖ ((g 𝟘) : proc).

Lemma BPz3_not_bad : forall (S : chset), ~ S (cst pf) -> ~ Bad S BPz3.
Proof.
  intros S HS. eapply (not_bad_out S BPz3 (cst pf) (cst pw)).
  - intros z Hz. unfold BPz3 in Hz. blastBP.
  - unfold BPz3. eapply lts_parL. eapply lts_parR. apply lts_output.
  - exact HS.
Qed.

Lemma BPz2_in_inv : forall d x z, lts BPz2 (ActExt (ActIn (d,x))) z ->
  (d = cst pc /\ z = (((g 𝟘) : proc) ‖ ((g 𝟘) : proc)) ‖ ((g 𝟘) : proc))
  \/ (d = cst pe /\ z = BPz3).
Proof.
  intros d x z Hz. unfold BPz2 in Hz.
  inversion Hz; subst.
  - inversion H3; subst.
    + inversion H4.
    + inversion H4; subst.
      * inversion H5; subst. left. split; [ reflexivity | simpl; reflexivity ].
      * inversion H5; subst. right. split; [ reflexivity | unfold BPz3; simpl; reflexivity ].
  - inversion H3.
Qed.

Lemma BPz2_no_tau : forall z, ~ lts BPz2 τ z.
Proof. intros z Hz. unfold BPz2 in Hz. blastBP. unfold BPsum in *. blastBP. Qed.

Lemma BPz2_in_pe : lts BPz2 (ActExt (ActIn (cst pe, cst pw))) BPz3.
Proof.
  unfold BPz2. apply lts_parL. apply lts_parR.
  unfold BPsum. apply lts_choiceR.
  assert (Hs : ((cst pf) ! (cst pw) • 𝟘) = subst_in_proc 0 (cst pw) ((cst pf) ! (cst pw) • 𝟘))
    by (simpl; reflexivity).
  unfold BPz3. rewrite Hs at 2. apply lts_input.
Qed.

Lemma BPz2_not_bad : forall (S : chset), ~ S (cst pf) -> ~ Bad S BPz2.
Proof.
  intros S HS HB.
  inversion HB as [ S0 p0 p1 Hl _ Heq1 Heq2 | S0 p0 Hst Ho Hi Heq1 Heq2 ]; subst.
  - eapply BPz2_no_tau; exact Hl.
  - destruct (Hi (cst pe) (cst pw) BPz3 BPz2_in_pe) as (z & Hlz & Hbz).
    destruct (BPz2_in_inv _ _ _ Hlz) as [ (Hd & _) | (_ & Hz) ].
    + inversion Hd; subst. congruence.
    + subst z. eapply BPz3_not_bad; [ | exact Hbz ].
      intros [ HSf | Hf ]; [ exact (HS HSf) | inversion Hf; subst; congruence ].
Qed.

Lemma BPz1_no_tau : forall z, ~ lts BPz1 τ z.
Proof. intros z Hz. unfold BPz1 in Hz. blastBP. Qed.

Lemma BPz1_in_pd : lts BPz1 (ActExt (ActIn (cst pd, cst pw))) BPz2.
Proof.
  unfold BPz1. apply lts_parL. apply lts_parR.
  assert (Hs : ((g BPsum) : proc) = subst_in_proc 0 (cst pw) ((g BPsum) : proc))
    by (simpl; reflexivity).
  unfold BPz2. rewrite Hs at 2. apply lts_input.
Qed.

Lemma BPz1_in_inv : forall d x z, lts BPz1 (ActExt (ActIn (d,x))) z ->
  d = cst pd /\ z = BPz2.
Proof.
  intros d x z Hz. unfold BPz1 in Hz.
  inversion Hz; subst.
  - inversion H3; subst.
    + inversion H4.
    + inversion H4; subst. split; [ reflexivity | unfold BPz2; simpl; reflexivity ].
  - inversion H3.
Qed.

Lemma BPz1_not_bad : forall (S : chset), ~ S (cst pf) -> ~ Bad S BPz1.
Proof.
  intros S HS HB.
  inversion HB as [ S0 p0 p1 Hl _ Heq1 Heq2 | S0 p0 Hst Ho Hi Heq1 Heq2 ]; subst.
  - eapply BPz1_no_tau; exact Hl.
  - destruct (Hi (cst pd) (cst pw) BPz2 BPz1_in_pd) as (z & Hlz & Hbz).
    destruct (BPz1_in_inv _ _ _ Hlz) as (_ & Hz). subst z.
    eapply BPz2_not_bad; [ | exact Hbz ].
    intros [ HSf | Hf ]; [ exact (HS HSf) | inversion Hf; subst; congruence ].
Qed.

Lemma BPpq_tau : lts (BPp ‖ BPq) τ BPz1.
Proof.
  unfold BPz1.
  eapply lts_comL.
  - unfold BPp, BPguard. apply lts_parL. apply lts_output.
  - unfold BPq.
    assert (Hs : ((g 𝟘) : proc) = subst_in_proc 0 (cst pv) ((g 𝟘) : proc))
      by (simpl; reflexivity).
    rewrite Hs at 2. apply lts_input.
Qed.

Lemma BPpq_tau_inv : forall z, lts (BPp ‖ BPq) τ z -> z = BPz1.
Proof.
  intros z Hz. inversion Hz; subst;
    try (exfalso; eapply BPp_no_tau; eassumption);
    try (match goal with H : lts BPq τ _ |- _ => unfold BPq in H; inversion H end);
    try (match goal with H : lts BPq (ActExt (ActOut _)) _ |- _ =>
           unfold BPq in H; inversion H end).
  match goal with H : lts BPp (ActExt (ActOut _)) _ |- _ =>
    unfold BPp, BPguard in H; inversion H; subst end.
  - match goal with H : lts (_ ! _ • 𝟘) _ _ |- _ => inversion H; subst end.
    match goal with H : lts BPq _ _ |- _ => unfold BPq in H; inversion H; subst end.
    unfold BPz1, BPguard. simpl. reflexivity.
  - match goal with H : lts (g (_ ? _)) (ActExt (ActOut _)) _ |- _ => inversion H end.
Qed.

(** ** [Bad] is not closed under [‖]

    Both operands are [Bad] at [S = {pc}], the composition is not. *)
Theorem bad_not_closed_under_par :
  Bad BPS BPp /\ Bad BPS BPq /\ ~ Bad BPS (BPp ‖ BPq).
Proof.
  split; [ apply BPp_bad | ]. split; [ apply BPq_bad | ].
  intro HB.
  inversion HB as [ S0 p0 p1 Hl Hb1 Heq1 Heq2 | S0 p0 Hst Ho Hi Heq1 Heq2 ]; subst.
  - assert (Hp1 : p1 = BPz1) by (apply BPpq_tau_inv; exact Hl). subst p1.
    eapply BPz1_not_bad; [ | exact Hb1 ].
    unfold BPS. intro Hf. inversion Hf; subst. congruence.
  - eapply Hst. apply BPpq_tau.
Qed.

(** ** …and the mechanism, isolated

    [Harmless] has [hm_out_step] — the residue of an emission on a
    channel of [S] stays harmless.  [Bad] cannot: here the same [BPp]
    is [Bad], emits on [pc ∈ S], and its residue is not.

    This is what the parallel case of any compositional proof would have
    needed, and it is why [hm_par] has no [Bad] analogue. *)

Definition BPres : proc :=
  ((g 𝟘) : proc) ‖ ((g ((cst pd) ? ((g BPsum) : proc))) : proc).
Definition BPres3 : proc := ((g 𝟘) : proc) ‖ ((cst pf) ! (cst pw) • 𝟘).
Definition BPsum0 : proc := ((g 𝟘) : proc) ‖ ((g BPsum) : proc).

Lemma BPres_no_tau : forall z, ~ lts BPres τ z.
Proof. intros z Hz. unfold BPres in Hz. blastBP. Qed.

Lemma BPres_in_pd : lts BPres (ActExt (ActIn (cst pd, cst pw))) BPsum0.
Proof.
  unfold BPres. apply lts_parR.
  assert (Hs : ((g BPsum) : proc) = subst_in_proc 0 (cst pw) ((g BPsum) : proc))
    by (simpl; reflexivity).
  unfold BPsum0. rewrite Hs at 2. apply lts_input.
Qed.

Lemma BPres_in_inv : forall d x z, lts BPres (ActExt (ActIn (d,x))) z ->
  d = cst pd /\ z = BPsum0.
Proof.
  intros d x z Hz. unfold BPres in Hz.
  inversion Hz; subst.
  - inversion H3.
  - inversion H3; subst. split; [ reflexivity | unfold BPsum0; simpl; reflexivity ].
Qed.

Lemma BPres3_not_bad : forall (S : chset), ~ S (cst pf) -> ~ Bad S BPres3.
Proof.
  intros S HS. eapply (not_bad_out S BPres3 (cst pf) (cst pw)).
  - intros z Hz. unfold BPres3 in Hz. blastBP.
  - unfold BPres3. eapply lts_parR. apply lts_output.
  - exact HS.
Qed.

Lemma BPsum0_no_tau : forall z, ~ lts BPsum0 τ z.
Proof. intros z Hz. unfold BPsum0 in Hz. blastBP. unfold BPsum in *. blastBP. Qed.

Lemma BPsum0_in_pe : lts BPsum0 (ActExt (ActIn (cst pe, cst pw))) BPres3.
Proof.
  unfold BPsum0. apply lts_parR. unfold BPsum. apply lts_choiceR.
  assert (Hs : ((cst pf) ! (cst pw) • 𝟘) = subst_in_proc 0 (cst pw) ((cst pf) ! (cst pw) • 𝟘))
    by (simpl; reflexivity).
  unfold BPres3. rewrite Hs at 2. apply lts_input.
Qed.

Lemma BPsum0_in_inv : forall d x z, lts BPsum0 (ActExt (ActIn (d,x))) z ->
  (d = cst pc /\ z = ((g 𝟘) : proc) ‖ ((g 𝟘) : proc)) \/ (d = cst pe /\ z = BPres3).
Proof.
  intros d x z Hz. unfold BPsum0 in Hz.
  inversion Hz; subst.
  - inversion H3.
  - inversion H3; subst.
    + inversion H4; subst. left. split; [ reflexivity | simpl; reflexivity ].
    + inversion H4; subst. right. split; [ reflexivity | unfold BPres3; simpl; reflexivity ].
Qed.

Lemma BPsum0_not_bad : forall (S : chset), ~ S (cst pf) -> ~ Bad S BPsum0.
Proof.
  intros S HS HB.
  inversion HB as [ S0 p0 p1 Hl _ Heq1 Heq2 | S0 p0 Hst Ho Hi Heq1 Heq2 ]; subst.
  - eapply BPsum0_no_tau; exact Hl.
  - destruct (Hi (cst pe) (cst pw) BPres3 BPsum0_in_pe) as (z & Hlz & Hbz).
    destruct (BPsum0_in_inv _ _ _ Hlz) as [ (Hd & _) | (_ & Hz) ].
    + inversion Hd; subst. congruence.
    + subst z. eapply BPres3_not_bad; [ | exact Hbz ].
      intros [ HSf | Hf ]; [ exact (HS HSf) | inversion Hf; subst; congruence ].
Qed.

Lemma BPres_not_bad : forall (S : chset), ~ S (cst pf) -> ~ Bad S BPres.
Proof.
  intros S HS HB.
  inversion HB as [ S0 p0 p1 Hl _ Heq1 Heq2 | S0 p0 Hst Ho Hi Heq1 Heq2 ]; subst.
  - eapply BPres_no_tau; exact Hl.
  - destruct (Hi (cst pd) (cst pw) BPsum0 BPres_in_pd) as (z & Hlz & Hbz).
    destruct (BPres_in_inv _ _ _ Hlz) as (_ & Hz). subst z.
    eapply BPsum0_not_bad; [ | exact Hbz ].
    intros [ HSf | Hf ]; [ exact (HS HSf) | inversion Hf; subst; congruence ].
Qed.

Theorem bad_not_preserved_by_output :
  Bad BPS BPp
  /\ lts BPp (ActExt (ActOut (cst pc, cst pv))) BPres
  /\ BPS (cst pc)
  /\ ~ Bad BPS BPres.
Proof.
  split; [ apply BPp_bad | ]. split.
  - unfold BPp, BPguard, BPres. apply lts_parL. apply lts_output.
  - split; [ reflexivity | ].
    apply BPres_not_bad. unfold BPS. intro Hf. inversion Hf; subst. congruence.
Qed.

End VACCS_BadPar.

(* ===================================================================== *)
(** * A TRAPPED MESSAGE IS NOT DELETABLE

    [VACCS_Matching.completeness_of_trapped_NF_step] keeps a restriction
    block exactly when its bag holds a message **trapped** on the
    just-restricted channel — one that [VACCS_Matching.untrappedB] rejects.
    The plan recorded, as hand analysis only, that such a message cannot
    simply be deleted.  This section machine-checks it.

    A trapped message can neither escape ([VarC_action_add 1] never
    produces [bvar 0], so [lts_res_ext] cannot expose it) nor be supplied
    from outside.  What it *can* do is be **delivered**, and in a guarded
    sum a delivery **commits** — it discards every sibling guard.  That is
    the whole content: the trapped message pre-empts.

        TrM  := (bvar 0 ? 𝟘) + (cst ta ? (cst te ! cst ty • 𝟘))
        TrS1 := ν ((bvar 0 ! tv • 𝟘) ‖ g TrM)        (* with the message *)
        TrS2 := ν (g TrM)                            (* without it *)
        TrT  := (cst ta ! tw • 𝟘) ‖ (cst te ? ①)

    [TrS2] is τ-stable and offers [ta]; it answers [TrT] on [te] and the
    client becomes good.  [TrS1] has a τ — the delivery — after which the
    [ta]-guard is gone and nothing at all is left, so [must]'s [pt] field
    fails against a τ-stuck non-good client.

    Note this is *not* an instance of message rigidity
    ([nil_not_below_msg_gen]): that argument needs the message to be
    emittable, and a trapped one is not.  The observation is pre-emption,
    the same mechanism as [VACCS_ChoiceProbes.v]'s unsoundness of
    sum-congruence, seen under a restriction. *)

Section VACCS_TrapProbe.

Context `{VP : VACCS_Parameters}.
Context {ta te : Channel} {tv tw ty : Value}.
Context {tae : ta <> te}.

Definition TrM : gproc :=
  ((bvar 0) ? ((g 𝟘) : proc)) + ((cst ta) ? (((cst te) ! (cst ty) • 𝟘) : proc)).
Definition TrS1 : proc := ν ((((bvar 0) ! (cst tv) • 𝟘) : proc) ‖ ((g TrM) : proc)).
Definition TrS2 : proc := ν ((g TrM) : proc).
Definition TrT : proc :=
  (((cst ta) ! (cst tw) • 𝟘) : proc) ‖ ((g ((cst te) ? ((g ①) : proc))) : proc).
Definition TrIn : proc := ν (((cst te) ! (cst ty) • 𝟘) : proc).
Definition TrT2 : proc :=
  ((g 𝟘) : proc) ‖ ((g ((cst te) ? ((g ①) : proc))) : proc).

(** A server with no transitions at all fails every τ-stuck non-good
    client: [must]'s [ex] field has nothing to fire on. *)
Lemma inert_fails_stuck : forall p u,
  (forall a z, ~ lts p a z) ->
  (forall z, ~ lts u τ z) -> ~ good_VACCS u -> ~ (p must_pass u).
Proof.
  intros p u Hp Hu Hng Hm. inversion Hm; subst.
  - contradiction.
  - match goal with Hex : exists _, _ |- _ => destruct Hex as (x & Hx) end.
    inversion Hx; subst; unfold lts_step in *; simpl in *.
    + eapply Hp; eassumption.
    + eapply Hu; eassumption.
    + eapply Hp; eassumption.
Qed.

Lemma varc_add_cst_inv : forall n (c : ChannelData) (a : Channel),
  VarC_add n c = cst a -> c = cst a.
Proof. intros n c a H. destruct c; simpl in H; [ exact H | discriminate ]. Qed.

Lemma TrT_not_good : ~ good_VACCS TrT.
Proof.
  intro Hg. unfold TrT in Hg. inversion Hg; subst.
  match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
Qed.

Lemma TrT_no_tau : forall z, ~ lts TrT τ z.
Proof.
  intros z Hz. unfold TrT in Hz. inversion Hz; subst.
  - inversion H1; subst. inversion H2; subst. congruence.
  - inversion H2.
  - inversion H3.
  - inversion H3.
Qed.

(** ** The side with the trapped message: it pre-empts *)

Lemma TrS1_tau : lts TrS1 τ (ν (((g 𝟘) : proc) ‖ ((g 𝟘) : proc))).
Proof.
  unfold TrS1. apply lts_res_tau.
  eapply lts_comL; [ apply lts_output | ].
  unfold TrM. apply lts_choiceL.
  assert (Hs : ((g 𝟘) : proc) = subst_in_proc 0 (cst tv) ((g 𝟘) : proc))
    by (simpl; reflexivity).
  rewrite Hs at 2. apply lts_input.
Qed.

Lemma res_nilnil_inert : forall a z, ~ lts (ν (((g 𝟘) : proc) ‖ ((g 𝟘) : proc))) a z.
Proof.
  intros a z Hz. inversion Hz; subst.
  - inversion H0; subst; match goal with H : lts (g 𝟘) _ _ |- _ => inversion H end.
  - inversion H0; subst; match goal with H : lts (g 𝟘) _ _ |- _ => inversion H end.
Qed.

Lemma TrS1_fails : ~ (TrS1 must_pass TrT).
Proof.
  intro Hm. inversion Hm; subst.
  - eapply TrT_not_good; eassumption.
  - specialize (pt _ TrS1_tau).
    eapply inert_fails_stuck;
      [ apply res_nilnil_inert | apply TrT_no_tau | apply TrT_not_good | exact pt ].
Qed.

(** ** The side without it: it answers *)

Lemma TrIn_ext_inv : forall mu z, lts TrIn (ActExt mu) z ->
  mu = ActOut (cst te, cst ty) /\ z = ν ((g 𝟘) : proc).
Proof.
  intros mu z Hz. unfold TrIn in Hz. inversion Hz; subst.
  inversion H1; subst.
  destruct mu as [ [c1 v1] | [c1 v1] ]; simpl in *; try discriminate.
  match goal with H : ActOut _ = ActOut _ |- _ => inversion H; subst end.
  split; [ | reflexivity ].
  f_equal. f_equal. eapply varc_add_cst_inv. symmetry. exact H2.
Qed.

Lemma TrIn_no_tau : forall z, ~ lts TrIn τ z.
Proof. intros z Hz. unfold TrIn in Hz. inversion Hz; subst. inversion H0. Qed.

Lemma TrT2_not_good : ~ good_VACCS TrT2.
Proof.
  intro Hg. unfold TrT2 in Hg. inversion Hg; subst.
  match goal with H : _ \/ _ |- _ => destruct H as [H|H]; inversion H end.
Qed.

Lemma TrT2_no_tau : forall z, ~ lts TrT2 τ z.
Proof.
  intros z Hz. unfold TrT2 in Hz. inversion Hz; subst.
  - inversion H1.
  - inversion H1.
  - inversion H3.
  - inversion H3.
Qed.

Lemma TrIn_out : lts TrIn (ActExt (ActOut (cst te, cst ty))) (ν ((g 𝟘) : proc)).
Proof. unfold TrIn. apply lts_res_ext. simpl. apply lts_output. Qed.

Lemma TrT2_in : lts TrT2 (ActExt (ActIn (cst te, cst ty)))
                     (((g 𝟘) : proc) ‖ ((g ①) : proc)).
Proof.
  unfold TrT2. apply lts_parR.
  assert (Hs : ((g ①) : proc) = subst_in_proc 0 (cst ty) ((g ①) : proc))
    by (simpl; reflexivity).
  rewrite Hs at 2. apply lts_input.
Qed.

Lemma TrIn_passes : TrIn must_pass TrT2.
Proof.
  apply m_step.
  - apply TrT2_not_good.
  - exists ((ν ((g 𝟘) : proc)) ▷ (((g 𝟘) : proc) ‖ ((g ①) : proc))).
    eapply (ParSync (ActOut (cst te, cst ty)) (ActIn (cst te, cst ty))).
    + simpl. reflexivity.
    + apply TrIn_out.
    + apply TrT2_in.
  - intros p' Hp'. exfalso. eapply TrIn_no_tau; eassumption.
  - intros t' Ht'. exfalso. eapply TrT2_no_tau; eassumption.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    destruct (TrIn_ext_inv _ _ Hp') as (Hmu & Hz). subst mu1.
    destruct mu2 as [ [c2 v2] | [c2 v2] ]; simpl in Hd; try contradiction.
    inversion Hd; subst.
    unfold TrT2 in Ht'. inversion Ht'; subst.
    + inversion H3.
    + inversion H3; subst. apply m_now. simpl. constructor. right. constructor.
Qed.

Lemma TrS2_no_tau : forall z, ~ lts TrS2 τ z.
Proof.
  intros z Hz. unfold TrS2 in Hz. inversion Hz; subst.
  unfold TrM in H0.
  inversion H0; subst; match goal with H : lts (g (_ ? _)) _ _ |- _ => inversion H end.
Qed.

Lemma TrS2_in : forall w, lts TrS2 (ActExt (ActIn (cst ta, w))) TrIn.
Proof.
  intro w. unfold TrS2. apply lts_res_ext. simpl.
  unfold TrM. apply lts_choiceR.
  assert (Hs : (((cst te) ! (cst ty) • 𝟘) : proc)
             = subst_in_proc 0 w (((cst te) ! (cst ty) • 𝟘) : proc))
    by (simpl; reflexivity).
  unfold TrIn. rewrite Hs at 2. apply lts_input.
Qed.

(** The [bvar 0] guard is invisible from outside — that is exactly what
    makes the message trapped, and it is why the only surviving offer is
    the one on the constant channel [ta]. *)
Lemma TrS2_ext_inv : forall mu z, lts TrS2 (ActExt mu) z ->
  (exists w, mu = ActIn (cst ta, w)) /\ z = TrIn.
Proof.
  intros mu z Hz. unfold TrS2 in Hz. inversion Hz; subst.
  unfold TrM in H1. inversion H1; subst.
  - inversion H4; subst.
    destruct mu as [ [c1 v1] | [c1 v1] ]; simpl in *; try discriminate.
    match goal with H : ActIn _ = ActIn _ |- _ => inversion H; subst end.
    destruct c1; simpl in *; discriminate.
  - inversion H4; subst.
    destruct mu as [ [c1 v1] | [c1 v1] ]; simpl in *; try discriminate.
    match goal with H : ActIn _ = ActIn _ |- _ => inversion H; subst end.
    assert (Hc : c1 = cst ta) by (eapply varc_add_cst_inv; symmetry; eassumption).
    subst c1. split; [ exists v1; reflexivity | unfold TrIn; simpl; reflexivity ].
Qed.

Lemma TrT_out : lts TrT (ActExt (ActOut (cst ta, cst tw))) TrT2.
Proof. unfold TrT, TrT2. apply lts_parL. apply lts_output. Qed.

Lemma TrT_out_inv : forall c v t', lts TrT (ActExt (ActOut (c,v))) t' ->
  c = cst ta /\ v = cst tw /\ t' = TrT2.
Proof.
  intros c v t' Ht. unfold TrT in Ht. inversion Ht; subst.
  - inversion H3; subst. unfold TrT2. auto.
  - inversion H3.
Qed.

Lemma TrS2_passes : TrS2 must_pass TrT.
Proof.
  apply m_step.
  - apply TrT_not_good.
  - exists (TrIn ▷ TrT2).
    eapply (ParSync (ActIn (cst ta, cst tw)) (ActOut (cst ta, cst tw))).
    + simpl. reflexivity.
    + apply TrS2_in.
    + apply TrT_out.
  - intros p' Hp'. exfalso. eapply TrS2_no_tau; eassumption.
  - intros t' Ht'. exfalso. eapply TrT_no_tau; eassumption.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    destruct (TrS2_ext_inv _ _ Hp') as ((w & Hmu) & Hz). subst mu1 p'.
    destruct mu2 as [ [c2 v2] | [c2 v2] ]; simpl in Hd; try contradiction.
    inversion Hd; subst.
    destruct (TrT_out_inv _ _ _ Ht') as (_ & _ & Ht2). subst t'.
    apply TrIn_passes.
Qed.

(** Deleting the trapped message is unsound: the two are not
    must-equivalent, so no [⊢]-step may perform the deletion. *)
Theorem trapped_message_is_not_deletable :
  TrS2 must_pass TrT
  /\ ~ (TrS1 must_pass TrT)
  /\ ~ (TrS2 ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ TrS1).
Proof.
  split; [ apply TrS2_passes | ]. split; [ apply TrS1_fails | ].
  intro Hle. eapply TrS1_fails. apply Hle. apply TrS2_passes.
Qed.

End VACCS_TrapProbe.

(* ===================================================================== *)
(** * `drain_forced_no_regen` CANNOT DROP ITS STABILITY HYPOTHESIS

    [VACCS_NormalForm.drain_forced_no_regen] concludes that a drain run
    leaves the process exactly where it was, from two hypotheses: [g M]
    is τ-stable, and no run of [g M] returns everything it took.  The
    plan flagged the stability as possibly removable, and kept
    [VACCS_Matching.no_regen_of_disjoint] on the grounds that it "would
    become useful again if [drain_forced_no_regen] were generalised".

    **It cannot be generalised**, and the counterexample is two symbols:

        DM := 𝛕 • (dc ! dv • 𝟘)        Dl := [(dc, dv)]

    The non-regeneration hypothesis holds *vacuously* — [DM] has no input
    anywhere, so [ichans (g DM) = []] and [no_regen_of_disjoint] applies.
    But [g DM ▷ bag Dl] has **two** runs over the drain trace [[dc!]]:
    emit the buffered message (reaching [g DM ▷ ∅], the intended one), or
    take the τ and emit the process's *own* message — reaching
    [𝟘 ▷ bag Dl], whose buffer is still full.

    So a τ lets the process supply the output the trace asks for, and the
    balance equation of [fw_conservation] no longer pins the buffer down.
    The two sufficient conditions on record — τ-stability plus
    non-regeneration ([drain_forced_no_regen]) and "never emits at all"
    ([VACCS_Matching.drain_forced_no_output], which does tolerate
    [𝛕]-summands) — are therefore genuinely incomparable, and neither
    subsumes the other.

    Consequence: [no_regen_of_disjoint]'s stated reason for being kept is
    void.  It remains correct, but it will not be revived this way. *)

Section VACCS_DrainProbe.

Context `{VP : VACCS_Parameters}.
Context {dc : Channel} {dv : Value}.

Definition DM : gproc := 𝛕 • (((cst dc) ! (cst dv) • 𝟘) : proc).
Definition Dl : list TypeOfActions := [(cst dc ▷ cst dv)].

Lemma DM_static : Static ((g DM) : proc).
Proof. apply static_g. unfold DM. repeat constructor. Qed.

Lemma DM_no_regen : forall r q, ((g DM) : proc) ⟹[r] q ->
  bag (ins r) ⊆ bag (outs r) -> ins r = [].
Proof.
  apply no_regen_of_disjoint; [ apply DM_static | ].
  intros c Hin. simpl in Hin. contradiction.
Qed.

(** The τ lets the *process* produce the output the drain trace asks
    for, so the buffer is untouched. *)
Lemma DM_run : ((g DM) : proc) ⟹[[ActOut (cst dc ▷ cst dv)]] ((g 𝟘) : proc).
Proof.
  eapply wt_tau; [ unfold DM; apply lts_tau | ].
  eapply wt_act; [ apply lts_output | ]. apply wt_nil.
Qed.

Theorem drain_forced_needs_stability :
  (forall r q, ((g DM) : proc) ⟹[r] q -> bag (ins r) ⊆ bag (outs r) -> ins r = [])
  /\ (((g DM) : proc) ▷ bag Dl) ⟹[map ActOut Dl] (((g 𝟘) : proc) ▷ bag Dl)
  /\ (((g 𝟘) : proc) ▷ bag Dl)
       <> (((g DM) : proc) ▷ (∅ : MO (ExtAct TypeOfActions))).
Proof.
  split; [ apply DM_no_regen | ]. split.
  - simpl. apply fw_wt_lift. apply DM_run.
  - intro He. inversion He.
Qed.

End VACCS_DrainProbe.

(* ===================================================================== *)
(** * `lts` IS NOT STABLE UNDER SUBSTITUTION

    Eliminating a restriction in general ([VACCS_EquivalenceAx.ResFree]
    for an arbitrary [ν p]) runs through [VACCS_ResNormalize.resg], which
    does not remove the [ν] but pushes it into each guard's continuation.
    Removing it there means rewriting **under an input guard**, i.e.
    feeding the omega rule [ax_input], which consumes a *single open*
    continuation: from [⊢ ν P ≂ P'] between two open terms one would need
    [∀ v, ⊢ (ν P)^v ≂ P'^v].

    So the route wants a **substitution lemma for [ax_pre]**, proved by
    induction on the derivation.  That proof cannot work: its
    [ax_tau_step] case needs [lts] to be stable under substitution, and
    it is not — a conditional decides its branch by [Eval_Eq 0], which
    substitution can flip.

        SP := If (bvar 0 == cst sv) Then (𝛕 • 𝟘) Else (𝛕 • ①)

    Open, the guard evaluates to [Some false] (a [bvar] and a [cst] are
    syntactically distinct), so [SP ⟶τ ①].  Substituting [cst sv] makes
    it [Some true], and the only τ then lands on [𝟘].

    **Honest scope.**  This refutes the *naive proof*, not the lemma:
    whether [ax_pre] happens to be closed under substitution is left
    open, and on this very instance it is (both [SP^v ≡* 𝛕•𝟘] and [①]
    reduce to [𝟘] through [ax_tau_step] and [ax_success_r]).  What is
    settled is that no induction on the derivation can establish it while
    [ax_tau_step] is a rule.

    This is the [lts]-level counterpart of
    [VACCS_NormalForm.if_open_branch_depends_on_value], which makes the
    same point about *normalisation*; together they are why an "open
    normal form" and a "uniform family of [⊢]-equalities" are both out of
    reach, and hence why [VACCS_EquivalenceAx.must_iff_ax_pre_gen] still
    carries [ResFree] on the right. *)

Section VACCS_SubstProbe.

Context `{VP : VACCS_Parameters}.
Context {sv : Value}.

Definition SE : Equation ValueData := (bvar 0) == (cst sv).
Definition SP : proc := If SE Then ((g (𝛕 • ((g 𝟘) : proc))) : proc)
                              Else ((g (𝛕 • ((g ①) : proc))) : proc).

Lemma SP_tau : lts SP τ ((g ①) : proc).
Proof. unfold SP. eapply lts_ifZero; [ simpl; reflexivity | apply lts_tau ]. Qed.

Lemma SP_subst_tau_inv : forall z,
  lts (subst_in_proc 0 (cst sv) SP) τ z -> z = ((g 𝟘) : proc).
Proof.
  intros z Hz. simpl in Hz. inversion Hz; subst.
  - inversion H5; subst. reflexivity.
  - simpl in H4. destruct (decide (sv = sv)); [ discriminate | congruence ].
Qed.

Theorem lts_not_substitutive :
  lts SP τ ((g ①) : proc)
  /\ ~ lts (subst_in_proc 0 (cst sv) SP) τ
          (subst_in_proc 0 (cst sv) ((g ①) : proc)).
Proof.
  split; [ apply SP_tau | ].
  intro Hz. apply SP_subst_tau_inv in Hz. simpl in Hz. discriminate.
Qed.

(** Read at the rule: [ax_tau_step]'s premise does not survive the
    substitution its conclusion would have to survive. *)
Corollary ax_tau_step_not_substitutive :
  ax_pre SP ((g ①) : proc)
  /\ ~ lts (subst_in_proc 0 (cst sv) SP) τ
          (subst_in_proc 0 (cst sv) ((g ①) : proc)).
Proof.
  split; [ apply ax_tau_step; apply SP_tau | apply lts_not_substitutive ].
Qed.

End VACCS_SubstProbe.
