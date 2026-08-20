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

(** * The echo condition: what an extra input on the right must do

    The starting observation is that for two **stable guarded sums** the
    acceptance condition at [ε] is *vacuous*: a guarded sum can never emit
    ([gproc_no_output], [gproc_coR_empty]), so its abstracted ready set is
    empty and [must_i_cond2_nil] says nothing.  All the information about
    stable sums therefore passes through [must_i_feed] — put a message in
    parallel and read the condition at [ε] again.

    Doing exactly that yields the law that explains, structurally, why the
    copycat is invisible:

        must_i_must_echo :  if [M₁] does not listen on [(c,v)] and
          [g M₁ ⊑ₘᵤₛₜᵢ g M₂], then every stable state reachable from
          [(c ! v • 𝟘) ‖ g M₂] still emits on [c]

    and its immediate reading

        must_i_extra_input : if moreover [M₂] *does* listen on [(c,v)]
          with continuation [P], then every stable [τ]-reduct of [𝟘 ‖ P]
          emits on [c] — i.e. [M₂]'s extra input must give the message
          back.

    That is the copycat condition, obtained from the semantics rather than
    postulated.  It is the exact counterpart, on the right-hand side, of
    [VACCS_Absorb.v]'s law on the left: an input the other side does not
    have is admissible only if it re-emits ([ax_ccat]) or only if it
    swallows harmlessly ([ax_input_drop]).

    The three supporting facts are elementary but load-bearing: a stable
    process reaches only itself along the empty trace, and a message beside
    a sum that refuses the matching input is again stable — which is what
    pins the witness [must_i_cond2_nil] returns down to a *known* process
    instead of an anonymous reduct. *)

From Stdlib Require Import List Lia.
From Stdlib.Wellfounded Require Import Inverse_Image.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import base sets gmap gmultiset.
From TestingTheory Require Import MultisetLTSConstruction VACCS_Forwarder.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Precongruence VACCS_Residues VACCS_Expansion VACCS_ReadySet VACCS_Cond2
  VACCS_Copycat VACCS_Absorb VACCS_DefinitionAxiomatic VACCS_SoundnessAx VACCS_Canonical
  VACCS_ResNormalize VACCS_Shift VACCS_NormalForm Termination DefinitionCI
  SetLTSConstruction FiniteImageLTS Lts_Finite_Output_Chain.

Section VACCS_Matching.

Context `{VP : VACCS_Parameters}.

(** ** Pinning the witness down *)

(** A stable process reaches only itself along the empty trace. *)
Lemma wt_nil_stable : forall (p q : proc), p ↛ -> p ⟹[[]] q -> q = p.
Proof.
  intros p q Hst H. remember (@nil (ExtAct TypeOfActions)) as s eqn:Hs.
  induction H as [x|s x r y Hl Hw IH|mu s x r y Hl Hw IH]; subst.
  - reflexivity.
  - exfalso. eapply stable_no_lts; [ exact Hst | exact Hl ].
  - discriminate.
Qed.

(** A message beside a stable sum that refuses the matching input is
    stable: the only candidate [τ] would be the delivery, and it is ruled
    out by hypothesis. *)
Lemma msg_sum_stable : forall c v (M : gproc),
  (g M) ↛ -> (forall r, ~ lts (g M) (ActExt (ActIn (c,v))) r) ->
  ((c ! v • 𝟘) ‖ (g M)) ↛.
Proof.
  intros c v M Hst Hno. apply no_lts_stable. intros q Hq. inversion Hq; subst.
  - inversion H1; subst. eapply Hno. exact H2.
  - inversion H2.
  - inversion H3.
  - eapply stable_no_lts; [ exact Hst | eassumption ].
Qed.

(** ** The echo condition *)

Theorem must_i_must_echo : forall (M1 M2 : gproc) c v,
  Static (g M1) -> Static (g M2) ->
  (g M1) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g M2) ->
  (g M1) ↛ -> (forall r, ~ lts (g M1) (ActExt (ActIn (c,v))) r) ->
  forall q1, ((c ! v • 𝟘) ‖ (g M2)) ⟹[[]] q1 -> q1 ↛ ->
  exists w r, lts q1 (ActExt (ActOut (c,w))) r.
Proof.
  intros M1 M2 c v HS1 HS2 Hpre Hst Hno q1 Hw Hq1st.
  assert (Hfed : ((c ! v • 𝟘) ‖ (g M1)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((c ! v • 𝟘) ‖ (g M2)))
    by (apply must_i_feed; exact Hpre).
  assert (HSl : Static ((c ! v • 𝟘) ‖ (g M1))) by (constructor; [constructor | exact HS1]).
  assert (HSr : Static ((c ! v • 𝟘) ‖ (g M2))) by (constructor; [constructor | exact HS2]).
  destruct (must_i_cond2_nil _ _ HSl HSr Hfed q1 Hw Hq1st) as (p1 & Hwp & Hstp & Hincl).
  assert (Hlst : ((c ! v • 𝟘) ‖ (g M1)) ↛) by (apply msg_sum_stable; assumption).
  assert (p1 = (c ! v • 𝟘) ‖ (g M1)) as Heq by (eapply wt_nil_stable; eassumption).
  subst p1.
  apply Hincl. exists v, (g 𝟘 ‖ (g M1)).
  apply lts_parL. apply lts_output.
Qed.

(** The reading that matters: an input [M₂] has and [M₁] has not must
    hand the message back. *)
Corollary must_i_extra_input : forall (M1 M2 : gproc) c v P,
  Static (g M1) -> Static (g M2) ->
  (g M1) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g M2) ->
  (g M1) ↛ -> (forall r, ~ lts (g M1) (ActExt (ActIn (c,v))) r) ->
  lts (g M2) (ActExt (ActIn (c,v))) P ->
  forall r, ((g 𝟘) ‖ P) ⟹[[]] r -> r ↛ ->
  exists w s, lts r (ActExt (ActOut (c,w))) s.
Proof.
  intros M1 M2 c v P HS1 HS2 Hpre Hst Hno Hin r Hw Hrst.
  eapply (must_i_must_echo M1 M2 c v HS1 HS2 Hpre Hst Hno r); [ | exact Hrst ].
  eapply wt_tau; [ | exact Hw ].
  eapply lts_comL; [ apply lts_output | exact Hin ].
Qed.

(** * The recursive engine, and the mirror summand

    ** Semantics: descending into a matched guard costs nothing

    In VCCS, turning [p ⊑ₘᵤₛₜᵢ q] into a relation between the two sides
    *after* an action needed a whole trace-shift development
    ([bhv_pre_shift], [must_i_shift], [after], [after_below_reduct]).  Here
    it is ten lines, because **feeding an input is definable in the
    syntax**: [must_i_feed] puts the message in parallel, the right-hand
    side consumes it by an ordinary [τ], and a [τ] of the server is
    already a [⊑ₘᵤₛₜᵢ]-step ([must_preserved_by_lts_tau_srv]).

        must_i_feed_below :  p ⊑ₘᵤₛₜᵢ q -> q ⟶[(c,v)?] Q ->
                             ((c ! v • 𝟘) ‖ p) ⊑ₘᵤₛₜᵢ Q

    Note what the left-hand side is: not "p after the input" — no such
    process exists in general — but *p with the message still pending*.
    That is precisely the asynchronous reading, and it is what makes the
    statement both true and cheap.  The right-hand side [Q] is a reduct of
    [q], hence strictly smaller in [size] ([Static_lts_decrease]), so this
    is a well-founded recursion on the right alone.

    ** Syntax: the mirror summand is the copycat

    The left-hand side [(c!v•𝟘) ‖ p] has to be produced as an *input
    continuation*, i.e. as [Q'^v] for a single open [Q'].  There is exactly
    one candidate, and it is the copycat in parallel with [p]:

        fwdg c M := c ? ((gNewVar 0 M) ‖ (c ! bvar₀ • 𝟘))

    which is literally [ext_r (c ? (c ! bvar₀ • 𝟘)) M] — the summand the
    expansion law produces for [g M ‖ ccat c].  So the two halves fit
    without any glue:

    - [ax_fwd_intro] reaches it, by [ax_ccat_r] (add a copycat, which is
      invisible) followed by [ax_expansion_l] (flatten);
    - [ax_fwd_match] consumes it, by [ax_input] fed by the recursive call,
      the substitution being cancelled by [gproc_NewVar_cancel].

    That the *same* term is what the copycat law introduces and what the
    omega rule consumes is the payoff of reading the laws off the
    forwarder: the buffer's "absorb any input, store the dual" is, at
    process level, exactly the shape an input summand of the mirror must
    have. *)

(** [must_i_tau_below] now lives in [VACCS_Precongruence.v]: it is the
    soundness of the [ax_tau_step] rule, so it has to precede the axiom
    system rather than sit here. *)

Theorem must_i_feed_below : forall (p q : proc) c v Q,
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> lts q (ActExt (ActIn (c,v))) Q ->
  ((c ! v • 𝟘) ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ Q.
Proof.
  intros p q c v Q Hpre Hin t Hm.
  assert (Hfed : ((c ! v • 𝟘) ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((c ! v • 𝟘) ‖ q))
    by (apply must_i_feed; exact Hpre).
  assert (Hstep : lts ((c ! v • 𝟘) ‖ q) τ ((g 𝟘) ‖ Q))
    by (eapply lts_comL; [ apply lts_output | exact Hin ]).
  assert (Hm2 : ((g 𝟘) ‖ Q) must_pass t)
    by (eapply must_i_tau_below; [ exact Hstep | apply Hfed; exact Hm ]).
  assert (Hc : ((g 𝟘) ‖ Q) ≂ₘᵤₛₜᵢ Q).
  { apply must_i_cgr. etransitivity; [ apply cgr_par_com | apply cgr_par_nil ]. }
  destruct Hc as [Hc1 Hc2]. apply Hc2. exact Hm2.
Qed.

(** ** The mirror summand *)

(** Generalised from a guarded sum to an **arbitrary** left-hand process:
    [NewVar 0 (g M)] is [g (gNewVar 0 M)] by conversion, so
    [fwdg c M] for a [gproc] [M] still elaborates to the old definition
    through the [g] coercion, and every existing use keeps working. *)

Definition fwdg (c : ChannelData) (p : proc) : gproc :=
  c ? ((NewVar 0 p) ‖ (c ! (bvar 0) • 𝟘)).

(** Reaching it: add a copycat on [c] — invisible by [ax_ccat_r] — and
    flatten with the expansion law.  Besides the mirror summand the
    expansion leaves [M]'s own guards, each carrying the copycat along. *)
Lemma ax_fwd_intro : forall c M,
  ax_pre (g M) (g ((ext M (c ? (c ! (bvar 0) • 𝟘))) + fwdg c M)).
Proof.
  intros c M.
  replace (fwdg c M) with (ext_r (c ? (c ! (bvar 0) • 𝟘)) M) by reflexivity.
  eapply ax_trans; [ | apply ax_expansion_l ].
  eapply ax_trans; [ apply ax_cgr_sym; apply cgr_par_nil | ].
  apply ax_par; [ apply ax_refl | apply ax_ccat_r; reflexivity ].
Qed.

(** Consuming it: the omega rule, at the premise [must_i_feed_below]
    supplies once the recursion has turned it into a derivation. *)
Lemma ax_fwd_match : forall c M Q,
  (forall v, ax_pre ((g M) ‖ (c ! v • 𝟘)) (Q ^ v)) ->
  ax_pre (g (fwdg c M)) (g (c ? Q)).
Proof.
  intros c M Q H. unfold fwdg. apply ax_input. intro v.
  simpl. rewrite gproc_NewVar_cancel. apply H.
Qed.

(** ** The two halves meet: everything above [𝟘] is an echo

    The first complete instance of the matching argument, and the exact
    converse of [must_i_extra_input]: a single input summand is above [𝟘]
    as soon as its continuation gives the message back.  [ax_ccat_r] is the
    case [Q := c ! bvar₀ • 𝟘], where the premise is [ax_refl].

    Every step of the general argument is already visible here — reach the
    mirror by [ax_fwd_intro], discard what the expansion left over, consume
    the mirror by [ax_fwd_match] — the only reason it closes outright is
    that [ext 𝟘 N] is [𝟘], so there is nothing left over. *)

Theorem ax_nil_below_echo : forall c Q,
  (forall v, ax_pre (c ! v • 𝟘) (Q ^ v)) -> ax_pre (g 𝟘) (g (c ? Q)).
Proof.
  intros c Q H.
  eapply ax_trans; [ apply (ax_fwd_intro c 𝟘) | ].
  eapply ax_trans; [ apply ax_cgr; simpl; apply cgr_choice_com | ].
  eapply ax_trans; [ apply ax_cgr; apply cgr_choice_nil | ].
  apply ax_fwd_match. intro v.
  eapply ax_trans; [ | apply H ].
  apply ax_cgr. etransitivity; [ apply cgr_par_com | apply cgr_par_nil ].
Qed.

(** * The matching argument, on one channel

    Everything above assembles into a complete case of the completeness
    proof: a left-hand side whose summands are all inputs on a single
    channel `c`, against a right-hand side that is a single input guard on
    the same channel.  Modulo the recursive call, it closes:

        ax_below_input_sem :
          gInputsOn c M ->
          (∀ v, ((c!v•𝟘) ‖ g M) ⊑ₘᵤₛₜᵢ Q^v -> ⊢ (c!v•𝟘) ‖ g M ⊑ Q^v) ->
          g M ⊑ₘᵤₛₜᵢ g (c ? Q) -> ⊢ g M ⊑ g (c ? Q)

    The recursion is on the *right-hand side*: `Q^v` is a reduct of
    `g (c ? Q)`, hence strictly smaller in `size` by
    [Static_lts_decrease].

    The derivation is three moves.  [ax_fwd_intro] adds an invisible
    copycat on `c` and flattens, producing the mirror summand beside
    `M`'s own guards; [ax_ext_absorb] merges those guards into the mirror,
    one at a time; [ax_fwd_match] consumes the mirror with the omega rule.

    ** Why the merge needs a context, and where that context comes from

    Merging is the only step that is not local.  [ax_input_distrib_l]
    carries a residue precisely so that [ax_ext_absorb] can iterate, and
    the iteration still cannot rewrite *under* a `_ + R` — there is no
    congruence in the second argument of `+`, and there must not be
    ([VACCS_ChoiceProbes.v]).  The way round is to keep the mirror summand
    as the recursion's own subject: at each step the sum is permuted (by
    [ax_cgr] alone) so that the guard to be merged and the mirror sit
    adjacent and leftmost, then [ax_merge_into_fwd_ctx] fires.  The two
    induction hypotheses are used *in sequence*, with a permutation
    between them — which is why both must be quantified over the residue. *)

Lemma ax_merge_into_fwd : forall (c : ChannelData) (A : proc) (M : gproc) (Q : proc),
  (forall v, ax_pre ((g M) ‖ (c ! v • 𝟘)) (Q ^ v)) ->
  ax_pre (g ((c ? A) + (fwdg c M))) (g (c ? Q)).
Proof.
  intros c A M Q H.
  eapply ax_trans; [ apply ax_cgr_sym; apply cgr_choice_nil | ].
  eapply ax_trans;
    [ apply (ax_input_distrib_l c A ((g (gNewVar 0 M)) ‖ (c ! (bvar 0) • 𝟘)) 𝟘) | ].
  eapply ax_trans; [ apply ax_cgr; apply cgr_choice_nil | ].
  apply ax_input. intro v. simpl.
  eapply ax_trans; [ apply ax_int_r | ].
  rewrite gproc_NewVar_cancel. apply H.
Qed.

(** The same merge with a residue, and with no premise: an input guard on
    [c] beside the mirror is simply absorbed by it. *)
Lemma ax_merge_into_fwd_ctx :
  forall (c : ChannelData) (A : proc) (M R : gproc),
  ax_pre (g (((c ? A) + (fwdg c M)) + R)) (g ((fwdg c M) + R)).
Proof.
  intros c A M R.
  eapply ax_trans;
    [ apply (ax_input_distrib_l c A ((g (gNewVar 0 M)) ‖ (c ! (bvar 0) • 𝟘)) R) | ].
  apply ax_choice_input. intro v. simpl. apply ax_int_r.
Qed.

Lemma cgr_swap3 : forall (A F R : gproc), (g (A + (F + R))) ≡* (g (F + (A + R))).
Proof.
  intros A F R.
  etransitivity; [ apply cgr_symm; apply cgr_choice_assoc | ].
  etransitivity; [ apply cgr_choice; apply cgr_choice_com | ].
  apply cgr_choice_assoc.
Qed.

(** Every summand is an input guard on [c] (and [①]/[𝟘] carry no guard).
    A [𝛕]-summand is excluded: it would leave a mixed sum, which is its
    own thing ([ax_tau_sep_*]). *)
Fixpoint gInputsOn (c : ChannelData) (M : gproc) : Prop :=
  match M with
  | gpr_success => True
  | gpr_nil => True
  | gpr_input d _ => d = c
  | gpr_tau _ => False
  | gpr_choice M1 M2 => gInputsOn c M1 /\ gInputsOn c M2
  end.

Lemma ax_ext_absorb : forall (c : ChannelData) (M : gproc), gInputsOn c M ->
  forall (N M0 R : gproc),
  ax_pre (g ((ext M N) + ((fwdg c M0) + R))) (g ((fwdg c M0) + R)).
Proof.
  intros c M. induction M as [ | | d p | p | M1 IH1 M2 IH2 ]; intros Hin N M0 R; simpl in *.
  - apply ax_cgr. etransitivity; [ apply cgr_choice_com | apply cgr_choice_nil ].
  - apply ax_cgr. etransitivity; [ apply cgr_choice_com | apply cgr_choice_nil ].
  - subst d. eapply ax_trans; [ apply ax_cgr_sym; apply cgr_choice_assoc | ].
    apply ax_merge_into_fwd_ctx.
  - contradiction.
  - destruct Hin as [Hin1 Hin2].
    eapply ax_trans; [ | apply (IH2 Hin2 N M0 R) ].
    eapply ax_trans; [ | apply ax_cgr; apply cgr_swap3 ].
    eapply ax_trans; [ | apply (IH1 Hin1 N M0 ((ext M2 N) + R)) ].
    apply ax_cgr.
    etransitivity; [ apply cgr_choice_assoc | ].
    apply cgr_fullchoice; [ apply cgr_refl | apply cgr_swap3 ].
Qed.

(** ** The case, syntactically *)

Theorem ax_below_input : forall (c : ChannelData) (M : gproc) (Q : proc),
  gInputsOn c M ->
  (forall v, ax_pre ((g M) ‖ (c ! v • 𝟘)) (Q ^ v)) ->
  ax_pre (g M) (g (c ? Q)).
Proof.
  intros c M Q Hin H.
  eapply ax_trans; [ apply (ax_fwd_intro c M) | ].
  eapply ax_trans; [ apply ax_cgr; apply cgr_fullchoice;
                     [ apply cgr_refl | apply cgr_symm; apply cgr_choice_nil ] | ].
  eapply ax_trans; [ apply (ax_ext_absorb c M Hin (c ? (c ! (bvar 0) • 𝟘)) M 𝟘) | ].
  eapply ax_trans; [ apply ax_cgr; apply cgr_choice_nil | ].
  apply ax_fwd_match. exact H.
Qed.

(** ** The case, with the semantic premise discharged

    [must_i_feed_below] supplies exactly what [ax_below_input] asks for,
    so the only remaining hypothesis is the recursive call — at a
    strictly smaller right-hand side. *)

Theorem ax_below_input_sem : forall (c : ChannelData) (M : gproc) (Q : proc),
  gInputsOn c M ->
  (forall v, ((c ! v • 𝟘) ‖ (g M)) ⊑ₘᵤₛₜᵢ (Q ^ v) ->
             ax_pre ((c ! v • 𝟘) ‖ (g M)) (Q ^ v)) ->
  (g M) ⊑ₘᵤₛₜᵢ (g (c ? Q)) ->
  ax_pre (g M) (g (c ? Q)).
Proof.
  intros c M Q Hin Hrec Hsem.
  apply (ax_below_input c M Q Hin). intro v.
  eapply ax_trans; [ apply ax_cgr; apply cgr_par_com | ].
  apply Hrec.
  eapply must_i_feed_below; [ exact Hsem | apply lts_input ].
Qed.

(** * The matching argument, on an arbitrary stable sum

    The general case splits cleanly in two, and the second half is now
    done in full.

    - **Phase A** (shape): [⊢ g M ⊑ g (mirrorN M N)], where [mirrorN M N]
      is [N] with every continuation replaced by the mirror one.  This is
      where the copycats are introduced and [M]'s own guards absorbed, and
      it is the only part still open in general ([ax_phaseA_one_channel]
      settles it when everything lives on a single channel).
    - **Phase B** (match): [⊢ g (mirrorN M N) ⊑ g N], summand by summand.

    Phase B is *easy and completely general*, and the reason is worth
    stating: [mirrorN M N] has **exactly [N]'s guards**.  So every step is
    an [ax_choice_input] — guard-preserving, hence sound in VACCS — and no
    rule that changes a guard is ever needed.  This is the concrete payoff
    of the design constraint that [VACCS_ChoiceProbes.v] forced: matching
    must pair summands *by guard*, and once the mirror is built the
    pairing is not a choice, it is the identity.

    The residue bookkeeping is the same as in [ax_ext_absorb]: no
    congruence in the second argument of [+], so each summand is permuted
    to the front by [ax_cgr] before being rewritten, and the two induction
    hypotheses run in sequence with a permutation between them.  [①] is
    handled by [ax_success_r], which is why that rule also had to be given
    a residue. *)

Fixpoint mirrorN (P : proc) (N : gproc) : gproc :=
  match N with
  | gpr_success => gpr_nil
  | gpr_nil => gpr_nil
  | gpr_input c _ => fwdg c P
  | gpr_tau p => gpr_tau p
  | gpr_choice N1 N2 => gpr_choice (mirrorN P N1) (mirrorN P N2)
  end.

(** The premise Phase B needs at each of [N]'s summands: the recursive
    call, already discharged. *)
Fixpoint mirror_ok (M : gproc) (N : gproc) : Prop :=
  match N with
  | gpr_success => True
  | gpr_nil => True
  | gpr_input c Q => forall v, ax_pre ((g M) ‖ (c ! v • 𝟘)) (Q ^ v)
  | gpr_tau _ => False
  | gpr_choice N1 N2 => mirror_ok M N1 /\ mirror_ok M N2
  end.

Lemma ax_mirrorN_match : forall (M N : gproc), mirror_ok M N ->
  forall (R : gproc), ax_pre (g ((mirrorN M N) + R)) (g (N + R)).
Proof.
  intros M N. induction N as [ | | c Q | p | N1 IH1 N2 IH2 ]; intros Hok R; simpl in *.
  - apply ax_success_r.
  - apply ax_refl.
  - apply ax_choice_input. intro v. unfold fwdg. simpl.
    rewrite gproc_NewVar_cancel. apply Hok.
  - contradiction.
  - destruct Hok as [Hok1 Hok2].
    eapply ax_trans; [ apply ax_cgr; apply cgr_choice_assoc | ].
    eapply ax_trans; [ apply (IH1 Hok1 ((mirrorN M N2) + R)) | ].
    eapply ax_trans; [ apply ax_cgr; apply cgr_swap3 | ].
    eapply ax_trans; [ apply (IH2 Hok2 (N1 + R)) | ].
    apply ax_cgr.
    etransitivity; [ apply cgr_swap3 | ].
    apply cgr_symm. apply cgr_choice_assoc.
Qed.

(** [mirror_ok] is exactly "one recursive call per input transition of
    [N]", read structurally. *)
Lemma mirror_ok_of : forall (M N : gproc),
  (forall p, ~ lts (g N) τ p) ->
  (forall c v Q', lts (g N) (ActExt (ActIn (c,v))) Q' -> ax_pre ((g M) ‖ (c ! v • 𝟘)) Q') ->
  mirror_ok M N.
Proof.
  intros M N. induction N as [ | | c Q | p | N1 IH1 N2 IH2 ]; intros Hst Hrec; simpl in *.
  - exact I.
  - exact I.
  - intro v. apply Hrec. apply lts_input.
  - exfalso. eapply Hst. apply lts_tau.
  - split.
    + apply IH1.
      * intros q Hq. eapply Hst. apply lts_choiceL. exact Hq.
      * intros c v Q' Hl. apply Hrec. apply lts_choiceL. exact Hl.
    + apply IH2.
      * intros q Hq. eapply Hst. apply lts_choiceR. exact Hq.
      * intros c v Q' Hl. apply Hrec. apply lts_choiceR. exact Hl.
Qed.

(** …and [must_i_feed_below] supplies its semantic side, so all that is
    asked of the caller is the recursive call itself.  Note the semantic
    hypothesis is used at the **whole** of [N] — it cannot be weakened to
    a sub-sum, since [g M ⊑ₘᵤₛₜᵢ g (N₁ + N₂)] does not imply
    [g M ⊑ₘᵤₛₜᵢ g N₁]; that is why the induction above carries no
    semantics at all. *)
Corollary mirror_ok_rec : forall (M N : gproc),
  (forall p, ~ lts (g N) τ p) ->
  (g M) ⊑ₘᵤₛₜᵢ (g N) ->
  (forall c v Q', lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ((c ! v • 𝟘) ‖ (g M)) ⊑ₘᵤₛₜᵢ Q' -> ax_pre ((c ! v • 𝟘) ‖ (g M)) Q') ->
  mirror_ok M N.
Proof.
  intros M N Hst Hsem Hrec. apply mirror_ok_of; [ exact Hst | ].
  intros c v Q' Hl.
  eapply ax_trans; [ apply ax_cgr; apply cgr_par_com | ].
  apply Hrec; [ exact Hl | ].
  eapply must_i_feed_below; [ exact Hsem | exact Hl ].
Qed.

(** ** The reduction: completeness against a stable sum IS Phase A

    Everything else — the pairing, the omega rule, the recursion's
    semantic premise — is discharged. *)

Theorem ax_below_stable_sum : forall (M N : gproc),
  (forall p, ~ lts (g N) τ p) ->
  ax_pre (g M) (g (mirrorN M N)) ->
  (g M) ⊑ₘᵤₛₜᵢ (g N) ->
  (forall c v Q', lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ((c ! v • 𝟘) ‖ (g M)) ⊑ₘᵤₛₜᵢ Q' -> ax_pre ((c ! v • 𝟘) ‖ (g M)) Q') ->
  ax_pre (g M) (g N).
Proof.
  intros M N Hst Hphase Hsem Hrec.
  eapply ax_trans; [ exact Hphase | ].
  eapply ax_trans; [ apply ax_cgr_sym; apply cgr_choice_nil | ].
  eapply ax_trans;
    [ apply (ax_mirrorN_match M N (mirror_ok_rec M N Hst Hsem Hrec) 𝟘) | ].
  apply ax_cgr. apply cgr_choice_nil.
Qed.

(** Phase A, settled when everything lives on one channel. *)
Theorem ax_phaseA_one_channel : forall (c : ChannelData) (M : gproc),
  gInputsOn c M -> ax_pre (g M) (g (fwdg c M)).
Proof.
  intros c M Hin.
  eapply ax_trans; [ apply (ax_fwd_intro c M) | ].
  eapply ax_trans; [ apply ax_cgr; apply cgr_fullchoice;
                     [ apply cgr_refl | apply cgr_symm; apply cgr_choice_nil ] | ].
  eapply ax_trans; [ apply (ax_ext_absorb c M Hin (c ? (c ! (bvar 0) • 𝟘)) M 𝟘) | ].
  apply ax_cgr. apply cgr_choice_nil.
Qed.

Corollary ax_phaseA_single_summand : forall (c : ChannelData) (M : gproc) (Q : proc),
  gInputsOn c M -> ax_pre (g M) (g (mirrorN M (c ? Q))).
Proof. intros c M Q Hin. simpl. apply ax_phaseA_one_channel. exact Hin. Qed.

(** * Reaching the mirror in one step, on all channels at once

    [ax_fwd_intro] adds one copycat.  Adding one per channel and expanding
    the [k]-fold parallel product would be painful — but it is unnecessary,
    because a whole **sum** of copycat guards is invisible too
    ([must_i_nil_below_copycats], the generalised [ax_ccat_r]).  So:

        guardsN N  :=  N with every continuation replaced by the copycat
                       (and [①]/[𝟘] by [𝟘])

    is a [gCopycats] sum, [⊢ g M ⊑ g M ‖ g (guardsN N)] is one [ax_par],
    and [ax_expansion_l] flattens that in a single step.  The point that
    makes it fit exactly:

        ext_r (guardsN N) M  =  mirrorN M N        (definitionally)

    — the expansion's *right* component **is** the mirror.  So

        ax_mirror_reach : ⊢ g M ⊑ g (ext M (guardsN N) + mirrorN M N)

    with no side condition beyond [N] being stable.

    ** What this leaves

    Exactly one obligation, and it is purely syntactic:

        ⊢ g (ext M (guardsN N) + mirrorN M N) ⊑ g (mirrorN M N)

    i.e. *[M]'s own guards, which the expansion left beside the mirror, are
    absorbed by it*.  [ax_ext_absorb] does this when everything lives on
    one channel.  In general it is where the two remaining gaps sit, and
    they are visible in the statement: a [𝛕]-summand of [M] produces a
    [𝛕]-summand of [ext M (guardsN N)] (a mixed sum — [ax_tau_sep_*]), and
    a guard of [M] on a channel [N] does not offer has no mirror summand to
    merge into ([ax_input_drop], [must_i_extra_input]). *)

Fixpoint guardsN (N : gproc) : gproc :=
  match N with
  | gpr_success => gpr_nil
  | gpr_nil => gpr_nil
  | gpr_input c _ => gpr_input c (c ! (bvar 0) • 𝟘)
  | gpr_tau p => gpr_tau p
  | gpr_choice N1 N2 => gpr_choice (guardsN N1) (guardsN N2)
  end.

Lemma guardsN_copycats : forall N, (forall p, ~ lts (g N) τ p) -> gCopycats (guardsN N).
Proof.
  induction N as [ | | c q | q | N1 IH1 N2 IH2 ]; intros Hst; simpl in *.
  - exact I.
  - exact I.
  - reflexivity.
  - exfalso. eapply Hst. apply lts_tau.
  - split.
    + apply IH1. intros p Hp. eapply Hst. apply lts_choiceL. exact Hp.
    + apply IH2. intros p Hp. eapply Hst. apply lts_choiceR. exact Hp.
Qed.

Lemma ext_r_guardsN : forall (N M : gproc), (forall p, ~ lts (g N) τ p) ->
  ext_r (guardsN N) M = mirrorN M N.
Proof.
  induction N as [ | | c q | q | N1 IH1 N2 IH2 ]; intros M Hst; simpl in *.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exfalso. eapply Hst. apply lts_tau.
  - f_equal.
    + apply IH1. intros p Hp. eapply Hst. apply lts_choiceL. exact Hp.
    + apply IH2. intros p Hp. eapply Hst. apply lts_choiceR. exact Hp.
Qed.

Theorem ax_mirror_reach : forall (M N : gproc), (forall p, ~ lts (g N) τ p) ->
  ax_pre (g M) (g ((ext M (guardsN N)) + (mirrorN M N))).
Proof.
  intros M N Hst.
  rewrite <- (ext_r_guardsN N M Hst).
  eapply ax_trans; [ | apply ax_expansion_l ].
  eapply ax_trans; [ apply ax_cgr_sym; apply cgr_par_nil | ].
  apply ax_par; [ apply ax_refl | apply ax_ccat_r; apply guardsN_copycats; exact Hst ].
Qed.

(** ** Completeness against a stable sum, reduced to the absorption alone

    Everything else is discharged: the semantic premise by
    [must_i_feed_below], the pairing by [ax_mirrorN_match], the shape by
    [ax_mirror_reach].  What is left is the one syntactic statement above,
    plus the recursive call — which is at a strictly smaller right-hand
    side, [Q'] being a reduct of [g N]. *)

Theorem ax_below_stable_sum_reduced : forall (M N : gproc),
  (forall p, ~ lts (g N) τ p) ->
  ax_pre (g ((ext M (guardsN N)) + (mirrorN M N))) (g (mirrorN M N)) ->
  (g M) ⊑ₘᵤₛₜᵢ (g N) ->
  (forall c v Q', lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ((c ! v • 𝟘) ‖ (g M)) ⊑ₘᵤₛₜᵢ Q' -> ax_pre ((c ! v • 𝟘) ‖ (g M)) Q') ->
  ax_pre (g M) (g N).
Proof.
  intros M N Hst Habs Hsem Hrec.
  eapply ax_below_stable_sum; [ exact Hst | | exact Hsem | exact Hrec ].
  eapply ax_trans; [ apply (ax_mirror_reach M N Hst) | exact Habs ].
Qed.

(** * The absorption, in general — and the stable case CLOSES

    What is left of Phase A is to absorb [M]'s own guards, which the
    expansion left beside the mirror.  The one new ingredient is a way to
    reach the mirror summand belonging to a given channel:

        mirror_pull : hasChan c N -> ∃ Rest, g (mirrorN M N) ≡* g (fwdg c M + Rest)

    — pure [≡*], since the mirror is built from [N]'s own tree.  With it,
    each guard of [M] on a channel [N] offers is permuted next to *its*
    mirror summand and absorbed by [ax_merge_into_fwd_ctx], exactly as in
    the one-channel case; the induction again runs the two hypotheses in
    sequence with a permutation between them.

    The side condition [gGuardsIn N M] — every guard of [M] is an input on
    a channel [N] offers — is where the two known gaps now live, stated
    rather than hidden: a [𝛕]-summand of [M] is excluded outright, and so
    is a guard on a channel [N] does not offer. *)

Fixpoint hasChan (c : ChannelData) (N : gproc) : Prop :=
  match N with
  | gpr_success => False
  | gpr_nil => False
  | gpr_input d _ => d = c
  | gpr_tau _ => False
  | gpr_choice N1 N2 => hasChan c N1 \/ hasChan c N2
  end.

Lemma mirror_pull : forall (N : gproc) (M : gproc) (c : ChannelData), hasChan c N ->
  exists Rest, (g (mirrorN M N)) ≡* (g ((fwdg c M) + Rest)).
Proof.
  induction N as [ | | d q | q | N1 IH1 N2 IH2 ]; intros M c Hc; simpl in *;
    try contradiction.
  - subst d. exists 𝟘. apply cgr_choice_nil_rev.
  - destruct Hc as [Hc | Hc].
    + destruct (IH1 M c Hc) as (R1 & HR1).
      exists (R1 + (mirrorN M N2)). etransitivity.
      * apply cgr_choice. exact HR1.
      * apply cgr_choice_assoc.
    + destruct (IH2 M c Hc) as (R2 & HR2).
      exists (R2 + (mirrorN M N1)). etransitivity.
      * apply cgr_choice_com.
      * etransitivity; [ apply cgr_choice; exact HR2 | apply cgr_choice_assoc ].
Qed.

Fixpoint gGuardsIn (N : gproc) (M : gproc) : Prop :=
  match M with
  | gpr_success => True
  | gpr_nil => True
  | gpr_input c _ => hasChan c N
  | gpr_tau _ => False
  | gpr_choice M1 M2 => gGuardsIn N M1 /\ gGuardsIn N M2
  end.

Lemma ax_ext_absorb_gen : forall (N M0 M : gproc), gGuardsIn N M ->
  forall (G R : gproc),
  ax_pre (g ((ext M G) + ((mirrorN M0 N) + R))) (g ((mirrorN M0 N) + R)).
Proof.
  intros N M0 M. induction M as [ | | c p | p | M1 IH1 M2 IH2 ];
    intros Hin G R; simpl in *.
  - apply ax_cgr. etransitivity; [ apply cgr_choice_com | apply cgr_choice_nil ].
  - apply ax_cgr. etransitivity; [ apply cgr_choice_com | apply cgr_choice_nil ].
  - destruct (mirror_pull N M0 c Hin) as (Rest & HR).
    eapply ax_trans.
    { apply ax_cgr. apply cgr_fullchoice; [ apply cgr_refl | apply cgr_choice; exact HR ]. }
    eapply ax_trans.
    { apply ax_cgr. apply cgr_fullchoice; [ apply cgr_refl | apply cgr_choice_assoc ]. }
    eapply ax_trans; [ apply ax_cgr_sym; apply cgr_choice_assoc | ].
    eapply ax_trans; [ apply (ax_merge_into_fwd_ctx c (p ‖ (g (gNewVar 0 G))) M0 (Rest + R)) | ].
    apply ax_cgr.
    etransitivity; [ apply cgr_symm; apply cgr_choice_assoc | ].
    apply cgr_choice. apply cgr_symm. exact HR.
  - contradiction.
  - destruct Hin as [Hin1 Hin2].
    eapply ax_trans; [ | apply (IH2 Hin2 G R) ].
    eapply ax_trans; [ | apply ax_cgr; apply cgr_swap3 ].
    eapply ax_trans; [ | apply (IH1 Hin1 G ((ext M2 G) + R)) ].
    apply ax_cgr.
    etransitivity; [ apply cgr_choice_assoc | ].
    apply cgr_fullchoice; [ apply cgr_refl | apply cgr_swap3 ].
Qed.

Theorem ax_absorb_into_mirror : forall (N M : gproc), gGuardsIn N M ->
  ax_pre (g ((ext M (guardsN N)) + (mirrorN M N))) (g (mirrorN M N)).
Proof.
  intros N M Hin.
  eapply ax_trans; [ apply ax_cgr; apply cgr_fullchoice;
                     [ apply cgr_refl | apply cgr_symm; apply cgr_choice_nil ] | ].
  eapply ax_trans; [ apply (ax_ext_absorb_gen N M M Hin (guardsN N) 𝟘) | ].
  apply ax_cgr. apply cgr_choice_nil.
Qed.

(** ** The stable case of completeness, closed

    Two arbitrary stable guarded sums, with no restriction on how many
    channels either offers or how many summands share one.  The only
    hypotheses left are the recursive call — at a strictly smaller
    right-hand side, [Q'] being a reduct of [g N] — and [gGuardsIn N M],
    which is precisely the two gaps that remain, stated. *)

Theorem ax_below_stable_sum_full : forall (M N : gproc),
  (forall p, ~ lts (g N) τ p) -> gGuardsIn N M ->
  (g M) ⊑ₘᵤₛₜᵢ (g N) ->
  (forall c v Q', lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ((c ! v • 𝟘) ‖ (g M)) ⊑ₘᵤₛₜᵢ Q' -> ax_pre ((c ! v • 𝟘) ‖ (g M)) Q') ->
  ax_pre (g M) (g N).
Proof.
  intros M N Hst Hin Hsem Hrec.
  eapply ax_below_stable_sum_reduced; try eassumption.
  apply ax_absorb_into_mirror. exact Hin.
Qed.

(** * The unstable right-hand side, and the whole [tau_nf] case

    An internal choice on the right costs nothing: [ax_int_glb] builds it,
    and the two semantic premises come from [must_i_tau_below] — a [𝛕] of
    the *server* is already a [⊑ₘᵤₛₜᵢ]-step, so [g M ⊑ₘᵤₛₜᵢ g (N₁ ⊕ N₂)]
    gives [g M ⊑ₘᵤₛₜᵢ g Nᵢ] for free.  (Note this is the direction that
    *does* hold; the converse — a sum on the right being a least upper
    bound — is false, which is why [mirror_ok_of] carries no semantics.)

    Recursing over [tau_nf] then handles an arbitrary normal form on the
    right: the [⊕]-layer by the rule, the stable leaves by
    [ax_below_stable_sum_full].  [leafOf] names the leaves so that the two
    per-leaf side conditions can be stated once for the whole tree. *)

Theorem ax_below_int_choice : forall (M N1 N2 : gproc),
  (g M) ⊑ₘᵤₛₜᵢ (g ((𝛕 • (g N1)) + (𝛕 • (g N2)))) ->
  ((g M) ⊑ₘᵤₛₜᵢ (g N1) -> ax_pre (g M) (g N1)) ->
  ((g M) ⊑ₘᵤₛₜᵢ (g N2) -> ax_pre (g M) (g N2)) ->
  ax_pre (g M) (g ((𝛕 • (g N1)) + (𝛕 • (g N2)))).
Proof.
  intros M N1 N2 Hsem H1 H2.
  apply ax_int_glb.
  - apply H1. intros t Hm.
    assert (Hl : lts (g ((𝛕 • (g N1)) + (𝛕 • (g N2)))) τ (g N1))
      by (apply lts_choiceL; apply lts_tau).
    eapply must_i_tau_below; [ exact Hl | apply Hsem; exact Hm ].
  - apply H2. intros t Hm.
    assert (Hl : lts (g ((𝛕 • (g N1)) + (𝛕 • (g N2)))) τ (g N2))
      by (apply lts_choiceR; apply lts_tau).
    eapply must_i_tau_below; [ exact Hl | apply Hsem; exact Hm ].
Qed.

Inductive leafOf : gproc -> gproc -> Prop :=
| leaf_self : forall M, gStable M -> leafOf M M
| leaf_l : forall M1 M2 L, leafOf L M1 -> leafOf L ((𝛕 • (g M1)) + (𝛕 • (g M2)))
| leaf_r : forall M1 M2 L, leafOf L M2 -> leafOf L ((𝛕 • (g M1)) + (𝛕 • (g M2))).

Theorem ax_below_tau_nf : forall (N : gproc), tau_nf N -> forall (M : gproc),
  (forall L, leafOf L N -> gGuardsIn L M) ->
  (g M) ⊑ₘᵤₛₜᵢ (g N) ->
  (forall L c v (Q' : proc), leafOf L N -> lts (g L) (ActExt (ActIn (c,v))) Q' ->
      ((c ! v • 𝟘) ‖ (g M)) ⊑ₘᵤₛₜᵢ Q' -> ax_pre ((c ! v • 𝟘) ‖ (g M)) Q') ->
  ax_pre (g M) (g N).
Proof.
  intros N Hnf. induction Hnf as [ N Hst | N1 N2 Hnf1 IH1 Hnf2 IH2 ];
    intros M Hg Hsem Hrec.
  - apply ax_below_stable_sum_full.
    + intros p Hp. eapply stable_no_lts; [ apply gStable_iff; exact Hst | exact Hp ].
    + apply Hg. apply leaf_self. exact Hst.
    + exact Hsem.
    + intros c v Q' Hl Hs. eapply Hrec; [ apply leaf_self; exact Hst | exact Hl | exact Hs ].
  - apply ax_below_int_choice; [ exact Hsem | | ].
    + intro Hs1. apply IH1.
      * intros L HL. apply Hg. apply leaf_l. exact HL.
      * exact Hs1.
      * intros L c v Q' HL Hl Hs. eapply Hrec; [ apply leaf_l; exact HL | exact Hl | exact Hs ].
    + intro Hs2. apply IH2.
      * intros L HL. apply Hg. apply leaf_r. exact HL.
      * exact Hs2.
      * intros L c v Q' HL Hl Hs. eapply Hrec; [ apply leaf_r; exact HL | exact Hl | exact Hs ].
Qed.

(** Two facts about leaves, for the measure the outer recursion will need:
    a leaf is reached from the whole normal form by [τ]s alone (so
    [Static_lts_decrease] bounds its size), and it inherits [gStatic]. *)

Lemma leafOf_reach : forall (N L : gproc), leafOf L N -> (g N) ⟹[[]] (g L).
Proof.
  intros N L H. induction H as [ M Hst | M1 M2 L H IH | M1 M2 L H IH ].
  - apply wt_nil.
  - eapply wt_tau; [ apply lts_choiceL; apply lts_tau | exact IH ].
  - eapply wt_tau; [ apply lts_choiceR; apply lts_tau | exact IH ].
Qed.

Lemma leafOf_gStatic : forall (N L : gproc), leafOf L N -> gStatic N -> gStatic L.
Proof.
  intros N L H. induction H as [ M Hst | M1 M2 L H IH | M1 M2 L H IH ]; intro HS.
  - exact HS.
  - inversion HS; subst. apply IH. inversion H2; subst. inversion H1; subst. assumption.
  - inversion HS; subst. apply IH. inversion H3; subst. inversion H1; subst. assumption.
Qed.

(** * Peeling a [𝛕]-summand — the inner recursion's step

    ** A retraction, first

    An earlier note conjectured that the leaves of the [tau_nf] produced by
    [tau_flatten_all]/[tau_separate] are [τ]-reachable from [g M], which
    would have given the outer recursion its measure.  **That is false**,
    and it is worth being explicit about why, since the shape of the
    remaining work depends on it.  [ax_tau_sep_anywhere] turns
    [M = X + 𝛕•(g Y)] into [𝛕•(g (X + Y)) + 𝛕•(g Y)], whose leaves include
    those of [X + Y]; but [g M]'s *only* [τ] is the one into [g Y], so
    [X + Y] is not reachable from [g M] at all.  Separation genuinely
    *creates* states — that is what it is for.

    ** So the recursion peels instead of pre-normalising

    The two normalisation steps are used one at a time, each as a step of a
    recursion rather than as a preprocessing pass:

    - [ax_below_tau_peel] separates one [𝛕]-summand and splits the goal in
      two by [ax_int_glb].  The branch [g Y] is the [𝛕]-continuation, which
      [VACCS_Descent.v] turns into a strictly smaller [Static] process —
      that is where the *outer* recursion is called.  The branch
      [g (rebuild r + Y)] continues the inner one.
    - [ax_below_tau_flatten] collapses a [𝛕] whose continuation is all-[𝛕];
      it is what keeps the inner measure decreasing.

    Both semantic premises come for free: [ax_tau_sep_anywhere] and
    [ax_tau_flatten_anywhere] are [⊢]-equalities, so [soundness_ax]
    transports [⊑ₘᵤₛₜᵢ] across them, and [must_i_tau_below] then projects
    onto each branch. *)

Lemma ax_below_int_choice_p : forall (p : proc) (N1 N2 : gproc),
  p ⊑ₘᵤₛₜᵢ (g ((𝛕 • (g N1)) + (𝛕 • (g N2)))) ->
  (p ⊑ₘᵤₛₜᵢ (g N1) -> ax_pre p (g N1)) ->
  (p ⊑ₘᵤₛₜᵢ (g N2) -> ax_pre p (g N2)) ->
  ax_pre p (g ((𝛕 • (g N1)) + (𝛕 • (g N2)))).
Proof.
  intros p N1 N2 Hsem H1 H2.
  apply ax_int_glb.
  - apply H1. intros t Hm.
    assert (Hl : lts (g ((𝛕 • (g N1)) + (𝛕 • (g N2)))) τ (g N1))
      by (apply lts_choiceL; apply lts_tau).
    eapply must_i_tau_below; [ exact Hl | apply Hsem; exact Hm ].
  - apply H2. intros t Hm.
    assert (Hl : lts (g ((𝛕 • (g N1)) + (𝛕 • (g N2)))) τ (g N2))
      by (apply lts_choiceR; apply lts_tau).
    eapply must_i_tau_below; [ exact Hl | apply Hsem; exact Hm ].
Qed.

(** **A structural caveat on this whole layer, found while assembling
    completeness.**  Every driver below carries [Forall tau_cont_nf
    (summands …)], i.e. *every τ-summand's continuation is literally a
    guarded sum* [g Y].  That invariant is **assumed everywhere and
    established nowhere**, and for a VACCS normal form it is generally
    **false**: [normal_form] builds sums with [ext]/[resg], whose τ
    summands carry continuations like [P ‖ g N] or [Ѵⁿ (msgs l ‖ …)] —
    configurations, not guarded sums.

    It is not an accident of the port.  The law the peeling rests on,
    [ax_tau_sep_l : X + 𝛕•(g Y) ≂ 𝛕•(g (X + Y)) + 𝛕•(g Y)], has to form
    [X + Y] — so the continuation *must* be a [gproc].  In VCCS a
    pre-pass ([tau_normalize_conts]) restored that shape; in VACCS it
    cannot, because a continuation's normal form is a configuration and
    a message is not a guard.

    So the τ-layer below applies to sums whose τ-continuations are
    already guarded sums, not to normal forms in general.  Closing that
    needs either a mixed-sum law for *configuration* continuations —
    whose soundness is doubtful, mixed sums being their own thing — or a
    treatment of a right-hand τ-summand that never separates it, e.g.
    through the descent ([VACCS_Descent.tau_summand_reduct]) alone. *)

Theorem ax_below_tau_peel : forall (p : proc) (M Y : gproc) (r : list gproc),
  gStatic M -> Permutation (summands M) ((𝛕 • (g Y)) :: r) ->
  p ⊑ₘᵤₛₜᵢ (g M) ->
  (p ⊑ₘᵤₛₜᵢ (g ((rebuild r) + Y)) -> ax_pre p (g ((rebuild r) + Y))) ->
  (p ⊑ₘᵤₛₜᵢ (g Y) -> ax_pre p (g Y)) ->
  ax_pre p (g M).
Proof.
  intros p M Y r HS Hperm Hsem H1 H2.
  destruct (ax_tau_sep_anywhere M Y r HS Hperm) as [Ha Hb].
  eapply ax_trans; [ | exact Hb ].
  apply ax_below_int_choice_p; [ | exact H1 | exact H2 ].
  intros t Hm. apply (soundness_ax _ _ Ha). apply Hsem. exact Hm.
Qed.

Theorem ax_below_tau_flatten : forall (p : proc) (M Y : gproc) (r : list gproc),
  gStatic M -> gAllTau Y -> Permutation (summands M) ((𝛕 • (g Y)) :: r) ->
  p ⊑ₘᵤₛₜᵢ (g M) ->
  (p ⊑ₘᵤₛₜᵢ (g ((rebuild r) + Y)) -> ax_pre p (g ((rebuild r) + Y))) ->
  ax_pre p (g M).
Proof.
  intros p M Y r HS Hall Hperm Hsem H1.
  destruct (ax_tau_flatten_anywhere M Y r HS Hall Hperm) as [Ha Hb].
  eapply ax_trans; [ | exact Hb ].
  apply H1. intros t Hm. apply (soundness_ax _ _ Ha). apply Hsem. exact Hm.
Qed.

(** * The inner driver: any guarded sum reduces to its stable case

    The two peeling steps are iterated exactly as [tau_flatten_all] and
    [tau_separate] iterate their rewrites — same searches, same measures,
    same invariants — but driving the *goal* [⊢ p ⊑ g M] instead of
    rewriting [M] into a [tau_nf].

    - [ax_below_mixed] separates, measure [ntaus].  Termination is bought
      by the invariant [tau_cont_ok] ("every [𝛕]-continuation is a
      **stable** sum"): peeling [𝛕•(g Y)] recurses into [rebuild r + Y],
      and a stable [Y] contributes no [𝛕]-summands of its own.
    - [ax_below_gsum] establishes that invariant first, by [tau_flatten_all]
      (measure [tau_weight]), and transports the goal across the resulting
      [⊢]-equality with [soundness_ax].

    **What the caller is left with is a single hypothesis about *stable*
    sums.**  Every [𝛕]-continuation peeled off is stable, so the two
    handlers the recursion needs — one for the leaves it stops at, one for
    the branches it descends into — collapse into the same one.  That is
    the whole point of running flattening first, and it is why the
    statement below is as simple as it is. *)

Lemma ax_below_mixed : forall n (M : gproc), gStatic M ->
  (ntaus (summands M) <= n)%nat -> Forall tau_cont_ok (summands M) ->
  forall (p : proc), p ⊑ₘᵤₛₜᵢ (g M) ->
  (forall (L : gproc), gStatic L -> gStable L -> p ⊑ₘᵤₛₜᵢ (g L) -> ax_pre p (g L)) ->
  ax_pre p (g M).
Proof.
  induction n as [|n IH]; intros M HM Hmeas Hok p Hsem Hstab.
  - apply Hstab; [ exact HM | | exact Hsem ].
    apply find_tau_none_stable.
    destruct (find_tau (summands M)) as [(q,r)|] eqn:E; [| reflexivity].
    exfalso. apply find_tau_spec in E.
    rewrite (ntaus_perm _ _ E) in Hmeas. simpl in Hmeas. lia.
  - destruct (find_tau (summands M)) as [(q,r)|] eqn:E.
    + apply find_tau_spec in E.
      assert (Hokperm : Forall tau_cont_ok ((𝛕 • q) :: r))
        by (eapply tau_cont_ok_perm; eassumption).
      inversion Hokperm as [|? ? Hp0 Hokr]; subst.
      destruct Hp0 as (Y & Hpy & HYst). subst q.
      assert (Hlv : Forall (fun a => summands a = [a]) ((𝛕 • (g Y)) :: r)).
      { apply Forall_forall. intros x Hx. pose proof (summands_leaves M) as Hsl.
        rewrite Forall_forall in Hsl. apply Hsl. rewrite E. exact Hx. }
      inversion Hlv as [|? ? _ Hlvr]; subst.
      destruct (tau_mid_static M Y r HM E) as (HYgst & Hrgst & _).
      assert (Hnew : gStatic (rebuild r + Y))
        by (constructor; [apply rebuild_gStatic; exact Hrgst | exact HYgst]).
      assert (Hmeas2 : ntaus (summands (rebuild r + Y)) <= n).
      { simpl. rewrite ntaus_app.
        rewrite (ntaus_summands_rebuild r Hlvr).
        rewrite (gStable_ntaus_zero Y HYst).
        rewrite (ntaus_perm _ _ E) in Hmeas. simpl in Hmeas. lia. }
      assert (Hok2 : Forall tau_cont_ok (summands (rebuild r + Y))).
      { simpl. apply Forall_app. split.
        - apply tau_cont_ok_rebuild; assumption.
        - apply tau_cont_ok_stable. exact HYst. }
      eapply ax_below_tau_peel; [ exact HM | exact E | exact Hsem | | ].
      * intro Hs1. exact (IH (rebuild r + Y) Hnew Hmeas2 Hok2 p Hs1 Hstab).
      * intro Hs2. apply Hstab; [ exact HYgst | exact HYst | exact Hs2 ].
    + apply Hstab; [ exact HM | apply find_tau_none_stable; exact E | exact Hsem ].
Qed.

Theorem ax_below_gsum : forall (M : gproc), gStatic M ->
  Forall tau_cont_nf (summands M) ->
  forall (p : proc), p ⊑ₘᵤₛₜᵢ (g M) ->
  (forall (L : gproc), gStatic L -> gStable L -> p ⊑ₘᵤₛₜᵢ (g L) -> ax_pre p (g L)) ->
  ax_pre p (g M).
Proof.
  intros M HM Hnf p Hsem Hstab.
  destruct (tau_flatten_all (tau_weight (summands M)) M HM (le_n _) Hnf)
    as (M' & HM' & Hok' & Hf & Hb).
  eapply ax_trans; [ | exact Hb ].
  eapply (ax_below_mixed (ntaus (summands M')) M' HM' (le_n _) Hok');
    [ | exact Hstab ].
  intros t Hm. apply (soundness_ax _ _ Hf). apply Hsem. exact Hm.
Qed.

(** * The outer measure, recovered

    The retraction above cost the naive route to the outer recursion's
    measure.  It is recovered by looking at what the driver actually hands
    to its handler, rather than at the [tau_nf] it no longer builds.

    Every leaf the driver stops at is either the sum itself or a
    [𝛕]-continuation, possibly iterated — and while a *created* state like
    [rebuild r + Y] is indeed not reachable from [g M], **its input
    transitions still are**: a summand of [r] is a summand of [M], and a
    summand of [Y] is reached after the [τ] into [g Y].  So the invariant
    to thread through the driver is not about the states but about the
    transitions,

        ∀ c v Q, g L ⟶[(c,v)?] Q  ->  g M₀ ⟹[[(c,v)?]] Q

    and that *is* preserved by both peeling steps.  The two lemmas below
    then convert it into the measure: a weak transition never grows a
    [Static] process, and one carrying a visible action strictly shrinks
    it.  Hence every recursive call sits at a strictly smaller [size], and
    the outer recursion is plain well-founded recursion on [size] — no
    [tbound], no semantic measure. *)

Lemma wt_size_le : forall (p : proc) s q, Static p -> p ⟹[s] q -> (size q <= size p)%nat.
Proof.
  intros p s q HS H. induction H as [x|s0 x r y Hl Hw IH|mu s0 x r y Hl Hw IH].
  - lia.
  - assert (Hlt : (size r < size x)%nat) by (eapply Static_lts_decrease; eassumption).
    assert (HSr : Static r) by (eapply Static_preserved_by_lts; eassumption).
    specialize (IH HSr). lia.
  - assert (Hlt : (size r < size x)%nat) by (eapply Static_lts_decrease; eassumption).
    assert (HSr : Static r) by (eapply Static_preserved_by_lts; eassumption).
    specialize (IH HSr). lia.
Qed.

Lemma wt_act_size_lt : forall (p : proc) mu s q, Static p -> p ⟹[mu :: s] q ->
  (size q < size p)%nat.
Proof.
  intros p mu s q HS H. remember (mu :: s) as s0 eqn:Hs.
  revert mu s Hs HS.
  induction H as [x|s1 x r y Hl Hw IH|mu1 s1 x r y Hl Hw IH]; intros mu s Hs HS.
  - discriminate.
  - assert (Hlt : (size r < size x)%nat) by (eapply Static_lts_decrease; eassumption).
    assert (HSr : Static r) by (eapply Static_preserved_by_lts; eassumption).
    specialize (IH mu s Hs HSr). lia.
  - assert (Hlt : (size r < size x)%nat) by (eapply Static_lts_decrease; eassumption).
    assert (HSr : Static r) by (eapply Static_preserved_by_lts; eassumption).
    assert (Hle : (size y <= size r)%nat) by (eapply wt_size_le; eassumption). lia.
Qed.

(** ** Flattening as a driver too

    [ax_below_gsum] above reaches its flattened form through
    [tau_flatten_all], which returns only a [⊢]-equality — and an equality
    is exactly what an LTS-level invariant cannot cross.  The same loop is
    therefore redone here as a *driver* of the goal, so that both phases
    are now transition-preserving steps and the invariant [Inv] of the
    previous section can be threaded end to end.  [ax_below_gsum_drive]
    has the same statement as [ax_below_gsum]; only its proof differs, and
    only that one is usable for the outer recursion. *)

Lemma ax_below_flatten_drive : forall n (M : gproc), gStatic M ->
  (tau_weight (summands M) <= n)%nat -> Forall tau_cont_nf (summands M) ->
  forall (p : proc), p ⊑ₘᵤₛₜᵢ (g M) ->
  (forall (M' : gproc), gStatic M' -> Forall tau_cont_ok (summands M') ->
      p ⊑ₘᵤₛₜᵢ (g M') -> ax_pre p (g M')) ->
  ax_pre p (g M).
Proof.
  induction n as [|n IH]; intros M HM Hmeas Hnf p Hsem Hok.
  - apply Hok; [ exact HM | | exact Hsem ].
    apply find_unstable_tau_none; [| exact Hnf].
    destruct (find_unstable_tau (summands M)) as [(Y,r)|] eqn:E; [| reflexivity].
    exfalso. destruct (find_unstable_tau_spec _ _ _ E) as (Hperm & Hst).
    rewrite (tau_weight_perm _ _ Hperm) in Hmeas. simpl in Hmeas.
    destruct Y; simpl in *; try discriminate Hst; lia.
  - destruct (find_unstable_tau (summands M)) as [(Y,r)|] eqn:E.
    + destruct (find_unstable_tau_spec _ _ _ E) as (Hperm & Hstb).
      assert (Hnfperm : Forall tau_cont_nf ((𝛕 • (g Y)) :: r))
        by (eapply tau_cont_nf_perm; eassumption).
      inversion Hnfperm as [|? ? Hhd Hnfr]; subst.
      destruct Hhd as (Y0 & HY0 & HnfY). injection HY0 as HY0. subst Y0.
      assert (HAT : gAllTau Y).
      { destruct (tau_nf_gAllTau_or_stable Y HnfY) as [Hs|Ha]; [| exact Ha].
        exfalso. apply gStableB_spec in Hs. rewrite Hstb in Hs. discriminate Hs. }
      assert (Hlv : Forall (fun a => summands a = [a]) ((𝛕 • (g Y)) :: r)).
      { apply Forall_forall. intros x Hx. pose proof (summands_leaves M) as Hsl.
        rewrite Forall_forall in Hsl. apply Hsl. rewrite Hperm. exact Hx. }
      inversion Hlv as [|? ? _ Hlvr]; subst.
      destruct (tau_mid_static M Y r HM Hperm) as (HYgst & Hrgst & _).
      assert (Hnew : gStatic (rebuild r + Y))
        by (constructor; [apply rebuild_gStatic; exact Hrgst | exact HYgst]).
      assert (Hmeas2 : tau_weight (summands (rebuild r + Y)) <= n).
      { simpl. rewrite tau_weight_app. rewrite (tau_weight_summands_rebuild r Hlvr).
        rewrite (tau_weight_perm _ _ Hperm) in Hmeas. simpl in Hmeas.
        inversion HnfY as [? Hs | A B HA HB]; subst.
        - exfalso. apply gStableB_spec in Hs. rewrite Hstb in Hs. discriminate Hs.
        - simpl in *. lia. }
      assert (Hnf2 : Forall tau_cont_nf (summands (rebuild r + Y))).
      { simpl. apply Forall_app. split.
        - apply tau_cont_nf_rebuild; assumption.
        - apply tau_cont_nf_of_tau_nf. exact HnfY. }
      eapply ax_below_tau_flatten; [ exact HM | exact HAT | exact Hperm | exact Hsem | ].
      intro Hs1. exact (IH (rebuild r + Y) Hnew Hmeas2 Hnf2 p Hs1 Hok).
    + apply Hok; [ exact HM | apply find_unstable_tau_none; [exact E | exact Hnf] | exact Hsem ].
Qed.

Theorem ax_below_gsum_drive : forall (M : gproc), gStatic M ->
  Forall tau_cont_nf (summands M) ->
  forall (p : proc), p ⊑ₘᵤₛₜᵢ (g M) ->
  (forall (L : gproc), gStatic L -> gStable L -> p ⊑ₘᵤₛₜᵢ (g L) -> ax_pre p (g L)) ->
  ax_pre p (g M).
Proof.
  intros M HM Hnf p Hsem Hstab.
  eapply (ax_below_flatten_drive (tau_weight (summands M)) M HM (le_n _) Hnf p Hsem).
  intros M' HM' Hok' Hs'.
  exact (ax_below_mixed (ntaus (summands M')) M' HM' (le_n _) Hok' p Hs' Hstab).
Qed.

(** ** The invariant itself

    [InvR M₀ L] is the two-component fact the drivers thread: every input
    transition of [g L] is reached from [M₀] by a single visible step, and
    every [𝛕]-continuation of [L] is [τ]-reachable from [M₀].  The second
    component is what makes the first inductive — it is *states* that
    survive the peel on the [𝛕]-branch, and *transitions* on the other. *)

Lemma summand_lts : forall (M a : gproc), In a (summands M) ->
  forall al q, lts (g a) al q -> lts (g M) al q.
Proof.
  induction M as [ | | c p | p | M1 IH1 M2 IH2 ]; intros a Hin al q Hl; simpl in Hin.
  - destruct Hin as [He|[]]; subst; exact Hl.
  - destruct Hin as [He|[]]; subst; exact Hl.
  - destruct Hin as [He|[]]; subst; exact Hl.
  - destruct Hin as [He|[]]; subst; exact Hl.
  - apply in_app_or in Hin. destruct Hin as [H1|H2].
    + apply lts_choiceL. eapply IH1; eassumption.
    + apply lts_choiceR. eapply IH2; eassumption.
Qed.

Lemma rebuild_lts_inv : forall (l : list gproc) al q, lts (g (rebuild l)) al q ->
  exists a, In a l /\ lts (g a) al q.
Proof.
  induction l as [|a l IH]; intros al q Hl; simpl in Hl.
  - inversion Hl.
  - inversion Hl; subst.
    + exists a. split; [ left; reflexivity | assumption ].
    + destruct (IH al q H3) as (b & Hb & Hlb). exists b. split; [ right; exact Hb | exact Hlb ].
Qed.

Lemma wt_nil_push : forall (p q : proc), p ⟹[[]] q ->
  forall s r, q ⟹[s] r -> p ⟹[s] r.
Proof.
  intros p q H. remember (@nil (ExtAct TypeOfActions)) as s0 eqn:Hs.
  induction H as [x|s1 x y z Hl Hw IH|mu s1 x y z Hl Hw IH]; intros s r Hr; subst.
  - exact Hr.
  - eapply wt_tau; [ exact Hl | apply IH; [ reflexivity | exact Hr ] ].
  - discriminate.
Qed.

Lemma rebuild_summands_in : forall (l : list gproc),
  Forall (fun a => summands a = [a]) l ->
  forall x, In x (summands (rebuild l)) -> In x l \/ x = 𝟘.
Proof.
  induction l as [|a l IH]; intros Hlv x Hin; simpl in *.
  - destruct Hin as [He|[]]; right; symmetry; exact He.
  - inversion Hlv as [|? ? Ha Hlv']; subst.
    apply in_app_or in Hin. destruct Hin as [H1|H2].
    + rewrite Ha in H1. destruct H1 as [He|[]]; left; left; exact He.
    + destruct (IH Hlv' x H2) as [Hl|Hz]; [ left; right; exact Hl | right; exact Hz ].
Qed.

Definition InvR (M0 : proc) (L : gproc) : Prop :=
  (forall c v Q, lts (g L) (ActExt (ActIn (c,v))) Q -> M0 ⟹[[ActIn (c,v)]] Q)
  /\ (forall Y, In (𝛕 • (g Y)) (summands L) -> M0 ⟹[[]] (g Y)).

Lemma InvR_self : forall (M : gproc), InvR (g M) M.
Proof.
  intro M. split.
  - intros c v Q Hl. eapply wt_act; [ exact Hl | apply wt_nil ].
  - intros Y Hin. eapply wt_tau; [ | apply wt_nil ].
    eapply summand_lts; [ exact Hin | apply lts_tau ].
Qed.

Lemma InvR_tau_cont : forall M0 (Y : gproc), M0 ⟹[[]] (g Y) -> InvR M0 Y.
Proof.
  intros M0 Y HY. split.
  - intros c v Q Hl. eapply wt_nil_push; [ exact HY | eapply wt_act; [ exact Hl | apply wt_nil ] ].
  - intros Z Hin. eapply wt_nil_push; [ exact HY | ].
    eapply wt_tau; [ eapply summand_lts; [ exact Hin | apply lts_tau ] | apply wt_nil ].
Qed.

(** The preservation lemma: one peel, both branches. *)
Lemma InvR_peel : forall M0 (M Y : gproc) (r : list gproc),
  InvR M0 M -> Forall (fun a => summands a = [a]) r ->
  Permutation (summands M) ((𝛕 • (g Y)) :: r) ->
  M0 ⟹[[]] (g Y) /\ InvR M0 (rebuild r + Y).
Proof.
  intros M0 M Y r [Hin1 Hin2] Hlv Hperm.
  assert (Htrans : forall x, In x ((𝛕 • (g Y)) :: r) -> In x (summands M)).
  { intros x Hx. eapply Permutation_in; [ apply Permutation_sym; exact Hperm | exact Hx ]. }
  assert (HY : M0 ⟹[[]] (g Y)) by (apply Hin2; apply Htrans; left; reflexivity).
  split; [ exact HY | ]. split.
  - intros c v Q Hl. simpl in Hl. inversion Hl; subst.
    + destruct (rebuild_lts_inv r _ _ H3) as (a & Ha & Hla).
      eapply Hin1. eapply summand_lts; [ apply Htrans; right; exact Ha | exact Hla ].
    + eapply wt_nil_push; [ exact HY | eapply wt_act; [ exact H3 | apply wt_nil ] ].
  - intros Z Hin. simpl in Hin. apply in_app_or in Hin. destruct Hin as [H1|H2].
    + destruct (rebuild_summands_in r Hlv _ H1) as [Hr|Hz]; [| discriminate Hz ].
      apply Hin2. apply Htrans. right. exact Hr.
    + eapply wt_nil_push; [ exact HY | ].
      eapply wt_tau; [ eapply summand_lts; [ exact H2 | apply lts_tau ] | apply wt_nil ].
Qed.

(** ** The invariant, threaded through both drivers

    Same proofs as [ax_below_mixed] and [ax_below_flatten_drive], with
    [InvR M₀ ·] carried along: [InvR_peel] supplies it for both branches
    of a peel and [InvR_tau_cont] for the [𝛕]-continuation handed to the
    handler, so the handler now receives it at every leaf.

    [ax_below_gsum_inv] starts the thread at [M₀ := g M] via [InvR_self].
    Together with [InvR_reduct_smaller] it gives the outer recursion its
    measure: every input-reduct of every leaf is strictly smaller than the
    guarded sum the driver started from. *)

Lemma ax_below_mixed_inv : forall n (M : gproc) (M0 : proc), gStatic M ->
  (ntaus (summands M) <= n)%nat -> Forall tau_cont_ok (summands M) ->
  InvR M0 M ->
  forall (p : proc), p ⊑ₘᵤₛₜᵢ (g M) ->
  (forall (L : gproc), gStatic L -> gStable L -> InvR M0 L ->
      p ⊑ₘᵤₛₜᵢ (g L) -> ax_pre p (g L)) ->
  ax_pre p (g M).
Proof.
  induction n as [|n IH]; intros M M0 HM Hmeas Hok HInv p Hsem Hstab.
  - apply Hstab; [ exact HM | | exact HInv | exact Hsem ].
    apply find_tau_none_stable.
    destruct (find_tau (summands M)) as [(q,r)|] eqn:E; [| reflexivity].
    exfalso. apply find_tau_spec in E.
    rewrite (ntaus_perm _ _ E) in Hmeas. simpl in Hmeas. lia.
  - destruct (find_tau (summands M)) as [(q,r)|] eqn:E.
    + apply find_tau_spec in E.
      assert (Hokperm : Forall tau_cont_ok ((𝛕 • q) :: r))
        by (eapply tau_cont_ok_perm; eassumption).
      inversion Hokperm as [|? ? Hp0 Hokr]; subst.
      destruct Hp0 as (Y & Hpy & HYst). subst q.
      assert (Hlv : Forall (fun a => summands a = [a]) ((𝛕 • (g Y)) :: r)).
      { apply Forall_forall. intros x Hx. pose proof (summands_leaves M) as Hsl.
        rewrite Forall_forall in Hsl. apply Hsl. rewrite E. exact Hx. }
      inversion Hlv as [|? ? _ Hlvr]; subst.
      destruct (tau_mid_static M Y r HM E) as (HYgst & Hrgst & _).
      destruct (InvR_peel M0 M Y r HInv Hlvr E) as (HYreach & HInv2).
      assert (Hnew : gStatic (rebuild r + Y))
        by (constructor; [apply rebuild_gStatic; exact Hrgst | exact HYgst]).
      assert (Hmeas2 : ntaus (summands (rebuild r + Y)) <= n).
      { simpl. rewrite ntaus_app.
        rewrite (ntaus_summands_rebuild r Hlvr).
        rewrite (gStable_ntaus_zero Y HYst).
        rewrite (ntaus_perm _ _ E) in Hmeas. simpl in Hmeas. lia. }
      assert (Hok2 : Forall tau_cont_ok (summands (rebuild r + Y))).
      { simpl. apply Forall_app. split.
        - apply tau_cont_ok_rebuild; assumption.
        - apply tau_cont_ok_stable. exact HYst. }
      eapply ax_below_tau_peel; [ exact HM | exact E | exact Hsem | | ].
      * intro Hs1. exact (IH (rebuild r + Y) M0 Hnew Hmeas2 Hok2 HInv2 p Hs1 Hstab).
      * intro Hs2. apply Hstab;
          [ exact HYgst | exact HYst | apply InvR_tau_cont; exact HYreach | exact Hs2 ].
    + apply Hstab;
        [ exact HM | apply find_tau_none_stable; exact E | exact HInv | exact Hsem ].
Qed.

Lemma ax_below_flatten_drive_inv : forall n (M : gproc) (M0 : proc), gStatic M ->
  (tau_weight (summands M) <= n)%nat -> Forall tau_cont_nf (summands M) ->
  InvR M0 M ->
  forall (p : proc), p ⊑ₘᵤₛₜᵢ (g M) ->
  (forall (M' : gproc), gStatic M' -> Forall tau_cont_ok (summands M') ->
      InvR M0 M' -> p ⊑ₘᵤₛₜᵢ (g M') -> ax_pre p (g M')) ->
  ax_pre p (g M).
Proof.
  induction n as [|n IH]; intros M M0 HM Hmeas Hnf HInv p Hsem Hok.
  - apply Hok; [ exact HM | | exact HInv | exact Hsem ].
    apply find_unstable_tau_none; [| exact Hnf].
    destruct (find_unstable_tau (summands M)) as [(Y,r)|] eqn:E; [| reflexivity].
    exfalso. destruct (find_unstable_tau_spec _ _ _ E) as (Hperm & Hst).
    rewrite (tau_weight_perm _ _ Hperm) in Hmeas. simpl in Hmeas.
    destruct Y; simpl in *; try discriminate Hst; lia.
  - destruct (find_unstable_tau (summands M)) as [(Y,r)|] eqn:E.
    + destruct (find_unstable_tau_spec _ _ _ E) as (Hperm & Hstb).
      assert (Hnfperm : Forall tau_cont_nf ((𝛕 • (g Y)) :: r))
        by (eapply tau_cont_nf_perm; eassumption).
      inversion Hnfperm as [|? ? Hhd Hnfr]; subst.
      destruct Hhd as (Y0 & HY0 & HnfY). injection HY0 as HY0. subst Y0.
      assert (HAT : gAllTau Y).
      { destruct (tau_nf_gAllTau_or_stable Y HnfY) as [Hs|Ha]; [| exact Ha].
        exfalso. apply gStableB_spec in Hs. rewrite Hstb in Hs. discriminate Hs. }
      assert (Hlv : Forall (fun a => summands a = [a]) ((𝛕 • (g Y)) :: r)).
      { apply Forall_forall. intros x Hx. pose proof (summands_leaves M) as Hsl.
        rewrite Forall_forall in Hsl. apply Hsl. rewrite Hperm. exact Hx. }
      inversion Hlv as [|? ? _ Hlvr]; subst.
      destruct (tau_mid_static M Y r HM Hperm) as (HYgst & Hrgst & _).
      destruct (InvR_peel M0 M Y r HInv Hlvr Hperm) as (HYreach & HInv2).
      assert (Hnew : gStatic (rebuild r + Y))
        by (constructor; [apply rebuild_gStatic; exact Hrgst | exact HYgst]).
      assert (Hmeas2 : tau_weight (summands (rebuild r + Y)) <= n).
      { simpl. rewrite tau_weight_app. rewrite (tau_weight_summands_rebuild r Hlvr).
        rewrite (tau_weight_perm _ _ Hperm) in Hmeas. simpl in Hmeas.
        inversion HnfY as [? Hs | A B HA HB]; subst.
        - exfalso. apply gStableB_spec in Hs. rewrite Hstb in Hs. discriminate Hs.
        - simpl in *. lia. }
      assert (Hnf2 : Forall tau_cont_nf (summands (rebuild r + Y))).
      { simpl. apply Forall_app. split.
        - apply tau_cont_nf_rebuild; assumption.
        - apply tau_cont_nf_of_tau_nf. exact HnfY. }
      eapply ax_below_tau_flatten; [ exact HM | exact HAT | exact Hperm | exact Hsem | ].
      intro Hs1. exact (IH (rebuild r + Y) M0 Hnew Hmeas2 Hnf2 HInv2 p Hs1 Hok).
    + apply Hok;
        [ exact HM | apply find_unstable_tau_none; [exact E | exact Hnf]
        | exact HInv | exact Hsem ].
Qed.

Theorem ax_below_gsum_inv : forall (M : gproc), gStatic M ->
  Forall tau_cont_nf (summands M) ->
  forall (p : proc), p ⊑ₘᵤₛₜᵢ (g M) ->
  (forall (L : gproc), gStatic L -> gStable L -> InvR (g M) L ->
      p ⊑ₘᵤₛₜᵢ (g L) -> ax_pre p (g L)) ->
  ax_pre p (g M).
Proof.
  intros M HM Hnf p Hsem Hstab.
  eapply (ax_below_flatten_drive_inv (tau_weight (summands M)) M (g M) HM (le_n _) Hnf
            (InvR_self M) p Hsem).
  intros M' HM' Hok' HInv' Hs'.
  exact (ax_below_mixed_inv (ntaus (summands M')) M' (g M) HM' (le_n _) Hok' HInv' p Hs' Hstab).
Qed.

(** The measure, delivered. *)
Corollary InvR_reduct_smaller : forall (M0 : proc) (L : gproc), Static M0 -> InvR M0 L ->
  forall c v (Q : proc), lts (g L) (ActExt (ActIn (c,v))) Q -> (size Q < size M0)%nat.
Proof.
  intros M0 L HS [H1 _] c v Q Hl.
  eapply wt_act_size_lt; [ exact HS | apply H1; exact Hl ].
Qed.

(** * `grestrict` meets `gGuardsIn`

    [VACCS_Absorb.grestrict N M] keeps exactly [M]'s guards on channels
    [N] offers, so it satisfies this file's structural side condition.
    [offers_hasChan] is the bridge: the transition-level statement
    [grestrict_offered] proved there becomes the structural [hasChan]
    this file's [mirror_pull] consumes. *)

Lemma offers_hasChan : forall (N : gproc) c, offers N c -> hasChan c N.
Proof.
  induction N as [ | | d P | P | N1 IH1 N2 IH2 ]; intros c (w & r & Hr); simpl.
  - inversion Hr.
  - inversion Hr.
  - inversion Hr; subst. reflexivity.
  - inversion Hr.
  - inversion Hr; subst.
    + left. apply IH1. exists w. eexists. eassumption.
    + right. apply IH2. exists w. eexists. eassumption.
Qed.

Lemma grestrict_guards : forall (N M : gproc), gGuardsIn N (grestrict N M).
Proof.
  induction M as [ | | c P | P | M1 IH1 M2 IH2 ]; simpl.
  - exact I.
  - exact I.
  - destruct (offersb N c) eqn:E; [ | exact I ].
    simpl. apply offers_hasChan. apply offersb_spec. exact E.
  - exact I.
  - split; assumption.
Qed.

(** **A third direction mismatch, recorded rather than papered over.**

    With [grestrict_guards] it is tempting to chain

        ⊢ g M ⊑ g (grestrict N M)          (ax_restrict, certificate)
        ⊢ g (grestrict N M) ⊑ g N          (ax_below_stable_sum_full)

    but the second step's *semantic* hypothesis is
    [g (grestrict N M) ⊑ₘᵤₛₜᵢ g N], and that is **not** implied by
    [g M ⊑ₘᵤₛₜᵢ g N].  Restriction moves *up* the preorder — dropping a
    guard drops a [com] obligation, so the restricted sum passes at least
    what [M] passes — hence [M ⊑ grestrict N M] and nothing about
    [grestrict N M] versus [N].

    This is the same shape of obstacle as the mirror-restriction route:
    an inequation available in one direction where the argument needs the
    other.  Both are recorded so neither is re-walked. *)

(** * Phase A without [gGuardsIn]: restrict the WHOLE expansion

    The three earlier routes all failed the same way — they weakened the
    left-hand side and then needed a hypothesis about the weakened side.
    The repair is to restrict a term that is [≂ₘᵤₛₜᵢ]-**equal** to [g M],
    not merely above it: the *whole* expansion

        ext M (guardsN N) + mirrorN M N   ≂ₘᵤₛₜᵢ   g M ‖ g (guardsN N)
                                          ≂ₘᵤₛₜᵢ   g M

    the second step because a sum of copycats is equivalent to [𝟘] in
    both directions ([must_i_nil_below_copycats] and
    [must_i_copycats_below_nil]).  [bigsum_below_M] is the direction that
    matters, and it is what makes the certificate's semantic content
    available: a τ-stuck, non-good client silent on [N]'s channels that
    the big sum passed would be passed by [g M], hence by [g N] — and a
    *stable* [g N] can only pass it by synchronising on a channel it
    offers, which the client is silent on.

    So [ax_restrict] cuts the big sum down to [mirrorN M N] in one step,
    and **the [gGuardsIn] side condition disappears entirely**: no guard
    of [M] has to be on a channel [N] offers, because the surplus ones
    are discarded jointly by the restriction instead of being absorbed
    one at a time. *)

Lemma bigsum_below_M : forall (M N : gproc), (forall p, ~ lts (g N) τ p) ->
  (g ((ext M (guardsN N)) + (mirrorN M N))) ⊑ₘᵤₛₜᵢ (g M).
Proof.
  intros M N Hst.
  rewrite <- (ext_r_guardsN N M Hst).
  intros t Hm.
  assert (Hpar : ((g M) ‖ (g (guardsN N))) must_pass t) by (apply must_i_expansion_r; exact Hm).
  assert (Hnil : ((g M) ‖ (g 𝟘)) must_pass t).
  { eapply must_i_par_compat_r; [ | exact Hpar ].
    apply must_i_copycats_below_nil. apply guardsN_copycats. exact Hst. }
  eapply must_i_cgr; [ | exact Hnil ]. apply cgr_par_nil.
Qed.

Lemma ext_no_tau : forall (M K : gproc), (forall p, ~ lts (g M) τ p) ->
  forall p, ~ lts (g (ext M K)) τ p.
Proof.
  induction M as [ | | c P | P | M1 IH1 M2 IH2 ]; intros K Hst p Hl; simpl in Hl.
  - inversion Hl.
  - inversion Hl.
  - inversion Hl.
  - exfalso. eapply Hst. apply lts_tau.
  - inversion Hl; subst.
    + eapply IH1; [ | eassumption ]. intros q Hq. eapply Hst. apply lts_choiceL. exact Hq.
    + eapply IH2; [ | eassumption ]. intros q Hq. eapply Hst. apply lts_choiceR. exact Hq.
Qed.

Lemma mirrorN_no_tau : forall (P : proc) (N : gproc), (forall p, ~ lts (g N) τ p) ->
  forall p, ~ lts (g (mirrorN P N)) τ p.
Proof.
  induction N as [ | | c Q | Q | N1 IH1 N2 IH2 ]; intros Hst p Hl; simpl in Hl.
  - inversion Hl.
  - inversion Hl.
  - inversion Hl.
  - exfalso. eapply Hst. apply lts_tau.
  - inversion Hl; subst.
    + eapply IH1; [ | eassumption ]. intros q Hq. eapply Hst. apply lts_choiceL. exact Hq.
    + eapply IH2; [ | eassumption ]. intros q Hq. eapply Hst. apply lts_choiceR. exact Hq.
Qed.

Lemma offers_mirrorN : forall (P : proc) (N : gproc) c v q,
  lts (g N) (ActExt (ActIn (c,v))) q -> offers (mirrorN P N) c.
Proof.
  intros P N. induction N as [ | | d Q | Q | N1 IH1 N2 IH2 ]; intros c v q Hl;
    simpl; inversion Hl; subst.
  - unfold fwdg. exists (cst O). eexists. apply lts_input.
  - destruct (IH1 c v _ H3) as (w & r & Hr). exists w, r. apply lts_choiceL. exact Hr.
  - destruct (IH2 c v _ H3) as (w & r & Hr). exists w, r. apply lts_choiceR. exact Hr.
Qed.

(** The certificate's semantic content, available from the hypothesis
    completeness starts with. *)

Theorem bigsum_sembadk : forall (M N : gproc), (forall p, ~ lts (g N) τ p) ->
  (g M) ⊑ₘᵤₛₜᵢ (g N) ->
  forall u, (forall q, ~ lts u τ q) -> ~ good_VACCS u ->
    EmitsNone (offers (mirrorN M N)) u ->
    ~ ((g ((ext M (guardsN N)) + (mirrorN M N))) must_pass u).
Proof.
  intros M N Hst Hsem u Hstu Hng Hem Hm.
  assert (HmN : (g N) must_pass u)
    by (apply Hsem; eapply bigsum_below_M; [ exact Hst | exact Hm ]).
  inversion HmN as [Ho | Ho Hex Hpt Het Hcom]; subst; [contradiction |].
  destruct Hex as (z & Hz). inversion Hz; subst; unfold lts_step in *; simpl in *.
  - eapply Hst. exact l.
  - eapply Hstu. exact l.
  - destruct μ1 as [[c1 v1]|[c1 v1]]; [ | exfalso; eapply gsum_no_out; exact l1 ].
    destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; try (exfalso; exact eq).
    inversion eq; subst.
    eapply (Hem c2); [ eapply offers_mirrorN; exact l1 | ].
    exists v2, b2. exact l2.
Qed.

(** Phase A, in general — no [gGuardsIn], no restriction on which
    channels [M] offers. *)

Theorem ax_phaseA_general : forall (M N : gproc), (forall p, ~ lts (g N) τ p) ->
  (forall p, ~ lts (g M) τ p) ->
  BadK (fun _ => False) (offers (mirrorN M N))
       (g ((ext M (guardsN N)) + (mirrorN M N))) ->
  ax_pre (g M) (g (mirrorN M N)).
Proof.
  intros M N HstN HstM HB.
  eapply ax_trans; [ apply ax_mirror_reach; exact HstN | ].
  apply ax_restrict; [ | | exact HB ].
  - intros al q Hl. apply lts_choiceR. exact Hl.
  - intros p Hl. inversion Hl; subst.
    + eapply ext_no_tau; [ exact HstM | eassumption ].
    + eapply mirrorN_no_tau; [ exact HstN | eassumption ].
Qed.

(** …and the whole stable case, with [gGuardsIn] gone.  Compare
    [ax_below_stable_sum_full], which needed it: the only hypothesis left
    beyond the recursion is a [BadK] derivation, whose semantic content
    [bigsum_sembadk] shows is always available. *)

Theorem ax_below_stable_sum_nogg : forall (M N : gproc),
  (forall p, ~ lts (g N) τ p) -> (forall p, ~ lts (g M) τ p) ->
  BadK (fun _ => False) (offers (mirrorN M N))
       (g ((ext M (guardsN N)) + (mirrorN M N))) ->
  (g M) ⊑ₘᵤₛₜᵢ (g N) ->
  (forall c v Q', lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ((c ! v • 𝟘) ‖ (g M)) ⊑ₘᵤₛₜᵢ Q' -> ax_pre ((c ! v • 𝟘) ‖ (g M)) Q') ->
  ax_pre (g M) (g N).
Proof.
  intros M N HstN HstM HB Hsem Hrec.
  eapply ax_below_stable_sum; [ exact HstN | | exact Hsem | exact Hrec ].
  apply ax_phaseA_general; assumption.
Qed.

(** * Feeding a surplus channel cannot help — the engine of the kill list

    A channel [M] offers and [N] does not is *useless to a client that
    stays inside [N]'s channels*: [g M] fails every such client even when
    the client is handed the surplus message for free.

    This is exactly the obligation [bk_kill] raises, and it is what makes
    the **last** position of any kill order go through: once every other
    surplus channel sits in [D], the client can emit only on the one
    being killed, so [must]'s [ex] field forces the [com] there and the
    lemma below closes it.

    **The open point, stated in the repository rather than only in
    notes.**  The earlier positions of the order are not covered: there
    the client may still emit on the channels not yet killed, and the
    failure of [g M] may come from a [com] at one of *those* instead.
    Whether some channel is always killable first — i.e. whether
    [VACCS_Absorb.KillOk] can always be met in *some* order — is the one
    thing separating this development from completeness for the stable
    case.  Two attempted counterexamples collapsed for the same reason (a
    client withholding a channel kills the guard that needs it, a client
    supplying every channel is passed), so the claim looks true; the
    missing construction has to combine the per-channel witness clients
    into one, and combining clients can create [τ]s. *)

Theorem feed_surplus_fails : forall (M N : gproc) (c : ChannelData) (v : ValueData),
  (forall q, ~ lts (g N) τ q) -> (g M) ⊑ₘᵤₛₜᵢ (g N) -> ~ offers N c ->
  forall u, (forall q, ~ lts u τ q) -> ~ good_VACCS u ->
    (forall x q, ~ lts u (ActExt (ActIn (c,x))) q) ->
    EmitsNone (offers N) u ->
    ~ ((g M) must_pass ((c ! v • 𝟘) ‖ u)).
Proof.
  intros M N c v HstN Hsem Hnoc u Hstu Hng Href Hem Hm.
  assert (HmN : (g N) must_pass ((c ! v • 𝟘) ‖ u)) by (apply Hsem; exact Hm).
  assert (Hstw : forall q, ~ lts ((c ! v • 𝟘) ‖ u) τ q).
  { intros q Hq. inversion Hq; subst.
    - inversion H1; subst. eapply Href. exact H2.
    - match goal with H : lts (_ ! _ • 𝟘) (ActExt (ActIn _)) _ |- _ => inversion H end.
    - match goal with H : lts (_ ! _ • 𝟘) τ _ |- _ => inversion H end.
    - eapply Hstu. eassumption. }
  assert (Hngw : ~ good_VACCS ((c ! v • 𝟘) ‖ u)).
  { intro Hg. inversion Hg; subst.
    match goal with H : _ \/ _ |- _ => destruct H as [H|H]; [ inversion H | ] end.
    apply Hng. assumption. }
  inversion HmN as [Ho | Ho Hex Hpt Het Hcom]; subst; [contradiction |].
  destruct Hex as (z & Hz). inversion Hz; subst; unfold lts_step in *; simpl in *.
  - eapply HstN. exact l.
  - eapply Hstw. exact l.
  - destruct μ1 as [[c1 v1]|[c1 v1]]; [ | exfalso; eapply gsum_no_out; exact l1 ].
    destruct μ2 as [[c2 v2]|[c2 v2]]; simpl in eq; try (exfalso; exact eq).
    inversion eq; subst.
    assert (Hoff : offers N c2) by (exists v2; eexists; exact l1).
    inversion l2; subst.
    + match goal with H : lts (_ ! _ • 𝟘) (ActExt (ActOut _)) _ |- _ => inversion H; subst end.
      apply Hnoc. exact Hoff.
    + eapply (Hem c2); [ exact Hoff | exists v2; eexists; eassumption ].
Qed.

(** * Bridging `grestrict` to the certificate

    `grestrict N M` keeps `M`'s guard on `c` exactly when `N` offers `c`
    ([grestrict_offers]).  So if the restricted sum is *stable* at a
    buffer, then every channel of that buffer which `M` offers is one `N`
    does **not** — i.e. it is surplus ([grestrict_stable_surplus]).

    That is precisely `certificate_N_refuses`'s hypothesis, so the
    certificate is discharged for every buffer whose channels `M` offers
    ([certificate_all_offered]).  What is left open is a buffer carrying a
    channel `M` does not offer at all — see the plan notes. *)

Lemma grestrict_offers : forall (N M : gproc) c,
  offers M c -> offers N c -> offers (grestrict N M) c.
Proof.
  intros N M c. induction M as [ | | d P | P | M1 IH1 M2 IH2 ];
    intros (w & r & Hr) HN; simpl; inversion Hr; subst.
  - assert (E : offersb N c = true) by (apply offersb_spec; exact HN).
    rewrite E. exists w. eexists. apply lts_input.
  - destruct (IH1 (ex_intro _ w (ex_intro _ _ H3)) HN) as (w1 & r1 & Hr1).
    exists w1, r1. apply lts_choiceL. exact Hr1.
  - destruct (IH2 (ex_intro _ w (ex_intro _ _ H3)) HN) as (w1 & r1 & Hr1).
    exists w1, r1. apply lts_choiceR. exact Hr1.
Qed.

Lemma grestrict_stable_surplus : forall (N M : gproc) (m : MO (ExtAct TypeOfActions)),
  ((g (grestrict N M)) ▷ m) ↛ ->
  forall c w, ActOut (c,w) ∈ m -> offers M c -> ~ offers N c.
Proof.
  intros N M m Hst c w Hin HM HN.
  destruct (grestrict_offers N M c HM HN) as (w0 & r0 & Hr0).
  destruct (lts_in_value_swap (g (grestrict N M)) (ActIn (c,w0)) r0 Hr0 c w0 w eq_refl)
    as (r1 & Hr1).
  eapply (@lts_refuses_spec2 (proc * MO (ExtAct TypeOfActions)) _ _ _
            ((g (grestrict N M)) ▷ m) τ); [ | exact Hst ].
  apply gmultiset_disj_union_difference' in Hin.
  rewrite Hin. eexists. apply fw_tau_deliver. exact Hr1.
Qed.

Theorem certificate_all_offered : forall (M N : gproc), gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N) ->
  forall m, OutOnly m -> ((g (grestrict N M)) ▷ m) ↛ ->
  (forall c w, ActOut (c,w) ∈ m -> offers M c) ->
  Settles (chans m) ((g M) ▷ m).
Proof.
  intros M N HM HN HstN Hsem m Hout Hst Hall.
  eapply certificate_N_refuses;
    [ apply static_g; exact HM | exact HN | exact HstN | exact Hsem | exact Hout | ].
  intros a Hin r Hr. destruct a as (c,w).
  eapply (grestrict_stable_surplus N M m Hst c w Hin).
  - eapply Hall. exact Hin.
  - exists w, r. exact Hr.
Qed.

(** * Restricting the WHOLE expansion to the mirror — semantically

    This is Phase A's semantic content, and unlike the `grestrict` route
    it has no mixed-buffer case at all.

    The reason is structural: `mirrorN M N` carries **exactly `N`'s
    channels**, so if `mirrorN M N ▷ m` is *stable* then no channel of
    `m` is one `N` offers.  That is precisely
    `VACCS_Cond2.certificate_N_refuses`'s hypothesis — the case split
    that defeated `grestrict` (a buffer mixing channels `M` absorbs with
    channels it does not) cannot arise here.

    The other ingredient is `bigsum_below_M`: the whole expansion is
    below `g M`, hence below `g N`, which is what
    `certificate_N_refuses` is applied to. *)

Lemma guardsN_gStatic : forall (N : gproc), gStatic N -> gStatic (guardsN N).
Proof.
  induction N as [ | | c q | q | N1 IH1 N2 IH2 ]; intro H; simpl.
  - constructor.
  - constructor.
  - repeat constructor.
  - inversion H; subst. constructor. auto.
  - inversion H; subst. constructor; auto.
Qed.

Lemma mirrorN_gStatic : forall (P : proc) (N : gproc), Static P -> gStatic N ->
  gStatic (mirrorN P N).
Proof.
  intros P N HM. induction N as [ | | c q | q | N1 IH1 N2 IH2 ]; intro H; simpl.
  - constructor.
  - constructor.
  - unfold fwdg. constructor. constructor.
    + apply Static_NewVar. exact HM.
    + constructor.
  - inversion H; subst. constructor. auto.
  - inversion H; subst. constructor; auto.
Qed.

(** The certificate, factored out: it is what both the semantic fact and
    the derivation need. *)

Lemma bigsum_gStatic : forall (M N : gproc), gStatic M -> gStatic N ->
  gStatic ((ext M (guardsN N)) + (mirrorN M N)).
Proof.
  intros M N HM HN. constructor.
  - apply ext_gStatic; [ exact HM | apply guardsN_gStatic; exact HN ].
  - apply mirrorN_gStatic; [ apply static_g; exact HM | exact HN ].
Qed.

Lemma bigsum_certificate : forall (M N : gproc), gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N) ->
  forall m, OutOnly m -> ((g (mirrorN M N)) ▷ m) ↛ ->
  Settles (emits ((g (mirrorN M N)) ▷ m))
          ((g ((ext M (guardsN N)) + (mirrorN M N))) ▷ m).
Proof.
  intros M N HM HN HstN Hsem m Hout Hst.
  assert (HB : gStatic ((ext M (guardsN N)) + (mirrorN M N)))
    by (apply bigsum_gStatic; assumption).
  assert (Hbn : (g ((ext M (guardsN N)) + (mirrorN M N))) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N)).
  { intros t Ht. apply Hsem. eapply bigsum_below_M; [ exact HstN | exact Ht ]. }
  apply (Settles_gsum_chans ((ext M (guardsN N)) + (mirrorN M N)) (mirrorN M N)).
  eapply certificate_N_refuses;
    [ apply static_g; exact HB | exact HN | exact HstN | exact Hbn | exact Hout | ].
  intros a Hin r Hr. destruct a as (c,w).
  destruct (offers_mirrorN M N c w r Hr) as (w0 & r0 & Hr0).
  destruct (lts_in_value_swap (g (mirrorN M N)) (ActIn (c,w0)) r0 Hr0 c w0 w eq_refl)
    as (r1 & Hr1).
  eapply (@lts_refuses_spec2 (proc * MO (ExtAct TypeOfActions)) _ _ _
            ((g (mirrorN M N)) ▷ m) τ); [ | exact Hst ].
  apply gmultiset_disj_union_difference' in Hin.
  rewrite Hin. eexists. apply fw_tau_deliver. exact Hr1.
Qed.

(** ** The same certificate at a LOADED buffer, from the CONFIGURATION hypothesis

    [bigsum_certificate] needs the *bare* [g M ⊑ₘᵤₛₜᵢ g N], which
    [VACCS_NormalForm.msgs_cancel] only supplies when the left
    configuration is τ-stable.  This variant takes the configuration
    hypothesis directly, so it says something in the **unstable** case —
    the one the whole matching argument is still missing.

    The route is the same three moves, one level up: [bigsum_below_M]
    lifted by [must_i_par_compat_r] puts the big sum below [g N] *at the
    bag*, [certificate_config] reads the acceptance condition at the
    trace that feeds the surplus, and [Settles_gsum_chans] turns the
    buffer's channels into the mirror's emitted ones.

    ** Its exact scope, and why it does not by itself close Phase A

    It covers precisely the buffers **above** the bag, [m ⊎ bag l].  That
    is not an artefact: [certificate_config] reads [bhv_pre_cond2] at a
    trace of *inputs*, and feeding is reversible
    ([VACCS_Cond2.fw_feed_inv_list]) — a run over [feed k] from
    [g M ▷ bag l] is a run over [ε] from [g M ▷ (bag k ⊎ bag l)], which is
    exactly what [Settles] asks for.  **Emission is not reversible**: a run
    that emits cannot be replayed from the smaller buffer, the message
    having left the system.

    So a [SettleSim] built on this certificate is stuck the moment the
    right-hand side emits a message of [bag l] — it leaves the cone, and
    below the bag no certificate is available.  Recorded here rather than
    only in the plan file, because it is the exact residue of the
    unstable-left gap: *the certificate holds on the cone above the bag
    and the simulation escapes it downwards*. *)

Lemma bigsum_certificate_config : forall (M N : gproc) (l : list TypeOfActions),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  forall m, OutOnly m ->
  ((g (mirrorN M N)) ▷ (m ⊎ bag l)) ↛ ->
  Settles (emits ((g (mirrorN M N)) ▷ (m ⊎ bag l)))
          ((g ((ext M (guardsN N)) + (mirrorN M N))) ▷ (m ⊎ bag l)).
Proof.
  intros M N l HM HN HstN Hsem m Hout Hst.
  assert (HB : gStatic ((ext M (guardsN N)) + (mirrorN M N)))
    by (apply bigsum_gStatic; assumption).
  assert (Hbn : (msgs l ‖ g ((ext M (guardsN N)) + (mirrorN M N)))
                  ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)).
  { intros t Ht. apply Hsem.
    eapply must_i_par_compat_r; [ apply bigsum_below_M; exact HstN | exact Ht ]. }
  apply (Settles_gsum_chans ((ext M (guardsN N)) + (mirrorN M N)) (mirrorN M N)).
  eapply certificate_config;
    [ exact HB | exact HN | exact HstN | exact Hbn | exact Hout | ].
  intros a Hin r Hr. destruct a as (c,w).
  destruct (offers_mirrorN M N c w r Hr) as (w0 & r0 & Hr0).
  destruct (lts_in_value_swap (g (mirrorN M N)) (ActIn (c,w0)) r0 Hr0 c w0 w eq_refl)
    as (r1 & Hr1).
  eapply (@lts_refuses_spec2 (proc * MO (ExtAct TypeOfActions)) _ _ _
            ((g (mirrorN M N)) ▷ (m ⊎ bag l)) τ); [ | exact Hst ].
  apply gmultiset_disj_union_difference' in Hin.
  rewrite Hin. eexists. apply fw_tau_deliver. exact Hr1.
Qed.

(** ** …and where it is FREE: buffers the left cannot touch

    The certificate has a large trivial region, and isolating it narrows
    the residue considerably.  A guarded sum settles at itself when it
    can do nothing ([Settles_gsum_stable]), and [settles_union] adds
    summands on the left of a [+] provided the added part is stable at
    that buffer.  So whenever [M] refuses every channel of the buffer,
    the big sum is stable there and the certificate costs **nothing** —
    no semantics, no drain, no hypothesis about the bag.

    Combined with the two positive results, the certificate for the big
    sum is now open only on buffers that are simultaneously

    - carrying a channel [M] offers and [N] refuses (a **surplus**
      channel — otherwise [bigsum_certificate_free] applies, the mirror
      being stable there by hypothesis), and
    - **not** above the bag (otherwise [bigsum_certificate_config]
      applies).

    That is the exact residue, and [VACCS_NormalForm.surplus_settles_drain]
    is what would cover it, at the price of the drain condition. *)

Lemma ext_no_input : forall (M K : gproc) (a : TypeOfActions),
  (forall r, ~ lts (g M) (ActExt (ActIn a)) r) ->
  forall r, ~ lts (g (ext M K)) (ActExt (ActIn a)) r.
Proof.
  induction M as [ | | c P | P | M1 IH1 M2 IH2 ]; intros K a Hst r Hl; simpl in Hl.
  - inversion Hl.
  - inversion Hl.
  - inversion Hl; subst. eapply Hst. apply lts_input.
  - inversion Hl.
  - inversion Hl; subst.
    + eapply IH1; [ | eassumption ]. intros r' Hr'. eapply Hst. apply lts_choiceL. exact Hr'.
    + eapply IH2; [ | eassumption ]. intros r' Hr'. eapply Hst. apply lts_choiceR. exact Hr'.
Qed.

Lemma bigsum_certificate_free : forall (M N : gproc) (K : MO (ExtAct TypeOfActions)),
  (forall p, ~ lts (g M) τ p) ->
  ((g (mirrorN M N)) ▷ K) ↛ ->
  (forall a, ActOut a ∈ K -> forall r, ~ lts (g M) (ActExt (ActIn a)) r) ->
  Settles (emits ((g (mirrorN M N)) ▷ K))
          ((g ((ext M (guardsN N)) + (mirrorN M N))) ▷ K).
Proof.
  intros M N K HstM Hst Hnoc.
  apply (Settles_gsum_chans ((ext M (guardsN N)) + (mirrorN M N)) (mirrorN M N)).
  apply settles_union.
  - apply Settles_gsum_stable. exact Hst.
  - apply fw_stable_iff. split; [ apply ext_no_tau; exact HstM | ].
    intros a Hin q Hq. eapply ext_no_input; [ | exact Hq ]. apply Hnoc. exact Hin.
Qed.

(** * PHASE A DIRECTLY, BY A SETTLING SIMULATION — no copycats, no big sum

    Every route to Phase A so far has gone through the big sum
    [ext M (guardsN N) + mirrorN M N]: add a sum of copycats
    ([ax_ccat_r]), flatten with the expansion law, then restrict away the
    surplus.  That construction has a cost the drain analysis makes
    precise — the mirror's guards are *copycats*, which **re-emit** the
    message they consumed, so [VACCS_NormalForm.drain_forced_of_no_output]
    does not apply to it and the certificate is unavailable below the bag.

    [ax_settle_sim] makes the detour unnecessary.  Phase A is an
    inequation between two **configurations**, and the rule proves such
    inequations from any [SettleSim] — so the mirror can be compared with
    [g M] *directly*, at the forwarder, with no intermediate term.

    ** The relation, and why it needs no [≡*]

    Three families, and the states are pinned exactly:

    - [F0] — before the mirror commits: [g M ▷ K] versus [mirror ▷ K].
    - [F1] — after it commits — **at most once**, guarded choice committing,
      so the mirror fires and is gone: the right holds the message *in
      its process*, the left still has it *in its buffer* —
      [p ▷ ({a} ⊎ K)] versus [(p ‖ a-message) ▷ K].  This is the
      syntactic shadow of [VACCS_Cond2.fw_msg_swap]: a pending output is
      part of the configuration, not of the process, and may sit on
      either side.
    - [F2] — after the message leaves: [p ▷ K] versus [(p ‖ 𝟘) ▷ K].

    [F2] is what keeps [≡*] out of the relation.  Emitting the message
    turns the right into [p ‖ 𝟘], which is *not* [p]; rather than closing
    the relation under structural congruence — which would drag
    [Congruence_Respects_Transition] through all three clauses — the
    residual [𝟘] is simply carried, and it is inert
    ([lts_par_nil_inv]), so the family is closed.

    ** What each clause costs

    Both step clauses are pure case analysis on [fw_tau_shape] /
    [fw_ext_shape] and the two parallel-inversion lemmas; the mirror
    committing lands in [F1] whether it was fed by a *delivery* (the left
    answers with **no step at all** — the message it holds is the one the
    right just moved) or by an *environment input* (the left absorbs it
    into its buffer).  And [F1]/[F2]'s stable clauses are **free**: the
    right's stability forces the left's, and the two emit on exactly the
    same channels, the message contributing its own either way.

    So the *entire* semantic content of Phase A is [F0]'s stable clause —
    the certificate [Settles (chans K) (g M ▷ K)] — and it is now about
    **[g M] itself**, not about a construction.  Its three known regions:
    free when [M] refuses [chans K] ([VACCS_Cond2.Settles_gsum_stable]),
    supplied by [VACCS_NormalForm.certificate_config] above the bag, and
    by [VACCS_NormalForm.surplus_settles_drain] below it — where the
    remaining obstruction, regeneration, is now a property of [M]'s own
    continuations rather than an artefact of the mirror. *)

Lemma mirrorN_lts_in_shape : forall (P : proc) (N : gproc) c v r,
  lts (g (mirrorN P N)) (ActExt (ActIn (c,v))) r ->
  r = (P ‖ (c ! v • 𝟘)).
Proof.
  intros P N. induction N as [ | | d Q | Q | N1 IH1 N2 IH2 ]; intros c v r Hl;
    simpl in Hl; inversion Hl; subst.
  - unfold fwdg. simpl. f_equal. apply NewVar_subst_cancel.
  - eapply IH1. eassumption.
  - eapply IH2. eassumption.
Qed.

Lemma lts_par_nil_inv : forall (p : proc) a z,
  lts (p ‖ (g 𝟘 : proc)) a z -> exists p', z = (p' ‖ (g 𝟘 : proc)) /\ lts p a p'.
Proof.
  intros p a z Hl. inversion Hl; subst;
    try (exfalso; match goal with H : lts (g gpr_nil) _ _ |- _ => inversion H end).
  - eexists. split; [ reflexivity | assumption ].
Qed.

Lemma lts_par_msg_inv : forall (p : proc) (a : TypeOfActions) al z,
  lts (p ‖ ((fst a) ! (snd a) • 𝟘)) al z ->
    (exists p', z = (p' ‖ ((fst a) ! (snd a) • 𝟘)) /\ lts p al p')
  \/ (al = ActExt (ActOut a) /\ z = (p ‖ (g 𝟘 : proc)))
  \/ (exists p', al = τ /\ z = (p' ‖ (g 𝟘 : proc)) /\ lts p (ActExt (ActIn a)) p').
Proof.
  intros p a al z Hl. destruct a as (c,v). simpl in Hl. inversion Hl; subst;
    try (exfalso;
         match goal with H : lts ((_ ! _ • 𝟘) : proc) (ActExt (ActIn _)) _ |- _ =>
           inversion H end).
  - right. right. inversion H1; subst. eexists.
    split; [ reflexivity | split; [ reflexivity | exact H4 ] ].
  - left. eexists. split; [ reflexivity | exact H3 ].
  - right. left. inversion H3; subst. split; reflexivity.
Qed.

Lemma outonly_of_bag : forall l, OutOnly (bag l).
Proof.
  induction l as [|a l IH]; simpl; [ apply OutOnly_empty | apply OutOnly_add; exact IH ].
Qed.

Definition mirrorRel (P : proc) (N : gproc)
  : (proc * MO (ExtAct TypeOfActions)) -> (proc * MO (ExtAct TypeOfActions)) -> Prop :=
  fun x y =>
    (exists K, OutOnly K /\ x = (P ▷ K) /\ y = ((g (mirrorN P N)) ▷ K))
    \/ (exists p a K, OutOnly K /\ x = (p ▷ ({[+ ActOut a +]} ⊎ K))
                   /\ y = ((p ‖ ((fst a) ! (snd a) • 𝟘)) ▷ K))
    \/ (exists p K, OutOnly K /\ x = (p ▷ K) /\ y = ((p ‖ (g 𝟘 : proc)) ▷ K)).

Lemma mirrorRel_tau : forall (P : proc) (N : gproc), (forall z, ~ lts (g N) τ z) ->
  forall x y y', mirrorRel P N x y -> y ⟶ y' ->
  exists x', x ⟹[[]] x' /\ mirrorRel P N x' y'.
Proof.
  intros P N HstN x y y' HR Hl.
  destruct HR as [ (K & HoK & Ex & Ey) | [ (p & a & K & HoK & Ex & Ey) | (p & K & HoK & Ex & Ey) ] ].
  - subst x y. destruct (fw_tau_shape (g (mirrorN P N)) K y' Hl) as [HA|HB].
    + destruct HA as (p' & Hp' & _). exfalso. eapply mirrorN_no_tau; eassumption.
    + destruct HB as (b & p' & K' & HK & Hp' & E). subst y'.
      destruct b as (c,v).
      pose proof (mirrorN_lts_in_shape P N c v p' Hp') as Es. subst p'.
      exists (P ▷ K). split; [ apply wt_nil | ].
      right. left. exists P, (c,v), K'.
      split; [ rewrite HK in HoK; eapply OutOnly_sub; exact HoK | ].
      split; [ | reflexivity ]. rewrite HK. reflexivity.
  - subst x y. destruct (fw_tau_shape (p ‖ ((fst a) ! (snd a) • 𝟘)) K y' Hl) as [HA|HB].
    + destruct HA as (p'' & Hp'' & E). subst y'.
      destruct (lts_par_msg_inv p a τ p'' Hp'')
        as [ (p1 & Ez & Hp1) | [ (Ea & _) | (p1 & _ & Ez & Hp1) ] ].
      * subst p''. exists (p1 ▷ ({[+ ActOut a +]} ⊎ K)). split.
        -- eapply wt_tau; [ apply fw_tau_left; exact Hp1 | apply wt_nil ].
        -- right. left. exists p1, a, K. split; [ exact HoK | split; reflexivity ].
      * discriminate Ea.
      * subst p''. exists (p1 ▷ K). split.
        -- eapply wt_tau; [ apply fw_tau_deliver; exact Hp1 | apply wt_nil ].
        -- right. right. exists p1, K. split; [ exact HoK | split; reflexivity ].
    + destruct HB as (b & p'' & K' & HK & Hp'' & E). subst y'.
      destruct (lts_par_msg_inv p a (ActExt (ActIn b)) p'' Hp'')
        as [ (p1 & Ez & Hp1) | [ (Ea & _) | (p1 & Ea & _ & _) ] ].
      * subst p''. exists (p1 ▷ ({[+ ActOut a +]} ⊎ K')). split.
        -- eapply wt_tau; [ | apply wt_nil ].
           replace ({[+ ActOut a +]} ⊎ K) with ({[+ ActOut b +]} ⊎ ({[+ ActOut a +]} ⊎ K')).
           ++ apply fw_tau_deliver. exact Hp1.
           ++ rewrite HK. rewrite !(assoc_L (@disj_union (MO (ExtAct TypeOfActions)) _)).
              f_equal. apply (comm_L (@disj_union (MO (ExtAct TypeOfActions)) _)).
        -- right. left. exists p1, a, K'.
           split; [ rewrite HK in HoK; eapply OutOnly_sub; exact HoK | split; reflexivity ].
      * discriminate Ea.
      * discriminate Ea.
  - subst x y. destruct (fw_tau_shape (p ‖ (g 𝟘 : proc)) K y' Hl) as [HA|HB].
    + destruct HA as (p'' & Hp'' & E). subst y'.
      destruct (lts_par_nil_inv p τ p'' Hp'') as (p1 & Ez & Hp1). subst p''.
      exists (p1 ▷ K). split.
      * eapply wt_tau; [ apply fw_tau_left; exact Hp1 | apply wt_nil ].
      * right. right. exists p1, K. split; [ exact HoK | split; reflexivity ].
    + destruct HB as (b & p'' & K' & HK & Hp'' & E). subst y'.
      destruct (lts_par_nil_inv p (ActExt (ActIn b)) p'' Hp'') as (p1 & Ez & Hp1). subst p''.
      exists (p1 ▷ K'). split.
      * eapply wt_tau; [ | apply wt_nil ]. rewrite HK. apply fw_tau_deliver. exact Hp1.
      * right. right. exists p1, K'.
        split; [ rewrite HK in HoK; eapply OutOnly_sub; exact HoK | split; reflexivity ].
Qed.

Lemma mirrorRel_ext : forall (P : proc) (N : gproc),
  forall x y mu y', mirrorRel P N x y -> y ⟶[mu] y' ->
  exists x', x ⟹{mu} x' /\ mirrorRel P N x' y'.
Proof.
  intros P N x y mu y' HR Hl.
  destruct HR as [ (K & HoK & Ex & Ey) | [ (p & a & K & HoK & Ex & Ey) | (p & K & HoK & Ex & Ey) ] ].
  - subst x y. destruct (fw_ext_shape (g (mirrorN P N)) K mu y' Hl) as [HA|[HB|HC]].
    + destruct HA as (p' & Hp' & E). subst y'.
      destruct mu as [(c,v)|(c,v)]; [ | exfalso; eapply gsum_no_output; exact Hp' ].
      pose proof (mirrorN_lts_in_shape P N c v p' Hp') as Es. subst p'.
      exists (P ▷ ({[+ ActOut (c,v) +]} ⊎ K)). split.
      * eapply wt_act; [ apply fw_input_always | apply wt_nil ].
      * right. left. exists P, (c,v), K. split; [ exact HoK | split; reflexivity ].
    + destruct HB as (b & Hb & E). subst mu y'.
      exists (P ▷ ({[+ ActOut b +]} ⊎ K)). split.
      * eapply wt_act; [ apply fw_input_always | apply wt_nil ].
      * left. exists ({[+ ActOut b +]} ⊎ K).
        split; [ apply OutOnly_add; exact HoK | split; reflexivity ].
    + destruct HC as (b & K' & Hb & HK & E). subst mu y'.
      exists (P ▷ K'). split.
      * eapply wt_act; [ | apply wt_nil ]. rewrite HK. apply fw_emit.
      * left. exists K'.
        split; [ rewrite HK in HoK; eapply OutOnly_sub; exact HoK | split; reflexivity ].
  - subst x y.
    destruct (fw_ext_shape (p ‖ ((fst a) ! (snd a) • 𝟘)) K mu y' Hl) as [HA|[HB|HC]].
    + destruct HA as (p'' & Hp'' & E). subst y'.
      destruct (lts_par_msg_inv p a (ActExt mu) p'' Hp'')
        as [ (p1 & Ez & Hp1) | [ (Ea & Ez) | (p1 & Ea & _ & _) ] ].
      * subst p''. exists (p1 ▷ ({[+ ActOut a +]} ⊎ K)). split.
        -- eapply wt_act; [ apply fw_ext_left; exact Hp1 | apply wt_nil ].
        -- right. left. exists p1, a, K. split; [ exact HoK | split; reflexivity ].
      * injection Ea as Ea. subst mu p''. exists (p ▷ K). split.
        -- eapply wt_act; [ apply fw_emit | apply wt_nil ].
        -- right. right. exists p, K. split; [ exact HoK | split; reflexivity ].
      * discriminate Ea.
    + destruct HB as (b & Hb & E). subst mu y'.
      exists (p ▷ ({[+ ActOut a +]} ⊎ ({[+ ActOut b +]} ⊎ K))). split.
      * eapply wt_act; [ | apply wt_nil ].
        replace ({[+ ActOut a +]} ⊎ ({[+ ActOut b +]} ⊎ K))
           with ({[+ ActOut b +]} ⊎ ({[+ ActOut a +]} ⊎ K)).
        -- apply fw_input_always.
        -- rewrite !(assoc_L (@disj_union (MO (ExtAct TypeOfActions)) _)).
           f_equal. apply (comm_L (@disj_union (MO (ExtAct TypeOfActions)) _)).
      * right. left. exists p, a, ({[+ ActOut b +]} ⊎ K).
        split; [ apply OutOnly_add; exact HoK | split; reflexivity ].
    + destruct HC as (b & K' & Hb & HK & E). subst mu y'.
      exists (p ▷ ({[+ ActOut a +]} ⊎ K')). split.
      * eapply wt_act; [ | apply wt_nil ].
        replace ({[+ ActOut a +]} ⊎ K)
           with ({[+ ActOut b +]} ⊎ ({[+ ActOut a +]} ⊎ K')).
        -- apply fw_emit.
        -- rewrite HK. rewrite !(assoc_L (@disj_union (MO (ExtAct TypeOfActions)) _)).
           f_equal. apply (comm_L (@disj_union (MO (ExtAct TypeOfActions)) _)).
      * right. left. exists p, a, K'.
        split; [ rewrite HK in HoK; eapply OutOnly_sub; exact HoK | split; reflexivity ].
  - subst x y. destruct (fw_ext_shape (p ‖ (g 𝟘 : proc)) K mu y' Hl) as [HA|[HB|HC]].
    + destruct HA as (p'' & Hp'' & E). subst y'.
      destruct (lts_par_nil_inv p (ActExt mu) p'' Hp'') as (p1 & Ez & Hp1). subst p''.
      exists (p1 ▷ K). split.
      * eapply wt_act; [ apply fw_ext_left; exact Hp1 | apply wt_nil ].
      * right. right. exists p1, K. split; [ exact HoK | split; reflexivity ].
    + destruct HB as (b & Hb & E). subst mu y'.
      exists (p ▷ ({[+ ActOut b +]} ⊎ K)). split.
      * eapply wt_act; [ apply fw_input_always | apply wt_nil ].
      * right. right. exists p, ({[+ ActOut b +]} ⊎ K).
        split; [ apply OutOnly_add; exact HoK | split; reflexivity ].
    + destruct HC as (b & K' & Hb & HK & E). subst mu y'.
      exists (p ▷ K'). split.
      * eapply wt_act; [ | apply wt_nil ]. rewrite HK. apply fw_emit.
      * right. right. exists p, K'.
        split; [ rewrite HK in HoK; eapply OutOnly_sub; exact HoK | split; reflexivity ].
Qed.

Lemma mirrorRel_stable : forall (P : proc) (N : gproc),
  (forall K, OutOnly K -> ((g (mirrorN P N)) ▷ K) ↛ -> Settles (chans K) (P ▷ K)) ->
  forall x y, mirrorRel P N x y -> y ↛ -> Settles (emits y) x.
Proof.
  intros P N Hcert x y HR Hst.
  destruct HR as [ (K & HoK & Ex & Ey) | [ (p & a & K & HoK & Ex & Ey) | (p & K & HoK & Ex & Ey) ] ]; subst x y.
  - eapply Settles_mono; [ | apply Hcert; assumption ].
    intros d Hd. apply emits_gsum_iff. exact Hd.
  - pose proof (no_step_of_stable _ Hst) as Hns.
    apply fw_stable_iff in Hns as (Hpm & Hrefus).
    assert (Hptau : forall z, ~ lts p τ z).
    { intros z Hz. eapply Hpm. eapply lts_parL. exact Hz. }
    assert (Hpa : forall z, ~ lts p (ActExt (ActIn a)) z).
    { intros z Hz. destruct a as (c,v). eapply Hpm.
      eapply lts_comR; [ apply lts_output | exact Hz ]. }
    apply Settles_here.
    + apply stable_of_no_step. apply fw_stable_iff. split; [ exact Hptau | ].
      intros b Hin q Hq.
      apply gmultiset_elem_of_disj_union in Hin as [Hin|Hin].
      * apply gmultiset_elem_of_singleton in Hin. injection Hin as Hin. subst b.
        eapply Hpa. exact Hq.
      * eapply Hrefus; [ exact Hin | eapply lts_parL; exact Hq ].
    + intros d w r Hr.
      destruct (fw_ext_shape p ({[+ ActOut a +]} ⊎ K) (ActOut (d,w)) r Hr) as [HA|[HB|HC]].
      * destruct HA as (p' & Hp' & _). exists w. eexists.
        apply fw_ext_left. eapply lts_parL. exact Hp'.
      * destruct HB as (b & Hb & _). discriminate Hb.
      * destruct HC as (b & K'' & Hb & HK & _). injection Hb as Hb. subst b.
        assert (Hin : ActOut (d,w) ∈ ({[+ ActOut a +]} ⊎ K)).
        { rewrite HK. apply gmultiset_elem_of_disj_union. left.
          apply gmultiset_elem_of_singleton. reflexivity. }
        apply gmultiset_elem_of_disj_union in Hin as [Hin|Hin].
        -- apply gmultiset_elem_of_singleton in Hin. injection Hin as Hin. subst a.
           exists w. eexists. apply fw_ext_left. eapply lts_parR. apply lts_output.
        -- exists w. apply fw_emit_of_mem. exact Hin.
  - pose proof (no_step_of_stable _ Hst) as Hns.
    apply fw_stable_iff in Hns as (Hpm & Hrefus).
    apply Settles_here.
    + apply stable_of_no_step. apply fw_stable_iff. split.
      * intros z Hz. eapply Hpm. eapply lts_parL. exact Hz.
      * intros b Hin q Hq. eapply Hrefus; [ exact Hin | eapply lts_parL; exact Hq ].
    + intros d w r Hr.
      destruct (fw_ext_shape p K (ActOut (d,w)) r Hr) as [HA|[HB|HC]].
      * destruct HA as (p' & Hp' & _). exists w. eexists.
        apply fw_ext_left. eapply lts_parL. exact Hp'.
      * destruct HB as (b & Hb & _). discriminate Hb.
      * destruct HC as (b & K'' & Hb & HK & _). injection Hb as Hb. subst b.
        exists w. apply fw_emit_of_mem. rewrite HK.
        apply gmultiset_elem_of_disj_union. left.
        apply gmultiset_elem_of_singleton. reflexivity.
Qed.

Theorem mirrorRel_settle_sim : forall (P : proc) (N : gproc), (forall z, ~ lts (g N) τ z) ->
  (forall K, OutOnly K -> ((g (mirrorN P N)) ▷ K) ↛ -> Settles (chans K) (P ▷ K)) ->
  SettleSim (mirrorRel P N).
Proof.
  intros P N HstN Hcert. split; [ | split ].
  - apply mirrorRel_tau. exact HstN.
  - apply mirrorRel_ext.
  - apply mirrorRel_stable. exact Hcert.
Qed.

(** Phase A at a configuration, from the certificate for [g M] alone. *)

(** **The residue, stated where it lives.**  The certificate below is the
    only semantic content of Phase A, and by the general objection
    recorded at [VACCS_Cond2.set_sim_clauses_hold_for_copre] it cannot be
    weakened to an existential over a set: a simulation premise is
    non-vacuous only if it pins the left to a single state.  So it must
    hold at *this* [P].

    Worth recording as evidence rather than as a claim: in every instance
    examined by hand, the certificate and the semantic hypothesis fail
    **together**.  Taking [N := 𝟘] (so the mirror is stable at every
    buffer) and [K := {c!v}]:

    - [P := ccat c] settles (deliver, re-emit on [c ∈ chans K]) — and
      [ccat c ⊑ₘᵤₛₜᵢ 𝟘] holds;
    - [P := g (c ? (e!y•𝟘))] does not (the delivery escapes to [e]) —
      and neither does the hypothesis, since [P] passes the τ-stuck
      non-good client [(c!v•𝟘) ‖ (e?①)];
    - [P := g (c ? 𝟘)] settles, and the hypothesis holds
      ([VACCS_Bad.unstable_delivery_below_nil], exercised end to end in
      [VACCS_AxExamples.ax_swallow_split]).

    That coincidence is what a proof would have to explain: from a
    *failure* to settle, build a τ-stuck non-good client that the left
    passes and the right fails.  That construction is the remaining
    work. *)

Theorem ax_phaseA_direct : forall (P : proc) (N : gproc) (l : list TypeOfActions),
  Static P -> gStatic N -> (forall z, ~ lts (g N) τ z) ->
  (forall K, OutOnly K -> ((g (mirrorN P N)) ▷ K) ↛ -> Settles (chans K) (P ▷ K)) ->
  ax_pre (msgs l ‖ P) (msgs l ‖ g (mirrorN P N)).
Proof.
  intros P N l HM HN HstN Hcert.
  apply (ax_settle_sim l l P (g (mirrorN P N)) (mirrorRel P N)
           HM (static_g _ (mirrorN_gStatic P N HM HN))).
  - apply mirrorRel_settle_sim; assumption.
  - left. exists (bag l). split; [ apply outonly_of_bag | split; reflexivity ].
Qed.

(** And the certificate is available outright when [M] itself never
    emits — by [VACCS_NormalForm.certificate_no_regeneration], which is
    where [drain_forced_of_no_output] is cashed in.  The refusal side
    condition comes from the mirror's stability: a mirror guard sits on
    every channel [N] offers ([offers_mirrorN]), and an input's
    availability is value-independent ([lts_in_value_swap]), so a message
    on such a channel would give the mirror a [τ]. *)

Theorem phaseA_config_no_regeneration : forall (M N : gproc) (l : list TypeOfActions),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (forall z, ~ lts (g M) τ z) ->
  (forall r q, ((g M) : proc) ⟹[r] q -> bag (ins r) ⊆ bag (outs r) -> ins r = []) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  ax_pre (msgs l ‖ g M) (msgs l ‖ g (mirrorN M N)).
Proof.
  intros M N l HM HN HstN HstM Hno Hsem.
  apply ax_phaseA_direct; [ apply static_g; exact HM | exact HN | exact HstN | ].
  intros K Hout Hst.
  eapply certificate_no_regeneration; try eassumption.
  intros a Hin r Hr. destruct a as (c,w).
  destruct (offers_mirrorN M N c w r Hr) as (w0 & r0 & Hr0).
  destruct (lts_in_value_swap (g (mirrorN M N)) (ActIn (c,w0)) r0 Hr0 c w0 w eq_refl)
    as (r1 & Hr1).
  eapply (@lts_refuses_spec2 (proc * MO (ExtAct TypeOfActions)) _ _ _
            ((g (mirrorN M N)) ▷ K) τ); [ | exact Hst ].
  apply gmultiset_disj_union_difference' in Hin.
  rewrite Hin. eexists. apply fw_tau_deliver. exact Hr1.
Qed.

Theorem restrict_bigsum : forall (M N : gproc), gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N) ->
  (g ((ext M (guardsN N)) + (mirrorN M N))) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g (mirrorN M N)).
Proof.
  intros M N HM HN HstN Hsem.
  apply restrict_by_settle_out;
    [ apply bigsum_gStatic; assumption
    | apply mirrorN_gStatic; [ apply static_g; exact HM | exact HN ]
    | intros al q Hl; apply lts_choiceR; exact Hl
    | apply bigsum_certificate; assumption ].
Qed.

(** * PHASE A, AS A DERIVATION — no [gGuardsIn], no [BadK]

    [ax_mirror_reach] reaches the whole expansion, [ax_restrict_settle]
    cuts it down to the mirror, and the certificate is
    [bigsum_certificate].  Nothing is assumed about which channels [M]
    offers. *)

Theorem ax_phaseA_settle : forall (M N : gproc), gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N) ->
  ax_pre (g M) (g (mirrorN M N)).
Proof.
  intros M N HM HN HstN Hsem.
  eapply ax_trans; [ apply ax_mirror_reach; exact HstN | ].
  apply ax_restrict_settle.
  - intros al q Hl. apply lts_choiceR. exact Hl.
  - apply bigsum_gStatic; assumption.
  - apply mirrorN_gStatic; [ apply static_g; assumption | assumption ].
  - apply bigsum_certificate; assumption.
Qed.

(** * THE STABLE CASE OF COMPLETENESS, with only the recursion left

    Compare [ax_below_stable_sum_full] (needs [gGuardsIn]) and
    [ax_below_stable_sum_nogg] (needs a [BadK] certificate).  Here the
    only hypotheses beyond [Static]-ness and stability of [N] are the
    semantic one and the recursive call. *)

Theorem ax_below_stable_sum_clean : forall (M N : gproc), gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g N) ->
  (forall c v Q', lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ((c ! v • 𝟘) ‖ (g M)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ Q' -> ax_pre ((c ! v • 𝟘) ‖ (g M)) Q') ->
  ax_pre (g M) (g N).
Proof.
  intros M N HM HN HstN Hsem Hrec.
  eapply ax_below_stable_sum; [ exact HstN | | exact Hsem | exact Hrec ].
  apply ax_phaseA_settle; assumption.
Qed.

(** ** THE STABLE CASE AT THE FULL NORMAL FORM

    The message layer costs nothing once the bag can be cancelled.
    [VACCS_NormalForm.msgs_cancel] removes a common bag from a *stable*
    configuration, after which the whole mirror / restrict / match chain
    above applies to the bare sums and [ax_par] carries the result back
    under [msgs l ‖ ·]; [ax_res_n] then carries it under the restriction
    block, so the statement holds at [NF n l M] — the forwarder state
    that VACCS normal forms actually have.

    Note what is *not* assumed: nothing about which channels [M] offers
    (that went with [ax_restrict_settle]), and nothing relating the two
    bags (they are literally the same, which for two stable
    configurations is forced — [VACCS_NormalForm.bags_agree]). *)

Theorem ax_below_stable_config : forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (forall z, ~ ((g M ▷ bag l) ⟶ z)) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  (forall c v Q', lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ((c ! v • 𝟘) ‖ (g M)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ Q' -> ax_pre ((c ! v • 𝟘) ‖ (g M)) Q') ->
  ax_pre (msgs l ‖ g M) (msgs l ‖ g N).
Proof.
  intros l M N HM HN HstN HstM Hpre Hrec.
  apply ax_par; [ apply ax_refl | ].
  apply ax_below_stable_sum_clean; try assumption.
  eapply msgs_cancel; eassumption.
Qed.

Theorem ax_below_stable_NF : forall (n : nat) (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (forall z, ~ ((g M ▷ bag l) ⟶ z)) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  (forall c v Q', lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ((c ! v • 𝟘) ‖ (g M)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ Q' -> ax_pre ((c ! v • 𝟘) ‖ (g M)) Q') ->
  ax_pre (NF n l M) (NF n l N).
Proof.
  intros n l M N HM HN HstN HstM Hpre Hrec.
  unfold NF. apply ax_res_n. apply ax_below_stable_config; assumption.
Qed.

(** *** CAVEAT: the recursive premise sits at the WRONG LEVEL for the measure

    [ax_below_stable_NF]'s recursive premise is inherited from the
    bare-sum theorem through [msgs_cancel], [ax_par] and [ax_res_n], so it
    is stated about `(c!v•𝟘) ‖ g M` versus a **bare** continuation `Q'` of
    `N` — the wrapper `Ѵⁿ (msgs l ‖ ·)` sits outside it.  That level is
    forced: it is what [ax_fwd_match]'s omega rule consumes.

    The outer measure, however, lives at the *wrapped* level.
    [VACCS_Descent.in_summand_reduct] says the normal form's transition
    target `Ѵⁿ (msgs l ‖ P^v)` is `⊢`-equal to a **strictly smaller**
    `Static` reduct of the original process — but nothing bounds
    `size (P^v)` itself, and normalisation is not size-decreasing, so the
    bare continuation need not be smaller than the process one started
    from.

    So [completeness_from_step]'s recursion cannot be fed from
    [ax_below_stable_NF] as the two are currently stated.  Closing this
    needs either the stable-sum theorem restated with its recursive
    premise at the wrapped level, or a measure that descends at the bare
    level.  Recorded here rather than in the plan file because it is a
    property of *these two statements*. *)

(** ** Chasing internal moves: the leaves of a configuration

    [ax_below_stable_config] needs its left stable, and that hypothesis is
    **necessary** — for an unstable configuration a common bag cannot be
    cancelled, because the left can regenerate a drained message from a
    continuation.  What is available instead is to *chase the deliveries*:
    an internal run is a chain of [ax_tau_step]s, and on the [Static]
    fragment every configuration reaches a stable one.

    Note the direction this can and cannot be used in.  [ax_tau_run] gives
    `⊢ p ⊑ p'`, so composing it with `⊢ p' ⊑ q` yields `⊢ p ⊑ q` — sound,
    and it is how the copycat example
    `(c!v•𝟘) ‖ ((c?(c!v•𝟘)) + (d?(e!y•𝟘))) ⊑ (c!v•𝟘) ‖ 𝟘` is derived.  But
    the semantic side condition `p' ⊑ₘᵤₛₜᵢ q` does **not** follow from
    `p ⊑ₘᵤₛₜᵢ q`: a reduct passes at least what `p` passes, so this is an
    *up*-move, legitimate only when the chosen reduct happens to stay
    below `q`.  With several delivery branches, different branches may be
    needed for different stable states of `q` — the same ∀∃ alternation
    that defeated [Harmless] and [Bad]. *)

Lemma ax_tau_run : forall (p p' : proc), p ⟹[[]] p' -> ax_pre p p'.
Proof.
  intros p p' Hw. remember (nil : trace (ExtAct TypeOfActions)) as s eqn:Hs.
  induction Hw as [x|s0 x q y Hl Hwt IH|mu s0 x q y Hl Hwt IH].
  - apply ax_refl.
  - eapply ax_trans; [ apply ax_tau_step; exact Hl | apply IH; exact Hs ].
  - discriminate Hs.
Qed.

Lemma ax_below_via_reduct : forall (p p' q : proc),
  p ⟹[[]] p' -> ax_pre p' q -> ax_pre p q.
Proof. intros p p' q Hw H. eapply ax_trans; [ apply ax_tau_run; exact Hw | exact H ]. Qed.

Theorem ax_config_leaf : forall (p : proc), Static p ->
  exists p', p ⟹[[]] p' /\ p' ↛ /\ ax_pre p p' /\ Static p'.
Proof.
  intros p HS.
  destruct (terminate_then_wt_refuses p (Static_terminate p HS)) as (p' & Hw & Hst).
  exists p'. split; [ exact Hw | ]. split; [ exact Hst | ].
  split; [ apply ax_tau_run; exact Hw | ].
  eapply Static_preserved_by_wt; [ exact HS | exact Hw ].
Qed.

(** ** n-ary internal choice: the derivable laws

    [ichoice] itself, [ichoice_gAllTau] and [lts_ichoice] live upstream,
    in [VACCS_Residues], so that a rule of the system can name them; what
    stays here is what mentions [ax_pre].

    [ax_ichoice_glb] is [ax_int_glb] made n-ary; the induction step needs
    [ax_tau_flatten_l] to turn [𝛕•p + 𝛕•(g (ichoice l'))] into
    [𝛕•p + ichoice l'], whose [gAllTau] side condition an [ichoice] tail
    satisfies. *)

Lemma ax_ichoice_glb : forall (l : list proc) (q : proc), l <> nil ->
  (forall p, In p l -> ax_pre q p) -> ax_pre q (g (ichoice l)).
Proof.
  induction l as [|p l IH]; intros q Hne Hall; [ contradiction | ].
  destruct l as [|p2 l2].
  - simpl. apply ax_int_glb; apply Hall; left; reflexivity.
  - eapply ax_trans.
    + apply ax_int_glb with (q1 := p) (q2 := g (ichoice (p2 :: l2))).
      * apply Hall. left. reflexivity.
      * apply IH; [ discriminate | ]. intros r Hr. apply Hall. right. exact Hr.
    + apply (ax_tau_flatten_l (𝛕 • p) (ichoice (p2 :: l2))).
      apply ichoice_gAllTau. discriminate.
Qed.

Lemma ax_ichoice_below : forall (l : list proc) (p : proc), In p l ->
  ax_pre (g (ichoice l)) p.
Proof. intros l p Hin. apply ax_tau_step. apply lts_ichoice. exact Hin. Qed.

(** ** Restriction is FREE when no channel is lost

    [ax_restrict_settle]'s certificate is normally the hard part — it is
    where the semantic hypothesis enters, and where the surplus-guard
    problem lives.  But when the target [M'] still offers **every channel**
    the source offers, the certificate costs nothing: a stable
    [g M' ▷ m] then forces [g M ▷ m] stable too (an input's availability
    is value-independent, [lts_in_value_swap]), and a stable configuration
    whose process is a guarded sum settles at itself, emitting exactly the
    buffer's channels.

    So restriction may always *merge* or *reorder*, and only *dropping a
    channel* needs an argument.  This is the [Settles]-side counterpart of
    [VACCS_Absorb.must_i_restrict_same].

    It is also what makes the "big mirror" route's restriction step free:
    a mirror built over [offers M ∪ offers N] keeps all of [M]'s channels
    by construction, so [g BIG] restricts to it with no semantic input at
    all — the whole difficulty then concentrates in discarding the surplus
    mirror summands afterwards. *)

Lemma certificate_free : forall (M M' : gproc),
  (forall c v p, lts (g M) (ActExt (ActIn (c,v))) p ->
                 exists w q, lts (g M') (ActExt (ActIn (c,w))) q) ->
  (forall p, ~ lts (g M) τ p) ->
  forall m, ((g M') ▷ m) ↛ -> Settles (emits ((g M') ▷ m)) ((g M) ▷ m).
Proof.
  intros M M' Hoff HstM m Hst.
  assert (Hns : forall z, ~ (((g M') ▷ m) ⟶ z)) by (apply no_step_of_stable; exact Hst).
  apply fw_stable_iff in Hns as (Hst1 & Hst2).
  apply Settles_gsum_chans. apply Settles_gsum_stable.
  apply stable_of_no_step. apply fw_stable_iff. split; [ exact HstM | ].
  intros a Ha q Hq. destruct a as (c,v).
  destruct (Hoff c v q Hq) as (w & r & Hr).
  destruct (lts_in_value_swap (g M') (ActIn (c,w)) r Hr c w v eq_refl) as (r2 & Hr2).
  eapply Hst2; [ exact Ha | exact Hr2 ].
Qed.

Lemma ax_restrict_keep : forall (M M' : gproc), gStatic M -> gStatic M' ->
  (forall al q, lts (g M') al q -> lts (g M) al q) ->
  (forall c v p, lts (g M) (ActExt (ActIn (c,v))) p ->
                 exists w q, lts (g M') (ActExt (ActIn (c,w))) q) ->
  (forall p, ~ lts (g M) τ p) ->
  ax_pre (g M) (g M').
Proof.
  intros M M' HM HM' Hsub Hoff HstM.
  apply ax_restrict_settle; try assumption.
  intros m _ Hst. apply certificate_free; assumption.
Qed.

(** ** Removing a duplicated residue — where [ax_sub_tau] and
       [ax_restrict_keep] meet

    [(A + R) + (B + R)] and [(A + B) + R] have *literally the same*
    transitions, so they are must-equivalent; but a **derivation** needs a
    rule, and the two available ones are complementary rather than
    general: [ax_restrict_keep] wants the bigger sum τ-stable,
    [ax_sub_tau] wants the smaller one to have a τ.  A case split on
    [lts_dec] covers both, and nothing else is needed.

    This is the first place the two meet, and it is what makes the
    *context* form of the split law derivable (see
    [VACCS_Canonical.ax_input_split_r] for the bare form). *)

Lemma dup_sub : forall (A B R : gproc) al q,
  lts ((g ((A + B) + R)) : proc) al q -> lts ((g ((A + R) + (B + R))) : proc) al q.
Proof.
  intros A B R al q Hl. inversion Hl; subst.
  - match goal with H : lts (g (A + B)) _ _ |- _ => inversion H; subst end.
    + apply lts_choiceL. apply lts_choiceL. assumption.
    + apply lts_choiceR. apply lts_choiceL. assumption.
  - apply lts_choiceL. apply lts_choiceR. assumption.
Qed.

Lemma dup_sub_rev : forall (A B R : gproc) al q,
  lts ((g ((A + R) + (B + R))) : proc) al q -> lts ((g ((A + B) + R)) : proc) al q.
Proof.
  intros A B R al q Hl. inversion Hl; subst.
  - match goal with H : lts (g (A + R)) _ _ |- _ => inversion H; subst end.
    + apply lts_choiceL. apply lts_choiceL. assumption.
    + apply lts_choiceR. assumption.
  - match goal with H : lts (g (B + R)) _ _ |- _ => inversion H; subst end.
    + apply lts_choiceL. apply lts_choiceR. assumption.
    + apply lts_choiceR. assumption.
Qed.

Lemma dup_stable : forall (A B R : gproc),
  (forall z, ~ lts ((g ((A + B) + R)) : proc) τ z) ->
  (forall z, ~ lts ((g ((A + R) + (B + R))) : proc) τ z).
Proof.
  intros A B R Hst z Hz. inversion Hz; subst.
  - match goal with H : lts (g (A + R)) _ _ |- _ => inversion H; subst end.
    + eapply Hst. apply lts_choiceL. apply lts_choiceL. eassumption.
    + eapply Hst. apply lts_choiceR. eassumption.
  - match goal with H : lts (g (B + R)) _ _ |- _ => inversion H; subst end.
    + eapply Hst. apply lts_choiceL. apply lts_choiceR. eassumption.
    + eapply Hst. apply lts_choiceR. eassumption.
Qed.

Lemma ax_dup_ctx : forall (A B R : gproc), gStatic A -> gStatic B -> gStatic R ->
  ax_pre ((g ((A + R) + (B + R))) : proc) ((g ((A + B) + R)) : proc).
Proof.
  intros A B R HA HB HR.
  destruct (lts_dec ((g ((A + B) + R)) : proc) τ) as [Hst | (z & Hz)].
  - apply ax_restrict_keep.
    + repeat (constructor; try assumption).
    + repeat (constructor; try assumption).
    + apply dup_sub.
    + intros c v p Hl. exists v, p. apply dup_sub_rev. exact Hl.
    + apply dup_stable. exact Hst.
  - apply ax_sub_tau; [ apply dup_sub | exists z; exact Hz ].
Qed.

(** …and hence the split law **with a residue**, which
    [VACCS_Precongruence.must_i_input_distrib_ctx_r] proves sound and no
    rule provides.  It is derivable after all — so the system has no gap
    here either. *)

Theorem ax_input_split_ctx_r : forall (c : ChannelData) (P Q : proc) (R : gproc),
  Static P -> Static Q -> gStatic R ->
  ax_pre ((g ((c ? ((g ((𝛕 • P) + (𝛕 • Q))) : proc)) + R)) : proc)
         ((g (((c ? P) + (c ? Q)) + R)) : proc).
Proof.
  intros c P Q R HP HQ HR.
  eapply ax_trans;
    [ | apply (ax_dup_ctx (c ? P) (c ? Q) R);
        [ constructor; exact HP | constructor; exact HQ | exact HR ] ].
  eapply ax_trans; [ | apply (ax_int_below_ext ((c ? P) + R) ((c ? Q) + R)) ].
  apply ax_int_glb.
  - apply ax_choice_input. intro v. simpl. apply ax_int_l.
  - apply ax_choice_input. intro v. simpl. apply ax_int_r.
Qed.

(** ** PHASE A OVER THE UNION OF CHANNELS — with no semantic hypothesis

    Build the mirror over [N + M] instead of [N].  Then the mirror offers
    every channel the expansion offers — [M]'s from the [ext] part, and
    [N]'s and [M]'s from its own guards — so [ax_restrict_keep] applies
    and the restriction step is **free**.

    Compare [ax_phaseA_settle], whose certificate needs
    [g M ⊑ₘᵤₛₜᵢ g N].  Here nothing semantic is used at all: Phase A over
    the union is a purely syntactic fact, and it lifts through [ax_par] to
    a configuration [msgs l ‖ ·] unchanged — which is exactly what the
    unstable-left case could not get from the [N]-only mirror.

    No new definition is needed for the "big mirror": [guardsN] and
    [mirrorN] applied to [N + M] already range over
    [offers N ∪ offers M]. *)

Theorem ax_phaseA_union : forall (M N : gproc), gStatic M -> gStatic N ->
  (forall p, ~ lts (g M) τ p) -> (forall p, ~ lts (g N) τ p) ->
  ax_pre (g M) (g (mirrorN M (N + M))).
Proof.
  intros M N HM HN HstM HstN.
  assert (HstNM : forall p, ~ lts (g (N + M)) τ p).
  { intros p Hp. inversion Hp; subst; [ eapply HstN | eapply HstM ]; eassumption. }
  eapply ax_trans; [ apply ax_mirror_reach; exact HstNM | ].
  apply ax_restrict_keep.
  - apply bigsum_gStatic; [ exact HM | ]. constructor; assumption.
  - apply mirrorN_gStatic; [ apply static_g; exact HM | ]. constructor; assumption.
  - intros al q Hl. apply lts_choiceR. exact Hl.
  - intros c v p Hp. inversion Hp; subst.
    + destruct (ext_lts_shape M (guardsN (N + M)) (ActExt (ActIn (c,v))) p H3)
        as (tgt' & E & Hm). subst p.
      assert (Hnm : lts (g (N + M)) (ActExt (ActIn (c,v))) tgt')
        by (apply lts_choiceR; exact Hm).
      destruct (offers_mirrorN M (N + M) c v tgt' Hnm) as (w & r & Hr).
      exists w, r. exact Hr.
    + exists v, p. exact H3.
  - intros p Hp. inversion Hp; subst.
    + eapply ext_no_tau; [ exact HstM | eassumption ].
    + eapply mirrorN_no_tau; [ exact HstNM | eassumption ].
Qed.

(** ** The outer recursion, as a frame

    Completeness is a well-founded recursion on the **size of the
    right-hand side**; this fixes that frame and checks the induction is
    well founded and the hypothesis shape usable.

    Read the hypothesis as "the step": given the semantic fact and the
    ability to recurse at any strictly smaller right-hand side, produce
    the derivation.  See the caveat recorded at [ax_below_stable_NF]
    about the *level* at which that recursion is currently available. *)

Theorem completeness_from_step :
  (forall p q, Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
     (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
        p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
     ax_pre p q) ->
  forall p q, Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intro Hstep.
  assert (H : forall n q, (size q <= n)%nat ->
                forall p, Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q).
  { induction n as [|n IH]; intros q Hn p Hp Hq Hpre.
    - apply Hstep; try assumption.
      intros p' q' Hp' Hq' Hlt Hpre'. exfalso. lia.
    - apply Hstep; try assumption.
      intros p' q' Hp' Hq' Hlt Hpre'. eapply IH; [ lia | assumption | assumption | assumption ]. }
  intros p q Hp Hq Hpre. eapply H; [ apply le_n | assumption | assumption | assumption ].
Qed.

Corollary ax_phaseA_union_config : forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g M) τ p) -> (forall p, ~ lts (g N) τ p) ->
  ax_pre (msgs l ‖ g M) (msgs l ‖ g (mirrorN M (N + M))).
Proof.
  intros l M N HM HN HstM HstN.
  apply ax_par; [ apply ax_refl | apply ax_phaseA_union; assumption ].
Qed.


(** ** …instantiated at a message bag

    A bag's transitions are exactly "emit one message, leaving the rest",
    so the family of bags reachable from [msgs l] — the sub-bags, up to
    [≡*] — meets the three structural conditions.  Instantiating gives the
    laws the matching actually needs, with the premise quantified over
    sub-bags only, which is precisely the range [domsim_wt] measures. *)

Lemma msgs_lts_inv : forall l mu r, lts (msgs l) (ActExt mu) r ->
  exists c v l', mu = ActOut (c,v) /\ Permutation l ((c,v) :: l') /\ r ≡* msgs l'.
Proof.
  induction l as [|cv l IH]; intros mu r H; simpl in H.
  - inversion H.
  - inversion H; subst.
    + match goal with HH : lts (_ ! _ • 𝟘) (ActExt mu) ?p2 |- _ =>
        inversion HH; subst end.
      exists (fst cv), (snd cv), l.
      split; [ reflexivity | ]. split.
      * rewrite <- surjective_pairing. reflexivity.
      * etransitivity; [ apply cgr_par_com | apply cgr_par_nil ].
    + match goal with HH : lts (msgs l) (ActExt mu) ?q2 |- _ =>
        destruct (IH mu q2 HH) as (c0 & v0 & l'' & Emu & Hperm & Hcgr) end.
      exists c0, v0, (cv :: l''). split; [ exact Emu | ]. split.
      * etransitivity; [ apply perm_skip; exact Hperm | apply perm_swap ].
      * simpl. apply cgr_fullpar; [ reflexivity | exact Hcgr ].
Qed.

Lemma msgs_no_tau : forall l q, ~ lts (msgs l) τ q.
Proof.
  induction l as [|cv l IH]; intros q H; simpl in H.
  - inversion H.
  - inversion H; subst.
    + match goal with HH : lts (msgs l) (ActExt (ActIn _)) _ |- _ =>
        eapply msgs_no_input; exact HH end.
    + match goal with HH : lts (_ ! _ • 𝟘) (ActExt (ActIn _)) _ |- _ => inversion HH end.
    + match goal with HH : lts (_ ! _ • 𝟘) τ _ |- _ => inversion HH end.
    + eapply IH; eassumption.
Qed.

Definition subbag (l' l : list TypeOfActions) : Prop :=
  exists l1, Permutation l (l1 ++ l').

Lemma subbag_refl : forall l, subbag l l.
Proof. intro l. exists []. reflexivity. Qed.

Lemma subbag_trans : forall l1 l2 l3, subbag l3 l2 -> subbag l2 l1 -> subbag l3 l1.
Proof.
  intros l1 l2 l3 (a & Ha) (b & Hb). exists (b ++ a).
  rewrite Hb, Ha. rewrite <- app_assoc. reflexivity.
Qed.

Lemma subbag_cons : forall a l' l, Permutation l (a :: l') -> subbag l' l.
Proof. intros a l' l H. exists [a]. simpl. exact H. Qed.

Definition bagctx (l : list TypeOfActions) (B : proc) : Prop :=
  exists l', subbag l' l /\ B ≡* msgs l'.

Lemma bagctx_no_tau : forall l B, bagctx l B -> forall q, ~ lts B τ q.
Proof.
  intros l B (l' & _ & Hc) q Hq.
  assert (Hsc : sc_then_lts (msgs l') τ q)
    by (exists B; split; [ symmetry; exact Hc | exact Hq ]).
  apply Congruence_Respects_Transition in Hsc as (r' & Hl & _).
  eapply msgs_no_tau; exact Hl.
Qed.

Lemma bagctx_no_input : forall l B, bagctx l B -> forall a q, ~ lts B (ActExt (ActIn a)) q.
Proof.
  intros l B (l' & _ & Hc) a q Hq.
  assert (Hsc : sc_then_lts (msgs l') (ActExt (ActIn a)) q)
    by (exists B; split; [ symmetry; exact Hc | exact Hq ]).
  apply Congruence_Respects_Transition in Hsc as (r' & Hl & _).
  destruct a as (c0,v0). eapply msgs_no_input; exact Hl.
Qed.

Lemma bagctx_closed : forall l B, bagctx l B ->
  forall mu B', lts B (ActExt mu) B' -> bagctx l B'.
Proof.
  intros l B (l' & Hs & Hc) mu B' Hq.
  assert (Hsc : sc_then_lts (msgs l') (ActExt mu) B')
    by (exists B; split; [ symmetry; exact Hc | exact Hq ]).
  apply Congruence_Respects_Transition in Hsc as (r' & Hl & Hr).
  destruct (msgs_lts_inv l' mu r' Hl) as (c0 & v0 & l'' & _ & Hperm & Hc2).
  exists l''. split.
  - eapply subbag_trans; [ eapply subbag_cons; exact Hperm | exact Hs ].
  - etransitivity; [ symmetry; exact Hr | exact Hc2 ].
Qed.

Lemma must_i_input_bag : forall (l : list TypeOfActions) (c : ChannelData) (P Q : proc),
  (forall l' v, subbag l' l ->
     (msgs l' ‖ (subst_in_proc 0 v P)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ (subst_in_proc 0 v Q))) ->
  (msgs l ‖ g (c ? P)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g (c ? Q)).
Proof.
  intros l c P Q HPQ.
  apply (must_i_input_ctx (bagctx l) c P Q
           (bagctx_no_tau l) (bagctx_no_input l) (bagctx_closed l)).
  - intros B (l' & Hs & Hc) v t Ht.
    assert (H1 : (B ‖ (subst_in_proc 0 v P)) ≡* (msgs l' ‖ (subst_in_proc 0 v P)))
      by (apply cgr_fullpar; [ exact Hc | reflexivity ]).
    assert (H2 : (msgs l' ‖ (subst_in_proc 0 v Q)) ≡* (B ‖ (subst_in_proc 0 v Q)))
      by (apply cgr_fullpar; [ symmetry; exact Hc | reflexivity ]).
    apply (proj2 (must_i_cgr _ _ H2)).
    apply (HPQ l' v Hs).
    apply (proj2 (must_i_cgr _ _ H1)). exact Ht.
  - exists l. split; [ apply subbag_refl | reflexivity ].
Qed.

Lemma must_i_choice_input_bag :
  forall (l : list TypeOfActions) (c : ChannelData) (P Q : proc) (G : gproc),
  (forall l' v, subbag l' l ->
     (msgs l' ‖ (subst_in_proc 0 v P)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ (subst_in_proc 0 v Q))) ->
  (msgs l ‖ g ((c ? P) + G)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g ((c ? Q) + G)).
Proof.
  intros l c P Q G HPQ.
  apply (must_i_choice_input_ctx (bagctx l) c P Q G
           (bagctx_no_tau l) (bagctx_no_input l) (bagctx_closed l)).
  - intros B (l' & Hs & Hc) v t Ht.
    assert (H1 : (B ‖ (subst_in_proc 0 v P)) ≡* (msgs l' ‖ (subst_in_proc 0 v P)))
      by (apply cgr_fullpar; [ exact Hc | reflexivity ]).
    assert (H2 : (msgs l' ‖ (subst_in_proc 0 v Q)) ≡* (B ‖ (subst_in_proc 0 v Q)))
      by (apply cgr_fullpar; [ symmetry; exact Hc | reflexivity ]).
    apply (proj2 (must_i_cgr _ _ H2)).
    apply (HPQ l' v Hs).
    apply (proj2 (must_i_cgr _ _ H1)). exact Ht.
  - exists l. split; [ apply subbag_refl | reflexivity ].
Qed.

(** ** …and at the level of [⊢]

    The same instantiation applied to the *rules* [ax_input_ctx] and
    [ax_choice_input_ctx].  These are the forms the matching consumes:
    a summand's continuation may be rewritten **beside a message bag**,
    provided the rewrite is derivable at every sub-bag — and the sub-bags
    are exactly the states [domsim_wt] measures. *)

Lemma ax_input_bag : forall (l : list TypeOfActions) (c : ChannelData) (P Q : proc),
  (forall l' v, subbag l' l ->
     ax_pre (msgs l' ‖ (subst_in_proc 0 v P)) (msgs l' ‖ (subst_in_proc 0 v Q))) ->
  ax_pre (msgs l ‖ g (c ? P)) (msgs l ‖ g (c ? Q)).
Proof.
  intros l c P Q H.
  apply (ax_input_ctx (bagctx l) c P Q (msgs l)
           (bagctx_no_tau l) (bagctx_no_input l) (bagctx_closed l)).
  - intros X (l' & Hs & Hc) v.
    eapply ax_trans;
      [ apply ax_cgr; apply cgr_fullpar; [ exact Hc | reflexivity ] | ].
    eapply ax_trans; [ apply (H l' v Hs) | ].
    apply ax_cgr_sym. apply cgr_fullpar; [ exact Hc | reflexivity ].
  - exists l. split; [ apply subbag_refl | reflexivity ].
Qed.

Lemma ax_choice_input_bag :
  forall (l : list TypeOfActions) (c : ChannelData) (P Q : proc) (G : gproc),
  (forall l' v, subbag l' l ->
     ax_pre (msgs l' ‖ (subst_in_proc 0 v P)) (msgs l' ‖ (subst_in_proc 0 v Q))) ->
  ax_pre (msgs l ‖ g ((c ? P) + G)) (msgs l ‖ g ((c ? Q) + G)).
Proof.
  intros l c P Q G H.
  apply (ax_choice_input_ctx (bagctx l) c P Q (msgs l) G
           (bagctx_no_tau l) (bagctx_no_input l) (bagctx_closed l)).
  - intros X (l' & Hs & Hc) v.
    eapply ax_trans;
      [ apply ax_cgr; apply cgr_fullpar; [ exact Hc | reflexivity ] | ].
    eapply ax_trans; [ apply (H l' v Hs) | ].
    apply ax_cgr_sym. apply cgr_fullpar; [ exact Hc | reflexivity ].
  - exists l. split; [ apply subbag_refl | reflexivity ].
Qed.

(** Pooling two **same-channel** guards is free at a bag: the law is a
    closed inequation, so [ax_par] carries it into any context.  This is
    what merges the delivery-branches a bag creates *at one channel*;
    nothing in the rule set merges branches at *different* channels, which
    is the open part of the unstable case
    ([VACCS_DropProbes.tau_successor_cannot_be_chosen] and
    [VACCS_DropProbes.ax_PC_below_nil] delimit it). *)
Lemma ax_input_distrib_bag : forall (l : list TypeOfActions) (c : ChannelData)
    (P Q : proc) (R : gproc),
  ax_pre (msgs l ‖ g (((c ? P) + (c ? Q)) + R))
         (msgs l ‖ g ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + R)).
Proof. intros. apply ax_par; [ apply ax_refl | apply ax_input_distrib_l ]. Qed.

(** The greatest lower bound, likewise at a bag. *)
Lemma ax_int_glb_bag : forall (l : list TypeOfActions) (p q1 q2 : proc),
  (forall l', subbag l' l -> ax_pre (msgs l' ‖ p) (msgs l' ‖ q1)) ->
  (forall l', subbag l' l -> ax_pre (msgs l' ‖ p) (msgs l' ‖ q2)) ->
  ax_pre (msgs l ‖ p) (msgs l ‖ g ((𝛕 • q1) + (𝛕 • q2))).
Proof.
  intros l p q1 q2 H1 H2.
  apply (ax_int_glb_ctx (bagctx l) p q1 q2 (msgs l)
           (bagctx_no_tau l) (bagctx_no_input l) (bagctx_closed l)).
  - intros X (l' & Hs & Hc).
    eapply ax_trans;
      [ apply ax_cgr; apply cgr_fullpar; [ exact Hc | reflexivity ] | ].
    eapply ax_trans; [ apply (H1 l' Hs) | ].
    apply ax_cgr_sym. apply cgr_fullpar; [ exact Hc | reflexivity ].
  - intros X (l' & Hs & Hc).
    eapply ax_trans;
      [ apply ax_cgr; apply cgr_fullpar; [ exact Hc | reflexivity ] | ].
    eapply ax_trans; [ apply (H2 l' Hs) | ].
    apply ax_cgr_sym. apply cgr_fullpar; [ exact Hc | reflexivity ].
  - exists l. split; [ apply subbag_refl | reflexivity ].
Qed.

(** ** Phase B, and the stable case, AT A CONFIGURATION

    The whole chain now lifts, and the point of lifting it is the shape of
    the **recursive premise**: it comes out as
    [⊢ msgs l' ‖ ((c!v•𝟘) ‖ g M) ⊑ msgs l' ‖ Q'] — *wrapped*, at every
    sub-bag [l'] — which is exactly what [VACCS_Descent.
    wrapped_premise_from_IH] discharges, and the sub-bags are exactly the
    states [domsim_wt] measures.  Compare [ax_below_stable_NF], whose
    premise is bare and therefore unmeasurable.

    Phase A stays bare: it is a [⊢]-statement about the two sums with no
    premise of its own, so one [ax_par] carries it into the context. *)

Lemma ax_par_bag : forall (l : list TypeOfActions) (X Y : proc),
  ax_pre X Y -> ax_pre (msgs l ‖ X) (msgs l ‖ Y).
Proof. intros l X Y H. apply ax_par; [ apply ax_refl | exact H ]. Qed.

Fixpoint mirror_ok_bag (l : list TypeOfActions) (P : proc) (N : gproc) : Prop :=
  match N with
  | gpr_success => True
  | gpr_nil => True
  | gpr_input c Q => forall l' v, subbag l' l ->
      ax_pre (msgs l' ‖ (P ‖ (c ! v • 𝟘))) (msgs l' ‖ (subst_in_proc 0 v Q))
  | gpr_tau _ => False
  | gpr_choice N1 N2 => mirror_ok_bag l P N1 /\ mirror_ok_bag l P N2
  end.

Lemma ax_mirrorN_match_bag : forall (l : list TypeOfActions) (P : proc) (N : gproc),
  mirror_ok_bag l P N ->
  forall (R : gproc), ax_pre (msgs l ‖ g ((mirrorN P N) + R)) (msgs l ‖ g (N + R)).
Proof.
  intros l P N. induction N as [ | | c Q | p | N1 IH1 N2 IH2 ]; intros Hok R; simpl in *.
  - apply ax_par_bag. apply ax_success_r.
  - apply ax_refl.
  - apply ax_choice_input_bag. intros l' v Hs. unfold fwdg. simpl.
    rewrite NewVar_subst_cancel. apply Hok. exact Hs.
  - contradiction.
  - destruct Hok as [Hok1 Hok2].
    eapply ax_trans; [ apply ax_par_bag; apply ax_cgr; apply cgr_choice_assoc | ].
    eapply ax_trans; [ apply (IH1 Hok1 ((mirrorN P N2) + R)) | ].
    eapply ax_trans; [ apply ax_par_bag; apply ax_cgr; apply cgr_swap3 | ].
    eapply ax_trans; [ apply (IH2 Hok2 (N1 + R)) | ].
    apply ax_par_bag. apply ax_cgr.
    etransitivity; [ apply cgr_swap3 | ].
    apply cgr_symm. apply cgr_choice_assoc.
Qed.

Lemma mirror_ok_bag_of : forall (l : list TypeOfActions) (P : proc) (N : gproc),
  (forall p, ~ lts (g N) τ p) ->
  (forall c v Q' l', subbag l' l -> lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ax_pre (msgs l' ‖ (P ‖ (c ! v • 𝟘))) (msgs l' ‖ Q')) ->
  mirror_ok_bag l P N.
Proof.
  intros l P N. induction N as [ | | c Q | p | N1 IH1 N2 IH2 ]; intros Hst Hrec; simpl in *.
  - exact I.
  - exact I.
  - intros l' v Hs. apply Hrec; [ exact Hs | apply lts_input ].
  - exfalso. eapply Hst. apply lts_tau.
  - split.
    + apply IH1.
      * intros q Hq. eapply Hst. apply lts_choiceL. exact Hq.
      * intros c v Q' l' Hs Hl. apply Hrec; [ exact Hs | apply lts_choiceL; exact Hl ].
    + apply IH2.
      * intros q Hq. eapply Hst. apply lts_choiceR. exact Hq.
      * intros c v Q' l' Hs Hl. apply Hrec; [ exact Hs | apply lts_choiceR; exact Hl ].
Qed.

Theorem ax_below_stable_sum_bag : forall (l : list TypeOfActions) (M N : gproc),
  (forall p, ~ lts (g N) τ p) ->
  ax_pre (g M) (g (mirrorN M N)) ->
  (forall c v Q' l', subbag l' l -> lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ax_pre (msgs l' ‖ ((c ! v • 𝟘) ‖ (g M))) (msgs l' ‖ Q')) ->
  ax_pre (msgs l ‖ g M) (msgs l ‖ g N).
Proof.
  intros l M N Hst HA Hrec.
  eapply ax_trans; [ apply ax_par_bag; exact HA | ].
  eapply ax_trans; [ apply ax_par_bag; apply ax_cgr_sym; apply cgr_choice_nil | ].
  eapply ax_trans;
    [ apply (ax_mirrorN_match_bag l M N) with (R := 𝟘)
    | apply ax_par_bag; apply ax_cgr; apply cgr_choice_nil ].
  apply mirror_ok_bag_of; [ exact Hst | ].
  intros c v Q' l' Hs Hl.
  eapply ax_trans; [ apply ax_par_bag; apply ax_cgr; apply cgr_par_com | ].
  apply Hrec; [ exact Hs | exact Hl ].
Qed.

Theorem ax_below_stable_config_bag : forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (forall z, ~ ((g M ▷ bag l) ⟶ z)) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  (forall c v Q' l', subbag l' l -> lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ax_pre (msgs l' ‖ ((c ! v • 𝟘) ‖ (g M))) (msgs l' ‖ Q')) ->
  ax_pre (msgs l ‖ g M) (msgs l ‖ g N).
Proof.
  intros l M N HM HN Hst Hstab Hsem Hrec.
  apply ax_below_stable_sum_bag; [ exact Hst | | exact Hrec ].
  apply ax_phaseA_settle; [ exact HM | exact HN | exact Hst | ].
  eapply msgs_cancel; [ exact HM | exact HN | exact Hstab | exact Hsem ].
Qed.

Theorem ax_below_stable_NF_bag : forall (n : nat) (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (forall z, ~ ((g M ▷ bag l) ⟶ z)) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  (forall c v Q' l', subbag l' l -> lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ax_pre (msgs l' ‖ ((c ! v • 𝟘) ‖ (g M))) (msgs l' ‖ Q')) ->
  ax_pre (NF n l M) (NF n l N).
Proof.
  intros n l M N HM HN Hst Hstab Hsem Hrec. unfold NF.
  apply ax_res_n. apply ax_below_stable_config_bag; assumption.
Qed.

(** ** THE SAME, WITH THE LEFT CONFIGURATION UNSTABLE — modulo ONE assumption

    [ax_below_stable_NF_bag] requires the left configuration
    [g M ▷ bag l] to be τ-stable, and that hypothesis is used in exactly
    one place: [msgs_cancel] strips the bag so that [ax_phaseA_settle]
    can be applied to the *bare* sums and carried back by [ax_par_bag].
    Everything downstream — Phase B, the omega rules at a bag, the
    wrapped recursive premise — never looks at it.

    So the whole unstable case reduces to Phase A **stated at the
    configuration**, and that is what [PhaseA_config] names.  With it,
    [ax_below_stable_NF_cfg] proves the stable-leaf step with **no
    stability requirement on the left at all**.

    [phaseA_config_of_stable] records the converse reading: the
    assumption is discharged whenever the left configuration *is* stable,
    so it is genuinely the unstable case and nothing else.

    Where it stands.  Phase A goes through [ax_restrict_settle], whose
    certificate at a loaded buffer is [bigsum_certificate_config] — valid
    on the cone **above** the bag — and, below the bag, by the drain
    reading [VACCS_NormalForm.surplus_settles_drain], whose side
    condition is "the left's drain run is forced".
    [VACCS_NormalForm.drain_forced_of_no_output] shows the only
    obstruction to that is **regeneration**: a continuation re-emitting a
    message already given up.  And Phase A's own mirror is built from
    *copycats*, which regenerate by construction.  That is the residue,
    and it is the whole of it. *)

Definition PhaseA_config : Prop :=
  forall (M N : gproc) (l : list TypeOfActions),
    gStatic M -> gStatic N -> (forall p, ~ lts (g N) τ p) ->
    ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
    ax_pre (msgs l ‖ g M) (msgs l ‖ g (mirrorN M N)).

Theorem ax_below_stable_sum_cfg : forall (l : list TypeOfActions) (P : proc) (N : gproc),
  (forall p, ~ lts (g N) τ p) ->
  ax_pre (msgs l ‖ P) (msgs l ‖ g (mirrorN P N)) ->
  (forall c v Q' l', subbag l' l -> lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ax_pre (msgs l' ‖ ((c ! v • 𝟘) ‖ P)) (msgs l' ‖ Q')) ->
  ax_pre (msgs l ‖ P) (msgs l ‖ g N).
Proof.
  intros l P N Hst HA Hrec.
  eapply ax_trans; [ exact HA | ].
  eapply ax_trans; [ apply ax_par_bag; apply ax_cgr_sym; apply cgr_choice_nil | ].
  eapply ax_trans;
    [ apply (ax_mirrorN_match_bag l P N) with (R := 𝟘)
    | apply ax_par_bag; apply ax_cgr; apply cgr_choice_nil ].
  apply mirror_ok_bag_of; [ exact Hst | ].
  intros c v Q' l' Hs Hl.
  eapply ax_trans; [ apply ax_par_bag; apply ax_cgr; apply cgr_par_com | ].
  apply Hrec; [ exact Hs | exact Hl ].
Qed.

(** ** COMPARING CONFIGURATIONS WITH DIFFERENT BAGS

    Everything above compares two configurations at a **common** bag,
    because the omega rules at a bag are congruences and a congruence
    needs the same context on both sides.  That is where the second open
    point lived: two normal forms carry bags [l1] and [l2], and
    [VACCS_NormalForm.bags_agree] forces [l1 = l2] only when *both* sides
    are τ-free — and the two witnesses
    ([VACCS_Bad.unstable_delivery_below_nil],
    [VACCS_DropProbes.msg_below_tau_msg]) show that cannot be weakened.

    Generalising the mirror from a guarded sum to an **arbitrary** left
    process removes the difficulty on one side.  [msgs_app] splits the
    left's bag, and the surplus is absorbed into the *process*:

        msgs (d ++ l) ‖ g M  ≡*  msgs l ‖ (msgs d ‖ g M)

    so the comparison runs at the common bag [l] with left [msgs d ‖ g M].
    That covers every case where the left's bag **contains** the right's.

    The symmetric case — surplus on the *right* — is not handled this way
    and remains open: Phase B matches the right summand by summand and so
    needs it to be a guarded sum, which [msgs e ‖ g N] is not. *)

Lemma cgr_par_shift : forall (A B C : proc), ((A ‖ B) ‖ C) ≡* (B ‖ (A ‖ C)).
Proof.
  intros A B C.
  etransitivity; [ apply cgr_par_assoc | ].
  etransitivity; [ apply cgr_par_com | ].
  etransitivity; [ apply cgr_par_assoc | ].
  apply cgr_fullpar; [ reflexivity | apply cgr_par_com ].
Qed.

Theorem ax_below_stable_split_bag :
  forall (l d : list TypeOfActions) (M N : gproc),
  (forall p, ~ lts (g N) τ p) ->
  ax_pre (msgs l ‖ (msgs d ‖ g M)) (msgs l ‖ g (mirrorN (msgs d ‖ g M) N)) ->
  (forall c v Q' l', subbag l' l -> lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ax_pre (msgs l' ‖ ((c ! v • 𝟘) ‖ (msgs d ‖ g M))) (msgs l' ‖ Q')) ->
  ax_pre (msgs (d ++ l) ‖ g M) (msgs l ‖ g N).
Proof.
  intros l d M N Hst HA Hrec.
  eapply ax_trans; [ apply ax_cgr | apply ax_below_stable_sum_cfg; eassumption ].
  etransitivity; [ apply cgr_fullpar; [ apply msgs_app | reflexivity ] | ].
  apply cgr_par_shift.
Qed.

Theorem ax_below_stable_NF_cfg : PhaseA_config ->
  forall (n : nat) (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  (forall c v Q' l', subbag l' l -> lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ax_pre (msgs l' ‖ ((c ! v • 𝟘) ‖ (g M))) (msgs l' ‖ Q')) ->
  ax_pre (NF n l M) (NF n l N).
Proof.
  intros HPA n l M N HM HN Hst Hsem Hrec. unfold NF.
  apply ax_res_n. apply ax_below_stable_sum_cfg; [ exact Hst | | exact Hrec ].
  apply HPA; assumption.
Qed.

Lemma phaseA_config_of_stable : forall (M N : gproc) (l : list TypeOfActions),
  gStatic M -> gStatic N -> (forall p, ~ lts (g N) τ p) ->
  (forall z, ~ ((g M ▷ bag l) ⟶ z)) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  ax_pre (msgs l ‖ g M) (msgs l ‖ g (mirrorN M N)).
Proof.
  intros M N l HM HN Hst Hstab Hsem.
  apply ax_par_bag. apply ax_phaseA_settle; [ exact HM | exact HN | exact Hst | ].
  eapply msgs_cancel; [ exact HM | exact HN | exact Hstab | exact Hsem ].
Qed.

(** ** THE STABLE-LEAF STEP AT AN UNSTABLE CONFIGURATION

    Putting the two together: [ax_below_stable_sum_cfg] needs Phase A at
    the configuration and nothing else, and
    [phaseA_config_no_regeneration] supplies it.  So the stable-leaf step
    holds with **no τ-stability requirement on the left configuration at
    all** — the hypothesis [ax_below_stable_NF_bag] carried — under the
    single condition that [M] never gives back everything it took —
    i.e. that no run of [g M] re-emits the whole of what it consumed.

    That condition is exactly non-regeneration
    ([VACCS_NormalForm.drain_forced_of_no_output]), and it is now a
    property of the process being compared rather than of the mirror
    construction: the copycats that used to break the drain argument are
    gone, [ax_phaseA_direct] not building any. *)

Theorem ax_below_stable_NF_no_regen :
  forall (n : nat) (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (forall z, ~ lts (g M) τ z) ->
  (forall r q, ((g M) : proc) ⟹[r] q -> bag (ins r) ⊆ bag (outs r) -> ins r = []) ->
  ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  (forall c v Q' l', subbag l' l -> lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ax_pre (msgs l' ‖ ((c ! v • 𝟘) ‖ (g M))) (msgs l' ‖ Q')) ->
  ax_pre (NF n l M) (NF n l N).
Proof.
  intros n l M N HM HN HstN HstM Hno Hsem Hrec. unfold NF.
  apply ax_res_n. apply ax_below_stable_sum_cfg; [ exact HstN | | exact Hrec ].
  apply phaseA_config_no_regeneration; assumption.
Qed.

(** ** The τ-layer, at a configuration

    The two drivers lift as mechanically as Phase B did.  Everything is
    phrased with two abbreviations, both **monotone in the bag** (a
    sub-bag of a sub-bag is a sub-bag), which is what lets the recursive
    calls be made at the *outer* bag and used at the inner ones. *)

Definition BagSem (l : list TypeOfActions) (p : proc) (X : gproc) : Prop :=
  forall l', subbag l' l -> (msgs l' ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ g X).

Definition BagBelow (l : list TypeOfActions) (p : proc) (X : gproc) : Prop :=
  forall l', subbag l' l -> ax_pre (msgs l' ‖ p) (msgs l' ‖ g X).

Lemma BagBelow_mono : forall l l' p X, subbag l' l -> BagBelow l p X -> BagBelow l' p X.
Proof. intros l l' p X Hs H l'' Hs''. apply H. eapply subbag_trans; eassumption. Qed.

Lemma ax_below_int_choice_bag : forall (l : list TypeOfActions) (p : proc) (N1 N2 : gproc),
  BagSem l p ((𝛕 • (g N1)) + (𝛕 • (g N2))) ->
  (BagSem l p N1 -> BagBelow l p N1) ->
  (BagSem l p N2 -> BagBelow l p N2) ->
  BagBelow l p ((𝛕 • (g N1)) + (𝛕 • (g N2))).
Proof.
  intros l p N1 N2 Hsem H1 H2.
  assert (S1 : BagSem l p N1).
  { intros l' Hs t Hm.
    assert (Hl : lts (msgs l' ‖ g ((𝛕 • (g N1)) + (𝛕 • (g N2)))) τ (msgs l' ‖ g N1))
      by (apply lts_parR; apply lts_choiceL; apply lts_tau).
    eapply must_i_tau_below; [ exact Hl | apply (Hsem l' Hs); exact Hm ]. }
  assert (S2 : BagSem l p N2).
  { intros l' Hs t Hm.
    assert (Hl : lts (msgs l' ‖ g ((𝛕 • (g N1)) + (𝛕 • (g N2)))) τ (msgs l' ‖ g N2))
      by (apply lts_parR; apply lts_choiceR; apply lts_tau).
    eapply must_i_tau_below; [ exact Hl | apply (Hsem l' Hs); exact Hm ]. }
  intros l0 Hl0. apply ax_int_glb_bag.
  - intros l' Hs'. apply (H1 S1). eapply subbag_trans; eassumption.
  - intros l' Hs'. apply (H2 S2). eapply subbag_trans; eassumption.
Qed.

Theorem ax_below_tau_peel_bag : forall (l : list TypeOfActions) (p : proc) (M Y : gproc)
    (r : list gproc),
  gStatic M -> Permutation (summands M) ((𝛕 • (g Y)) :: r) ->
  BagSem l p M ->
  (BagSem l p ((rebuild r) + Y) -> BagBelow l p ((rebuild r) + Y)) ->
  (BagSem l p Y -> BagBelow l p Y) ->
  BagBelow l p M.
Proof.
  intros l p M Y r HS Hperm Hsem H1 H2.
  destruct (ax_tau_sep_anywhere M Y r HS Hperm) as [Ha Hb].
  intros l0 Hl0.
  eapply ax_trans; [ | apply ax_par_bag; exact Hb ].
  apply (ax_below_int_choice_bag l p ((rebuild r) + Y) Y);
    [ | exact H1 | exact H2 | exact Hl0 ].
  intros l' Hs t Hm. apply (soundness_ax _ _ (ax_par_bag l' _ _ Ha)).
  apply (Hsem l' Hs). exact Hm.
Qed.

Theorem ax_below_tau_flatten_bag : forall (l : list TypeOfActions) (p : proc) (M Y : gproc)
    (r : list gproc),
  gStatic M -> gAllTau Y -> Permutation (summands M) ((𝛕 • (g Y)) :: r) ->
  BagSem l p M ->
  (BagSem l p ((rebuild r) + Y) -> BagBelow l p ((rebuild r) + Y)) ->
  BagBelow l p M.
Proof.
  intros l p M Y r HS Hall Hperm Hsem H1.
  destruct (ax_tau_flatten_anywhere M Y r HS Hall Hperm) as [Ha Hb].
  assert (Hs2 : BagSem l p ((rebuild r) + Y)).
  { intros l' Hs t Hm. apply (soundness_ax _ _ (ax_par_bag l' _ _ Ha)).
    apply (Hsem l' Hs). exact Hm. }
  intros l0 Hl0.
  eapply ax_trans; [ | apply ax_par_bag; exact Hb ].
  apply (H1 Hs2). exact Hl0.
Qed.

Lemma ax_below_mixed_bag : forall n (l : list TypeOfActions) (M : gproc), gStatic M ->
  (ntaus (summands M) <= n)%nat -> Forall tau_cont_ok (summands M) ->
  forall (p : proc), BagSem l p M ->
  (forall (L : gproc), gStatic L -> gStable L -> BagSem l p L -> BagBelow l p L) ->
  BagBelow l p M.
Proof.
  induction n as [|n IH]; intros l M HM Hmeas Hok p Hsem Hstab.
  - apply Hstab; [ exact HM | | exact Hsem ].
    apply find_tau_none_stable.
    destruct (find_tau (summands M)) as [(q,r)|] eqn:E; [| reflexivity].
    exfalso. apply find_tau_spec in E.
    rewrite (ntaus_perm _ _ E) in Hmeas. simpl in Hmeas. lia.
  - destruct (find_tau (summands M)) as [(q,r)|] eqn:E.
    + apply find_tau_spec in E.
      assert (Hokperm : Forall tau_cont_ok ((𝛕 • q) :: r))
        by (eapply tau_cont_ok_perm; eassumption).
      inversion Hokperm as [|? ? Hp0 Hokr]; subst.
      destruct Hp0 as (Y & Hpy & HYst). subst q.
      assert (Hlv : Forall (fun a => summands a = [a]) ((𝛕 • (g Y)) :: r)).
      { apply Forall_forall. intros x Hx. pose proof (summands_leaves M) as Hsl.
        rewrite Forall_forall in Hsl. apply Hsl. rewrite E. exact Hx. }
      inversion Hlv as [|? ? _ Hlvr]; subst.
      destruct (tau_mid_static M Y r HM E) as (HYgst & Hrgst & _).
      assert (Hnew : gStatic (rebuild r + Y))
        by (constructor; [apply rebuild_gStatic; exact Hrgst | exact HYgst]).
      assert (Hmeas2 : ntaus (summands (rebuild r + Y)) <= n).
      { simpl. rewrite ntaus_app.
        rewrite (ntaus_summands_rebuild r Hlvr).
        rewrite (gStable_ntaus_zero Y HYst).
        rewrite (ntaus_perm _ _ E) in Hmeas. simpl in Hmeas. lia. }
      assert (Hok2 : Forall tau_cont_ok (summands (rebuild r + Y))).
      { simpl. apply Forall_app. split.
        - apply tau_cont_ok_rebuild; assumption.
        - apply tau_cont_ok_stable. exact HYst. }
      eapply ax_below_tau_peel_bag; [ exact HM | exact E | exact Hsem | | ].
      * intro Hs1. exact (IH l (rebuild r + Y) Hnew Hmeas2 Hok2 p Hs1 Hstab).
      * intro Hs2. apply Hstab; [ exact HYgst | exact HYst | exact Hs2 ].
    + apply Hstab; [ exact HM | apply find_tau_none_stable; exact E | exact Hsem ].
Qed.

Theorem ax_below_gsum_bag : forall (l : list TypeOfActions) (M : gproc), gStatic M ->
  Forall tau_cont_nf (summands M) ->
  forall (p : proc), BagSem l p M ->
  (forall (L : gproc), gStatic L -> gStable L -> BagSem l p L -> BagBelow l p L) ->
  BagBelow l p M.
Proof.
  intros l M HM Hnf p Hsem Hstab.
  destruct (tau_flatten_all (tau_weight (summands M)) M HM (le_n _) Hnf)
    as (M' & HM' & Hok' & Hf & Hb).
  assert (Hsem' : BagSem l p M').
  { intros l' Hs t Hm. apply (soundness_ax _ _ (ax_par_bag l' _ _ Hf)).
    apply (Hsem l' Hs). exact Hm. }
  intros l0 Hl0.
  eapply ax_trans; [ | apply ax_par_bag; exact Hb ].
  eapply (ax_below_mixed_bag (ntaus (summands M')) l M' HM' (le_n _) Hok');
    [ exact Hsem' | exact Hstab | exact Hl0 ].
Qed.


(** * THE WHOLE RIGHT-HAND SIDE AT A CONFIGURATION, modulo [PhaseA_config]

    [ax_below_gsum_bag] reduces an arbitrary right-hand sum to its
    **stable leaves**, at a configuration, by the two τ-drivers; and
    [ax_below_stable_sum_cfg] handles a stable leaf given Phase A there.
    Composing them leaves exactly one hypothesis apiece:

    - [PhaseA_config] — the one open point, and by
      [phaseA_config_of_stable] it is discharged whenever the left
      configuration is τ-stable, by [phaseA_config_no_regeneration]
      whenever the left does not regenerate;
    - the **recursive premise**, one call per input transition of a leaf,
      at every sub-bag — the shape [VACCS_Descent.wrapped_premise_from_IH]
      discharges from the outer induction hypothesis, with
      [VACCS_NormalForm.domsim_wt] supplying the measure.

    Nothing else is left of the right-hand side: the τ-layer, the mirror,
    Phase B, the omega rules at a bag and the bag bookkeeping are all
    inside. *)

Theorem ax_below_gsum_stable_cfg : PhaseA_config ->
  forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
  BagSem l (g M) N ->
  (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
     BagSem l (g M) L -> subbag l' l ->
     forall c v Q' l'', subbag l'' l' -> lts (g L) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ (g M))) (msgs l'' ‖ Q')) ->
  BagBelow l (g M) N.
Proof.
  intros HPA l M N HM HN Hnf Hsem Hrec.
  apply ax_below_gsum_bag; try assumption.
  intros L HL HstL HsemL l' Hs'.
  assert (HtauL : forall p, ~ lts (g L) τ p).
  { intros p Hp. eapply stable_no_lts; [ apply gStable_iff; exact HstL | exact Hp ]. }
  apply ax_below_stable_sum_cfg; [ exact HtauL | | ].
  - apply HPA; [ exact HM | exact HL | exact HtauL | apply HsemL; exact Hs' ].
  - intros c v Q' l'' Hs'' Hl. eapply Hrec; eassumption.
Qed.

Corollary ax_below_NF_cfg : PhaseA_config ->
  forall (n : nat) (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
  BagSem l (g M) N ->
  (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
     BagSem l (g M) L -> subbag l' l ->
     forall c v Q' l'', subbag l'' l' -> lts (g L) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ (g M))) (msgs l'' ‖ Q')) ->
  ax_pre (NF n l M) (NF n l N).
Proof.
  intros HPA n l M N HM HN Hnf Hsem Hrec. unfold NF.
  apply ax_res_n.
  apply (ax_below_gsum_stable_cfg HPA l M N HM HN Hnf Hsem Hrec l).
  apply subbag_refl.
Qed.


(** * MOVING A PENDING MESSAGE FROM THE BUFFER INTO THE PROCESS

    [Settles] is insensitive to where a pending output sits.  This is the
    [Settles]-level counterpart of [VACCS_Precongruence.must_msg_swap]
    and [VACCS_Cond2.fw_msg_swap], and it is the brick the drain argument
    needs now that the left-hand side of Phase A may be an arbitrary
    process rather than a guarded sum: a left of the shape [msgs d ‖ g M]
    carries messages of its own, and [VACCS_NormalForm.gsum_run_no_input]
    — which leans on [gsum_no_output] — no longer applies to it.

    The proof is the mirror image of the analysis already carried out in
    [mirrorRel], run in the other direction: the **buffer** side moves and
    the **process** side answers.  The same two families reappear —
    [Rmsg]'s first disjunct is [mirrorRel]'s [F1], its second is [F2] —
    and the four cases are the same: a [τ] of [q] is matched by
    [lts_parL]; a delivery from [k] likewise; a delivery of the moved
    message [a] is matched by the *internal synchronisation* on the
    process side, dropping into the second family; and stability
    transfers because the buffer side's stability already says [q]
    refuses [a]. *)

Lemma disj_swap : forall (A : Type) (EA : EqDecision A) (CA : Countable A)
  (X Y Z : gmultiset A), X ⊎ (Y ⊎ Z) = Y ⊎ (X ⊎ Z).
Proof.
  intros A EA CA X Y Z.
  rewrite !(assoc_L (@disj_union (gmultiset A) _)). f_equal.
  apply (comm_L (@disj_union (gmultiset A) _)).
Qed.

Definition Rmsg (a : TypeOfActions)
  : (proc * MO (ExtAct TypeOfActions)) -> (proc * MO (ExtAct TypeOfActions)) -> Prop :=
  fun y z =>
    (exists q k, y = (q ▷ ({[+ ActOut a +]} ⊎ k))
              /\ z = ((q ‖ ((fst a) ! (snd a) • 𝟘)) ▷ k))
    \/ (exists q k, y = (q ▷ k) /\ z = ((q ‖ (g 𝟘 : proc)) ▷ k)).

Lemma step_msg_to_buffer : forall a x z x1, Rmsg a x z -> x ⟶ x1 ->
  exists z1, z ⟹[[]] z1 /\ Rmsg a x1 z1.
Proof.
  intros a x z x1 HR Hl.
  destruct HR as [ (q & k & Ex & Ez) | (q & k & Ex & Ez) ]; subst x z.
  - destruct (fw_tau_shape q ({[+ ActOut a +]} ⊎ k) x1 Hl) as [HA|HB].
    + destruct HA as (q' & Hq' & E). subst x1.
      exists ((q' ‖ ((fst a) ! (snd a) • 𝟘)) ▷ k). split.
      * eapply wt_tau; [ apply fw_tau_left; eapply lts_parL; exact Hq' | apply wt_nil ].
      * left. exists q', k. split; reflexivity.
    + destruct HB as (b & q' & k'' & HK & Hq' & E). subst x1.
      destruct (decide (b = a)) as [Eb|Nb].
      * subst b.
        assert (Ek : k = k'')
          by (apply (gmultiset_disj_union_inj_1
                       ({[+ ActOut a +]} : MO (ExtAct TypeOfActions))); exact HK).
        subst k''.
        exists ((q' ‖ (g 𝟘 : proc)) ▷ k). split.
        -- eapply wt_tau; [ apply fw_tau_left | apply wt_nil ].
           destruct a as (c,v). simpl. eapply lts_comR; [ apply lts_output | exact Hq' ].
        -- right. exists q', k. split; reflexivity.
      * assert (Hin : ActOut b ∈ ({[+ ActOut a +]} ⊎ k)).
        { rewrite HK. apply gmultiset_elem_of_disj_union. left.
          apply gmultiset_elem_of_singleton. reflexivity. }
        apply gmultiset_elem_of_disj_union in Hin as [Hin|Hin].
        -- exfalso. apply gmultiset_elem_of_singleton in Hin.
           injection Hin as Hin. apply Nb. exact Hin.
        -- assert (Hex : exists k1, k = {[+ ActOut b +]} ⊎ k1).
           { exists (k ∖ {[+ ActOut b +]}).
             apply gmultiset_disj_union_difference'. exact Hin. }
           destruct Hex as (k1 & Hk). subst k.
           assert (Ek'' : k'' = {[+ ActOut a +]} ⊎ k1).
           { apply (gmultiset_disj_union_inj_1
                      ({[+ ActOut b +]} : MO (ExtAct TypeOfActions))).
             etransitivity; [ symmetry; exact HK | apply disj_swap ]. }
           subst k''.
           exists ((q' ‖ ((fst a) ! (snd a) • 𝟘)) ▷ k1). split.
           ++ eapply wt_tau; [ | apply wt_nil ].
              apply fw_tau_deliver. eapply lts_parL. exact Hq'.
           ++ left. exists q', k1. split; reflexivity.
  - destruct (fw_tau_shape q k x1 Hl) as [HA|HB].
    + destruct HA as (q' & Hq' & E). subst x1.
      exists ((q' ‖ (g 𝟘 : proc)) ▷ k). split.
      * eapply wt_tau; [ apply fw_tau_left; eapply lts_parL; exact Hq' | apply wt_nil ].
      * right. exists q', k. split; reflexivity.
    + destruct HB as (b & q' & k'' & HK & Hq' & E). subst x1.
      exists ((q' ‖ (g 𝟘 : proc)) ▷ k''). split.
      * eapply wt_tau; [ | apply wt_nil ]. rewrite HK.
        apply fw_tau_deliver. eapply lts_parL. exact Hq'.
      * right. exists q', k''. split; reflexivity.
Qed.

Lemma run_msg_to_buffer : forall (x y : proc * MO (ExtAct TypeOfActions)), x ⟹[[]] y ->
  forall a z, Rmsg a x z -> exists z', z ⟹[[]] z' /\ Rmsg a y z'.
Proof.
  intros x y Hw. remember (nil : trace (ExtAct TypeOfActions)) as s eqn:Es.
  revert Es. induction Hw; intros Es a z HR.
  - exists z. split; [ apply wt_nil | exact HR ].
  - subst s.
    destruct (step_msg_to_buffer a _ z _ HR l) as (z1 & Hz1 & HR1).
    destruct (IHHw eq_refl a z1 HR1) as (z' & Hz' & HR').
    exists z'. split; [ | exact HR' ]. eapply wt_join_nil; eassumption.
  - discriminate Es.
Qed.

Lemma Rmsg_stable : forall a y z, Rmsg a y z -> y ↛ -> z ↛.
Proof.
  intros a y z HR Hst.
  destruct HR as [ (q & k & Ey & Ez) | (q & k & Ey & Ez) ]; subst y z.
  - pose proof (no_step_of_stable _ Hst) as Hns.
    apply fw_stable_iff in Hns as (Hq & Href).
    apply stable_of_no_step. apply fw_stable_iff. split.
    + intros w Hw. destruct (lts_par_msg_inv q a τ w Hw)
        as [ (q1 & _ & Hq1) | [ (Ea & _) | (q1 & _ & _ & Hq1) ] ].
      * eapply Hq. exact Hq1.
      * discriminate Ea.
      * eapply Href; [ | exact Hq1 ].
        apply gmultiset_elem_of_disj_union. left.
        apply gmultiset_elem_of_singleton. reflexivity.
    + intros b Hin w Hw. destruct (lts_par_msg_inv q a (ActExt (ActIn b)) w Hw)
        as [ (q1 & _ & Hq1) | [ (Ea & _) | (q1 & Ea & _ & _) ] ].
      * eapply Href; [ | exact Hq1 ].
        apply gmultiset_elem_of_disj_union. right. exact Hin.
      * discriminate Ea.
      * discriminate Ea.
  - pose proof (no_step_of_stable _ Hst) as Hns.
    apply fw_stable_iff in Hns as (Hq & Href).
    apply stable_of_no_step. apply fw_stable_iff. split.
    + intros w Hw. destruct (lts_par_nil_inv q τ w Hw) as (q1 & _ & Hq1).
      eapply Hq. exact Hq1.
    + intros b Hin w Hw. destruct (lts_par_nil_inv q (ActExt (ActIn b)) w Hw)
        as (q1 & _ & Hq1). eapply Href; [ exact Hin | exact Hq1 ].
Qed.

Lemma Rmsg_emits : forall a y z, Rmsg a y z -> forall d w r,
  z ⟶[ActOut (d,w)] r -> exists w' r', y ⟶[ActOut (d,w')] r'.
Proof.
  intros a y z HR d w r Hr.
  destruct HR as [ (q & k & Ey & Ez) | (q & k & Ey & Ez) ]; subst y z.
  - destruct (fw_ext_shape (q ‖ ((fst a) ! (snd a) • 𝟘)) k (ActOut (d,w)) r Hr)
      as [HA|[HB|HC]].
    + destruct HA as (q'' & Hq'' & _).
      destruct (lts_par_msg_inv q a (ActExt (ActOut (d,w))) q'' Hq'')
        as [ (q1 & _ & Hq1) | [ (Ea & _) | (q1 & Ea & _ & _) ] ].
      * exists w. eexists. apply fw_ext_left. exact Hq1.
      * injection Ea as Ea. subst a. exists w. apply fw_emit_of_mem.
        apply gmultiset_elem_of_disj_union. left.
        apply gmultiset_elem_of_singleton. reflexivity.
      * discriminate Ea.
    + destruct HB as (b & Hb & _). discriminate Hb.
    + destruct HC as (b & k'' & Hb & HK & _). injection Hb as Hb. subst b.
      exists w. apply fw_emit_of_mem.
      apply gmultiset_elem_of_disj_union. right. rewrite HK.
      apply gmultiset_elem_of_disj_union. left.
      apply gmultiset_elem_of_singleton. reflexivity.
  - destruct (fw_ext_shape (q ‖ (g 𝟘 : proc)) k (ActOut (d,w)) r Hr) as [HA|[HB|HC]].
    + destruct HA as (q'' & Hq'' & _).
      destruct (lts_par_nil_inv q (ActExt (ActOut (d,w))) q'' Hq'') as (q1 & _ & Hq1).
      exists w. eexists. apply fw_ext_left. exact Hq1.
    + destruct HB as (b & Hb & _). discriminate Hb.
    + destruct HC as (b & k'' & Hb & HK & _). injection Hb as Hb. subst b.
      exists w. apply fw_emit_of_mem. rewrite HK.
      apply gmultiset_elem_of_disj_union. left.
      apply gmultiset_elem_of_singleton. reflexivity.
Qed.

Theorem Settles_msg_to_buffer : forall S (q : proc) (a : TypeOfActions) k,
  Settles S (q ▷ ({[+ ActOut a +]} ⊎ k)) ->
  Settles S ((q ‖ ((fst a) ! (snd a) • 𝟘)) ▷ k).
Proof.
  intros S q a k (y & Hw & Hst & He).
  destruct (run_msg_to_buffer _ y Hw a ((q ‖ ((fst a) ! (snd a) • 𝟘)) ▷ k))
    as (z' & Hz' & HR').
  { left. exists q, k. split; reflexivity. }
  exists z'. split; [ exact Hz' | ].
  split; [ eapply Rmsg_stable; eassumption | ].
  intros d w r Hr.
  destruct (Rmsg_emits a y z' HR' d w r Hr) as (w' & r' & Hr').
  eapply He. exact Hr'.
Qed.


(** ** …and a WHOLE bag, which needs [Settles] up to structural congruence

    Iterating [Settles_msg_to_buffer] over a list needs the messages to
    accumulate on the *left* of the process, whereas the lemma puts each
    one on the right.  Rather than duplicate it, [Settles] is shown
    invariant under [≡*] on the process component — which is a fact worth
    having on its own, and cheap: the forwarder's steps are built from
    the process's, so [Congruence_Respects_Transition] transfers each of
    them, and stability and emissions follow by transferring back. *)

Definition Rcgr (x y : proc * MO (ExtAct TypeOfActions)) : Prop :=
  exists p q m, x = (p ▷ m) /\ y = (q ▷ m) /\ p ≡* q.

Lemma cgr_lts_transfer : forall (p p' : proc) al x, p ≡* p' -> lts p al x ->
  exists x', lts p' al x' /\ x ≡* x'.
Proof.
  intros p p' al x Hc Hl.
  destruct (Congruence_Respects_Transition p' x al) as (r & Hr & Hrc).
  { exists p. split; [ apply cgr_symm; exact Hc | exact Hl ]. }
  exists r. split; [ exact Hr | apply cgr_symm; exact Hrc ].
Qed.

Lemma step_cgr_tau : forall x y x1, Rcgr x y -> x ⟶ x1 ->
  exists y1, y ⟶ y1 /\ Rcgr x1 y1.
Proof.
  intros x y x1 (p & q & m & Ex & Ey & Hc) Hl. subst x y.
  destruct (fw_tau_shape p m x1 Hl) as [HA|HB].
  - destruct HA as (p1 & Hp1 & E). subst x1.
    destruct (cgr_lts_transfer p q τ p1 Hc Hp1) as (q1 & Hq1 & Hc1).
    exists (q1 ▷ m). split; [ apply fw_tau_left; exact Hq1 | ].
    exists p1, q1, m. split; [ reflexivity | split; [ reflexivity | exact Hc1 ] ].
  - destruct HB as (b & p1 & m' & HK & Hp1 & E). subst x1.
    destruct (cgr_lts_transfer p q (ActExt (ActIn b)) p1 Hc Hp1) as (q1 & Hq1 & Hc1).
    exists (q1 ▷ m'). split.
    + rewrite HK. apply fw_tau_deliver. exact Hq1.
    + exists p1, q1, m'. split; [ reflexivity | split; [ reflexivity | exact Hc1 ] ].
Qed.

Lemma step_cgr_ext : forall x y mu x1, Rcgr x y -> x ⟶[mu] x1 ->
  exists y1, y ⟶[mu] y1 /\ Rcgr x1 y1.
Proof.
  intros x y mu x1 (p & q & m & Ex & Ey & Hc) Hl. subst x y.
  destruct (fw_ext_shape p m mu x1 Hl) as [HA|[HB|HC]].
  - destruct HA as (p1 & Hp1 & E). subst x1.
    destruct (cgr_lts_transfer p q (ActExt mu) p1 Hc Hp1) as (q1 & Hq1 & Hc1).
    exists (q1 ▷ m). split; [ apply fw_ext_left; exact Hq1 | ].
    exists p1, q1, m. split; [ reflexivity | split; [ reflexivity | exact Hc1 ] ].
  - destruct HB as (b & Hb & E). subst mu x1.
    exists (q ▷ ({[+ ActOut b +]} ⊎ m)). split; [ apply fw_input_always | ].
    exists p, q, ({[+ ActOut b +]} ⊎ m).
    split; [ reflexivity | split; [ reflexivity | exact Hc ] ].
  - destruct HC as (b & m' & Hb & HK & E). subst mu x1.
    exists (q ▷ m'). split.
    + rewrite HK. apply fw_emit.
    + exists p, q, m'. split; [ reflexivity | split; [ reflexivity | exact Hc ] ].
Qed.

Lemma run_cgr : forall (x y : proc * MO (ExtAct TypeOfActions)), x ⟹[[]] y ->
  forall z, Rcgr x z -> exists z', z ⟹[[]] z' /\ Rcgr y z'.
Proof.
  intros x y Hw. remember (nil : trace (ExtAct TypeOfActions)) as s eqn:Es.
  revert Es. induction Hw; intros Es z HR.
  - exists z. split; [ apply wt_nil | exact HR ].
  - subst s.
    destruct (step_cgr_tau _ z _ HR l) as (z1 & Hz1 & HR1).
    destruct (IHHw eq_refl z1 HR1) as (z' & Hz' & HR').
    exists z'. split; [ | exact HR' ]. eapply wt_tau; eassumption.
  - discriminate Es.
Qed.

Theorem Settles_cgr : forall S (p q : proc) m, p ≡* q ->
  Settles S (p ▷ m) -> Settles S (q ▷ m).
Proof.
  intros S p q m Hc (y & Hw & Hst & He).
  destruct (run_cgr _ y Hw (q ▷ m)) as (z' & Hz' & HR').
  { exists p, q, m. split; [ reflexivity | split; [ reflexivity | exact Hc ] ]. }
  exists z'. split; [ exact Hz' | ]. split.
  - apply stable_of_no_step. intros w Hw'.
    destruct HR' as (p1 & q1 & m1 & Ey & Ez & Hc1). subst y z'.
    destruct (step_cgr_tau (q1 ▷ m1) (p1 ▷ m1) w) as (w' & Hw'' & _).
    + exists q1, p1, m1.
      split; [ reflexivity | split; [ reflexivity | apply cgr_symm; exact Hc1 ] ].
    + exact Hw'.
    + eapply no_step_of_stable; eassumption.
  - intros d w r Hr.
    destruct HR' as (p1 & q1 & m1 & Ey & Ez & Hc1). subst y z'.
    destruct (step_cgr_ext (q1 ▷ m1) (p1 ▷ m1) (ActOut (d,w)) r) as (r' & Hr' & _).
    + exists q1, p1, m1.
      split; [ reflexivity | split; [ reflexivity | apply cgr_symm; exact Hc1 ] ].
    + exact Hr.
    + eapply He. exact Hr'.
Qed.

(** The payoff: a whole bag moves from the buffer into the process.  This
    is what turns a certificate for [g M] at a loaded buffer into one for
    the left-hand side [msgs d ‖ g M] that
    [ax_below_stable_split_bag] compares. *)

Theorem Settles_msgs_to_buffer : forall S (d : list TypeOfActions) (q : proc) k,
  Settles S (q ▷ (bag d ⊎ k)) -> Settles S ((msgs d ‖ q) ▷ k).
Proof.
  induction d as [|a d IH]; intros q k H; simpl in *.
  - eapply Settles_cgr; [ apply ax_nil_par | ].
    replace ((∅ : MO (ExtAct TypeOfActions)) ⊎ k) with k in H; [ exact H | ].
    symmetry. apply (left_id_L (∅ : MO (ExtAct TypeOfActions))
                       (@disj_union (MO (ExtAct TypeOfActions)) _)).
  - eapply Settles_cgr; [ | apply (IH (q ‖ ((fst a) ! (snd a) • 𝟘)) k) ].
    + apply cgr_symm.
      etransitivity; [ apply cgr_par_assoc | ].
      etransitivity; [ apply cgr_par_com | ].
      apply cgr_par_assoc.
    + apply Settles_msg_to_buffer.
      replace ({[+ ActOut a +]} ⊎ (bag d ⊎ k))
         with (({[+ ActOut a +]} ⊎ bag d) ⊎ k); [ exact H | ].
      symmetry. apply (assoc_L (@disj_union (MO (ExtAct TypeOfActions)) _)).
Qed.


(** * THE CONFIGURATION STEP AT DIFFERENT BAGS, FROM ONE CERTIFICATE

    Assembling the two: [Settles_msgs_to_buffer] turns a certificate
    stated at the **shifted buffer** [bag d ⊎ K] for the plain sum [g M]
    into one for the left-hand side [msgs d ‖ g M] at [K], which is what
    [ax_phaseA_direct] consumes; [ax_below_stable_split_bag] then puts the
    surplus back into the bag.

    Note what the hypothesis says, and that it is exactly the residue.
    [Settles (chans K) (g M ▷ (bag d ⊎ K))] asks the left to settle
    emitting **only within [chans K]** — so it must absorb the whole of
    [d], since a state still carrying those messages emits on [chans d]
    too.  That is the unstable-left case, and nothing else: were the left
    configuration stable, [VACCS_NormalForm.bags_agree] would force
    [d = []] and the hypothesis would degenerate to
    [VACCS_NormalForm.certificate_config]. *)

Theorem ax_below_split_from_certificate :
  forall (l d : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (forall K, OutOnly K ->
     ((g (mirrorN ((msgs d) ‖ ((g M) : proc)) N)) ▷ K) ↛ ->
     Settles (chans K) (((g M) : proc) ▷ (bag d ⊎ K))) ->
  (forall c v Q' l', subbag l' l -> lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ax_pre (msgs l' ‖ ((c ! v • 𝟘) ‖ ((msgs d) ‖ ((g M) : proc))))
            (msgs l' ‖ Q')) ->
  ax_pre (msgs (d ++ l) ‖ g M) (msgs l ‖ g N).
Proof.
  intros l d M N HM HN HstN Hcert Hrec.
  apply ax_below_stable_split_bag; [ exact HstN | | exact Hrec ].
  apply ax_phaseA_direct; [ | exact HN | exact HstN | ].
  - constructor; [ apply msgs_Static | apply static_g; exact HM ].
  - intros K Hout Hst. apply Settles_msgs_to_buffer. apply Hcert; assumption.
Qed.


(** * THE PRINCIPLE THE SET-BASED ROUTE RUNS ON

    Every failed route above needed the semantics to name a *specific*
    matching state, while [bhv_pre_cond2] — and its coinductive
    equivalent [DefinitionCI.copre] — only ever promise *some* element of
    a set.  The internal choice reconciles the two, and these three
    lemmas are the whole of the principle:

    - [ax_ichoice_some] — an internal choice sits **below** each of its
      members ([ax_ichoice_below], itself one [ax_tau_step]), so **one**
      good member places the whole choice below the target.  This is the
      direction the semantics supplies.
    - [ichoice_below_of_some] — the same reading semantically, through
      [soundness_ax].
    - [ax_ichoice_of_taus] — and the choice is **above** the process
      whenever every member is τ-reachable from it ([ax_ichoice_glb] fed
      by [ax_tau_run]).  This is how the set is entered.

    Together: a process may be replaced by the internal choice of its
    τ-reducts (going up), and that choice discharged by any single reduct
    that works (coming down).  [VACCS_Cond2.copre_settles_after] is what
    produces the good member after one action of the right-hand side,
    an emission included. *)

Lemma ax_ichoice_some : forall (L : list proc) (x q : proc),
  In x L -> ax_pre x q -> ax_pre (g (ichoice L)) q.
Proof.
  intros L x q Hin Hx. eapply ax_trans; [ apply ax_ichoice_below; exact Hin | exact Hx ].
Qed.

Lemma ichoice_below_of_some : forall (L : list proc) (x q : proc),
  In x L -> (x ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q) -> ((g (ichoice L)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q).
Proof.
  intros L x q Hin Hx t Ht.
  apply Hx. eapply soundness_ax; [ apply ax_ichoice_below; exact Hin | exact Ht ].
Qed.

Lemma ax_ichoice_of_taus : forall (L : list proc) (p : proc), L <> nil ->
  (forall x, In x L -> p ⟹[[]] x) -> ax_pre p (g (ichoice L)).
Proof.
  intros L p Hne Hall. apply ax_ichoice_glb; [ exact Hne | ].
  intros x Hin. apply ax_tau_run. apply Hall. exact Hin.
Qed.


(** And the certificate for an internal choice needs **one** member to
    settle — which is exactly the shape [DefinitionCI.c_now] promises. *)

Lemma Settles_ichoice : forall S (L : list proc) (x : proc) K,
  In x L -> Settles S (x ▷ K) -> Settles S ((g (ichoice L)) ▷ K).
Proof.
  intros S L x K Hin HS.
  eapply Settles_wt; [ | exact HS ].
  eapply wt_tau; [ apply fw_tau_left; apply lts_ichoice; exact Hin | apply wt_nil ].
Qed.

(** ** Why this is still not a short cut — recorded so it is not retried

    [ax_phaseA_direct] accepts an arbitrary [proc] on the left since the
    mirror was generalised, and [g (ichoice L)] is one, so Phase A does
    apply to a set-shaped left with no new rule.  But that does **not**
    close the gap, for a reason worth stating.

    [ax_settle_sim]'s premise is a [SettleSim], and a [SettleSim] relates
    *states of the LTS*: when the right performs an action, the left must
    answer by an actual transition of its own.  An internal choice's
    [μ]-reducts are the [μ]-reducts of its **members**, one at a time —
    the term [g (ichoice L')] collecting the *new* set is not an LTS
    reduct of [g (ichoice L)].  So a simulation cannot carry the set
    forward across an action, and after one step one is back to needing a
    *specific* member.

    The set therefore has to be carried by the **recursion that builds
    the derivation**, not by the simulation — which is exactly how VCCS's
    [CompletenessAx.ax_M_below] is organised, and why porting that layer
    is the remaining work rather than a new rule.  What is in place for
    it: [VACCS_Cond2.copre_step_single] and
    [VACCS_Cond2.copre_settles_after] to decompose the hypothesis one
    action at a time, [ax_ichoice_of_taus] to enter the set,
    [ax_ichoice_some] and [Settles_ichoice] to leave it by a single good
    member. *)


(** * SETS OF CONFIGURATIONS, SYNTACTICALLY

    The set-based recursion works with *configurations* — a process and a
    pending bag — and has to name them syntactically.  A configuration
    [(p, l)] is the forwarder state [p ▷ bag l] on the semantic side and
    the term [msgs l ‖ p] on the syntactic one; a set of them is their
    internal choice.

    [Settles_ichoice_cfg] is the brick the route turns on, in the form
    the derivation will use it: **one** configuration of the set settling
    is enough for the whole choice to settle, at the empty buffer.  It
    composes [Settles_msgs_to_buffer] (the bag moves from the buffer into
    the process) with [Settles_ichoice] (an internal choice inherits any
    member's settling, by one [τ]).

    That is exactly what [DefinitionCI.c_now] hands over — *some* element
    of the left set — so the two fit without a choice principle. *)

Definition cfg : Type := proc * list TypeOfActions.
Definition cfg_proc (c : cfg) : proc := msgs (snd c) ‖ (fst c).
Definition cfg_state (c : cfg) : proc * MO (ExtAct TypeOfActions) :=
  ((fst c) ▷ bag (snd c)).

Lemma Settles_cfg : forall S (c : cfg),
  Settles S (cfg_state c) -> Settles S ((cfg_proc c) ▷ (∅ : MO (ExtAct TypeOfActions))).
Proof.
  intros S (p, l) HS. unfold cfg_proc, cfg_state in *. simpl in *.
  apply Settles_msgs_to_buffer.
  match goal with |- Settles _ (_ ▷ @disj_union ?T ?d (bag l) ?e) =>
    assert (Eg : @disj_union T d (bag l) e = bag l)
      by (apply gmultiset_disj_union_right_id)
  end.
  rewrite Eg. exact HS.
Qed.

Definition ichoice_cfg (L : list cfg) : gproc := ichoice (map cfg_proc L).

Lemma Settles_ichoice_cfg : forall S (L : list cfg) (c : cfg),
  In c L -> Settles S (cfg_state c) ->
  Settles S ((g (ichoice_cfg L)) ▷ (∅ : MO (ExtAct TypeOfActions))).
Proof.
  intros S L c Hin HS. unfold ichoice_cfg.
  eapply Settles_ichoice; [ apply in_map; exact Hin | ].
  apply Settles_cfg. exact HS.
Qed.


(** ** From a SET of forwarder states to a list of configurations

    [DefinitionCI]'s sets live at the pair type, with an arbitrary
    multiset as buffer; the syntax needs a *list*.  The two are
    reconciled by [VACCS_Cond2.outonly_bag] — every buffer the forwarder
    reaches from [∅] is a bag — applied element by element down the
    list, which needs no choice principle.

    [copre_settles_ichoice_cfg] is then the junction the whole route was
    aiming at:

      the left **set** of a coinductive step, written as one internal
      choice of configurations, settles below the right's stable state.

    Its two halves are exactly the two sides of the mismatch that blocked
    every earlier route: [c_now] promises *some* element ([copre_now_settles]),
    and an internal choice inherits any member's settling
    ([Settles_ichoice_cfg]). *)

(** Every buffer the forwarder reaches from an [OutOnly] one is again
    [OutOnly]: messages enter only through [lts_multiset_add], which
    stores an output, so [fw_buffer_bounded] bounds the final buffer by
    the initial one together with a bag. *)

Lemma OutOnly_subseteq : forall (m m' : MO (ExtAct TypeOfActions)),
  m ⊆ m' -> OutOnly m' -> OutOnly m.
Proof.
  intros m m' Hsub Ho x Hx. apply Ho. eapply gmultiset_elem_of_subseteq; eassumption.
Qed.

Lemma OutOnly_disj : forall (m m' : MO (ExtAct TypeOfActions)),
  OutOnly m -> OutOnly m' -> OutOnly (m ⊎ m').
Proof.
  intros m m' H H' x Hx.
  apply gmultiset_elem_of_disj_union in Hx as [Hx|Hx]; [ apply H | apply H' ]; exact Hx.
Qed.

Lemma OutOnly_wt : forall s (x y : proc * MO (ExtAct TypeOfActions)),
  x ⟹[s] y -> OutOnly (snd x) -> OutOnly (snd y).
Proof.
  intros s x y Hw Ho.
  eapply OutOnly_subseteq; [ apply (fw_buffer_bounded s x y Hw) | ].
  apply OutOnly_disj; [ exact Ho | apply outonly_of_bag ].
Qed.

(** The list covers the set **and** contains nothing else — the second
    conjunct is what lets a caller conclude that every configuration of
    the list is a genuine reduct. *)

Lemma cfg_list_full : forall (xs : list (proc * MO (ExtAct TypeOfActions))),
  (forall x, In x xs -> OutOnly (snd x)) ->
  exists L : list cfg,
    (forall x, In x xs -> exists c, In c L /\ cfg_state c = x)
    /\ (forall c, In c L -> In (cfg_state c) xs).
Proof.
  induction xs as [|x xs IH]; intros Hall.
  - exists nil. split; [ intros y [] | intros c [] ].
  - destruct IH as (L & HL & HR); [ intros y Hy; apply Hall; right; exact Hy | ].
    destruct (outonly_bag (snd x) (Hall x (or_introl eq_refl))) as (k & Hk).
    assert (Ex : cfg_state (fst x, k) = x)
      by (unfold cfg_state; simpl; destruct x as (x1,x2); simpl in *; congruence).
    exists ((fst x, k) :: L). split.
    + intros y [E|Hin].
      * subst y. exists (fst x, k). split; [ left; reflexivity | exact Ex ].
      * destruct (HL y Hin) as (c & Hc & Ec).
        exists c. split; [ right; exact Hc | exact Ec ].
    + intros c [E|Hin].
      * subst c. left. symmetry. exact Ex.
      * right. apply HR. exact Hin.
Qed.

Lemma cfg_set_full : forall (X : gset (proc * MO (ExtAct TypeOfActions))),
  (forall x, x ∈ X -> OutOnly (snd x)) ->
  exists L : list cfg,
    (forall x, x ∈ X -> exists c, In c L /\ cfg_state c = x)
    /\ (forall c, In c L -> cfg_state c ∈ X).
Proof.
  intros X Hall.
  destruct (cfg_list_full (elements X)) as (L & HL & HR).
  - intros x Hx. apply Hall. apply elem_of_elements. apply list_elem_of_In. exact Hx.
  - exists L. split.
    + intros x Hx. apply HL. apply list_elem_of_In. apply elem_of_elements. exact Hx.
    + intros c Hc. apply elem_of_elements. apply list_elem_of_In. apply HR. exact Hc.
Qed.

Theorem copre_settles_ichoice_cfg :
  forall (X : gset (proc * MO (ExtAct TypeOfActions))) y,
  (forall x, x ∈ X -> OutOnly (snd x)) ->
  copre X ({[ y ]} : gset (proc * MO (ExtAct TypeOfActions))) -> X ⤓ -> y ↛ ->
  exists L : list cfg,
    (forall x, x ∈ X -> exists c, In c L /\ cfg_state c = x)
    /\ Settles (emits y) ((g (ichoice_cfg L)) ▷ (∅ : MO (ExtAct TypeOfActions))).
Proof.
  intros X y Hout Hco Ht Hst.
  destruct (cfg_set_full X Hout) as (L & HL & _).
  destruct (copre_now_settles X _ Hco Ht y (elem_of_singleton_2 _ _ eq_refl) Hst)
    as (x & Hx & HS).
  destruct (HL x Hx) as (c & Hc & Ec).
  exists L. split; [ exact HL | ].
  eapply Settles_ichoice_cfg; [ exact Hc | rewrite Ec; exact HS ].
Qed.


(** ** The set of a coinductive step, as one internal choice

    [VACCS_Cond2.copre_step_single] carries the hypothesis across **one**
    visible action and hands back the canonical set of the left's
    [μ]-reducts.  Every member of that set is reachable from
    [p ▷ bag l], so its buffer is again [OutOnly] ([OutOnly_wt]) and the
    set can be written as a list of configurations.

    The conclusion is the two halves of the mismatch that blocked every
    earlier route, now on the same object:

    - **every** configuration of the list is a genuine [μ]-reduct of the
      left, so the derivation may reason about the whole list;
    - the internal choice of the list **settles** below the right's
      stable state, because [c_now] promises *some* element and an
      internal choice inherits any member's settling.

    Taking [μ] to be an *emission* puts the left at the smaller buffer —
    the certificate below the bag, which no trace reading could produce
    since an emission cannot be replayed backwards. *)

Theorem copre_settles_ichoice_after :
  forall (l l' : list TypeOfActions) (p q : proc) mu y', Static p ->
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q)) ->
  ((q ▷ bag l') ⟶[mu] y') -> y' ↛ ->
  exists L : list cfg,
    (forall c, In c L -> (p ▷ bag l) ⟹{mu} (cfg_state c))
    /\ Settles (emits y') ((g (ichoice_cfg L)) ▷ (∅ : MO (ExtAct TypeOfActions))).
Proof.
  intros l l' p q mu y' Hp Hsem Hl Hst.
  assert (Hcnv : forall x, x ∈ ({[ (p ▷ bag l) ]} : gset (proc * MO (ExtAct TypeOfActions))) ->
                   x ⇓ [mu]).
  { intros x Hx. apply elem_of_singleton_1 in Hx. subst x.
    apply fw_converge_static. exact Hp. }
  destruct (copre_step_single _ _ (q ▷ bag l') y' mu
              (msgs_copre l l' p q Hsem) Hcnv
              (elem_of_singleton_2 _ _ eq_refl) Hl)
    as (X' & (Hs1 & Hs2) & Hco').
  assert (Hout : forall x, x ∈ X' -> OutOnly (snd x)).
  { intros x Hx. destruct (Hs1 x Hx) as (x0 & Hx0 & Hw).
    apply elem_of_singleton_1 in Hx0. subst x0.
    eapply OutOnly_wt; [ exact Hw | simpl; apply outonly_of_bag ]. }
  destruct (cfg_set_full X' Hout) as (L & HL & HR).
  edestruct (copre_now_settles X' _ Hco') as (x & Hx & HS).
  - apply SetLTSConstruction.termination_forall. intros z Hz.
    apply SetLTSConstruction.termination_set_if_termination.
    destruct (Hs1 z Hz) as (z0 & Hz0 & Hw).
    apply elem_of_singleton_1 in Hz0. subst z0.
    assert (Hz1 : Static z.1)
      by (eapply (fw_static_wt _ (p ▷ bag l)); [ exact Hp | exact Hw ]).
    destruct z as (z1, z2). simpl in Hz1.
    eapply fw_terminate_static; [ exact Hz1 | apply Nat.le_refl ].
  - apply elem_of_singleton_2. reflexivity.
  - exact Hst.
  - destruct (HL x Hx) as (c & Hc & Ec).
    exists L. split.
    + intros c0 Hc0. destruct (Hs1 (cfg_state c0) (HR c0 Hc0)) as (x0 & Hx0 & Hw).
      apply elem_of_singleton_1 in Hx0. subst x0. exact Hw.
    + eapply Settles_ichoice_cfg; [ exact Hc | rewrite Ec; exact HS ].
Qed.


(** ** Phase A, and the stable step, with a SET on the left

    The certificate is the only semantic content of Phase A, and for a
    single left-hand process it is a statement about *that* process.
    With an internal choice on the left it weakens to an **existential
    over the members** — because a choice inherits any member's settling
    ([Settles_ichoice]) — and that is exactly the shape the semantics
    delivers: [c_now] promises *some* element of the set
    ([copre_now_settles], [copre_settles_ichoice_after]), never a
    specific one.

    This is the mismatch that defeated every earlier route, resolved on
    the object where it can be: the internal choice, carried by the
    derivation rather than by the simulation (a [SettleSim] relates LTS
    states, so it cannot transport a set across an action — see the note
    at [ichoice_cfg]). *)

Lemma ichoice_gStatic : forall (L : list proc), Forall Static L -> gStatic (ichoice L).
Proof.
  induction L as [|p L IH]; intros Hall.
  - constructor.
  - inversion Hall as [|? ? Hp Hrest]; subst.
    destruct L as [|p2 L2].
    + simpl. repeat constructor; assumption.
    + simpl. constructor; [ constructor; assumption | apply IH; assumption ].
Qed.

Lemma cfg_Static : forall (L : list cfg),
  Forall (fun c => Static (cfg_proc c)) L -> Static (g (ichoice_cfg L)).
Proof.
  intros L Hall. apply static_g. unfold ichoice_cfg. apply ichoice_gStatic.
  apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx as (c & Ec & Hc). subst x.
  rewrite Forall_forall in Hall. apply Hall. exact Hc.
Qed.

Theorem ax_phaseA_ichoice : forall (L : list cfg) (N : gproc) (l : list TypeOfActions),
  Forall (fun c => Static (cfg_proc c)) L -> gStatic N ->
  (forall z, ~ lts (g N) τ z) ->
  (forall K, OutOnly K -> ((g (mirrorN (g (ichoice_cfg L)) N)) ▷ K) ↛ ->
     exists c, In c L /\ Settles (chans K) ((cfg_proc c) ▷ K)) ->
  ax_pre (msgs l ‖ g (ichoice_cfg L))
         (msgs l ‖ g (mirrorN (g (ichoice_cfg L)) N)).
Proof.
  intros L N l Hall HN Hnt Hcert.
  apply ax_phaseA_direct; [ apply cfg_Static; exact Hall | exact HN | exact Hnt | ].
  intros K HK Hst.
  destruct (Hcert K HK Hst) as (c & Hc & HS).
  unfold ichoice_cfg. eapply Settles_ichoice; [ apply in_map; exact Hc | exact HS ].
Qed.

(** The stable step at a set-shaped left: Phase A above, Phase B and the
    wrapped recursive premise unchanged.  Only the certificate differs
    from [ax_below_stable_sum_cfg], and it differs by being existential. *)

Theorem ax_below_stable_ichoice : forall (L : list cfg) (N : gproc) (l : list TypeOfActions),
  Forall (fun c => Static (cfg_proc c)) L -> gStatic N ->
  (forall p, ~ lts (g N) τ p) ->
  (forall K, OutOnly K -> ((g (mirrorN (g (ichoice_cfg L)) N)) ▷ K) ↛ ->
     exists c, In c L /\ Settles (chans K) ((cfg_proc c) ▷ K)) ->
  (forall c v Q' l', subbag l' l -> lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ax_pre (msgs l' ‖ ((c ! v • 𝟘) ‖ g (ichoice_cfg L))) (msgs l' ‖ Q')) ->
  ax_pre (msgs l ‖ g (ichoice_cfg L)) (msgs l ‖ g N).
Proof.
  intros L N l Hall HN Hnt Hcert Hrec.
  eapply ax_below_stable_sum_cfg; [ exact Hnt | | exact Hrec ].
  apply ax_phaseA_ichoice; assumption.
Qed.


(** The same at an arbitrary trace, via [VACCS_Cond2.copre_step_trace]:
    after the right-hand side runs [s] and settles, the set of states
    the left reaches over the **same** [s] settles below it, written as
    one internal choice of configurations.  [copre_settles_ichoice_after]
    is the case of a single action.  Taking [s] to contain emissions is
    what reaches the buffers *below* the bag. *)

Theorem copre_settles_ichoice_along :
  forall (s : trace (ExtAct TypeOfActions)) (l l' : list TypeOfActions) (p q : proc) y',
  Static p ->
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q)) ->
  ((q ▷ bag l') ⟹[s] y') -> y' ↛ ->
  exists L : list cfg,
    (forall c, In c L -> (p ▷ bag l) ⟹[s] (cfg_state c))
    /\ Settles (emits y') ((g (ichoice_cfg L)) ▷ (∅ : MO (ExtAct TypeOfActions))).
Proof.
  intros s l l' p q y' Hp Hsem Hw Hst.
  destruct (copre_step_trace s _ _ (q ▷ bag l') y'
              (msgs_copre l l' p q Hsem)
              (fun x Hx => ltac:(apply elem_of_singleton_1 in Hx; subst x; exact Hp))
              (elem_of_singleton_2 _ _ eq_refl) Hw)
    as (X' & Hs1 & Hco').
  assert (Hout : forall x, x ∈ X' -> OutOnly (snd x)).
  { intros x Hx. destruct (Hs1 x Hx) as (x0 & Hx0 & Hwx).
    apply elem_of_singleton_1 in Hx0. subst x0.
    eapply OutOnly_wt; [ exact Hwx | simpl; apply outonly_of_bag ]. }
  destruct (cfg_set_full X' Hout) as (L & HL & HR).
  edestruct (copre_now_settles X' _ Hco') as (x & Hx & HS).
  - apply SetLTSConstruction.termination_forall. intros z Hz.
    apply SetLTSConstruction.termination_set_if_termination.
    destruct (Hs1 z Hz) as (z0 & Hz0 & Hwz).
    apply elem_of_singleton_1 in Hz0. subst z0.
    assert (Hz1 : Static z.1)
      by (eapply (fw_static_wt _ (p ▷ bag l)); [ exact Hp | exact Hwz ]).
    destruct z as (z1, z2). simpl in Hz1.
    eapply fw_terminate_static; [ exact Hz1 | apply Nat.le_refl ].
  - apply elem_of_singleton_2. reflexivity.
  - exact Hst.
  - destruct (HL x Hx) as (c & Hc & Ec).
    exists L. split.
    + intros c0 Hc0. destruct (Hs1 (cfg_state c0) (HR c0 Hc0)) as (x0 & Hx0 & Hwx).
      apply elem_of_singleton_1 in Hx0. subst x0. exact Hwx.
    + eapply Settles_ichoice_cfg; [ exact Hc | rewrite Ec; exact HS ].
Qed.


(** ** Entering the set: a configuration is below the choice of its τ-reducts

    [ax_ichoice_of_taus] enters an internal choice whenever every member
    is τ-reachable.  At a *configuration* the τ-reducts are again
    configurations — a forwarder [τ] is either the process's own step or
    a **delivery** ([fw_tau_shape]) — but the two sides live in
    different LTSs: [(p ▷ bag l)] in the forwarder, [msgs l ‖ p] in the
    syntax.  [cfg_tau_transfer] is the bridge, and it is where the
    asynchrony shows: a delivery is a *synchronisation* on the syntactic
    side, between one message pulled out of the bag by [msgs_perm] and
    the process's input, so the reached term is only **structurally
    congruent** to the configuration it names.

    That [≡*] slack costs nothing, because the consumer is a derivation:
    [ax_ichoice_of_cfg] absorbs it with one [ax_cgr]. *)

Lemma ax_ichoice_of_cfg : forall (L : list cfg) (r : proc), L <> nil ->
  (forall c, In c L -> exists u, r ⟹[[]] u /\ u ≡* cfg_proc c) ->
  ax_pre r (g (ichoice_cfg L)).
Proof.
  intros L r Hne Hall. unfold ichoice_cfg.
  apply ax_ichoice_glb.
  - intro E. apply Hne. destruct L; [ reflexivity | discriminate E ].
  - intros x Hx. apply in_map_iff in Hx as (c & Ec & Hc). subst x.
    destruct (Hall c Hc) as (u & Hw & Hcgr).
    eapply ax_trans; [ apply ax_tau_run; exact Hw | apply ax_cgr; exact Hcgr ].
Qed.

Lemma bag_split_msg : forall (l : list TypeOfActions) a m,
  bag l = {[+ ActOut a +]} ⊎ m -> exists l', Permutation l (a :: l') /\ m = bag l'.
Proof.
  intros l a m Heq.
  assert (Hin : ActOut a ∈ bag l).
  { rewrite Heq. apply gmultiset_elem_of_disj_union. left.
    apply gmultiset_elem_of_singleton. reflexivity. }
  apply bag_elem in Hin. apply in_split in Hin as (l1 & l2 & E). subst l.
  exists (l1 ++ l2). split.
  - symmetry. apply Permutation_middle.
  - assert (Hp : Permutation (l1 ++ a :: l2) (a :: l1 ++ l2))
      by (symmetry; apply Permutation_middle).
    apply bag_perm in Hp. rewrite Hp in Heq. simpl in Heq.
    eapply gmultiset_disj_union_inj_1. symmetry. exact Heq.
Qed.

Lemma cfg_tau_transfer : forall (p : proc) (l : list TypeOfActions) x,
  ((p ▷ bag l) ⟶ x) ->
  exists (p' : proc) (l' : list TypeOfActions) (r : proc),
    x = (p' ▷ bag l') /\ lts (msgs l ‖ p) τ r /\ r ≡* (msgs l' ‖ p').
Proof.
  intros p l x Hl.
  apply fw_tau_shape in Hl as [ (p' & Hp' & Ex) | (a & p' & m' & Hm & Hin & Ex) ].
  - exists p', l, (msgs l ‖ p'). split; [ exact Ex | ].
    split; [ apply lts_parR; exact Hp' | apply cgr_refl ].
  - apply bag_split_msg in Hm as (l0 & Hperm & Em). subst m'.
    exists p', l0.
    assert (Hc : msgs l ‖ p ≡* (msgs (a :: l0)) ‖ p).
    { apply cgr_fullpar; [ apply msgs_perm; exact Hperm | apply cgr_refl ]. }
    destruct a as (c,v). simpl in Hin.
    assert (Hstep : lts ((msgs ((c,v) :: l0)) ‖ p) τ ((g 𝟘 ‖ msgs l0) ‖ p')).
    { simpl. eapply lts_comL; [ apply lts_parL; apply lts_output | exact Hin ]. }
    destruct (Congruence_Respects_Transition (msgs l ‖ p) ((g 𝟘 ‖ msgs l0) ‖ p') τ
                (ex_intro _ _ (conj Hc Hstep))) as (r & Hr & Hcr).
    exists r. split; [ exact Ex | ]. split; [ exact Hr | ].
    eapply cgr_trans; [ exact Hcr | ].
    apply cgr_fullpar; [ | apply cgr_refl ].
    etransitivity; [ apply cgr_par_com | apply cgr_par_nil ].
Qed.

Lemma cfg_tau_run_transfer : forall (x y : proc * MO (ExtAct TypeOfActions)),
  x ⟹[[]] y ->
  forall p l r, x = (p ▷ bag l) -> r ≡* (msgs l ‖ p) ->
  exists p' l' r', y = (p' ▷ bag l') /\ r ⟹[[]] r' /\ r' ≡* (msgs l' ‖ p').
Proof.
  intros x y Hw. remember (nil : trace (ExtAct TypeOfActions)) as s eqn:Hs.
  induction Hw as [x0|s0 x0 q0 y0 Hl Hwt IH|mu s0 x0 q0 y0 Hl Hwt IH];
    intros p l r Ex Hcgr.
  - subst x0. exists p, l, r.
    split; [ reflexivity | split; [ apply wt_nil | exact Hcgr ] ].
  - subst x0.
    destruct (cfg_tau_transfer p l q0 Hl) as (p1 & l1 & r1 & Eq & Hstep & Hc1).
    destruct (Congruence_Respects_Transition r r1 τ (ex_intro _ _ (conj Hcgr Hstep)))
      as (r2 & Hr2 & Hc2).
    assert (Hc3 : r2 ≡* msgs l1 ‖ p1) by (etransitivity; [ exact Hc2 | exact Hc1 ]).
    destruct (IH Hs p1 l1 r2 Eq Hc3) as (p' & l' & r' & Ey & Hrun & Hc').
    exists p', l', r'. split; [ exact Ey | ].
    split; [ eapply wt_tau; [ exact Hr2 | exact Hrun ] | exact Hc' ].
  - discriminate Hs.
Qed.

Theorem ax_cfg_below_ichoice : forall (p : proc) (l : list TypeOfActions) (L : list cfg),
  L <> nil ->
  (forall c, In c L -> (p ▷ bag l) ⟹[[]] (cfg_state c)) ->
  ax_pre (msgs l ‖ p) (g (ichoice_cfg L)).
Proof.
  intros p l L Hne Hall. apply ax_ichoice_of_cfg; [ exact Hne | ].
  intros c Hc.
  assert (Hrefl : msgs l ‖ p ≡* msgs l ‖ p) by reflexivity.
  destruct (cfg_tau_run_transfer _ _ (Hall c Hc) p l (msgs l ‖ p) eq_refl Hrefl)
    as (p' & l' & r' & Ey & Hrun & Hc').
  exists r'. split; [ exact Hrun | ].
  unfold cfg_state in Ey. destruct c as (c1, c2). simpl in *.
  injection Ey as E1 E2. subst p'.
  eapply cgr_trans; [ exact Hc' | ]. unfold cfg_proc. simpl.
  apply cgr_fullpar; [ apply bag_msgs_eq; symmetry; exact E2 | apply cgr_refl ].
Qed.


(** ** The drain-then-refill certificate, at the SET level

    This is the point of the whole set-based route.  Compare the
    single-process certificates:

    - [VACCS_Cond2.surplus_settles_bag] settles at buffers **above** the
      bag, because feeding is reversible ([fw_feed_inv_list]) while
      emission is not;
    - [VACCS_NormalForm.surplus_settles_drain] reaches the buffers
      *below* the bag by first draining it — at the price of a side
      condition, "the drain run is forced", whose only obstruction is
      **regeneration** ([drain_forced_no_regen]); and the mirror's own
      guards are copycats, which regenerate.

    Here the side condition simply **evaporates**.  Reading
    [bhv_pre_cond2] along [map ActOut l ++ feed k] leaves the left at
    *some* state, and the single-process argument had to pin down which
    one; the set carries them all, and [c_now] then promises that one of
    them settles.  So the certificate holds at **every** buffer the
    right-hand side refuses — above the bag and below it alike — from
    the configuration hypothesis alone. *)

Theorem cfg_certificate_drain :
  forall (l k : list TypeOfActions) (p : proc) (N : gproc),
  Static p -> gStatic N ->
  (forall z, ~ lts (g N) τ z) ->
  (forall a, ActOut a ∈ bag k -> forall r, ~ lts (g N) (ActExt (ActIn a)) r) ->
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
  exists L : list cfg,
    (forall c, In c L -> (p ▷ bag l) ⟹[map ActOut l ++ feed k] (cfg_state c))
    /\ Settles (chans (bag k)) ((g (ichoice_cfg L)) ▷ (∅ : MO (ExtAct TypeOfActions))).
Proof.
  intros l k p N Hp HN HstN Hnoc Hsem.
  assert (Hsty : ((g N) ▷ bag k) ↛).
  { assert (Hnostep : forall x, ~ (((g N) ▷ bag k) ⟶ x)).
    { apply fw_stable_iff. split; [ exact HstN | ].
      intros a Hin q Hq. eapply Hnoc; [ exact Hin | exact Hq ]. }
    destruct (decide (lts_refuses ((g N) ▷ bag k) τ)) as [Hy|Hn]; [ exact Hy | ].
    exfalso. apply lts_refuses_spec1 in Hn as (z & Hz). eapply Hnostep. exact Hz. }
  destruct (copre_settles_ichoice_along (map ActOut l ++ feed k) l l p (g N)
              ((g N) ▷ bag k) Hp Hsem (drain_refill_run N l k) Hsty)
    as (L & HL & HS).
  exists L. split; [ exact HL | ].
  eapply Settles_mono; [ | exact HS ].
  intros d Hd. eapply emits_gsum_chans. exact Hd.
Qed.


(** ** Where the set can and cannot be entered — the delimitation

    [Settles_tau_reduct] says the certificate is inherited **backwards**
    along an internal run ([fw_wt_lift] + [Settles_wt]).  Hence
    [Settles_of_some_reduct]: an existential over τ-reducts is worth
    nothing, since it collapses to the certificate for the process
    itself.  So the whole gain of an internal choice on the left must
    come from members that are *not* τ-reducts.

    And those cannot be entered.  Going up to an internal choice needs
    every member derivably above the original ([ax_ichoice_glb], the
    engine of [ax_ichoice_of_cfg]); a state reached after an **emission**
    is not, because messages are rigid
    ([VACCS_DropProbes.msg_not_below_nil] / [nil_not_below_msg]).  That
    is precisely what [cfg_certificate_drain]'s members are: reached over
    [map ActOut l ++ feed k].

    So the two ends do not meet, and the reason is not a missing lemma:

    - the *entry* ([ax_cfg_below_ichoice]) admits only τ-reducts, where
      the set is redundant by the two lemmas below;
    - the *exit* ([cfg_certificate_drain]) delivers a set of
      drain-reachable states, which no derivation can climb to;
    - and a [SettleSim] cannot bridge them, since it relates LTS
      *states* while [copre] relates *sets* — the note at [ichoice_cfg].

    [cfg_certificate_drain] therefore stands as a strictly stronger
    **semantic** fact (the certificate at every refused buffer, with no
    non-regeneration side condition), not as a step of a derivation. *)

Lemma Settles_tau_reduct : forall S (p p' : proc) K,
  p ⟹[[]] p' -> Settles S (p' ▷ K) -> Settles S (p ▷ K).
Proof.
  intros S p p' K Hw HS. eapply Settles_wt; [ | exact HS ].
  apply (fw_wt_lift [] p p' K Hw).
Qed.

Lemma Settles_of_some_reduct : forall S (p : proc) K (L : list proc),
  (forall x, In x L -> p ⟹[[]] x) ->
  (exists x, In x L /\ Settles S (x ▷ K)) ->
  Settles S (p ▷ K).
Proof.
  intros S p K L Hall (x & Hx & HS).
  eapply Settles_tau_reduct; [ apply Hall; exact Hx | exact HS ].
Qed.


(** ** The escape channel is inside the footprint — the client is finite

    Lifting [VACCS_Absorb.emits_in_pchans] to the forwarder: along an
    **internal** run, an emission comes either from the process (so its
    channel is in the process's footprint, [fw_conservation] projecting
    the run) or from the buffer (so it is one of the buffer's channels,
    [fw_buffer_bounded] with an empty trace).

    [EscapesOutside S x] is the constructive negation of [Settles S x]:
    *every* stable state reachable from [x] emits on some channel
    outside [S].  Stating it positively avoids a de Morgan step that
    would need decidability of [emits].

    [escapes_in_pchans] is the point.  If [(P ▷ K)] escapes [chans K],
    the escaping channel cannot be one of the buffer's, so it lies in
    [pchans P] — a **finite, syntactically computable** set.  The
    separating client can therefore be the guarded sum
    [Σ_{d ∈ pchans P, d ∉ chans K} d ? ①], which is a term of the
    calculus.  That was the one thing the construction needed and could
    not have without a footprint. *)

Lemma fw_emits_pchans_nil : forall (x y : proc * MO (ExtAct TypeOfActions)) d w r,
  Static (fst x) -> x ⟹[[]] y -> (y ⟶[ActOut (d,w)] r) ->
  In d (pchans (fst x)) \/ chans (snd x) d.
Proof.
  intros x y d w r Hst Hw Hl.
  destruct y as (y1,y2). simpl in *.
  destruct (fw_ext_shape y1 y2 (ActOut (d,w)) r Hl) as
    [ (p' & Hp' & Ey) | [ (a & Ha & Ey) | (a & m' & Ha & Hm & Ey) ] ].
  - left.
    destruct (fw_conservation [] x (y1,y2) Hw) as (rr & Hrun & _).
    simpl in Hrun.
    assert (Hsy : Static y1)
      by (eapply (fw_static_wt [] x (y1,y2)); [ exact Hst | exact Hw ]).
    eapply wt_pchans; [ exact Hst | exact Hrun | ].
    eapply lts_pchans_out; [ exact Hsy | exact Hp' | reflexivity ].
  - discriminate Ha.
  - right. injection Ha as Ha. subst a.
    pose proof (fw_buffer_bounded [] x (y1,y2) Hw) as Hb. simpl in Hb.
    exists w.
    assert (Hb2 : y2 ⊆ x.2).
    { replace (x.2) with (x.2 ⊎ (∅ : MO (ExtAct TypeOfActions)))
        by (apply gmultiset_disj_union_right_id). exact Hb. }
    eapply gmultiset_elem_of_subseteq; [ | exact Hb2 ].
    rewrite Hm. apply gmultiset_elem_of_disj_union. left.
    apply gmultiset_elem_of_singleton. reflexivity.
Qed.

Definition EscapesOutside (S : ChannelData -> Prop)
                          (x : proc * MO (ExtAct TypeOfActions)) : Prop :=
  forall y, x ⟹[[]] y -> y ↛ ->
    exists d w r, (y ⟶[ActOut (d,w)] r) /\ ~ S d.

Lemma escapes_not_settles : forall S x, Static (fst x) ->
  EscapesOutside S x -> ~ Settles S x.
Proof.
  intros S x Hst Hesc (y & Hw & Hsty & Hem).
  destruct (Hesc y Hw Hsty) as (d & w & r & Hr & Hnot).
  apply Hnot. eapply Hem. exact Hr.
Qed.

Lemma escapes_in_pchans : forall (P : proc) K, Static P ->
  EscapesOutside (chans K) (P ▷ K) ->
  forall y, ((P ▷ K) ⟹[[]] y) -> y ↛ ->
    exists d w r, (y ⟶[ActOut (d,w)] r) /\ ~ chans K d /\ In d (pchans P).
Proof.
  intros P K Hst Hesc y Hw Hsty.
  destruct (Hesc y Hw Hsty) as (d & w & r & Hr & Hnot).
  exists d, w, r. split; [ exact Hr | ]. split; [ exact Hnot | ].
  destruct (fw_emits_pchans_nil (P ▷ K) y d w r Hst Hw Hr) as [Hin|Hin].
  - simpl in Hin. exact Hin.
  - exfalso. apply Hnot. simpl in Hin. exact Hin.
Qed.


(** ** The separating client itself

    [probes L] is [Σ_{d ∈ L} d ? ①] — a finite guarded sum, which is
    what [escapes_in_pchans] makes possible: the channels to listen on
    can be taken from [pchans P], a finite syntactic set.

    Its three structural properties are what the [must] argument will
    consume: it is **not good** (so [nh] is satisfiable), it has **no
    τ** (so [must]'s [et] field is vacuous and the client can never move
    on its own), and it accepts an input on every channel of [L],
    becoming [①] — good — at once.  [EscapesOutside_run] says the
    escaping hypothesis survives internal steps, which is the invariant
    the induction on termination will carry. *)

Fixpoint probes (L : list ChannelData) : gproc :=
match L with
| [] => 𝟘
| d :: L' => (d ? (g ①)) + probes L'
end.

Lemma probes_not_good : forall L, ~ good_VACCS (g (probes L)).
Proof.
  induction L as [|d L IH]; intro Hg; simpl in Hg.
  - inversion Hg.
  - inversion Hg; subst.
    match goal with H : _ \/ _ |- _ => destruct H as [H|H] end.
    + inversion H0.
    + apply IH. exact H0.
Qed.

Lemma probes_no_tau : forall L z, ~ lts (g (probes L)) τ z.
Proof.
  induction L as [|d L IH]; intros z Hz; simpl in Hz; inversion Hz; subst.
  - inversion H3.
  - eapply IH. eassumption.
Qed.

Lemma probes_in : forall L d v, In d L ->
  lts (g (probes L)) (ActExt (ActIn (d,v))) (g ①).
Proof.
  induction L as [|c L IH]; intros d v Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [E|Hin].
    + subst c. simpl. apply lts_choiceL.
      assert (E : (g ① : proc) = ((g ①) ^ v)) by reflexivity.
      rewrite E at 2. apply lts_input.
    + simpl. apply lts_choiceR. apply IH. exact Hin.
Qed.

Lemma EscapesOutside_run : forall S x x',
  EscapesOutside S x -> x ⟹[[]] x' -> EscapesOutside S x'.
Proof.
  intros S x x' Hesc Hw y Hwy Hsty.
  apply Hesc; [ eapply wt_join_nil; [ exact Hw | exact Hwy ] | exact Hsty ].
Qed.


(** ** The client SEPARATES — both halves proved

    [escapes_must_probes] is the left half, by induction on
    **termination** ([fw_terminate_static]) with [EscapesOutside] as the
    invariant ([EscapesOutside_run] carries it across each τ):

    - [nh] : the probe is not good;
    - [ex] : either the state has a τ — take it — or it is stable, and
      then [escapes_in_pchans] hands over an emission on a channel of
      [pchans P] outside [chans K], with which [probes_in] synchronises;
    - [pt] : the induction hypothesis;
    - [et] : vacuous, the probe has no τ of its own;
    - [com] : any transition of the probe lands on [①]
      ([probes_lts_target]), which is good — so [m_now] closes it.

    [settled_fails_probes] is the right half, and it is a single
    inversion: a state that is stable and emits on no channel of [L] has
    no step at all in the pair, so [must]'s [ex] field cannot be
    satisfied.

    Together: a left that **escapes** [chans K] passes a client that
    every state **settling within** [chans K] fails.  That is the
    contrapositive of the certificate, and it is what a proof of Phase A
    for an unstable configuration has to be built from. *)

Lemma probes_lts_target : forall L a t', lts (g (probes L)) a t' -> t' = (g ①).
Proof.
  induction L as [|d L IH]; intros a t' Hl; simpl in Hl; inversion Hl; subst.
  - inversion H3; subst. reflexivity.
  - eapply IH. eassumption.
Qed.

Lemma probes_lts_in_inv : forall L a t', lts (g (probes L)) a t' ->
  exists d v, a = ActExt (ActIn (d,v)) /\ In d L.
Proof.
  induction L as [|c L IH]; intros a t' Hl; simpl in Hl; inversion Hl; subst.
  - inversion H3; subst. exists c, v. split; [ reflexivity | left; reflexivity ].
  - destruct (IH _ _ H3) as (d & v & Ha & Hin).
    exists d, v. split; [ exact Ha | right; exact Hin ].
Qed.

Theorem escapes_must_probes : forall (P : proc) K L, Static P ->
  (forall d, In d (pchans P) -> ~ chans K d -> In d L) ->
  EscapesOutside (chans K) (P ▷ K) ->
  forall x, x ⤓ -> ((P ▷ K) ⟹[[]] x) -> x must_pass (g (probes L)).
Proof.
  intros P K L HP HL Hesc x Ht. induction Ht as [x Hacc IH]. intros Hw.
  apply m_step.
  - apply probes_not_good.
  - destruct (decide (lts_refuses x τ)) as [Hs|Hn].
    + destruct (escapes_in_pchans P K HP Hesc x Hw Hs) as (d & w & r & Hr & Hnot & Hin).
      exists (r, (g ① : proc)).
      eapply (ParSync (ActOut (d,w)) (ActIn (d,w)));
        [ reflexivity | exact Hr | apply probes_in; apply HL; assumption ].
    + apply lts_refuses_spec1 in Hn as (z & Hz).
      exists (z, (g (probes L) : proc)). apply ParLeft. exact Hz.
  - intros x' Hx'. apply IH; [ exact Hx' | ].
    eapply wt_push_nil_right; [ exact Hw | eapply wt_tau; [ exact Hx' | apply wt_nil ] ].
  - intros t' Ht'. exfalso. eapply probes_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hdual Hp' Ht'.
    apply m_now. rewrite (probes_lts_target L _ _ Ht'). constructor.
Qed.

Corollary escapes_passes : forall (P : proc) K L, Static P ->
  (forall d, In d (pchans P) -> ~ chans K d -> In d L) ->
  EscapesOutside (chans K) (P ▷ K) ->
  (P ▷ K) must_pass (g (probes L)).
Proof.
  intros P K L HP HL Hesc.
  eapply escapes_must_probes; [ exact HP | exact HL | exact Hesc | | apply wt_nil ].
  eapply fw_terminate_static; [ exact HP | apply Nat.le_refl ].
Qed.

Lemma settled_fails_probes : forall (y : proc * MO (ExtAct TypeOfActions)) L,
  y ↛ -> (forall d, In d L -> forall w r, ~ (y ⟶[ActOut (d,w)] r)) ->
  ~ (y must_pass (g (probes L))).
Proof.
  intros y L Hst Hno Hm. destruct Hm as [Hg | Hnh Hex Hpt Het Hcom ].
  - eapply probes_not_good. exact Hg.
  - destruct Hex as (z & Hz). inversion Hz; subst.
    + eapply no_step_of_stable; [ exact Hst | eassumption ].
    + eapply probes_no_tau. eassumption.
    + destruct (probes_lts_in_inv L _ _ l2) as (d & v & Ha & Hin).
      injection Ha as Ha. subst μ2.
      destruct μ1 as [a|a]; simpl in eq; [ inversion eq | ].
      inversion eq; subst. eapply Hno; [ exact Hin | exact l1 ].
Qed.


(** ** The sink — how a test reaches buffers BELOW the bag

    The assembly needs a test for the whole *configuration*, whose
    buffer is [bag l], while the certificate speaks of an arbitrary
    buffer [K].  A test can only ever *add* messages — its own outputs —
    so it reaches [K ⊇ bag l]; that is the buffer locality which has
    blocked every route.

    But a test can also **take messages away**.  An input guard with
    continuation [𝟘] — a *sink* — absorbs a message without becoming
    good.  So the test to build is

      msgs K  ‖  sinks (chans (bag l) minus chans K)  ‖  probes L

    supplying [K]'s messages, draining the bag's surplus, and watching
    for an emission outside [chans K].  This is the first way seen of
    getting **below** the bag at the level of tests, where the trace
    reading could not: an emission cannot be replayed, but it can be
    absorbed.

    [sinks] and its structural lemmas mirror [probes] exactly, with [𝟘]
    in place of [①] — which is the whole point: [sinks_not_good] is what
    makes absorption invisible to the outcome. *)

Fixpoint sinks (L : list ChannelData) : gproc :=
match L with
| [] => 𝟘
| d :: L' => (d ? (g 𝟘)) + sinks L'
end.

Lemma sinks_not_good : forall L, ~ good_VACCS (g (sinks L)).
Proof.
  induction L as [|d L IH]; intro Hg; simpl in Hg.
  - inversion Hg.
  - inversion Hg; subst.
    match goal with H : _ \/ _ |- _ => destruct H as [H|H] end.
    + inversion H0.
    + apply IH. exact H0.
Qed.

Lemma sinks_no_tau : forall L z, ~ lts (g (sinks L)) τ z.
Proof.
  induction L as [|d L IH]; intros z Hz; simpl in Hz; inversion Hz; subst.
  - inversion H3.
  - eapply IH. eassumption.
Qed.

Lemma sinks_in : forall L d v, In d L ->
  lts (g (sinks L)) (ActExt (ActIn (d,v))) (g 𝟘).
Proof.
  induction L as [|c L IH]; intros d v Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [E|Hin].
    + subst c. simpl. apply lts_choiceL.
      assert (E : (g 𝟘 : proc) = ((g 𝟘) ^ v)) by reflexivity.
      rewrite E at 2. apply lts_input.
    + simpl. apply lts_choiceR. apply IH. exact Hin.
Qed.

Lemma sinks_lts_target : forall L a t', lts (g (sinks L)) a t' -> t' = (g 𝟘).
Proof.
  induction L as [|d L IH]; intros a t' Hl; simpl in Hl; inversion Hl; subst.
  - inversion H3; subst. reflexivity.
  - eapply IH. eassumption.
Qed.

Lemma sinks_lts_in_inv : forall L a t', lts (g (sinks L)) a t' ->
  exists d v, a = ActExt (ActIn (d,v)) /\ In d L.
Proof.
  induction L as [|c L IH]; intros a t' Hl; simpl in Hl; inversion Hl; subst.
  - inversion H3; subst. exists c, v. split; [ reflexivity | left; reflexivity ].
  - destruct (IH _ _ H3) as (d & v & Ha & Hin).
    exists d, v. split; [ exact Ha | right; exact Hin ].
Qed.


(** ** The composed test

    **Scope, checked before building on it.**  The left half does *not*
    go through for the composed test, and the reason is worth stating
    rather than discovering twice.  [escapes_must_probes] needs the
    escape hypothesis at **every stable state the server can reach**,
    and [EscapesOutside (chans K) (P ▷ K)] delivers exactly that — but
    only for the states reachable *internally from the buffer [K]*.  As
    soon as the test interferes, the buffer moves: handing a message of
    [kk] over enlarges it, a sink absorbing an emission shrinks it, and
    the server visits intermediate buffers about which the hypothesis
    says nothing.  A run that settles quietly at one of those deadlocks
    the pair, and [must] fails.

    So the contrapositive of the certificate — escape at the *single*
    buffer [K] — is strictly weaker than what a test-based argument
    consumes.  It is the same ∀/∃ mismatch as everywhere else in this
    development, in a new guise: a test observes *all* runs, while the
    certificate is about *one*.

    **And the design error is now identified**, by reading the
    repository's own test generator ([VACCS_ta_tc_gen.gen_test_raw], see
    the note at [VACCS_Cond2.settles_or_test]).  Two things are wrong
    with composing the phases in **parallel**:

    - a permanently available escape is fatal.  A test that can always
      [τ] to [①] is passed by *every* terminating server: [ex] is met by
      that [τ], [et] lands on a good state, and [pt] recurses.  So the
      escape must sit on a **prefix that gets consumed**, not beside the
      probe forever;
    - conversely, a driving phase with **no** escape is deadlockable by
      a deviating run — which is what kills the left half here.

    [gen_test_raw] has it both ways because it is **sequential**: each
    absorbing guard carries [+ 𝛕 • ①] and a wrong value falls to [①], so
    deviations are forgiven, but each synchronisation *shortens* the
    test, and the chain ends on the strict probe with no escape at all.
    The obligation that bites is [com], not [ex].

    So a composed test for this argument has to be built as a chain, in
    that style — and [gen_acc E (coₜ s)] at the drain-then-refill trace
    already is one.  What that still does not give is a certificate at a
    buffer the trace merely *passes through*: the dichotomy's good
    branch produces a state reachable **over the trace**, never one
    reachable **internally from [(P ▷ K)]**, and the bridge between the
    two exists for inputs ([fw_feed_inv_list]) and not for outputs.
    That is the residue, in its final form.

    What is proved and stands: the pure-probe half
    ([escapes_must_probes], [escapes_passes]) at the state itself, and
    the composed test's structure below — [probe_test_lts_inv] pins its
    moves down completely, and [settled_fails_test] is the right half.
    What the composed test would need is an escape hypothesis along the
    whole reachable set, which is not what a failing certificate gives.

    [probe_test kk Ls L] supplies the messages of [kk], drains with
    sinks on [Ls], and watches with probes on [L].  Its three parts play
    the three roles the assembly needs — *add*, *remove*, *observe* —
    and only the first two are new: [probes] alone could never reach a
    buffer below the bag.

    [probe_test_not_good] is the field [nh] of any [must] against it,
    and it holds for the reason the design turns on: a message is not
    good, a sink is not good (its continuation is [𝟘]), and only the
    probes can ever produce [①] — after an actual emission. *)

Lemma msgs_not_good : forall (kk : list TypeOfActions), ~ good_VACCS (msgs kk).
Proof.
  induction kk as [|a kk IH]; intro Hg; simpl in Hg.
  - inversion Hg.
  - inversion Hg; subst.
    match goal with H : _ \/ _ |- _ => destruct H as [H|H] end.
    + inversion H0.
    + apply IH. exact H0.
Qed.

Definition probe_test (kk : list TypeOfActions) (Ls L : list ChannelData) : proc :=
  msgs kk ‖ ((g (sinks Ls)) ‖ (g (probes L))).

Lemma probe_test_not_good : forall kk Ls L, ~ good_VACCS (probe_test kk Ls L).
Proof.
  intros kk Ls L Hg. unfold probe_test in Hg. inversion Hg; subst.
  match goal with H : _ \/ _ |- _ => destruct H as [H|H] end.
  - eapply msgs_not_good. exact H0.
  - inversion H0; subst.
    match goal with H' : _ \/ _ |- _ => destruct H' as [H'|H'] end.
    + eapply sinks_not_good. exact H1.
    + eapply probes_not_good. exact H1.
Qed.


(** The composed test never moves on its own — under exactly the
    disjointness the construction will supply ([kk]'s channels lie
    inside [chans K], the sinks' and probes' outside it).  Both
    synchronisations inside the test are ruled out for their own reason:
    a guarded sum never emits ([gsum_no_out]), and a message bag never
    inputs ([msgs_no_input]); what is left is a message meeting a guard,
    and that is precisely what the disjointness forbids. *)

Lemma sinks_probes_no_tau : forall Ls L z,
  ~ lts ((g (sinks Ls)) ‖ (g (probes L))) τ z.
Proof.
  intros Ls L z Hz. inversion Hz; subst.
  - eapply gsum_no_out; eassumption.
  - eapply gsum_no_out; eassumption.
  - eapply sinks_no_tau; eassumption.
  - eapply probes_no_tau; eassumption.
Qed.

Lemma sinks_probes_in_inv : forall Ls L a t',
  lts ((g (sinks Ls)) ‖ (g (probes L))) a t' ->
  exists d v, a = ActExt (ActIn (d,v)) /\ (In d Ls \/ In d L).
Proof.
  intros Ls L a t' Hl. inversion Hl; subst.
  - exfalso. eapply gsum_no_out; eassumption.
  - exfalso. eapply gsum_no_out; eassumption.
  - destruct (sinks_lts_in_inv Ls _ _ H3) as (d & v & Ha & Hin).
    exists d, v. split; [ exact Ha | left; exact Hin ].
  - destruct (probes_lts_in_inv L _ _ H3) as (d & v & Ha & Hin).
    exists d, v. split; [ exact Ha | right; exact Hin ].
Qed.

Lemma probe_test_no_tau : forall kk Ls L,
  (forall a, In a kk -> ~ In (fst a) Ls) ->
  (forall a, In a kk -> ~ In (fst a) L) ->
  forall z, ~ lts (probe_test kk Ls L) τ z.
Proof.
  intros kk Ls L H1 H2 z Hz. unfold probe_test in Hz. inversion Hz; subst.
  - destruct (msgs_lts_inv kk _ _ H3) as (c0 & v0 & l' & Emu & Hperm & _).
    injection Emu as E1 E2. subst c0 v0.
    destruct (sinks_probes_in_inv Ls L _ _ H4) as (d & w & Ha & Hin).
    injection Ha as Ha. subst d w.
    assert (Hk : In (c,v) kk)
      by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
    destruct Hin as [Hin|Hin].
    + eapply (H1 (c,v) Hk). exact Hin.
    + eapply (H2 (c,v) Hk). exact Hin.
  - exfalso. eapply msgs_no_input. eassumption.
  - eapply msgs_no_tau. eassumption.
  - eapply sinks_probes_no_tau. eassumption.
Qed.


(** ** The right half at the composed test

    [probe_test_lts_inv] characterises the test's visible moves
    completely — an **input** on [Ls ∪ L], or an **output** of the bag
    [kk], and nothing else.  With it the right half is again a single
    inversion: a state that is stable, emits on none of the test's
    listening channels, and refuses the test's messages has **no step at
    all** in the pair, so [must]'s [ex] field cannot be satisfied.

    Read against the intended instance ([kk] carrying [K]'s messages,
    [Ls]/[L] outside [chans K]): a right-hand side settling within
    [chans K] and refusing inputs there fails the test, which is exactly
    the second half of the separation. *)

Lemma probe_test_lts_inv : forall kk Ls L a t',
  lts (probe_test kk Ls L) (ActExt a) t' ->
  (exists d v, a = ActIn (d,v) /\ (In d Ls \/ In d L))
  \/ (exists c v, a = ActOut (c,v) /\ In (c,v) kk).
Proof.
  intros kk Ls L a t' Hl. unfold probe_test in Hl. inversion Hl; subst.
  - right. destruct (msgs_lts_inv kk _ _ H3) as (c & v & l' & Emu & Hperm & _).
    exists c, v. split; [ exact Emu | ].
    apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity.
  - left. destruct (sinks_probes_in_inv Ls L _ _ H3) as (d & v & Ha & Hin).
    injection Ha as Ha. subst a. exists d, v. split; [ reflexivity | exact Hin ].
Qed.

Lemma settled_fails_test : forall (y : proc * MO (ExtAct TypeOfActions)) kk Ls L,
  y ↛ ->
  (forall a, In a kk -> ~ In (fst a) Ls) ->
  (forall a, In a kk -> ~ In (fst a) L) ->
  (forall d, (In d Ls \/ In d L) -> forall w r, ~ (y ⟶[ActOut (d,w)] r)) ->
  (forall a, In a kk -> forall r, ~ (y ⟶[ActIn a] r)) ->
  ~ (y must_pass (probe_test kk Ls L)).
Proof.
  intros y kk Ls L Hst Hd1 Hd2 Hout Hin Hm.
  destruct Hm as [Hg | Hnh Hex Hpt Het Hcom ].
  - eapply probe_test_not_good. exact Hg.
  - destruct Hex as (z & Hz). inversion Hz; subst.
    + eapply no_step_of_stable; [ exact Hst | eassumption ].
    + eapply probe_test_no_tau; [ exact Hd1 | exact Hd2 | eassumption ].
    + destruct (probe_test_lts_inv kk Ls L _ _ l2)
        as [ (d & v & Ha & Hmem) | (c & v & Ha & Hmem) ]; subst.
      * destruct μ1 as [a|a]; simpl in eq; [ inversion eq | ].
        inversion eq; subst. eapply Hout; [ exact Hmem | exact l1 ].
      * destruct μ1 as [a|a]; simpl in eq; [ | inversion eq ].
        inversion eq; subst. eapply Hin; [ exact Hmem | exact l1 ].
Qed.


(** ** [ax_glb_tau] at a CONFIGURATION

    The rule's two output premises are read through [msgs_lts_inv]: an
    emission of [msgs l ‖ g N] always comes from the **bag** — never from
    [N], which is a guarded sum ([gsum_no_out]) — so it is a message of
    [l] leaving, and the residue is [msgs l0 ‖ g N] for a permutation
    [l ≡ₚ (c,v) :: l0].  The left, carrying the *same* bag, has the
    matching emission ([cfg_out_of_perm]), and the two residues sit at
    permutation-equal bags, so the recursive premise at [l0] covers them
    up to [ax_cgr].

    Hence: a right-hand **configuration** with a deliverable message is
    taken apart by the rule, and the recursion decreases in two
    independent ways — on the reducts (the τ premise) and on the bag (the
    output premise).  Only the input premise leaves the configuration
    shape, and there in the asynchronous form the recursion is expecting
    ([must_i_feed_below]). *)

Lemma cfg_out_inv : forall (l : list TypeOfActions) (N : gproc) c v q'',
  lts (msgs l ‖ g N) (ActExt (ActOut (c,v))) q'' ->
  exists l0, Permutation l ((c,v) :: l0) /\ q'' ≡* (msgs l0 ‖ g N).
Proof.
  intros l N c v q'' Hl. inversion Hl; subst.
  - destruct (msgs_lts_inv l _ _ H3) as (c0 & v0 & l0 & Emu & Hperm & Hcgr).
    injection Emu as E1 E2. subst c0 v0.
    exists l0. split; [ exact Hperm | ].
    apply cgr_fullpar; [ exact Hcgr | apply cgr_refl ].
  - exfalso. eapply gsum_no_out. eassumption.
Qed.

Lemma cfg_out_of_perm : forall (l l0 : list TypeOfActions) c v (P : proc),
  Permutation l ((c,v) :: l0) ->
  exists r, lts (msgs l ‖ P) (ActExt (ActOut (c,v))) r /\ r ≡* (msgs l0 ‖ P).
Proof.
  intros l l0 c v P Hperm.
  assert (Hc : msgs l ‖ P ≡* (msgs ((c,v) :: l0)) ‖ P)
    by (apply cgr_fullpar; [ apply msgs_perm; exact Hperm | apply cgr_refl ]).
  assert (Hstep : lts ((msgs ((c,v) :: l0)) ‖ P) (ActExt (ActOut (c,v)))
                      ((g 𝟘 ‖ msgs l0) ‖ P)).
  { simpl. apply lts_parL. apply lts_parL. apply lts_output. }
  destruct (Congruence_Respects_Transition (msgs l ‖ P) ((g 𝟘 ‖ msgs l0) ‖ P)
              (ActExt (ActOut (c,v))) (ex_intro _ _ (conj Hc Hstep))) as (r & Hr & Hcr).
  exists r. split; [ exact Hr | ].
  eapply cgr_trans; [ exact Hcr | ].
  apply cgr_fullpar; [ | apply cgr_refl ].
  etransitivity; [ apply cgr_par_com | apply cgr_par_nil ].
Qed.

Theorem ax_below_cfg_glb : forall (l : list TypeOfActions) (M N : gproc),
  (exists q0, lts (msgs l ‖ g N) τ q0) ->
  (forall q', lts (msgs l ‖ g N) τ q' -> ax_pre (msgs l ‖ g M) q') ->
  (forall c v q'', lts (msgs l ‖ g N) (ActExt (ActIn (c,v))) q'' ->
     ax_pre ((c ! v • 𝟘) ‖ (msgs l ‖ g M)) q'') ->
  (forall c v l0, Permutation l ((c,v) :: l0) ->
     ax_pre (msgs l0 ‖ g M) (msgs l0 ‖ g N)) ->
  ax_pre (msgs l ‖ g M) (msgs l ‖ g N).
Proof.
  intros l M N Hex Htau Hin Hrec.
  apply ax_glb_tau; [ exact Hex | exact Htau | exact Hin | | ].
  - intros c v q'' Hq''.
    destruct (cfg_out_inv l N c v q'' Hq'') as (l0 & Hperm & _).
    destruct (cfg_out_of_perm l l0 c v (g M) Hperm) as (r & Hr & _).
    exists r. exact Hr.
  - intros c v p'' q'' Hp'' Hq''.
    destruct (cfg_out_inv l M c v p'' Hp'') as (l1 & Hp1 & Hcp).
    destruct (cfg_out_inv l N c v q'' Hq'') as (l0 & Hp0 & Hcq).
    assert (Hpp : Permutation l1 l0).
    { apply (Permutation_cons_inv (a := (c,v))).
      etransitivity; [ symmetry; exact Hp1 | exact Hp0 ]. }
    eapply ax_trans; [ apply ax_cgr; exact Hcp | ].
    eapply ax_trans; [ apply (Hrec c v l1 Hp1) | ].
    apply ax_cgr_sym.
    eapply cgr_trans; [ exact Hcq | ].
    apply cgr_fullpar; [ apply msgs_perm; symmetry; exact Hpp | apply cgr_refl ].
Qed.


(** ** THE RESIDUE, NAMED — everything rests on one [Settles] statement

    [CertAll] is the certificate of [ax_phaseA_direct], quantified over
    the data the matching actually supplies: two [gStatic] sums, a
    stable right, the configuration hypothesis, and any [OutOnly] buffer
    at which the mirror is stable.

    [phaseA_config_of_cert] then reduces [PhaseA_config] — and with it
    the whole stable-leaf step ([ax_below_stable_NF_cfg]) — to it.  So
    the development's single open point is now a **statement about
    settling**, with no derivation, no mirror and no test in it:

      the left process, handed any buffer the right refuses, settles
      without emitting outside that buffer.

    What is proved about it: it holds at the bag and above
    ([certificate_at_bag], [certificate_above_bag], and at the set level
    with no side condition at all, [cfg_certificate_drain]); it holds
    when the left configuration is stable
    ([phaseA_config_of_stable]) and when the left never regenerates a
    message it has emitted ([phaseA_config_no_regeneration]).  What is
    open is the buffers *below* the bag for a regenerating left — and
    the notes at [ax_phaseA_direct] and [probe_test] record why each
    route to them fails. *)

Definition CertAll : Prop :=
  forall (M N : gproc) (l : list TypeOfActions),
    gStatic M -> gStatic N -> (forall z, ~ lts (g N) τ z) ->
    ((msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ g N)) ->
    forall K, OutOnly K -> ((g (mirrorN (g M) N)) ▷ K) ↛ ->
      Settles (chans K) ((g M) ▷ K).

Theorem phaseA_config_of_cert : CertAll -> PhaseA_config.
Proof.
  intros Hcert M N l HM HN Hnt Hsem.
  apply ax_phaseA_direct; [ apply static_g; exact HM | exact HN | exact Hnt | ].
  intros K HK Hst. eapply Hcert; eassumption.
Qed.


(** ** The descent step, at a configuration

    The other half of the dichotomy for an unstable left (see the note at
    [ax_phaseA_direct] and [VACCS_DropProbes]): when a guard of [M]
    consumes a message of the bag, the configuration may simply be
    *descended*, since a server τ is already a [⊑ₘᵤₛₜᵢ]-step
    ([ax_tau_step]).

    Two things make this usable where the general "choose a successor"
    move is not.  On a **canonical** sum the delivery is deterministic —
    one guard per channel — so there is no choice to make
    ([VACCS_DropProbes.canonical_delivery_is_deterministic_and_works]).
    And at **equal bags** the successor is below the target exactly when
    the continuation gives the message back: otherwise it has lost a
    message the right still holds, and messages are rigid
    ([VACCS_DropProbes.nil_not_below_msg]).  That is the complement of
    [phaseA_config_no_regeneration]'s hypothesis, which is why the two
    together look like a dichotomy. *)

Lemma cfg_deliver_step : forall (l l0 : list TypeOfActions) c v (M : gproc) (Mc : proc),
  Permutation l ((c,v) :: l0) ->
  lts (g M) (ActExt (ActIn (c,v))) Mc ->
  exists r, lts (msgs l ‖ g M) τ r /\ r ≡* (msgs l0 ‖ Mc).
Proof.
  intros l l0 c v M Mc Hperm Hin.
  assert (Hc : msgs l ‖ g M ≡* (msgs ((c,v) :: l0)) ‖ g M)
    by (apply cgr_fullpar; [ apply msgs_perm; exact Hperm | apply cgr_refl ]).
  assert (Hstep : lts ((msgs ((c,v) :: l0)) ‖ g M) τ (((g 𝟘) ‖ msgs l0) ‖ Mc)).
  { simpl. eapply lts_comL; [ apply lts_parL; apply lts_output | exact Hin ]. }
  destruct (Congruence_Respects_Transition (msgs l ‖ g M) (((g 𝟘) ‖ msgs l0) ‖ Mc) τ
              (ex_intro _ _ (conj Hc Hstep))) as (r & Hr & Hcr).
  exists r. split; [ exact Hr | ].
  eapply cgr_trans; [ exact Hcr | ].
  apply cgr_fullpar; [ | apply cgr_refl ].
  etransitivity; [ apply cgr_par_com | apply cgr_par_nil ].
Qed.

(** ** The descent disjunct, reduced to a LOCAL condition

    [CfgDisjunction]'s second disjunct asks for *some* [τ]-successor of
    the configuration to be below the target — a statement about the whole
    configuration.  It follows from a condition on **one continuation**,
    strictly smaller than the configuration:

      the guard's continuation, after receiving, is below *the message it
      just consumed, put back beside the target*.

    That is what the copycat, the responder and the swallower have in
    common on the four instances recorded in `VACCS_DropProbes.v`, and it
    is what distinguishes them from the guards that make the descent fail
    there: those do something observable beyond returning the message.

    The proof is three moves — [cfg_deliver_step] for the [τ], then
    [must_i_par_compat_r] under the remaining bag, then [msgs_perm] to put
    the consumed message back where it came from. *)

Theorem descent_of_cont_below :
  forall (l l0 : list TypeOfActions) (c : ChannelData) (v : ValueData)
         (M N : gproc) (Mc : proc),
  Permutation l ((c,v) :: l0) ->
  lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc ->
  Mc ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (((c ! v • 𝟘) : proc) ‖ ((g N) : proc)) ->
  exists p', lts ((msgs l ‖ (g M)) : proc) τ p'
          /\ p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((msgs l ‖ (g N)) : proc).
Proof.
  intros l l0 c v M N Mc Hperm Hin Hbelow.
  destruct (cfg_deliver_step l l0 c v M Mc Hperm Hin) as (r & Hr & Hcr).
  exists r. split; [ exact Hr | ].
  intros t Hm.
  assert (H1 : (msgs l0 ‖ Mc) must_pass t)
    by (exact (proj2 (must_i_cgr _ _ Hcr) t Hm)).
  assert (H2 : (msgs l0 ‖ (((c ! v • 𝟘) : proc) ‖ ((g N) : proc))) must_pass t)
    by (exact (must_i_par_compat_r (msgs l0) _ _ Hbelow t H1)).
  assert (Hc2 : (msgs l0 ‖ (((c ! v • 𝟘) : proc) ‖ ((g N) : proc)))
                ≡* (msgs l ‖ ((g N) : proc))).
  { eapply cgr_trans;
      [ | apply cgr_fullpar; [ apply msgs_perm; apply Permutation_sym; exact Hperm
                             | apply cgr_refl ] ].
    simpl. eapply cgr_trans; [ apply cgr_par_assoc_rev | ].
    apply cgr_fullpar; [ apply cgr_par_com | apply cgr_refl ]. }
  exact (proj2 (must_i_cgr _ _ Hc2) t H2).
Qed.

(** The copycat / responder shape, where the continuation literally
    returns the message beside a residue.  Both [VACCS_DropProbes]'s
    [MCert] (residue [𝟘], target [𝟘]) and the [rb]-guard of its
    regenerating probe are this instance.

    The **swallower** shape ([Mc = 𝟘]) is *not* covered, and the reason
    is sharper than it looks: it would need [𝟘 ⊑ₘᵤₛₜᵢ ((c!v•𝟘) ‖ g N)],
    and already at [N := 𝟘] that is [𝟘 ⊑ₘᵤₛₜᵢ (c!v•𝟘)], which
    [VACCS_Bad.nil_not_below_msg_gen] **refutes at every channel** — the probe
    [𝛕•① + c?𝟘] is passed by [𝟘] (its own [𝛕] reaches [①]) and failed by
    the message, whose [com] at [c] leaves [𝟘] against [𝟘].  Restricting
    to [Static] does not help: the counterexample is [Static].

    So a swallowing guard does *not* license the descent by this route,
    and the informal reading "the continuation merely absorbs the
    message, so nothing is lost" is wrong — absorbing a message **is**
    observable ([msg_not_below_nil] / [nil_not_below_msg] are the two
    halves of that). *)

Corollary descent_of_copycat_cont :
  forall (l l0 : list TypeOfActions) (c : ChannelData) (v : ValueData)
         (M N : gproc) (Mc K : proc),
  Permutation l ((c,v) :: l0) ->
  lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc ->
  Mc ≡* (((c ! v • 𝟘) : proc) ‖ K) ->
  K ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc) ->
  exists p', lts ((msgs l ‖ (g M)) : proc) τ p'
          /\ p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((msgs l ‖ (g N)) : proc).
Proof.
  intros l l0 c v M N Mc K Hperm Hin Hcgr HK.
  eapply descent_of_cont_below; [ exact Hperm | exact Hin | ].
  intros t Hm.
  apply (must_i_par_compat_r ((c ! v • 𝟘) : proc) K ((g N) : proc) HK t).
  exact (proj2 (must_i_cgr _ _ Hcgr) t Hm).
Qed.


Theorem ax_below_cfg_descend : forall (l l0 : list TypeOfActions) c v
    (M : gproc) (Mc q : proc),
  Permutation l ((c,v) :: l0) ->
  lts (g M) (ActExt (ActIn (c,v))) Mc ->
  ax_pre (msgs l0 ‖ Mc) q ->
  ax_pre (msgs l ‖ g M) q.
Proof.
  intros l l0 c v M Mc q Hperm Hin Hax.
  destruct (cfg_deliver_step l l0 c v M Mc Hperm Hin) as (r & Hr & Hcr).
  eapply ax_trans; [ apply ax_tau_step; exact Hr | ].
  eapply ax_trans; [ apply ax_cgr; exact Hcr | exact Hax ].
Qed.

(** ** La délivrance est réversible — le cas garde unique

    Le dernier énoncé ouvert de la complétude est la branche
    *régénérante* de la dichotomie : lorsque la garde qui consomme le
    message le rend, le successeur de délivrance est-il encore sous la
    cible ?  Deux tentatives de contre-exemple ont échoué pour la même
    raison — [p] passe tout ce que le successeur passe — d'où la
    formulation ci-dessous, qui est plus forte et ne mentionne plus la
    cible du tout :

        successeur ⊑ₘᵤₛₜᵢ p

    Avec [must_i_tau_below] (qui donne l'autre sens gratuitement) cela
    fait de la délivrance une **équivalence**, et la branche régénérante
    tombe par simple transitivité.

    Deux conditions latérales, et ce sont exactement les deux champs
    [com] :

    - [Hrendu] : une fois le message rendu, le résidu est sous la garde
      d'origine.  Pour le copycat pur c'est [ax_ccat_r].
    - [Hsym] : « [P^v'] tenant [v] vaut [P^v] tenant [v'] » — la
      symétrie en la valeur en attente, obtenue en poussant le message
      du serveur vers le client par [must_msg_swap] des deux côtés.
      Pour le copycat les deux membres deviennent le même énoncé.

    La régénération **seule** ne suffit donc pas : ces deux conditions
    disent ensemble que la garde se comporte en copycat.  Mais elles
    sont locales et vérifiables, là où l'énoncé de départ quantifiait
    sur tous les clients.

    Le champ [pt] n'est réglé que parce que le sac n'a qu'un message et
    la somme qu'une garde — sur une somme **canonique**
    ([VACCS_Canonical.canonicalize]) la seconde condition est acquise.
    À plusieurs messages délivrables la branche « délivrer un *autre*
    message » n'a aucun rapport avec le successeur, et c'est le point
    laissé de côté par la dichotomie. *)

Lemma must_i_delivery_reversible :
  forall (c : ChannelData) (v : ValueData) (P : proc),
    (exists P', lts (P ^ v) ((c ▷ v) !) P') ->
    (forall (P' t' : proc),
        lts (P ^ v) ((c ▷ v) !) P' -> P' must_pass t' ->
        ((c ? P) : proc) must_pass t') ->
    (forall (v' : ValueData) (t' : proc),
        (P ^ v) must_pass ((c ! v' • 𝟘) ‖ t') ->
        (P ^ v') must_pass ((c ! v • 𝟘) ‖ t')) ->
    (P ^ v) ⊑ₘᵤₛₜᵢ ((c ! v • 𝟘) ‖ ((c ? P) : proc)).
Proof.
  intros c v P Hreg Hrendu Hsym t Hm.
  remember (P ^ v) as p0 eqn:Heq. revert Heq.
  induction Hm as [p0 t Hgood | p0 t nh ex pt IHpt et IHet com IHcom]; intros Heq.
  - apply m_now. exact Hgood.
  - assert (Hm0 : p0 must_pass t) by (apply m_step; assumption).
    subst p0.
    apply m_step.
    + exact nh.
    + exists ((𝟘 : proc) ‖ (P ^ v), t). apply ParLeft.
      eapply lts_comL; [ apply lts_output | apply lts_input ].
    + intros p' Hstep. inversion Hstep; subst.
      * inversion H1; subst. inversion H2; subst.
        exact (proj2 (must_i_cgr _ _ (ax_nil_par (P ^ v0))) t Hm0).
      * inversion H1.
      * inversion H3.
      * inversion H3.
    + intros t' Hstep. exact (IHet t' Hstep Hreg Hrendu Hsym eq_refl).
    + intros p' t' mu1 mu2 Hdual Hp Ht. inversion Hp; subst.
      * inversion H3; subst.
        destruct Hreg as [Pr HPr].
        assert (HPt : Pr must_pass t') by (eapply com; [ exact Hdual | exact HPr | exact Ht ]).
        assert (HG : ((c ? P) : proc) must_pass t') by (eapply Hrendu; [ exact HPr | exact HPt ]).
        exact (proj2 (must_i_cgr _ _ (ax_nil_par ((c ? P) : proc))) t' HG).
      * inversion H3; subst.
        destruct mu2 as [a2|a2]; simpl in Hdual; try contradiction. subst a2.
        assert (Hc : t ≡* ((c ! v0 • 𝟘) ‖ t'))
          by (eapply TransitionShapeForOutputSimplified; exact Ht).
        assert (Ha : (P ^ v) must_pass ((c ! v0 • 𝟘) ‖ t'))
          by (eapply must_eq_client; [ exact Hc | exact Hm0 ]).
        assert (Hb : (P ^ v0) must_pass ((c ! v • 𝟘) ‖ t')) by (apply Hsym; exact Ha).
        assert (Hd : ((P ^ v0) ‖ (c ! v • 𝟘)) must_pass t')
          by (apply (proj2 (must_msg_swap _ _ _ _)); exact Hb).
        assert (Hcom2 : ((c ! v • 𝟘) ‖ (P ^ v0)) ≡* ((P ^ v0) ‖ (c ! v • 𝟘)))
          by (apply cgr_par_com).
        exact (proj1 (must_i_cgr _ _ Hcom2) t' Hd).
Qed.

(** La délivrance est alors une **équivalence** : l'autre sens est
    [must_i_tau_below] sur le τ de délivrance, composé avec
    [ax_nil_par]. *)
Lemma must_i_delivery_equiv :
  forall (c : ChannelData) (v : ValueData) (P : proc),
    (exists P', lts (P ^ v) ((c ▷ v) !) P') ->
    (forall (P' t' : proc),
        lts (P ^ v) ((c ▷ v) !) P' -> P' must_pass t' ->
        ((c ? P) : proc) must_pass t') ->
    (forall (v' : ValueData) (t' : proc),
        (P ^ v) must_pass ((c ! v' • 𝟘) ‖ t') ->
        (P ^ v') must_pass ((c ! v • 𝟘) ‖ t')) ->
    ((c ! v • 𝟘) ‖ ((c ? P) : proc)) ≂ₘᵤₛₜᵢ (P ^ v).
Proof.
  intros c v P Hreg Hrendu Hsym. split.
  - exact (must_i_delivery_reversible c v P Hreg Hrendu Hsym).
  - intros t Hm.
    assert (Hstep : lts ((c ! v • 𝟘) ‖ ((c ? P) : proc)) τ ((𝟘 : proc) ‖ (P ^ v)))
      by (eapply lts_comL; [ apply lts_output | apply lts_input ]).
    assert (Hnil : (P ^ v) ≡* ((𝟘 : proc) ‖ (P ^ v))) by (apply ax_nil_par).
    exact (proj1 (must_i_cgr _ _ Hnil) t (must_i_tau_below _ _ Hstep t Hm)).
Qed.

(** Et la branche régénérante de la dichotomie tombe par transitivité,
    **sans jamais parler de la cible** [q] — c'est tout l'intérêt de
    l'avoir reformulée en [successeur ⊑ p]. *)
Corollary must_i_delivery_below_target :
  forall (c : ChannelData) (v : ValueData) (P q : proc),
    (exists P', lts (P ^ v) ((c ▷ v) !) P') ->
    (forall (P' t' : proc),
        lts (P ^ v) ((c ▷ v) !) P' -> P' must_pass t' ->
        ((c ? P) : proc) must_pass t') ->
    (forall (v' : ValueData) (t' : proc),
        (P ^ v) must_pass ((c ! v' • 𝟘) ‖ t') ->
        (P ^ v') must_pass ((c ! v • 𝟘) ‖ t')) ->
    ((c ! v • 𝟘) ‖ ((c ? P) : proc)) ⊑ₘᵤₛₜᵢ q ->
    (P ^ v) ⊑ₘᵤₛₜᵢ q.
Proof.
  intros c v P q Hreg Hrendu Hsym Hpq t Hm.
  apply Hpq. exact (must_i_delivery_reversible c v P Hreg Hrendu Hsym t Hm).
Qed.

(** *** Les hypothèses sont satisfaisables — le copycat les vérifie

    Une loi dont les prémisses ne sont jamais remplies ne vaut rien ;
    voici donc l'instance qui les remplit, et c'est celle qui a motivé
    tout l'énoncé.  Pour [ccat c = c ? (c ! x • 𝟘)] :

    - **RENDU** est littéralement [must_i_ccat_r] ([𝟘 ⊑ₘᵤₛₜᵢ ccat c]),
      puisque le résidu après ré-émission est [𝟘] ;
    - **SYMÉTRIE** devient une identité une fois les deux messages
      poussés du côté client par [must_msg_swap] : les deux membres ne
      diffèrent que par la commutativité de [‖].

    Le résultat est par ailleurs vrai indépendamment ([ccat c ≂ₘᵤₛₜᵢ 𝟘],
    donc [msg ‖ ccat c ≂ₘᵤₛₜᵢ msg]), ce qui en fait un contrôle et non
    seulement une instanciation. *)

Lemma ccat_delivery_equiv :
  forall (c : ChannelData) (v : ValueData),
    ((c ! v • 𝟘) ‖ ccat c) ≂ₘᵤₛₜᵢ (c ! v • 𝟘).
Proof.
  intros c v. unfold ccat.
  apply (must_i_delivery_equiv c v (c ! 0 • 𝟘)).
  - exists 𝟘. simpl. apply lts_output.
  - intros P' t' H Hm. simpl in H. inversion H; subst.
    exact (must_i_ccat_r c t' Hm).
  - intros v' t' H.
    assert (H1 : ((c ! v • 𝟘) ‖ (c ! v' • 𝟘)) must_pass t')
      by (apply (proj2 (must_msg_swap _ _ _ _)); exact H).
    assert (Hc : ((c ! v' • 𝟘) ‖ (c ! v • 𝟘)) ≡* ((c ! v • 𝟘) ‖ (c ! v' • 𝟘)))
      by (apply cgr_par_com).
    apply (proj1 (must_msg_swap _ _ _ _)).
    exact (proj1 (must_i_cgr _ _ Hc) t' H1).
Qed.

(** *** À sac quelconque : pour un copycat, la délivrance reste réversible

    [must_i_delivery_reversible] est limitée à un sac d'un seul message,
    parce que son champ [pt] doit couvrir *tous* les τ de [p] et qu'un
    second message délivrable en produit un autre, sans rapport avec le
    successeur choisi.  Il vaut la peine de délimiter cet obstacle : il
    n'est **pas** dû au sac.

    Pour une garde copycat, la délivrance est réversible à **n'importe
    quel** sac, et pour une raison qui court-circuite entièrement le
    champ [pt] : le copycat est invisible ([must_i_ccat_l]/[_r]), donc
    [must_i_par_compat_r] transporte l'équivalence sous le sac tel quel,
    et le successeur n'est que le sac remis en ordre.

    Ce qui reste réellement ouvert est donc la conjonction « plusieurs
    messages délivrables **et** une somme à plusieurs gardes » — là le
    choix gardé *commet*, les deux délivrances sont incompatibles
    (chacune jette la garde de l'autre), et les successeurs ne sont pas
    confluents.  C'est le mécanisme déjà isolé par
    [VACCS_ChoiceProbes.v], une couche plus bas. *)

Lemma msgs_ccat_equiv :
  forall (l : list TypeOfActions) (c : ChannelData),
    ((msgs l) ‖ ccat c) ≂ₘᵤₛₜᵢ (msgs l).
Proof.
  intros l c.
  assert (Hnil : ((msgs l) ‖ (𝟘 : proc)) ≡* (msgs l)) by (apply cgr_par_nil).
  split.
  - intros t Hm.
    apply (must_i_par_compat_r (msgs l) (𝟘 : proc) (ccat c) (must_i_ccat_r c) t).
    exact (proj1 (must_i_cgr _ _ Hnil) t Hm).
  - intros t Hm.
    apply (proj2 (must_i_cgr _ _ Hnil) t).
    exact (must_i_par_compat_r (msgs l) (ccat c) (𝟘 : proc) (must_i_ccat_l c) t Hm).
Qed.

Lemma msgs_ccat_delivery :
  forall (l l0 : list TypeOfActions) (c : ChannelData) (v : ValueData),
    Permutation l ((c,v) :: l0) ->
    ((msgs l0) ‖ (c ! v • 𝟘)) ≂ₘᵤₛₜᵢ ((msgs l) ‖ ccat c).
Proof.
  intros l l0 c v Hp.
  assert (H1 : msgs l ≡* msgs ((c,v) :: l0)) by (apply msgs_perm; exact Hp).
  simpl in H1.
  assert (Hc : ((msgs l0) ‖ (c ! v • 𝟘)) ≡* (msgs l)).
  { eapply cgr_trans; [ apply cgr_par_com | apply cgr_symm; exact H1 ]. }
  destruct (must_i_cgr _ _ Hc) as [Hcgr1 Hcgr2].
  destruct (msgs_ccat_equiv l c) as [Hm1 Hm2].
  split.
  - intros t H. exact (Hcgr1 t (Hm2 t H)).
  - intros t H. exact (Hm1 t (Hcgr2 t H)).
Qed.

(** *** …et à somme quelconque : le cas copycat est clos en toute généralité

    [msgs_ccat_delivery] ci-dessus lève l'hypothèse « un seul message » ;
    il reste celle d'« une seule garde ».  Elle tombe de la même façon,
    et c'est le point : une **somme** de copycats est elle aussi
    invisible ([VACCS_Copycat.must_i_copycats_below_nil] et
    [must_i_nil_below_copycats]), bien que le choix gardé *commette* —
    quelle que soit la branche prise, le message revient.

    Donc pour un [M] copycat, la délivrance est réversible à sac
    quelconque **et** à somme quelconque, et la branche régénérante de la
    dichotomie est close sur toute cette classe
    ([copycat_delivery_below_target]).  Les deux lemmes [msgs_ccat_*]
    n'en sont que l'instance à une garde.

    Reste, et c'est désormais tout ce qui reste : un [M] régénérant qui
    n'est **pas** un copycat — une garde qui rend le message mais fait
    aussi autre chose — avec plusieurs messages délivrables.  Là les
    successeurs ne sont pas confluents (le choix commet) et rien ne les
    relie ; c'est le mécanisme de [VACCS_ChoiceProbes.v] et de
    [delivery_successor_cannot_be_chosen]. *)

Lemma msgs_copycats_equiv :
  forall (l : list TypeOfActions) (M : gproc),
    gCopycats M -> ((msgs l) ‖ ((g M) : proc)) ≂ₘᵤₛₜᵢ (msgs l).
Proof.
  intros l M HM.
  assert (Hnil : ((msgs l) ‖ (𝟘 : proc)) ≡* (msgs l)) by (apply cgr_par_nil).
  split.
  - intros t Hm.
    apply (must_i_par_compat_r (msgs l) (𝟘 : proc) ((g M) : proc)
             (must_i_nil_below_copycats M HM) t).
    exact (proj1 (must_i_cgr _ _ Hnil) t Hm).
  - intros t Hm.
    apply (proj2 (must_i_cgr _ _ Hnil) t).
    exact (must_i_par_compat_r (msgs l) ((g M) : proc) (𝟘 : proc)
             (must_i_copycats_below_nil M HM) t Hm).
Qed.

Lemma msgs_copycats_delivery :
  forall (l l0 : list TypeOfActions) (M : gproc)
         (c : ChannelData) (v : ValueData) (Mc : proc),
    gCopycats M -> Permutation l ((c,v) :: l0) ->
    lts ((g M) : proc) ((c ▷ v) ?) Mc ->
    ((msgs l0) ‖ Mc) ≂ₘᵤₛₜᵢ ((msgs l) ‖ ((g M) : proc)).
Proof.
  intros l l0 M c v Mc HM Hp Hlts.
  destruct (gCopycats_lts M HM _ _ Hlts) as (c0 & v0 & Hmu & HMc).
  inversion Hmu; subst.
  assert (H1 : msgs l ≡* msgs ((c0,v0) :: l0)) by (apply msgs_perm; exact Hp).
  simpl in H1.
  assert (Hc : ((msgs l0) ‖ (c0 ! v0 • 𝟘)) ≡* (msgs l)).
  { eapply cgr_trans; [ apply cgr_par_com | apply cgr_symm; exact H1 ]. }
  destruct (must_i_cgr _ _ Hc) as [Hcgr1 Hcgr2].
  destruct (msgs_copycats_equiv l M HM) as [Hm1 Hm2].
  split.
  - intros t H. exact (Hcgr1 t (Hm2 t H)).
  - intros t H. exact (Hm1 t (Hcgr2 t H)).
Qed.

(** La branche régénérante de la dichotomie, close pour toute la classe
    copycat : sac quelconque, somme quelconque, et **sans rien supposer
    de la cible**. *)
Corollary copycat_delivery_below_target :
  forall (l l0 : list TypeOfActions) (M : gproc)
         (c : ChannelData) (v : ValueData) (Mc q : proc),
    gCopycats M -> Permutation l ((c,v) :: l0) ->
    lts ((g M) : proc) ((c ▷ v) ?) Mc ->
    ((msgs l) ‖ ((g M) : proc)) ⊑ₘᵤₛₜᵢ q ->
    ((msgs l0) ‖ Mc) ⊑ₘᵤₛₜᵢ q.
Proof.
  intros l l0 M c v Mc q HM Hp Hlts Hpq t Hm.
  apply Hpq.
  exact (proj2 (msgs_copycats_delivery l l0 M c v Mc HM Hp Hlts) t Hm).
Qed.

(** ** LA CIBLE INSTABLE EST GRATUITE — Phase A se réduit aux cibles stables

    Les gardes du miroir sont [fwdg c P = c ? ((NewVar 0 P) ‖ (c ! bvar₀ • 𝟘))] :
    **le miroir rend le message qu'il consomme**.  Sa délivrance
    reconstitue donc exactement la configuration de départ, ce qui rend
    les prémisses de [ax_below_cfg_glb] libres :

    | transition de la cible | état atteint | prémisse |
    |---|---|---|
    | τ (délivrance d'un message du sac) | ≂ [msgs l ‖ g M] | réflexivité (via [ax_cgr]) |
    | entrée sur [c] | ≂ [(c!v•𝟘) ‖ (msgs l ‖ g M)] | réflexivité |
    | sortie d'un message du sac | la cible au sac plus petit | récurrence |

    D'où : **tant que la cible a un τ, Phase A ne coûte rien**, et la
    récurrence sur la taille du sac ramène tout au cas où la cible est
    τ-stable.  Aucune hypothèse sémantique n'intervient dans cette
    réduction — c'est [ax_glb_tau] qui fait tout le travail, en faisant
    descendre la **droite** pendant que la gauche reste en place.

    C'est le premier progrès sur ce trou obtenu par une **règle** et non
    par un certificat de pose.  Il retire du problème le cas « le sac
    porte un message sur un canal que [N] offre », qui passait jusqu'ici
    par [ax_phaseA_settle].

    **Caveat, à ne pas gommer** : l'hypothèse est demandée à *tous* les
    sous-sacs, parce que la prémisse de sortie descend le long du sac.
    Si le consommateur a besoin d'un fait sémantique
    ([msgs l ‖ g M ⊑ₘᵤₛₜᵢ msgs l ‖ g N]), il lui faudra à chaque
    sous-sac — et ce fait ne se transporte pas d'un sac à un sous-sac
    (pas d'annulation en général : [VACCS_DropProbes.nil_not_below_msg]).
    Ce que la réduction élimine est donc le cas *instable* de la cible,
    pas la dépendance sémantique du cas stable. *)

Lemma mir_tau_inv : forall (M N : gproc) (l : list TypeOfActions) q',
  (forall z, ~ lts ((g N) : proc) τ z) ->
  lts (msgs l ‖ ((g (mirrorN ((g M) : proc) N)) : proc)) τ q' ->
  exists c v l0, Permutation l ((c,v) :: l0) /\
     q' ≡* (msgs l0 ‖ (((g M) : proc) ‖ ((c ! v • 𝟘) : proc))).
Proof.
  intros M N l q' HstN Hl. inversion Hl; subst.
  - destruct (msgs_lts_inv l _ _ H1) as (c0 & v0 & l0 & Emu & Hperm & Hcgr).
    injection Emu as E1 E2. subst c0 v0.
    pose proof (mirrorN_lts_in_shape ((g M) : proc) N c v q2 H2) as Es. subst q2.
    exists c, v, l0. split; [ exact Hperm | ].
    apply cgr_fullpar; [ exact Hcgr | apply cgr_refl ].
  - exfalso. eapply msgs_no_input; eassumption.
  - exfalso. eapply msgs_no_tau; eassumption.
  - exfalso. eapply (mirrorN_no_tau ((g M) : proc) N HstN); eassumption.
Qed.

Lemma mir_in_inv : forall (M N : gproc) (l : list TypeOfActions) c v q'',
  lts (msgs l ‖ ((g (mirrorN ((g M) : proc) N)) : proc)) (ActExt (ActIn (c,v))) q'' ->
  q'' = (msgs l ‖ (((g M) : proc) ‖ ((c ! v • 𝟘) : proc))).
Proof.
  intros M N l c v q'' Hl. inversion Hl; subst.
  - exfalso. eapply msgs_no_input; eassumption.
  - f_equal. eapply mirrorN_lts_in_shape. eassumption.
Qed.

Lemma cgr_par_rot : forall (X Y Z : proc), (X ‖ (Y ‖ Z)) ≡* (Z ‖ (X ‖ Y)).
Proof.
  intros X Y Z. etransitivity; [ apply cgr_par_assoc_rev | apply cgr_par_com ].
Qed.

Lemma cgr_bag_pull : forall (l l0 : list TypeOfActions) c v (P : proc),
  Permutation l ((c,v) :: l0) ->
  (msgs l ‖ P) ≡* (msgs l0 ‖ (P ‖ ((c ! v • 𝟘) : proc))).
Proof.
  intros l l0 c v P Hperm.
  etransitivity; [ apply cgr_fullpar; [ apply msgs_perm; exact Hperm | apply cgr_refl ] | ].
  simpl. etransitivity; [ apply cgr_par_assoc | ].
  apply cgr_symm. apply cgr_par_rot.
Qed.

Lemma ax_phaseA_glb_bag : forall n (M N : gproc) (l : list TypeOfActions),
  (forall z, ~ lts ((g N) : proc) τ z) ->
  length l <= n ->
  (forall l', (forall q0, ~ lts (msgs l' ‖ ((g (mirrorN ((g M) : proc) N)) : proc)) τ q0) ->
      ax_pre (msgs l' ‖ ((g M) : proc))
             (msgs l' ‖ ((g (mirrorN ((g M) : proc) N)) : proc))) ->
  ax_pre (msgs l ‖ ((g M) : proc))
         (msgs l ‖ ((g (mirrorN ((g M) : proc) N)) : proc)).
Proof.
  induction n as [|n IH]; intros M N l HstN Hlen Hstable.
  - apply Hstable. intros q0 Hq0.
    destruct (mir_tau_inv M N l q0 HstN Hq0) as (c & v & l0 & Hperm & _).
    apply Permutation_length in Hperm. simpl in Hperm. lia.
  - destruct (lts_dec (msgs l ‖ ((g (mirrorN ((g M) : proc) N)) : proc)) τ)
      as [Hno | [q0 Hq0]].
    + apply Hstable. exact Hno.
    + apply ax_below_cfg_glb.
      * exists q0. exact Hq0.
      * intros q' Hq'.
        destruct (mir_tau_inv M N l q' HstN Hq') as (c & v & l0 & Hperm & Hcgr).
        apply ax_cgr.
        etransitivity; [ apply (cgr_bag_pull l l0 c v ((g M) : proc) Hperm) | ].
        apply cgr_symm. exact Hcgr.
      * intros c v q'' Hq''.
        rewrite (mir_in_inv M N l c v q'' Hq'').
        apply ax_cgr. apply cgr_symm. apply cgr_par_rot.
      * intros c v l0 Hperm. apply IH; [ exact HstN | | exact Hstable ].
        apply Permutation_length in Hperm. simpl in Hperm. lia.
Qed.

Corollary ax_phaseA_reduce_to_stable : forall (M N : gproc),
  (forall z, ~ lts ((g N) : proc) τ z) ->
  (forall l', (forall q0, ~ lts (msgs l' ‖ ((g (mirrorN ((g M) : proc) N)) : proc)) τ q0) ->
      ax_pre (msgs l' ‖ ((g M) : proc))
             (msgs l' ‖ ((g (mirrorN ((g M) : proc) N)) : proc))) ->
  forall l, ax_pre (msgs l ‖ ((g M) : proc))
                   (msgs l ‖ ((g (mirrorN ((g M) : proc) N)) : proc)).
Proof.
  intros M N HstN Hstable l.
  eapply (ax_phaseA_glb_bag (length l)); [ exact HstN | apply Nat.le_refl | exact Hstable ].
Qed.

(** ** LE RÉSIDU, NOMMÉ : Phase A à cible STABLE

    La récurrence de [ax_phaseA_glb_bag] ne visite que des **sous-sacs**
    ([Permutation l ((c,v)::l0)], donc [subbag l0 l] par [subbag_cons]),
    et le site d'appel réel fournit précisément l'hypothèse sémantique
    sur tous les sous-sacs : c'est [BagSem], la prémisse que
    [ax_below_gsum_bag] passe à son gestionnaire de feuilles stables.
    Il n'y a donc pas de circularité, et le résidu se nomme :

    [PhaseA_stable_target] est [PhaseA_config] **plus l'hypothèse que la
    cible est τ-stable** — c'est-à-dire qu'aucun message du sac n'est sur
    un canal que [N] offre.  C'est strictement plus petit, et dans ce cas
    [msgs l ‖ g N] est stable lui aussi, de sorte que
    [VACCS_NormalForm.certificate_at_bag] donne gratuitement le
    certificat **au sac** ; les buffers en dessous du sac, eux, sont
    désormais traités par la récurrence elle-même. *)

Definition PhaseA_stable_target : Prop :=
  forall (M N : gproc) (l : list TypeOfActions),
    (forall p, ~ lts ((g N) : proc) τ p) ->
    (forall q0, ~ lts (msgs l ‖ ((g (mirrorN ((g M) : proc) N)) : proc)) τ q0) ->
    (msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc)) ->
    ax_pre (msgs l ‖ ((g M) : proc))
           (msgs l ‖ ((g (mirrorN ((g M) : proc) N)) : proc)).

Lemma ax_phaseA_glb_sub : forall n (M N : gproc) (l : list TypeOfActions),
  (forall z, ~ lts ((g N) : proc) τ z) ->
  length l <= n ->
  (forall l', subbag l' l ->
     (forall q0, ~ lts (msgs l' ‖ ((g (mirrorN ((g M) : proc) N)) : proc)) τ q0) ->
      ax_pre (msgs l' ‖ ((g M) : proc))
             (msgs l' ‖ ((g (mirrorN ((g M) : proc) N)) : proc))) ->
  ax_pre (msgs l ‖ ((g M) : proc))
         (msgs l ‖ ((g (mirrorN ((g M) : proc) N)) : proc)).
Proof.
  induction n as [|n IH]; intros M N l HstN Hlen Hstable.
  - apply Hstable; [ apply subbag_refl | ]. intros q0 Hq0.
    destruct (mir_tau_inv M N l q0 HstN Hq0) as (c & v & l0 & Hperm & _).
    apply Permutation_length in Hperm. simpl in Hperm. lia.
  - destruct (lts_dec (msgs l ‖ ((g (mirrorN ((g M) : proc) N)) : proc)) τ)
      as [Hno | [q0 Hq0]].
    + apply Hstable; [ apply subbag_refl | exact Hno ].
    + apply ax_below_cfg_glb.
      * exists q0. exact Hq0.
      * intros q' Hq'.
        destruct (mir_tau_inv M N l q' HstN Hq') as (c & v & l0 & Hperm & Hcgr).
        apply ax_cgr.
        etransitivity; [ apply (cgr_bag_pull l l0 c v ((g M) : proc) Hperm) | ].
        apply cgr_symm. exact Hcgr.
      * intros c v q'' Hq''.
        rewrite (mir_in_inv M N l c v q'' Hq'').
        apply ax_cgr. apply cgr_symm. apply cgr_par_rot.
      * intros c v l0 Hperm. apply IH; [ exact HstN | | ].
        -- apply Permutation_length in Hperm. simpl in Hperm. lia.
        -- intros l'' Hsub Hst. apply Hstable; [ | exact Hst ].
           eapply subbag_trans;
             [ exact Hsub | apply (subbag_cons (c,v) l0 l Hperm) ].
Qed.

(** Et la réduction : le cas à cible stable suffit, l'hypothèse
    sémantique étant demandée exactement sous la forme que [BagSem]
    fournit. *)
Theorem phaseA_of_stable_target : PhaseA_stable_target ->
  forall (M N : gproc) (l : list TypeOfActions),
    (forall z, ~ lts ((g N) : proc) τ z) ->
    (forall l', subbag l' l ->
        (msgs l' ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ ((g N) : proc))) ->
    ax_pre (msgs l ‖ ((g M) : proc))
           (msgs l ‖ ((g (mirrorN ((g M) : proc) N)) : proc)).
Proof.
  intros HST M N l HstN Hsem.
  eapply (ax_phaseA_glb_sub (length l)); [ exact HstN | apply Nat.le_refl | ].
  intros l' Hsub Hst. apply HST; [ exact HstN | exact Hst | apply Hsem; exact Hsub ].
Qed.

(** ** PHASE A EST PROUVÉE — l'hypothèse [PhaseA_config] disparaît

    Le certificat de [ax_phaseA_direct] est demandé à **tous** les
    buffers où le miroir est stable.  [VACCS_Cond2.certificate_N_refuses]
    le fournit exactement là — pour tout buffer dont [N] refuse les
    canaux — **à partir du fait sémantique au sac VIDE** :

        certificate_N_refuses : … -> (g M) ⊑ₘᵤₛₜᵢ (g N) ->
          ∀ m, OutOnly m -> (N refuse les canaux de m) ->
          Settles (chans m) ((g M) ▷ m)

    Et « le miroir est stable en [m] » **est** « [N] refuse les canaux de
    [m] », parce que le miroir a une garde sur [c] dès que [N] en a une
    ([offers_mirrorN]) et que la disponibilité d'une entrée ne dépend pas
    de la valeur ([lts_in_value_swap]).

    Pourquoi cela ne contredit pas [VACCS_DropProbes.CertAll_is_false] :
    ce contre-exemple ne suppose l'inéquation qu'au sac [[(a,v)]], pas au
    sac vide — et au sac vide elle est **fausse** pour lui
    ([g MCert ⋢ₘᵤₛₜᵢ g 𝟘], le client [(b!w•𝟘) ‖ (e?①)] les sépare).  Le
    certificat n'était donc pas réfuté sous cette hypothèse-ci.

    Or le fait au sac vide est précisément ce que [BagSem] fournit :
    [subbag [] l] vaut toujours.  D'où [sem_at_empty], puis les versions
    **inconditionnelles** de [ax_below_gsum_stable_cfg] et
    [ax_below_NF_cfg] : tout le côté droit à une configuration ne dépend
    plus d'aucune hypothèse ouverte. *)

Lemma mirror_refuses_of_N : forall (P : proc) (N : gproc) c v,
  (forall r, ~ lts ((g (mirrorN P N)) : proc) (ActExt (ActIn (c,v))) r) ->
  forall q, ~ lts ((g N) : proc) (ActExt (ActIn (c,v))) q.
Proof.
  intros P N c v Hno q Hq.
  destruct (offers_mirrorN P N c v q Hq) as (w & r & Hr).
  destruct (lts_in_value_swap _ _ _ Hr c w v eq_refl) as (r' & Hr').
  eapply Hno. exact Hr'.
Qed.

Theorem phaseA_of_empty_bag_sem : forall (P : proc) (N : gproc) (l : list TypeOfActions),
  Static P -> gStatic N -> (forall z, ~ lts ((g N) : proc) τ z) ->
  P ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc) ->
  ax_pre (msgs l ‖ P) (msgs l ‖ ((g (mirrorN P N)) : proc)).
Proof.
  intros P N l HP HN HstN Hsem.
  apply ax_phaseA_direct; [ exact HP | exact HN | exact HstN | ].
  intros K Hout Hst.
  eapply certificate_N_refuses;
    [ exact HP | exact HN | exact HstN | exact Hsem | exact Hout | ].
  intros a Hin r Hr. destruct a as (c,v).
  pose proof (no_step_of_stable _ Hst) as Hns.
  rewrite fw_stable_iff in Hns. destruct Hns as (_ & Hin2).
  eapply (mirror_refuses_of_N P N c v); [ | exact Hr ].
  intros r' Hr'. eapply Hin2; [ exact Hin | exact Hr' ].
Qed.

(** [BagSem] quantifie sur les sous-sacs, et [subbag [] l] vaut toujours :
    le fait au sac vide est donc gratuit. *)
Lemma sem_at_empty : forall (l : list TypeOfActions) (M L : gproc),
  BagSem l ((g M) : proc) L -> ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g L) : proc).
Proof.
  intros l M L H.
  assert (Hnil : subbag ([] : list TypeOfActions) l)
    by (exists l; rewrite app_nil_r; reflexivity).
  specialize (H [] Hnil). simpl in H.
  intros t Hm.
  apply (proj1 (must_i_cgr _ _ (ax_nil_par ((g L) : proc))) t).
  apply H.
  apply (proj2 (must_i_cgr _ _ (ax_nil_par ((g M) : proc))) t). exact Hm.
Qed.

Theorem ax_below_gsum_stable_cfg_uncond :
  forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
  BagSem l ((g M) : proc) N ->
  (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
     BagSem l ((g M) : proc) L -> subbag l' l ->
     forall c v Q' l'', subbag l'' l' -> lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ ((g M) : proc))) (msgs l'' ‖ Q')) ->
  BagBelow l ((g M) : proc) N.
Proof.
  intros l M N HM HN Hnf Hsem Hrec.
  apply ax_below_gsum_bag; try assumption.
  intros L HL HstL HsemL l' Hs'.
  assert (HtauL : forall p, ~ lts ((g L) : proc) τ p).
  { intros p Hp. eapply stable_no_lts; [ apply gStable_iff; exact HstL | exact Hp ]. }
  apply ax_below_stable_sum_cfg; [ exact HtauL | | ].
  - apply phaseA_of_empty_bag_sem;
      [ apply static_g; exact HM | exact HL | exact HtauL
      | eapply sem_at_empty; exact HsemL ].
  - intros c v Q' l'' Hs'' Hl. eapply Hrec; eassumption.
Qed.

Corollary ax_below_NF_cfg_uncond :
  forall (n : nat) (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
  BagSem l ((g M) : proc) N ->
  (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
     BagSem l ((g M) : proc) L -> subbag l' l ->
     forall c v Q' l'', subbag l'' l' -> lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ ((g M) : proc))) (msgs l'' ‖ Q')) ->
  ax_pre (NF n l M) (NF n l N).
Proof.
  intros n l M N HM HN Hnf Hsem Hrec. unfold NF.
  apply ax_res_n.
  apply (ax_below_gsum_stable_cfg_uncond l M N HM HN Hnf Hsem Hrec l).
  apply subbag_refl.
Qed.

(** ** `BagSem` DISPARAÎT DE L'INTERFACE — quand la gauche est τ-stable

    `BagSem` (l'inéquation à **tous** les sous-sacs) est strictement plus
    forte que l'inéquation au sac, et même **fausse** en général :
    `VACCS_DropProbes.MCert_below` la vérifie au sac `[(a,v)]` et la
    viole au sac vide.

    Mais quand la configuration gauche est **τ-stable**, elle est
    gratuite, en deux coups déjà sur disque :

    - `VACCS_NormalForm.msgs_cancel` retire le sac — c'est là que la
      stabilité sert, via l'argument de vidange ;
    - `must_i_par_compat_r` le remet à n'importe quel sous-sac, `⊑ₘᵤₛₜᵢ`
      étant une précongruence pour `‖` **sans condition** (les deux ponts
      `must`-niveau de `VACCS_Erasure` / `VACCS_Shift`).

    D'où [ax_below_cfg_stable_left] et [ax_below_NF_stable_left], dont
    l'hypothèse sémantique est l'inéquation **au sac courant** — celle
    que `completeness_from_NF` fournit. *)

Lemma bagsem_of_cancel : forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  (forall z, ~ (((g M) ▷ bag l) ⟶ z)) ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
  BagSem l ((g M) : proc) N.
Proof.
  intros l M N HM HN HstM Hpre l' _.
  apply must_i_par_compat_r.
  eapply msgs_cancel; eassumption.
Qed.

Theorem ax_below_cfg_stable_left : forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
  (forall z, ~ (((g M) ▷ bag l) ⟶ z)) ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
  (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
     BagSem l ((g M) : proc) L -> subbag l' l ->
     forall c v Q' l'', subbag l'' l' -> lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ ((g M) : proc))) (msgs l'' ‖ Q')) ->
  ax_pre (msgs l ‖ ((g M) : proc)) (msgs l ‖ ((g N) : proc)).
Proof.
  intros l M N HM HN Hnf HstM Hpre Hrec.
  apply (ax_below_gsum_stable_cfg_uncond l M N HM HN Hnf
           (bagsem_of_cancel l M N HM HN HstM Hpre) Hrec l).
  apply subbag_refl.
Qed.

Corollary ax_below_NF_stable_left :
  forall (n : nat) (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
  (forall z, ~ (((g M) ▷ bag l) ⟶ z)) ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
  (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
     BagSem l ((g M) : proc) L -> subbag l' l ->
     forall c v Q' l'', subbag l'' l' -> lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ ((g M) : proc))) (msgs l'' ‖ Q')) ->
  ax_pre (NF n l M) (NF n l N).
Proof.
  intros n l M N HM HN Hnf HstM Hpre Hrec. unfold NF. apply ax_res_n.
  eapply ax_below_cfg_stable_left; eassumption.
Qed.

(** ** LE RÉSIDU, ISOLÉ PAR UN CAS : gauche τ-stable / gauche instable

    « La configuration gauche a-t-elle un τ ? » est **décidable**
    ([fw_tau_dec]) : un τ du forwarder est soit un τ du processus
    ([lts_dec]), soit une délivrance d'un message du sac (récurrence sur
    le sac).  Le cas stable est complet ([ax_below_cfg_stable_left]) ;
    l'autre est nommé [CfgUnstableLeft], et [ax_below_NF_all] montre que
    c'est **tout ce qui manque** au niveau de la forme normale. *)

Lemma fw_tau_dec : forall (p : proc) (l : list TypeOfActions),
  (forall z, ~ ((p ▷ bag l) ⟶ z)) \/ (exists z, ((p ▷ bag l) ⟶ z)).
Proof.
  intros p l. destruct (lts_dec p τ) as [Hnt | [q Hq]].
  - induction l as [|a l IH]; simpl.
    + left. apply fw_stable_iff. split; [ exact Hnt | ].
      intros b Hb. exfalso. eapply gmultiset.gmultiset_not_elem_of_empty. exact Hb.
    + destruct (lts_dec p (ActExt (ActIn a))) as [Hna | [r Hr]].
      * destruct IH as [Hno | [z Hz]].
        -- left. apply fw_stable_iff. split; [ exact Hnt | ].
           intros b Hb. apply gmultiset.gmultiset_elem_of_disj_union in Hb.
           destruct Hb as [Hb | Hb].
           ++ apply gmultiset.gmultiset_elem_of_singleton in Hb.
              injection Hb as Hb. subst b. exact Hna.
           ++ rewrite fw_stable_iff in Hno. destruct Hno as (_ & Hno2).
              apply Hno2. exact Hb.
        -- right. exists ((z.1) ▷ ({[+ ActOut a +]} ⊎ z.2)).
           apply (fw_tau_add (p ▷ bag l) z ({[+ ActOut a +]}) Hz).
      * right. eexists. apply fw_tau_deliver. exact Hr.
  - right. eexists. apply fw_tau_left. exact Hq.
Qed.

Definition CfgUnstableLeft : Prop :=
  forall (l : list TypeOfActions) (M N : gproc),
    gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
    (exists z, (((g M) : proc) ▷ bag l) ⟶ z) ->
    ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
    (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
       BagSem l ((g M) : proc) L -> subbag l' l ->
       forall c v Q' l'', subbag l'' l' -> lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
         ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ ((g M) : proc))) (msgs l'' ‖ Q')) ->
    ax_pre (msgs l ‖ ((g M) : proc)) (msgs l ‖ ((g N) : proc)).

Theorem ax_below_NF_all : CfgUnstableLeft ->
  forall (n : nat) (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
  (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
     BagSem l ((g M) : proc) L -> subbag l' l ->
     forall c v Q' l'', subbag l'' l' -> lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ ((g M) : proc))) (msgs l'' ‖ Q')) ->
  ax_pre (NF n l M) (NF n l N).
Proof.
  intros HU n l M N HM HN Hnf Hpre Hrec. unfold NF. apply ax_res_n.
  destruct (fw_tau_dec ((g M) : proc) l) as [Hno | Hex].
  - eapply ax_below_cfg_stable_left; eassumption.
  - eapply HU; eassumption.
Qed.

(** ** LE CAS NU (SAC VIDE) EST COMPLET, SANS RÉSIDU

    Assembler le pilote τ nu ([ax_below_gsum_inv]) et l'étape de feuille
    stable nue ([ax_below_stable_sum_clean], dont Phase A est déchargée
    par [ax_phaseA_settle] à partir de l'inéquation elle-même) donne la
    comparaison de deux sommes gardées **sans aucune hypothèse ouverte**,
    et donc le cas du sac vide par [ax_nil_par].

    C'est le témoin que l'architecture fonctionne de bout en bout dès que
    le sac ne s'en mêle pas : tout ce que [CfgUnstableLeft] laisse ouvert
    tient au sac, pas au reste. *)

Theorem ax_below_bare : forall (M N : gproc), gStatic M -> gStatic N ->
  Forall tau_cont_nf (summands N) ->
  ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc) ->
  (forall (L : gproc), gStatic L -> gStable L ->
     forall c v Q', lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       (((c ! v • 𝟘) ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ Q') ->
       ax_pre ((c ! v • 𝟘) ‖ ((g M) : proc)) Q') ->
  ax_pre ((g M) : proc) ((g N) : proc).
Proof.
  intros M N HM HN Hnf Hsem Hrec.
  apply ax_below_gsum_inv; try assumption.
  intros L HL HstL _ Hsem'.
  assert (HtauL : forall p, ~ lts ((g L) : proc) τ p).
  { intros p Hp. eapply stable_no_lts; [ apply gStable_iff; exact HstL | exact Hp ]. }
  apply ax_below_stable_sum_clean; try assumption.
  intros c v Q' Hl Hs. eapply Hrec; eassumption.
Qed.

Corollary ax_below_cfg_nil_bag : forall (M N : gproc), gStatic M -> gStatic N ->
  Forall tau_cont_nf (summands N) ->
  ((msgs [] ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs [] ‖ ((g N) : proc))) ->
  (forall (L : gproc), gStatic L -> gStable L ->
     forall c v Q', lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       (((c ! v • 𝟘) ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ Q') ->
       ax_pre ((c ! v • 𝟘) ‖ ((g M) : proc)) Q') ->
  ax_pre (msgs [] ‖ ((g M) : proc)) (msgs [] ‖ ((g N) : proc)).
Proof.
  intros M N HM HN Hnf Hsem Hrec.
  assert (HcM : ((g M) : proc) ≡* (msgs [] ‖ ((g M) : proc))) by (apply ax_nil_par).
  assert (HcN : ((g N) : proc) ≡* (msgs [] ‖ ((g N) : proc))) by (apply ax_nil_par).
  eapply ax_trans; [ apply ax_cgr_sym; exact HcM | ].
  eapply ax_trans; [ | apply ax_cgr; exact HcN ].
  apply ax_below_bare; try assumption.
  intros t Ht.
  apply (proj1 (must_i_cgr _ _ HcN) t). apply Hsem.
  apply (proj2 (must_i_cgr _ _ HcM) t). exact Ht.
Qed.

(** *** La version qui garde [InvR] — et le contrôle de non-vacuité

    Le pilote τ fournit en plus [InvR (g N) L] : toute transition
    d'entrée d'une feuille est atteignable depuis la cible.  La garder
    dans la prémisse récursive n'a l'air de rien, mais c'est elle qui la
    rend **vide** quand la cible n'a pas d'entrée — d'où le contrôle
    ci-dessous, qui re-dérive [ax_ccat_l] *par la machinerie générale*
    (pilote τ, feuille stable, Phase A, Phase B) au lieu de la règle. *)

Theorem ax_below_bare_inv : forall (M N : gproc), gStatic M -> gStatic N ->
  Forall tau_cont_nf (summands N) ->
  ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc) ->
  (forall (L : gproc), gStatic L -> gStable L -> InvR ((g N) : proc) L ->
     forall c v Q', lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       (((c ! v • 𝟘) ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ Q') ->
       ax_pre ((c ! v • 𝟘) ‖ ((g M) : proc)) Q') ->
  ax_pre ((g M) : proc) ((g N) : proc).
Proof.
  intros M N HM HN Hnf Hsem Hrec.
  apply ax_below_gsum_inv; try assumption.
  intros L HL HstL HInv Hsem'.
  assert (HtauL : forall p, ~ lts ((g L) : proc) τ p).
  { intros p Hp. eapply stable_no_lts; [ apply gStable_iff; exact HstL | exact Hp ]. }
  apply ax_below_stable_sum_clean; try assumption.
  intros c v Q' Hl Hs. eapply Hrec; eassumption.
Qed.

Example ax_below_bare_ccat : forall c : ChannelData,
  ax_pre ((g ((c ? (c ! (bvar 0) • 𝟘)))) : proc) ((g 𝟘) : proc).
Proof.
  intro c.
  apply ax_below_bare_inv.
  - repeat constructor.
  - constructor.
  - simpl. repeat constructor.
  - apply must_i_ccat_l.
  - intros L HL HstL HInv c0 v Q' Hl Hs. exfalso.
    destruct HInv as (HInv1 & _).
    pose proof (HInv1 c0 v Q' Hl) as Hw.
    inversion Hw; subst.
    + inversion l.
    + inversion l.
Qed.

(** ** LA COUCHE τ SANS LES PILOTES : `ax_glb_tau` fait tout, et sans `tau_cont_nf`

    Les pilotes τ portés depuis VCCS ([ax_below_gsum_inv] et ses
    variantes) exigent `Forall tau_cont_nf (summands N)` — que les
    continuations des `𝛕`-sommants soient des **sommes gardées**.  C'est
    faux pour une forme normale VACCS, dont les continuations sont des
    `p ‖ g N` ou des `Ѵⁿ (msgs l ‖ g M)`.

    `ax_glb_tau` s'en passe.  Sur une **somme gardée** à droite ses deux
    prémisses de sortie sont **vides** ([gsum_no_out]), et il ne reste
    que :

    - les τ-réduits, avec `p ⊑ₘᵤₛₜᵢ q ⊑ₘᵤₛₜᵢ q'` par [must_i_tau_below] ;
    - les entrées, avec [must_i_feed_below].

    Les deux descendent sur `size` ([Static_lts_decrease]), donc un seul
    pas de récursion externe suffit.  Le cas stable est
    [ax_below_stable_sum_clean], dont Phase A est déchargée par
    [ax_phaseA_settle] à partir de l'inéquation elle-même.

    Résultat : un **pas de complétude complet** à droite somme gardée,
    sans `tau_cont_nf`, sans sac, sans hypothèse ouverte — seulement
    l'hypothèse de récurrence sur `size q`.

    Réserve honnête : la gauche doit être une somme gardée, et la
    prémisse d'entrée en produit une qui ne l'est pas
    ([(c!v•𝟘) ‖ g M]) ; la renormaliser ramène le sac, et donc
    [CfgUnstableLeft]. *)

Lemma ax_glb_gsum : forall (p : proc) (N : gproc),
  (exists q0, lts ((g N) : proc) τ q0) ->
  (forall q', lts ((g N) : proc) τ q' -> ax_pre p q') ->
  (forall c v q'', lts ((g N) : proc) (ActExt (ActIn (c,v))) q'' ->
     ax_pre ((c ! v • 𝟘) ‖ p) q'') ->
  ax_pre p ((g N) : proc).
Proof.
  intros p N Hex Htau Hin. apply ax_glb_tau; try assumption.
  - intros c v q'' Hl. exfalso. eapply gsum_no_out. exact Hl.
  - intros c v p'' q'' _ Hl. exfalso. eapply gsum_no_out. exact Hl.
Qed.

(** ** The stable case for a GUARDED SUM, at an arbitrary left

    [ax_below_stable_sum_clean] asks the left to be a guarded sum too;
    nothing in the chain needs that.  Phase A ([ax_phaseA_direct]) has
    accepted an arbitrary [Static] left since the mirror was generalised,
    and its certificate ([VACCS_Cond2.certificate_N_refuses]) has just
    been generalised the same way — its proof never inspected the left,
    only fed it to [fw_converge_static] and to the acceptance bridge.

    So the whole chain runs at [l = []], and [subbag l' []] forces
    [l' = []], which collapses [ax_below_stable_sum_cfg]'s sub-bag
    quantifier. *)

Lemma subbag_nil_inv : forall l', subbag l' [] -> l' = [].
Proof.
  intros l' (l1 & Hp).
  apply Permutation_nil in Hp. destruct l1; simpl in Hp; [ exact Hp | discriminate ].
Qed.

Theorem ax_below_stable_gsum_gen : forall (P : proc) (N : gproc),
  Static P -> gStatic N -> (forall z, ~ lts ((g N) : proc) τ z) ->
  P ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc) ->
  (forall c v Q', lts ((g N) : proc) (ActExt (ActIn (c,v))) Q' ->
     ax_pre (((c ! v • 𝟘) : proc) ‖ P) Q') ->
  ax_pre P ((g N) : proc).
Proof.
  intros P N HP HN HstN Hsem Hrec.
  assert (Hmain : ax_pre (msgs [] ‖ P) (msgs [] ‖ ((g N) : proc))).
  { apply ax_below_stable_sum_cfg; [ exact HstN | | ].
    - apply phaseA_of_empty_bag_sem; assumption.
    - intros c v Q' l'' Hs'' Hl. apply subbag_nil_inv in Hs''. subst l''.
      simpl. eapply ax_trans; [ apply ax_cgr_sym; apply ax_nil_par | ].
      eapply ax_trans; [ apply (Hrec c v Q' Hl) | apply ax_cgr; apply ax_nil_par ]. }
  simpl in Hmain.
  eapply ax_trans; [ apply ax_cgr; apply ax_nil_par | ].
  eapply ax_trans; [ exact Hmain | apply ax_cgr_sym; apply ax_nil_par ].
Qed.

(** Hence the whole step for a guarded-sum right-hand side, at an
    arbitrary left: stable by the above, unstable by [ax_glb_gsum] (whose
    output premises are vacuous — a guarded sum never emits). *)

Theorem completeness_gsum_step_gen : forall (P : proc) (N : gproc),
  Static P -> gStatic N ->
  P ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc) ->
  (forall p' q', Static p' -> Static q' -> (size q' < size ((g N) : proc))%nat ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
  ax_pre P ((g N) : proc).
Proof.
  intros P N HP HN Hsem IH.
  assert (HsN : Static ((g N) : proc)) by (apply static_g; exact HN).
  destruct (lts_dec ((g N) : proc) τ) as [Hno | [q0 Hq0]].
  - apply ax_below_stable_gsum_gen; try assumption.
    intros c v Q' Hl. apply IH.
    + constructor; [ constructor | exact HP ].
    + eapply Static_preserved_by_lts; [ exact HsN | exact Hl ].
    + eapply Static_lts_decrease; [ exact HsN | exact Hl ].
    + eapply must_i_feed_below; [ exact Hsem | exact Hl ].
  - apply ax_glb_gsum.
    + exists q0. exact Hq0.
    + intros q' Hl. apply IH.
      * exact HP.
      * eapply Static_preserved_by_lts; [ exact HsN | exact Hl ].
      * eapply Static_lts_decrease; [ exact HsN | exact Hl ].
      * intros t Ht. apply (must_i_tau_below _ _ Hl t). apply Hsem. exact Ht.
    + intros c v q'' Hl. apply IH.
      * constructor; [ constructor | exact HP ].
      * eapply Static_preserved_by_lts; [ exact HsN | exact Hl ].
      * eapply Static_lts_decrease; [ exact HsN | exact Hl ].
      * eapply must_i_feed_below; [ exact Hsem | exact Hl ].
Qed.


(** ** Vers une cible QUELCONQUE : la réduction, et ce qu'elle laisse

    [VACCS_AxExamples.completeness_from_NF] ramène déjà la complétude à la
    comparaison de deux **formes normales** [Ѵⁿ (msgs l ‖ g M)].  Le pas
    suivant est d'aligner les profondeurs : rembourrer chaque côté par une
    restriction vide ([NF_pad]) jusqu'à [n₁ + n₂].

    Ce qui reste après cela, et qui est l'obstacle réel :

    - les deux **sacs** peuvent différer ([bags_agree] ne les égalise que
      pour une gauche τ-stable et une droite τ-libre) ;
    - surtout, [completeness_from_NF] livre l'hypothèse sémantique
      **sous le bloc de restriction**, alors que tous les
      [ax_below_NF_*] la réclament **au niveau de la configuration**,
      c'est-à-dire hors du bloc.  Et l'on ne peut pas la faire sortir :
      [ν] cache, donc [ν p ⊑ₘᵤₛₜᵢ ν q] n'entraîne pas [p ⊑ₘᵤₛₜᵢ q].

    Le bloc est donc un obstacle à part entière, distinct du sac et de la
    disjonction.  Il disparaît sur le fragment **sans [ν]**, où
    [normal_form] rend [n = 0] — c'est le sous-fragment naturel où toute
    la machinerie de configuration s'applique telle quelle. *)

Theorem NF_pad_to_common_depth :
  (forall n l1 M l2 N, gStatic M -> gStatic N ->
     (NF n l1 M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (NF n l2 N) -> ax_pre (NF n l1 M) (NF n l2 N)) ->
  forall n1 l1 M n2 l2 N, gStatic M -> gStatic N ->
    (NF n1 l1 M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (NF n2 l2 N) -> ax_pre (NF n1 l1 M) (NF n2 l2 N).
Proof.
  intros H n1 l1 M n2 l2 N HM HN Hsem.
  assert (HcA : NF ((n1 + n2)%nat) (map (shiftCn 0 n2) l1) (gNewVarCn 0 n2 M)
                ≡* NF n1 l1 M) by apply NF_pad.
  assert (HcB : NF ((n2 + n1)%nat) (map (shiftCn 0 n1) l2) (gNewVarCn 0 n1 N)
                ≡* NF n2 l2 N) by apply NF_pad.
  eapply ax_trans; [ apply ax_cgr_sym; exact HcA | ].
  eapply ax_trans; [ | apply ax_cgr; exact HcB ].
  assert (Ec : (n2 + n1)%nat = (n1 + n2)%nat) by apply Nat.add_comm.
  rewrite Ec. rewrite Ec in HcB.
  apply H.
  - apply gStatic_gNewVarCn. exact HM.
  - apply gStatic_gNewVarCn. exact HN.
  - intros t Ht.
    apply (proj1 (must_i_cgr _ _ HcB)).
    apply Hsem.
    apply (proj2 (must_i_cgr _ _ HcA)). exact Ht.
Qed.

(** ** …et pourquoi ce pas ne se généralise PAS à une cible quelconque

    [completeness_gsum_step_gen] fonctionne parce que la cible est une somme
    gardée : elle n'émet jamais ([gsum_no_out]), donc les deux prémisses
    d'émission d'[ax_glb_tau] sont vides.  Pour une cible arbitraire elles
    mordent, et **la première n'est pas conséquence de la sémantique** :

        p := g (𝛕 • (c!v•𝟘))     q := c!v•𝟘

    [p ⊑ₘᵤₛₜᵢ q] par [must_i_tau_below] (le [τ] du serveur ne fait que
    diminuer), [q] émet [(c,v)], et [p] n'a **aucune** transition de
    sortie — son unique transition est le [τ].

    Ce n'est pas une impasse pour l'inéquation elle-même : sur cette
    instance [ax_tau_step] la donne directement.  C'est une impasse pour
    *cette voie-là* — la récursion générale sur [size q] ne peut pas
    invoquer [ax_glb_tau] dès que la cible émet, et doit disposer d'un
    autre pas pour ce cas. *)

Theorem glb_output_premise_not_semantic : forall (c : ChannelData) (v : ValueData),
  (((g (𝛕 • (((c ! v • 𝟘)) : proc))) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (((c ! v • 𝟘)) : proc))
  /\ (exists q'', lts (((c ! v • 𝟘)) : proc) (ActExt (ActOut (c,v))) q'')
  /\ ~ (exists p'', lts ((g (𝛕 • (((c ! v • 𝟘)) : proc))) : proc)
                        (ActExt (ActOut (c,v))) p'').
Proof.
  intros c v. split; [ | split ].
  - eapply must_i_tau_below. apply lts_tau.
  - exists ((g 𝟘) : proc). apply lts_output.
  - intros (p'' & H). inversion H.
Qed.

(** ** CE QUE L'ARGUMENT DE VIDANGE SERT VRAIMENT À PRODUIRE

    [ax_below_cfg_stable_left] passait par [msgs_cancel] — l'argument de
    vidange, qui est du `≼ₐₛ` pur — pour retirer le sac.  Mais le seul
    usage qu'il en fait est d'obtenir l'inéquation **au sac vide** ; tout
    le reste (la remettre à chaque sous-sac) est [must_i_par_compat_r],
    et `⊑ₘᵤₛₜᵢ` est une précongruence pour `‖` **sans condition**.

    En isolant les deux, on obtient un théorème plus général : la
    stabilité de la gauche n'est plus une hypothèse, l'inéquation au sac
    vide la remplace — et [msgs_cancel] devient un simple *moyen* de
    l'obtenir, parmi d'autres.

    Le cas gauche-stable en est l'instance :
    [ax_below_cfg_stable_left = msgs_cancel + ax_below_cfg_empty_sem]. *)

Lemma bagsem_of_empty_sem : forall (l : list TypeOfActions) (M N : gproc),
  ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc) -> BagSem l ((g M) : proc) N.
Proof.
  intros l M N Hsem l' _. apply must_i_par_compat_r. exact Hsem.
Qed.

Theorem ax_below_cfg_empty_sem : forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
  ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc) ->
  (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
     BagSem l ((g M) : proc) L -> subbag l' l ->
     forall c v Q' l'', subbag l'' l' -> lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ ((g M) : proc))) (msgs l'' ‖ Q')) ->
  ax_pre (msgs l ‖ ((g M) : proc)) (msgs l ‖ ((g N) : proc)).
Proof.
  intros l M N HM HN Hnf Hsem Hrec.
  apply (ax_below_gsum_stable_cfg_uncond l M N HM HN Hnf
           (bagsem_of_empty_sem l M N Hsem) Hrec l).
  apply subbag_refl.
Qed.

Corollary ax_below_NF_empty_sem :
  forall (n : nat) (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
  ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc) ->
  (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
     BagSem l ((g M) : proc) L -> subbag l' l ->
     forall c v Q' l'', subbag l'' l' -> lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ ((g M) : proc))) (msgs l'' ‖ Q')) ->
  ax_pre (NF n l M) (NF n l N).
Proof.
  intros n l M N HM HN Hnf Hsem Hrec. unfold NF. apply ax_res_n.
  eapply ax_below_cfg_empty_sem; eassumption.
Qed.

(** ** …et le cas GAUCHE INSTABLE, sous non-régénération

    [ax_below_NF_stable_left] exige que la **configuration**
    [(g M ▷ bag l)] soit τ-stable — c'est-à-dire que [M] refuse tout ce
    que le sac contient — parce que c'est ce dont [msgs_cancel] a besoin
    pour retirer le sac.

    [VACCS_NormalForm.msgs_cancel_no_regen] obtient la même annulation
    d'une autre prémisse : que [M] ne **régénère** pas (aucun run ne rend
    tout ce qu'il a pris sans avoir rien pris), la τ-stabilité demandée
    n'étant plus que celle de la **somme nue** [g M], gratuite pour une
    somme [gStable].  D'où le cas gauche instable, qui est précisément
    celui que [ax_below_NF_stable_left] ne peut pas atteindre.

    C'est un fragment strict de [CfgUnstableLeft], pas sa totalité : la
    sonde régénérante de `VACCS_DropProbes.v` viole la prémisse par
    construction, et c'est là que la disjonction reste ouverte. *)

Theorem ax_below_NF_no_regen : forall (n : nat) (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
  (forall z, ~ lts ((g M) : proc) τ z) ->
  (forall r q, ((g M) : proc) ⟹[r] q -> bag (ins r) ⊆ bag (outs r) -> ins r = []) ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
  (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
     BagSem l ((g M) : proc) L -> subbag l' l ->
     forall c v Q' l'', subbag l'' l' -> lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ ((g M) : proc))) (msgs l'' ‖ Q')) ->
  ax_pre (NF n l M) (NF n l N).
Proof.
  intros n l M N HM HN Hnf HstM Hno Hcfg Hrec.
  eapply ax_below_NF_empty_sem; try eassumption.
  eapply msgs_cancel_no_regen; eassumption.
Qed.

(** ** …et la prémisse de non-régénération est SYNTAXIQUE

    [ax_below_NF_no_regen]'s premise quantifies over *runs*, which nobody
    can discharge by hand.  It follows from a check on the syntax:

      no continuation of [M] can ever emit on **its own** guard's channel.

    [ochans] — the **emission-only** footprint of `VACCS_Absorb.v` — is
    all it takes, and only the guard's **own** channel has to be checked,
    so the condition is one finite membership test per summand;
    [ochans_subst] makes it independent of the value received.  Using
    [ochans] rather than [pchans] matters: the latter also counts guarded
    channels, so it would reject [c ? (c ? 𝟘)], which guards [c] again
    but never returns it.

    Why it suffices: a run of a τ-stable guarded sum starts with an
    **input** (it cannot emit, [gsum_no_out], and cannot move silently),
    on a channel of [gchans M].  If that input were also returned, the
    return would come from the continuation, hence from [pchans] of it —
    which the check forbids.  The multiset inclusion
    [bag (ins r) ⊆ bag (outs r)] is exactly what says the first input is
    returned. *)

Lemma trace_out_in_ochans : forall s (p q : proc) c v, Static p ->
  p ⟹[s] q -> In (c,v) (outs s) -> In c (ochans p).
Proof.
  intros s p q c v Hst Hw. revert Hst.
  induction Hw as [x|s0 x y z Hl Hwt IH|mu s0 x y z Hl Hwt IH]; intros Hst Hin.
  - simpl in Hin. contradiction.
  - eapply lts_ochans_target; [ exact Hst | exact Hl | ].
    eapply IH; [ eapply Static_preserved_by_lts; eassumption | exact Hin ].
  - destruct mu as [[d w]|[d w]]; simpl in Hin.
    + eapply lts_ochans_target; [ exact Hst | exact Hl | ].
      eapply IH; [ eapply Static_preserved_by_lts; eassumption | exact Hin ].
    + destruct Hin as [He|Hin].
      * injection He as He1 He2. subst d w.
        eapply lts_ochans_out; [ exact Hst | exact Hl | reflexivity ].
      * eapply lts_ochans_target; [ exact Hst | exact Hl | ].
        eapply IH; [ eapply Static_preserved_by_lts; eassumption | exact Hin ].
Qed.

Lemma no_regen_of_own_channel : forall (M : gproc),
  (forall z, ~ lts ((g M) : proc) τ z) ->
  Static ((g M) : proc) ->
  (forall c v P', lts ((g M) : proc) (ActExt (ActIn (c,v))) P' -> ~ In c (ochans P')) ->
  forall r q, ((g M) : proc) ⟹[r] q -> bag (ins r) ⊆ bag (outs r) -> ins r = [].
Proof.
  intros M HstM HStat Hcrit r q Hw Hsub.
  inversion Hw as [ x Hx | s0 x y z Hl Hwt Hs Hx | mu s0 x y z Hl Hwt Hs Hx ]; subst.
  - reflexivity.
  - exfalso. eapply HstM. exact Hl.
  - exfalso. destruct mu as [[c v]|[c v]].
    + simpl in Hsub.
      assert (Hmem : ActOut (c,v) ∈ bag (outs s0))
        by (eapply gmultiset_elem_of_subseteq;
            [ apply gmultiset_elem_of_disj_union; left;
              apply gmultiset_elem_of_singleton; reflexivity
            | exact Hsub ]).
      apply bag_elem in Hmem.
      assert (HStaty : Static y) by (eapply Static_preserved_by_lts; eassumption).
      eapply (Hcrit c v y Hl).
      eapply trace_out_in_ochans; [ exact HStaty | exact Hwt | exact Hmem ].
    + eapply gsum_no_out. exact Hl.
Qed.

(** ** Le même critère, sans τ-stabilité : voies d'entrée et de sortie DISJOINTES

    [no_regen_of_own_channel] ne fait qu'une **inversion** sur le premier
    pas du run, et c'est là que la τ-stabilité de la somme intervient :
    elle force ce premier pas à être l'entrée.  Le critère global
    ci-dessous ne regarde plus le premier pas du tout — si aucune voie
    n'est à la fois d'entrée et de sortie, un run ne peut pas rendre ce
    qu'il a pris, quel que soit son ordre.

    **CORRECTION — le critère de disjonction est SUBSUMÉ.**  Une première
    rédaction annonçait les deux critères « incomparables ».  C'est faux,
    et [disjoint_implies_own_channel] ci-dessous le prouve : la
    disjonction entraîne le critère par garde, puisque le canal d'une
    garde est dans [ichans] et que [ochans] décroît le long des
    transitions.

    Et l'avantage annoncé — se passer de la τ-stabilité — ne se réalise
    pas non plus : le seul consommateur de la condition de vidange,
    [VACCS_NormalForm.msgs_cancel_no_regen], la réclame **aussi** pour son
    propre compte via [drain_forced_no_regen] (un processus avec un [𝛕]
    peut se déplacer pendant la vidange).  Le critère qui traite
    réellement les [𝛕]-sommants est [drain_forced_no_output] plus bas, et
    il passe par un autre chemin.

    [no_regen_of_disjoint] est conservé parce qu'il est correct et que sa
    preuve n'utilise pas la τ-stabilité : il redeviendrait utile si
    [drain_forced_no_regen] était un jour généralisé.  [ichans] et ses
    lemmes, eux, servent à énoncer la correction ci-dessus. *)

Lemma trace_in_in_ichans : forall s (p q : proc) c v, Static p ->
  p ⟹[s] q -> In (c,v) (ins s) -> In c (ichans p).
Proof.
  intros s p q c v Hst Hw. revert Hst.
  induction Hw as [x|s0 x y z Hl Hwt IH|mu s0 x y z Hl Hwt IH]; intros Hst Hin.
  - simpl in Hin. contradiction.
  - eapply lts_ichans_target; [ exact Hst | exact Hl | ].
    eapply IH; [ eapply Static_preserved_by_lts; eassumption | exact Hin ].
  - destruct mu as [[d w]|[d w]]; simpl in Hin.
    + destruct Hin as [He|Hin].
      * injection He as He1 He2. subst d w.
        eapply lts_ichans_in; [ exact Hst | exact Hl | reflexivity ].
      * eapply lts_ichans_target; [ exact Hst | exact Hl | ].
        eapply IH; [ eapply Static_preserved_by_lts; eassumption | exact Hin ].
    + eapply lts_ichans_target; [ exact Hst | exact Hl | ].
      eapply IH; [ eapply Static_preserved_by_lts; eassumption | exact Hin ].
Qed.

Lemma no_regen_of_disjoint : forall (p : proc),
  Static p ->
  (forall c, In c (ichans p) -> ~ In c (ochans p)) ->
  forall r q, p ⟹[r] q -> bag (ins r) ⊆ bag (outs r) -> ins r = [].
Proof.
  intros p Hst Hdisj r q Hw Hsub.
  destruct (ins r) as [|cv l0] eqn:E; [ reflexivity | exfalso ].
  destruct cv as (c,v).
  assert (Hmem : ActOut (c,v) ∈ bag (outs r)).
  { eapply gmultiset_elem_of_subseteq; [ | exact Hsub ].
    simpl. apply gmultiset_elem_of_disj_union. left.
    apply gmultiset_elem_of_singleton. reflexivity. }
  apply bag_elem in Hmem.
  eapply (Hdisj c).
  - eapply trace_in_in_ichans; [ exact Hst | exact Hw | ].
    rewrite E. left. reflexivity.
  - eapply trace_out_in_ochans; [ exact Hst | exact Hw | exact Hmem ].
Qed.

(** La subsomption annoncée : rien de ce que la disjonction donne n'est
    hors de portée du critère par garde. *)

Lemma disjoint_implies_own_channel : forall (p : proc), Static p ->
  (forall c, In c (ichans p) -> ~ In c (ochans p)) ->
  forall c v P', lts p (ActExt (ActIn (c,v))) P' -> ~ In c (ochans P').
Proof.
  intros p Hst Hdisj c v P' Hl Hin.
  eapply (Hdisj c).
  - eapply lts_ichans_in; [ exact Hst | exact Hl | reflexivity ].
  - eapply lts_ochans_target; [ exact Hst | exact Hl | exact Hin ].
Qed.

(** ** Une somme qui n'émet JAMAIS : le sac s'annule, `𝛕`-sommants compris

    [VACCS_NormalForm.drain_forced_no_regen] réclame la τ-stabilité pour
    conclure que la vidange laisse le processus **exactement** où il
    était.  Ce n'est pas ce dont [msgs_cancel] a besoin : il lui suffit
    que l'état atteint soit **τ-atteignable** avec un buffer vide, la
    composition [g M ⟹[[]] z₁ ⟹[s] x] donnant le run que [cond2]
    demande.

    Et cette conclusion-là s'obtient sans τ-stabilité, sous l'hypothèse
    que le terme n'émet jamais : le bilan de [fw_conservation] le long
    d'une trace de sorties pures donne
    [bag l ⊎ ∅ ⊎ bag (outs r) = z₂ ⊎ bag l ⊎ bag (ins r)], et
    [outs r = []] (rien n'est émis) force [z₂ = ∅] **et** [ins r = []],
    donc [r = []].

    C'est le premier résultat de ce développement qui traite un
    [𝛕]-sommant à gauche.  Le prix est une hypothèse forte —
    [ochans (g M) = []] — mais elle est **syntaxique et décidable**, et
    incomparable au critère [ochans] par garde de
    [no_regen_of_own_channel] : celui-ci autorise les émissions pourvu
    qu'aucune garde ne rende sa propre voie, celui-là les interdit toutes
    mais se passe de la τ-stabilité. *)

Lemma drain_forced_no_output : forall (l : list TypeOfActions) (p : proc) y,
  Static p -> ochans p = [] ->
  ((p ▷ bag l) ⟹[map ActOut l] y) ->
  y.2 = (∅ : MO (ExtAct TypeOfActions)) /\ p ⟹[[]] y.1.
Proof.
  intros l p y Hst Hoc Hw.
  destruct (fw_conservation _ _ _ Hw) as (r & Hr & Hbal). simpl in Hbal.
  assert (Houts : outs r = []).
  { destruct (outs r) as [|cv l0] eqn:E; [ reflexivity | exfalso ].
    destruct cv as (c,v).
    assert (Hin : In c (ochans p)).
    { eapply trace_out_in_ochans; [ exact Hst | exact Hr | ].
      rewrite E. left. reflexivity. }
    rewrite Hoc in Hin. exact Hin. }
  rewrite ins_map_out in Hbal. rewrite outs_map_out in Hbal.
  rewrite Houts in Hbal. simpl in Hbal.
  destruct (disj_union_cancel_empty _ _ _ _ _ _ Hbal) as (Ey & Er).
  assert (Hins : ins r = []) by (apply bag_nil_inv; exact Er).
  split; [ exact Ey | ].
  rewrite <- (trace_nil_of_ins_outs r Hins Houts). exact Hr.
Qed.

Theorem msgs_cancel_no_output : forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  ochans ((g M) : proc) = [] ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
  ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc).
Proof.
  intros l M N HM HN Hoc Hpre.
  destruct (msgs_accept l l (g M) (g N) Hpre) as (Hc1 & Hc2).
  apply must_iff_acceptance_set_VACCS. split.
  - intros s _. apply fw_converge_static. apply static_g. exact HN.
  - intros s y _ Hwy Hsty.
    assert (Hdrain : ((g N) ▷ bag l)
                       ⟹[map ActOut l] ((g N) ▷ (∅ : MO (ExtAct TypeOfActions)))).
    { replace (bag l) with (bag l ⊎ (∅ : MO (ExtAct TypeOfActions))) at 1
        by (apply gmultiset.gmultiset_disj_union_right_id).
      apply bag_wt_drain. }
    assert (Hbig : ((g N) ▷ bag l) ⟹[map ActOut l ++ s] y)
      by (eapply wt_concat; [ exact Hdrain | exact Hwy ]).
    destruct (Hc2 (map ActOut l ++ s) y
                (fw_converge_static (map ActOut l ++ s) (g M) (bag l) (static_g M HM))
                Hbig Hsty)
      as (x & Hwx & Hstx & Hincl).
    destruct (wt_split _ _ _ _ Hwx) as (z & Hz1 & Hz2).
    destruct (drain_forced_no_output l ((g M) : proc) z (static_g M HM) Hoc Hz1)
      as (Ez2 & Ez1).
    exists x. split; [ | split; [ exact Hstx | exact Hincl ] ].
    destruct z as (z1,z2). simpl in Ez2, Ez1. subst z2.
    replace s with (@nil (ExtAct TypeOfActions) ++ s) by reflexivity.
    eapply wt_concat; [ apply fw_wt_lift; exact Ez1 | exact Hz2 ].
Qed.

(** …d'où le premier disjoint de [CfgDisjunctionLocal] **sans aucune
    hypothèse de τ-stabilité** : c'est le cas (3) de la liste des trous,
    traité pour les sommes qui n'émettent jamais. *)

Lemma cfg_local_of_no_output :
  forall (l : list TypeOfActions) (M N : gproc), gStatic M -> gStatic N ->
  ochans ((g M) : proc) = [] ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
  (((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc))
  \/ (exists c v l0 Mc,
        Permutation l ((c,v) :: l0)
        /\ lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc
        /\ Mc ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (((c ! v • 𝟘) : proc) ‖ ((g N) : proc))).
Proof.
  intros l M N HM HN Hoc Hsem. left.
  eapply msgs_cancel_no_output; eassumption.
Qed.

Corollary ax_below_NF_no_return : forall (n : nat) (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
  (forall z, ~ lts ((g M) : proc) τ z) ->
  (forall c v P', lts ((g M) : proc) (ActExt (ActIn (c,v))) P' -> ~ In c (ochans P')) ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
  (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
     BagSem l ((g M) : proc) L -> subbag l' l ->
     forall c v Q' l'', subbag l'' l' -> lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ ((g M) : proc))) (msgs l'' ‖ Q')) ->
  ax_pre (NF n l M) (NF n l N).
Proof.
  intros n l M N HM HN Hnf HstM Hcrit Hcfg Hrec.
  eapply ax_below_NF_no_regen; try eassumption.
  eapply no_regen_of_own_channel; [ exact HstM | apply static_g; exact HM | exact Hcrit ].
Qed.

(** …et la variante qui **n'exige plus la τ-stabilité** : la somme gauche
    peut porter des [𝛕]-sommants, pourvu qu'elle n'émette jamais.  C'est
    la seule des trois formes de non-régénération qui se passe de la
    τ-stabilité de bout en bout — les deux autres alimentent
    [VACCS_NormalForm.msgs_cancel_no_regen], qui la réclame pour son
    propre compte via [drain_forced_no_regen]. *)

Corollary ax_below_NF_no_output : forall (n : nat) (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
  ochans ((g M) : proc) = [] ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
  (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
     BagSem l ((g M) : proc) L -> subbag l' l ->
     forall c v Q' l'', subbag l'' l' -> lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ ((g M) : proc))) (msgs l'' ‖ Q')) ->
  ax_pre (NF n l M) (NF n l N).
Proof.
  intros n l M N HM HN Hnf Hoc Hcfg Hrec.
  eapply ax_below_NF_empty_sem; try eassumption.
  eapply msgs_cancel_no_output; eassumption.
Qed.

(** Et le critère n'est pas vide sur le cas qu'il vise : voici une somme
    qui le satisfait **et** porte un [𝛕]-sommant, donc que
    [ax_below_NF_no_return] ne peut pas traiter. *)

Lemma no_output_criterion_covers_tau : forall (c : ChannelData),
  ochans ((g ((c ? ((g 𝟘) : proc)) + (𝛕 • ((g 𝟘) : proc)))) : proc) = []
  /\ (exists z, lts ((g ((c ? ((g 𝟘) : proc)) + (𝛕 • ((g 𝟘) : proc)))) : proc) τ z).
Proof.
  intro c. split.
  - reflexivity.
  - exists ((g 𝟘) : proc). apply lts_choiceR. apply lts_tau.
Qed.

(** ** LE RÉSIDU COMME DISJONCTION — les deux disjoints sont des théorèmes

    Pour une configuration gauche **instable**, deux mécanismes sont
    disponibles, et tous deux sont prouvés :

    - l'inéquation **au sac vide** donne [BagSem] par
      [must_i_par_compat_r], donc tout le matching
      ([ax_below_cfg_empty_sem]) ;
    - un successeur de délivrance **sous la cible** donne la descente
      ([ax_tau_step] + [ax_trans]).

    [CfgDisjunction] dit qu'au moins l'un des deux s'applique toujours.
    C'est le seul énoncé sémantique encore ouvert, et les trois
    contre-exemples du dépôt le vérifient — chacun réfutait *un* des
    disjoints et tombe dans l'autre :

    - [VACCS_DropProbes.MCert_below] : sac vide faux
      ([g MCert ⋢ₘᵤₛₜᵢ g 𝟘]), mais la délivrance dans le copycat donne un
      successeur [≂] la cible → **descente** ;
    - [regenerating_successor_can_fail] : idem, la délivrance de [b]
      convient → **descente** ;
    - [no_delivery_is_reversible] / [cfg_descent_is_false] : aucune
      descente, mais la cible **est** la gauche, donc le sac vide vaut
      par réflexivité → **Phase A**.

    La mesure de la descente est [size] de la **gauche**
    ([Static_lts_decrease]), celle du reste [size] de la droite : une
    récursion lexicographique les combine. *)

Definition CfgDisjunction : Prop :=
  forall (l : list TypeOfActions) (M N : gproc), gStatic M -> gStatic N ->
    (exists z, (((g M) : proc) ▷ bag l) ⟶ z) ->
    ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
    (((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc))
    \/ (exists p', lts (msgs l ‖ ((g M) : proc)) τ p'
                   /\ p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))).

(** ** …et « la continuation rend-elle le message ? » est DÉCIDABLE

    [descent_of_copycat_cont] asks for [Mc ≡* ((c!v•𝟘) ‖ K)].  By
    [TransitionShapeForOutputSimplified] that is exactly *"[Mc] can emit
    [(c,v)]"* — asynchrony again: an emitting process **is** the message
    beside its residue.  So the first half of the discriminant is an
    ordinary transition test, decidable by [VACCS_Absorb.lts_dec], and
    what is left of the descent disjunct is the residual [K ⊑ₘᵤₛₜᵢ g N]
    on a strictly smaller object.

    Output determinacy (an OBA axiom of this calculus) makes [K] unique
    up to [≡*], so the test really does determine the residual
    obligation rather than leaving a choice. *)

Corollary descent_of_returning_cont :
  forall (l l0 : list TypeOfActions) (c : ChannelData) (v : ValueData)
         (M N : gproc) (Mc K : proc),
  Permutation l ((c,v) :: l0) ->
  lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc ->
  lts Mc (ActExt (ActOut (c,v))) K ->
  K ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc) ->
  exists p', lts ((msgs l ‖ (g M)) : proc) τ p'
          /\ p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((msgs l ‖ (g N)) : proc).
Proof.
  intros l l0 c v M N Mc K Hperm Hin Hout HK.
  eapply descent_of_copycat_cont; [ exact Hperm | exact Hin | | exact HK ].
  eapply TransitionShapeForOutputSimplified. exact Hout.
Qed.

Corollary cont_returns_dec :
  forall (Mc : proc) (c : ChannelData) (v : ValueData),
  (forall K, ~ lts Mc (ActExt (ActOut (c,v))) K)
  \/ (exists K, lts Mc (ActExt (ActOut (c,v))) K).
Proof. intros Mc c v. apply lts_dec. Qed.

(** ** …et le second disjoint devient SANS CIBLE

    [descent_of_cont_below] asks for [Mc ⊑ₘᵤₛₜᵢ ((c!v•𝟘) ‖ g N)], which
    still mentions the target.  There is a stronger and much more
    tractable route: make the delivery **reversible**, so the successor
    lands *below the source* — and then it is below anything the source
    is below, target included.

    Concretely, when the guard returns the message ([Mc ⟶[(c,v)!] K]),
    the successor is [≂ msgs l ‖ K] — the message is back in the bag —
    so [K ⊑ₘᵤₛₜᵢ g M] suffices, by [must_i_par_compat_r] under the bag.

    That premise mentions **only the left-hand side**, and [K] is a
    reduct of a reduct of [g M].  It is what the copycat class satisfies
    ([K = 𝟘] and [VACCS_Copycat.must_i_nil_below_copycats]), and it is
    the shape a recursion can discharge. *)

Theorem descent_of_residue_below_source :
  forall (l l0 : list TypeOfActions) (c : ChannelData) (v : ValueData)
         (M : gproc) (Mc K q : proc),
  Permutation l ((c,v) :: l0) ->
  lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc ->
  lts Mc (ActExt (ActOut (c,v))) K ->
  K ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g M) : proc) ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q) ->
  exists p', lts ((msgs l ‖ (g M)) : proc) τ p' /\ p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q.
Proof.
  intros l l0 c v M Mc K q Hperm Hin Hout HK Hq.
  destruct (cfg_deliver_step l l0 c v M Mc Hperm Hin) as (r & Hr & Hcr).
  exists r. split; [ exact Hr | ].
  intros t Hm. apply Hq.
  assert (Hsh : Mc ≡* (((c ! v • 𝟘) : proc) ‖ K))
    by (eapply TransitionShapeForOutputSimplified; exact Hout).
  assert (H1 : (msgs l0 ‖ Mc) must_pass t)
    by (exact (proj2 (must_i_cgr _ _ Hcr) t Hm)).
  assert (Hc1 : (msgs l0 ‖ Mc) ≡* (msgs l0 ‖ (((c ! v • 𝟘) : proc) ‖ K)))
    by (apply cgr_fullpar; [ reflexivity | exact Hsh ]).
  assert (H2 : (msgs l0 ‖ (((c ! v • 𝟘) : proc) ‖ K)) must_pass t)
    by (exact (proj2 (must_i_cgr _ _ Hc1) t H1)).
  assert (H3 : (msgs l0 ‖ (((c ! v • 𝟘) : proc) ‖ ((g M) : proc))) must_pass t)
    by (exact (must_i_par_compat_r (msgs l0) _ _
                 (must_i_par_compat_r ((c ! v • 𝟘) : proc) _ _ HK) t H2)).
  assert (Hc2 : (msgs l0 ‖ (((c ! v • 𝟘) : proc) ‖ ((g M) : proc)))
                ≡* (msgs l ‖ ((g M) : proc))).
  { eapply cgr_trans;
      [ | apply cgr_fullpar; [ apply msgs_perm; apply Permutation_sym; exact Hperm
                             | reflexivity ] ].
    simpl. eapply cgr_trans; [ apply cgr_par_assoc_rev | ].
    apply cgr_fullpar; [ apply cgr_par_com | reflexivity ]. }
  exact (proj2 (must_i_cgr _ _ Hc2) t H3).
Qed.

(** ⚠ **[CfgDisjunctionSource] et [CfgDisjunctionSourceBag] sont FAUSSES**
    — [VACCS_DropProbes.cfg_disjunction_source_is_false] et
    [..._source_bag_is_false], réfutées par [MCert].  Elles sont
    conservées parce que les implications vers [CfgDisjunction] restent
    correctes et parce que [cfg_source_disjunct_at_copycats] montre que
    la classe copycat satisfait bien le disjoint — c'est *le disjoint
    pour tout le monde* qui échoue.

    Raison, et c'est la même que partout ici : le disjoint source dit
    « un pas interne est réversible » — le successeur est au-dessus de la
    **source** — et une garde sœur sur une voie étrangère au sac rend la
    source strictement plus forte que son propre successeur — cf.
    [VACCS_Bad.nil_not_below_dead_summand].

    [CfgDisjunction] et [CfgDisjunctionLocal] ne sont PAS touchées : leurs
    disjoints mentionnent la cible. *)

Definition CfgDisjunctionSource : Prop :=
  forall (l : list TypeOfActions) (M N : gproc), gStatic M -> gStatic N ->
    (exists z, (((g M) : proc) ▷ bag l) ⟶ z) ->
    ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
    (((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc))
    \/ (exists c v l0 Mc K,
          Permutation l ((c,v) :: l0)
          /\ lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc
          /\ lts Mc (ActExt (ActOut (c,v))) K
          /\ K ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g M) : proc)).

Theorem cfg_disjunction_of_source : CfgDisjunctionSource -> CfgDisjunction.
Proof.
  intros HS l M N HM HN Htau Hsem.
  destruct (HS l M N HM HN Htau Hsem)
    as [Hempty | (c & v & l0 & Mc & K & Hp & Hin & Hout & HK)].
  - left. exact Hempty.
  - right. eapply descent_of_residue_below_source; eassumption.
Qed.

(** [CfgDisjunctionSource]'s second disjunct is satisfied outright by the
    **copycat** class: such a guard's residue after returning the message
    is [𝟘], and a sum of copycats is above [𝟘]
    ([must_i_nil_below_copycats]).  This is the same positive case the
    instance table records for [MCert] and for the [rb]-guard of the
    regenerating probe — here at the level of the source-only disjunct,
    so the target plays no role at all. *)

Lemma source_disjunct_of_copycats :
  forall (c : ChannelData) (v : ValueData) (M : gproc) (Mc : proc),
  gCopycats M ->
  lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc ->
  exists K, lts Mc (ActExt (ActOut (c,v))) K /\ K ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g M) : proc).
Proof.
  intros c v M Mc Hcop Hin.
  destruct (gCopycats_lts M Hcop (ActIn (c,v)) Mc Hin) as (c0 & v0 & He & Hp).
  injection He as He1 He2. subst c0 v0. subst Mc.
  exists ((g 𝟘) : proc). split.
  - apply lts_output.
  - apply must_i_nil_below_copycats. exact Hcop.
Qed.

(** Un [τ] d'une configuration dont la somme est τ-stable est
    nécessairement une **délivrance** : [fw_tau_shape] n'a que deux
    formes, et la première est exclue.  [bag_split_msg] remet ensuite le
    message consommé en tête de la liste, ce que le disjoint attend. *)

Lemma cfg_tau_delivers : forall (l : list TypeOfActions) (M : gproc),
  (forall z, ~ lts ((g M) : proc) τ z) ->
  (exists z, (((g M) : proc) ▷ bag l) ⟶ z) ->
  exists c v l0 Mc, Permutation l ((c,v) :: l0)
                 /\ lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc.
Proof.
  intros l M Hno (z & Hz).
  apply fw_tau_shape in Hz as [(p' & Hp' & _) | (a & p' & m' & Heq & Hin & _)].
  - exfalso. eapply Hno. exact Hp'.
  - apply bag_split_msg in Heq as (l' & Hperm & _).
    destruct a as (c,v). exists c, v, l', p'. split; assumption.
Qed.

(** …d'où, pour une gauche **copycat**, le second disjoint de
    [CfgDisjunctionSource] **sans aucune hypothèse sémantique** : la
    seule chose demandée est que la configuration ait un [τ], ce qui est
    déjà la prémisse de la disjonction. *)

Corollary cfg_source_disjunct_at_copycats :
  forall (l : list TypeOfActions) (M : gproc),
  gCopycats M ->
  (exists z, (((g M) : proc) ▷ bag l) ⟶ z) ->
  exists c v l0 Mc K,
    Permutation l ((c,v) :: l0)
    /\ lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc
    /\ lts Mc (ActExt (ActOut (c,v))) K
    /\ K ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g M) : proc).
Proof.
  intros l M Hcop Hex.
  destruct (cfg_tau_delivers l M (gCopycats_no_tau M Hcop) Hex)
    as (c & v & l0 & Mc & Hperm & Hin).
  destruct (source_disjunct_of_copycats c v M Mc Hcop Hin) as (K & Hout & HK).
  exists c, v, l0, Mc, K. repeat split; assumption.
Qed.

(** ** Le disjoint source, RELATIVISÉ AU SAC

    [descent_of_residue_below_source] n'emploie [K ⊑ₘᵤₛₜᵢ g M] qu'à
    travers [must_i_par_compat_r], c'est-à-dire uniquement sous le sac.
    L'hypothèse utile est donc la forme relativisée
    [msgs l ‖ K ⊑ₘᵤₛₜᵢ msgs l ‖ g M], **strictement plus faible** — il n'y
    a pas d'annulation dans ce calcul ([VACCS_DropProbes.msg_not_below_nil]
    et sa réciproque) — d'où un disjoint plus facile à satisfaire, et une
    disjonction plus faible qui implique encore [CfgDisjunction].

    **Mais l'affaiblissement ne fait pas disparaître l'obstruction** :
    [VACCS_Bad.nil_not_below_dead_summand_bag] refuse aussi la forme
    relativisée, dès qu'une garde morte de [M] porte sur une voie **hors
    du sac**.  Ce que le sac achète est exactement les gardes mortes
    *sur ses propres voies* — leur résidu le laisse intact. *)

Lemma cgr_msg_bag_cons : forall (l l0 : list TypeOfActions) (c : ChannelData)
                                (v : ValueData) (X : proc),
  Permutation l ((c,v) :: l0) ->
  (msgs l0 ‖ (((c ! v • 𝟘) : proc) ‖ X)) ≡* (msgs l ‖ X).
Proof.
  intros l l0 c v X Hperm.
  eapply cgr_trans;
    [ | apply cgr_fullpar; [ apply msgs_perm; apply Permutation_sym; exact Hperm
                           | reflexivity ] ].
  simpl.
  eapply cgr_trans; [ apply cgr_par_assoc_rev | ].
  apply cgr_fullpar; [ apply cgr_par_com | reflexivity ].
Qed.

Theorem descent_of_residue_below_source_bag :
  forall (l l0 : list TypeOfActions) (c : ChannelData) (v : ValueData)
         (M : gproc) (Mc K q : proc),
  Permutation l ((c,v) :: l0) ->
  lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc ->
  lts Mc (ActExt (ActOut (c,v))) K ->
  ((msgs l ‖ K) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g M) : proc))) ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q) ->
  exists p', lts ((msgs l ‖ (g M)) : proc) τ p' /\ p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q.
Proof.
  intros l l0 c v M Mc K q Hperm Hin Hout HK Hq.
  destruct (cfg_deliver_step l l0 c v M Mc Hperm Hin) as (r & Hr & Hcr).
  exists r. split; [ exact Hr | ].
  intros t Hm. apply Hq. apply HK.
  assert (Hsh : Mc ≡* (((c ! v • 𝟘) : proc) ‖ K))
    by (eapply TransitionShapeForOutputSimplified; exact Hout).
  assert (H1 : (msgs l0 ‖ Mc) must_pass t)
    by (exact (proj2 (must_i_cgr _ _ Hcr) t Hm)).
  assert (Hc1 : (msgs l0 ‖ Mc) ≡* (msgs l0 ‖ (((c ! v • 𝟘) : proc) ‖ K)))
    by (apply cgr_fullpar; [ reflexivity | exact Hsh ]).
  assert (H2 : (msgs l0 ‖ (((c ! v • 𝟘) : proc) ‖ K)) must_pass t)
    by (exact (proj2 (must_i_cgr _ _ Hc1) t H1)).
  exact (proj2 (must_i_cgr _ _ (cgr_msg_bag_cons l l0 c v K Hperm)) t H2).
Qed.

Definition CfgDisjunctionSourceBag : Prop :=
  forall (l : list TypeOfActions) (M N : gproc), gStatic M -> gStatic N ->
    (exists z, (((g M) : proc) ▷ bag l) ⟶ z) ->
    ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
    (((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc))
    \/ (exists c v l0 Mc K,
          Permutation l ((c,v) :: l0)
          /\ lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc
          /\ lts Mc (ActExt (ActOut (c,v))) K
          /\ ((msgs l ‖ K) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g M) : proc)))).

Theorem cfg_disjunction_of_source_bag : CfgDisjunctionSourceBag -> CfgDisjunction.
Proof.
  intros HS l M N HM HN Htau Hsem.
  destruct (HS l M N HM HN Htau Hsem)
    as [Hempty | (c & v & l0 & Mc & K & Hp & Hin & Hout & HK)].
  - left. exact Hempty.
  - right. eapply descent_of_residue_below_source_bag; eassumption.
Qed.

(** …et elle est bien plus faible que la version nue. *)

Theorem cfg_source_bag_of_source : CfgDisjunctionSource -> CfgDisjunctionSourceBag.
Proof.
  intros HS l M N HM HN Htau Hsem.
  destruct (HS l M N HM HN Htau Hsem)
    as [Hempty | (c & v & l0 & Mc & K & Hp & Hin & Hout & HK)].
  - left. exact Hempty.
  - right. exists c, v, l0, Mc, K. repeat split; try assumption.
    apply must_i_par_compat_r. exact HK.
Qed.

(** ** La même disjonction, avec le second disjoint LOCAL

    [CfgDisjunction]'s second disjunct quantifies over the successors of
    the whole configuration.  [descent_of_cont_below] shows it follows
    from a condition on **one continuation** — a strict reduct of the
    left-hand sum — so the disjunction can be stated that way instead.

    [CfgDisjunctionLocal] is therefore *stronger* (it implies
    [CfgDisjunction]) but it is the shape a recursion can consume: both
    disjuncts are then about objects strictly smaller than the
    configuration, whereas "some τ-successor is below the target" is not.

    On the three machine-checked instances of `VACCS_DropProbes.v` it
    holds: [MCert] and the [rb]-guard of the regenerating probe give the
    second disjunct (their continuation returns the message it consumed —
    [descent_of_copycat_cont]), and [XProbe] gives the first by
    reflexivity.  It remains, like [CfgDisjunction], a **classical**
    statement: choosing the branch is what needs excluded middle. *)

Definition CfgDisjunctionLocal : Prop :=
  forall (l : list TypeOfActions) (M N : gproc), gStatic M -> gStatic N ->
    (exists z, (((g M) : proc) ▷ bag l) ⟶ z) ->
    ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
    (((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc))
    \/ (exists c v l0 Mc,
          Permutation l ((c,v) :: l0)
          /\ lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc
          /\ Mc ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (((c ! v • 𝟘) : proc) ‖ ((g N) : proc))).

Theorem cfg_disjunction_of_local : CfgDisjunctionLocal -> CfgDisjunction.
Proof.
  intros HL l M N HM HN Htau Hsem.
  destruct (HL l M N HM HN Htau Hsem) as [Hempty | (c & v & l0 & Mc & Hp & Hin & Hb)].
  - left. exact Hempty.
  - right. eapply descent_of_cont_below; eassumption.
Qed.

(** ** ATTENTION : [CfgDisjunctionLocal] est **FAUSSE**

    [VACCS_DropProbes.CfgDisjunctionLocal_is_false] la réfute.  Le défaut
    est la *localisation* : son second disjoint n'admet qu'une
    **délivrance**, alors que le [τ] qui sauve la configuration peut être
    une **branche [𝛕]** de la somme.  Le témoin est
    [(a ? 𝟘) + 𝛕•(g MCert)] : le disjoint (A) échoue, la seule délivrance
    mène à [𝟘] qui n'est pas sous le message, et c'est la branche [𝛕] —
    invisible aux deux disjoints — qui porte l'inéquation.

    [CfgDisjunction] elle-même **reste vraie sur ce témoin** : son second
    disjoint quantifie sur les τ-successeurs de la *configuration*, donc
    il attrape la branche [𝛕].  C'est donc bien la localisation, et elle
    seule, qui est trop forte.

    La forme corrigée ajoute le troisième disjoint. *)

Definition CfgDisjunctionLocal3 : Prop :=
  forall (l : list TypeOfActions) (M N : gproc), gStatic M -> gStatic N ->
    (exists z, (((g M) : proc) ▷ bag l) ⟶ z) ->
    ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
    (((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc))
    \/ (exists c v l0 Mc,
          Permutation l ((c,v) :: l0)
          /\ lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc
          /\ Mc ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (((c ! v • 𝟘) : proc) ‖ ((g N) : proc)))
    \/ (exists K, lts ((g M) : proc) τ K
          /\ (msgs l ‖ K) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))).

Theorem cfg_disjunction_of_local3 : CfgDisjunctionLocal3 -> CfgDisjunction.
Proof.
  intros HL l M N HM HN Htau Hsem.
  destruct (HL l M N HM HN Htau Hsem)
    as [Ha | [ (c & v & l0 & Mc & Hp & Hin & Hb) | (K & Hk & Hb) ]].
  - left. exact Ha.
  - right. eapply descent_of_cont_below; eassumption.
  - right. exists (msgs l ‖ K). split; [ apply lts_parR; exact Hk | exact Hb ].
Qed.

(** Le second disjoint de [CfgDisjunctionLocal] est satisfait dès que la
    garde **rend** le message consommé et que son résidu est sous la
    cible : le message revient alors *à côté* de la cible, ce qui est
    exactement la forme du disjoint.

    Contrairement au disjoint source-only — réfuté, cf. le commentaire
    au-dessus de [CfgDisjunctionSource] — celui-ci mentionne la cible, et
    c'est ce qui le sauve : la source peut être strictement plus forte
    que son propre successeur sans que cela gêne. *)

Lemma local_disjunct_of_returning :
  forall (c : ChannelData) (v : ValueData) (N : gproc) (Mc K : proc),
  lts Mc (ActExt (ActOut (c,v))) K ->
  K ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc) ->
  Mc ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((((c ! v • 𝟘)) : proc) ‖ ((g N) : proc)).
Proof.
  intros c v N Mc K Hout HK.
  assert (Hsh : Mc ≡* (((c ! v • 𝟘) : proc) ‖ K))
    by (eapply TransitionShapeForOutputSimplified; exact Hout).
  intros t Hm.
  apply (must_i_par_compat_r ((c ! v • 𝟘) : proc) _ _ HK).
  exact (proj2 (must_i_cgr _ _ Hsh) t Hm).
Qed.

(** ** Les deux moitiés de [CfgDisjunctionLocal] que l'on sait produire

    Elles se répartissent selon le **critère syntaxique** [ochans] — le
    même qui commande [ax_below_NF_no_return] :

    - si **aucune** continuation ne peut émettre sur la voie de sa propre
      garde, le sac s'annule ([msgs_cancel_no_regen], via
      [no_regen_of_own_channel]) et le **premier** disjoint tombe.  Rien
      d'autre n'est demandé que la τ-stabilité de la somme nue ;
    - si une garde **rend** effectivement son message et que le résidu
      est sous la cible, le **second** disjoint tombe
      ([local_disjunct_of_returning]).

    Ce qui reste ouvert est exactement la zone entre les deux : une somme
    dont une continuation *peut* émettre sur sa propre voie ([ochans]
    sur-approxime), sans qu'on sache placer le résidu sous la cible.  Et,
    à part, le cas où [M] porte un [𝛕]-sommant — la configuration est
    alors instable sans qu'aucune délivrance ne soit en jeu, et
    [cfg_local_of_no_return] ne s'applique pas. *)

Lemma cfg_local_of_no_return :
  forall (l : list TypeOfActions) (M N : gproc), gStatic M -> gStatic N ->
  (forall z, ~ lts ((g M) : proc) τ z) ->
  (forall c v P', lts ((g M) : proc) (ActExt (ActIn (c,v))) P' -> ~ In c (ochans P')) ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
  (((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc))
  \/ (exists c v l0 Mc,
        Permutation l ((c,v) :: l0)
        /\ lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc
        /\ Mc ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (((c ! v • 𝟘) : proc) ‖ ((g N) : proc))).
Proof.
  intros l M N HM HN HstM Hcrit Hsem. left.
  eapply msgs_cancel_no_regen; try eassumption.
  eapply no_regen_of_own_channel; try eassumption.
  apply static_g. exact HM.
Qed.

Lemma cfg_local_of_returning :
  forall (l l0 : list TypeOfActions) (c : ChannelData) (v : ValueData)
         (M N : gproc) (Mc K : proc),
  Permutation l ((c,v) :: l0) ->
  lts ((g M) : proc) (ActExt (ActIn (c,v))) Mc ->
  lts Mc (ActExt (ActOut (c,v))) K ->
  K ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc) ->
  (((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc))
  \/ (exists c0 v0 l1 Mc0,
        Permutation l ((c0,v0) :: l1)
        /\ lts ((g M) : proc) (ActExt (ActIn (c0,v0))) Mc0
        /\ Mc0 ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (((c0 ! v0 • 𝟘) : proc) ‖ ((g N) : proc))).
Proof.
  intros l l0 c v M N Mc K Hperm Hin Hout HK.
  right. exists c, v, l0, Mc. split; [ exact Hperm | split; [ exact Hin | ] ].
  eapply local_disjunct_of_returning; eassumption.
Qed.

Theorem cfg_unstable_of_disjunction : CfgDisjunction ->
  forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
  (exists z, (((g M) : proc) ▷ bag l) ⟶ z) ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
  (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
     BagSem l ((g M) : proc) L -> subbag l' l ->
     forall c v Q' l'', subbag l'' l' -> lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ ((g M) : proc))) (msgs l'' ‖ Q')) ->
  (forall p', lts (msgs l ‖ ((g M) : proc)) τ p' ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc)) ->
     ax_pre p' (msgs l ‖ ((g N) : proc))) ->
  ax_pre (msgs l ‖ ((g M) : proc)) (msgs l ‖ ((g N) : proc)).
Proof.
  intros HD l M N HM HN Hnf Hex Hsem Hrec Hdesc.
  destruct (HD l M N HM HN Hex Hsem) as [Hempty | (p' & Hstep & Hle)].
  - eapply ax_below_cfg_empty_sem; eassumption.
  - eapply ax_trans; [ apply ax_tau_step; exact Hstep | ].
    apply Hdesc; assumption.
Qed.

(** La même conclusion à partir de la forme la plus forte des trois, dont
    les deux disjoints portent sur des objets strictement plus petits que
    la configuration **et** ne parlent que d'un seul côté à la fois. *)

Corollary cfg_unstable_of_source : CfgDisjunctionSource ->
  forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> Forall tau_cont_nf (summands N) ->
  (exists z, (((g M) : proc) ▷ bag l) ⟶ z) ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
  (forall (L : gproc) (l' : list TypeOfActions), gStatic L -> gStable L ->
     BagSem l ((g M) : proc) L -> subbag l' l ->
     forall c v Q' l'', subbag l'' l' -> lts ((g L) : proc) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l'' ‖ ((c ! v • 𝟘) ‖ ((g M) : proc))) (msgs l'' ‖ Q')) ->
  (forall p', lts (msgs l ‖ ((g M) : proc)) τ p' ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc)) ->
     ax_pre p' (msgs l ‖ ((g N) : proc))) ->
  ax_pre (msgs l ‖ ((g M) : proc)) (msgs l ‖ ((g N) : proc)).
Proof.
  intro HS. apply cfg_unstable_of_disjunction.
  apply cfg_disjunction_of_source. exact HS.
Qed.

(** * L'APPARIEMENT DES SACS — une INCLUSION, pas une égalité

    [VACCS_NormalForm.bags_agree] égalise les deux sacs, mais au prix de
    deux hypothèses de stabilité, toutes deux nécessaires.  Ce qui vaut
    sans elles est l'inclusion **dans un seul sens**, et c'est la bonne :

        bag l2 ⊆ bag l1

    « la droite ne peut pas porter plus de messages que la gauche ».  Le
    sens inverse est faux — [VACCS_Bad.unstable_delivery_below_nil] met un
    sac à un message sous un sac vide, la garde avalant le message au lieu
    de l'émettre.

    Preuve : lire [bhv_pre_cond2] à la trace qui **vide le sac de droite**.
    La droite atteint [g N ▷ ∅], stable ; la gauche doit suivre sur la même
    trace, et l'équation de bilan de [fw_conservation] donne alors
    [bag l1 = x.2 ⊎ bag l2 ⊎ bag (ins r)] dès que la gauche n'émet rien
    d'elle-même ([ochans (g M) = []], via [trace_out_in_ochans]).

    Et l'inclusion se lit en liste : [l1 ≡ₚ l2 ++ d].  La comparaison
    devient donc

        msgs l2 ‖ (msgs d ‖ g M)   contre   msgs l2 ‖ g N

    — **même sac des deux côtés**, ce qui est exactement la forme que
    [ax_below_stable_sum_cfg] et [ax_below_split_from_certificate]
    consomment, le surplus [d] passant dans le processus de gauche. *)

Lemma bag_sub_cancel : forall (a : TypeOfActions) (X Y : MO (ExtAct TypeOfActions)),
  {[+ ActOut a +]} ⊎ X ⊆ {[+ ActOut a +]} ⊎ Y -> X ⊆ Y.
Proof.
  intros a X Y H. intro x. specialize (H x).
  assert (E1 : multiplicity x ({[+ ActOut a +]} ⊎ X)
               = (multiplicity x ({[+ ActOut a +]}) + multiplicity x X)%nat)
    by (apply gmultiset.multiplicity_disj_union).
  assert (E2 : multiplicity x ({[+ ActOut a +]} ⊎ Y)
               = (multiplicity x ({[+ ActOut a +]}) + multiplicity x Y)%nat)
    by (apply gmultiset.multiplicity_disj_union).
  rewrite E1, E2 in H. lia.
Qed.

Lemma bag_sub_split : forall (l2 l1 : list TypeOfActions),
  bag l2 ⊆ bag l1 -> exists d, Permutation l1 (l2 ++ d).
Proof.
  induction l2 as [|a l2 IH]; intros l1 Hsub.
  - exists l1. reflexivity.
  - assert (Hmem : ActOut a ∈ bag l1).
    { eapply gmultiset_elem_of_subseteq; [ | exact Hsub ].
      simpl. apply gmultiset_elem_of_disj_union. left.
      apply gmultiset_elem_of_singleton. reflexivity. }
    apply bag_elem in Hmem. apply in_split in Hmem as (u1 & u2 & E). subst l1.
    assert (Hp : Permutation (u1 ++ a :: u2) (a :: (u1 ++ u2)))
      by (symmetry; apply Permutation_middle).
    assert (Hb : bag (u1 ++ a :: u2) = bag (a :: (u1 ++ u2)))
      by (apply bag_perm; exact Hp).
    rewrite Hb in Hsub. simpl in Hsub.
    apply bag_sub_cancel in Hsub.
    destruct (IH (u1 ++ u2) Hsub) as (d & Hd).
    exists d. etransitivity; [ exact Hp | ]. simpl. apply perm_skip. exact Hd.
Qed.

(** Énoncé au type **générique** à dessein : à [MO (ExtAct TypeOfActions)]
    les deux élaborations de [⊎] que le développement transporte sont
    convertibles sans être syntaxiquement égales, et [rewrite] rate.  Même
    précaution que pour [VACCS_NormalForm.disj_union_cancel_empty]. *)

Lemma disj_union_sub_middle : forall (A : Type) (EqA : EqDecision A) (CA : Countable A)
  (X Y Z W : gmultiset A), X ⊎ ∅ ⊎ ∅ = Y ⊎ Z ⊎ W -> Z ⊆ X.
Proof.
  intros A EqA CA X Y Z W H a.
  apply (f_equal (multiplicity a)) in H.
  rewrite !multiplicity_disj_union in H.
  rewrite !multiplicity_empty in H. lia.
Qed.

(** The state reached by draining the right bag need not be **stable** —
    [bhv_pre_cond2] only needs *some* stable state, and its emissions are
    never used here (the inclusion comes from the balance equation on the
    LEFT run).  So follow the drain by [τ]s, which leave the trace
    unchanged; on the [Static] fragment such a state always exists. *)

Lemma fw_stable_reach : forall (p : proc) (m : MO (ExtAct TypeOfActions)),
  Static p -> exists y, (p ▷ m) ⟹[[]] y /\ y ↛.
Proof.
  intros p m HS.
  apply terminate_then_wt_refuses.
  eapply fw_terminate_static; [ exact HS | apply Nat.le_refl ].
Qed.

Theorem bag_incl_of_below : forall (l1 l2 : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  ochans ((g M) : proc) = [] ->
  ((msgs l1 ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))) ->
  bag l2 ⊆ bag l1.
Proof.
  intros l1 l2 M N HM HN Hoc Hpre.
  destruct (msgs_accept l1 l2 (g M) (g N) Hpre) as (Hc1 & Hc2).
  assert (Hdrain : (((g N) : proc) ▷ bag l2)
                     ⟹[map ActOut l2] (((g N) : proc) ▷ (∅ : MO (ExtAct TypeOfActions)))).
  { replace (bag l2) with (bag l2 ⊎ (∅ : MO (ExtAct TypeOfActions))) at 1
      by (apply gmultiset.gmultiset_disj_union_right_id).
    apply bag_wt_drain. }
  destruct (fw_stable_reach ((g N) : proc) (∅ : MO (ExtAct TypeOfActions))
              (static_g N HN)) as (y & Hwy & Hsty).
  assert (Hbig : (((g N) : proc) ▷ bag l2) ⟹[map ActOut l2] y).
  { replace (map ActOut l2) with (map ActOut l2 ++ (@nil (ExtAct TypeOfActions)))
      by (rewrite app_nil_r; reflexivity).
    eapply wt_concat; [ exact Hdrain | exact Hwy ]. }
  destruct (Hc2 (map ActOut l2) y
              (fw_converge_static (map ActOut l2) (g M) (bag l1) (static_g M HM))
              Hbig Hsty)
    as (x & Hwx & Hstx & Hincl).
  destruct (fw_conservation _ _ _ Hwx) as (r & Hr & Hbal). simpl in Hbal.
  assert (Houts : outs r = []).
  { destruct (outs r) as [|cv u] eqn:E; [ reflexivity | exfalso ].
    destruct cv as (c,v).
    assert (Hin : In c (ochans ((g M) : proc))).
    { eapply trace_out_in_ochans; [ apply static_g; exact HM | exact Hr | ].
      rewrite E. left. reflexivity. }
    rewrite Hoc in Hin. exact Hin. }
  rewrite ins_map_out in Hbal. rewrite outs_map_out in Hbal.
  rewrite Houts in Hbal. simpl in Hbal.
  eapply disj_union_sub_middle. exact Hbal.
Qed.

Corollary bag_split_of_below : forall (l1 l2 : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  ochans ((g M) : proc) = [] ->
  ((msgs l1 ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))) ->
  exists d, Permutation l1 (l2 ++ d).
Proof.
  intros l1 l2 M N HM HN Hoc Hpre.
  apply bag_sub_split.
  exact (bag_incl_of_below l1 l2 M N HM HN Hoc Hpre).
Qed.

(* ------------------------------------------------------------------ *)
(*  Obstacle (5), the grey-zone-free half: a configuration step at a   *)
(*  COMMON bag, when the left-hand sum never emits.                    *)
(*                                                                     *)
(*  [msgs_cancel_no_output] strips the bag outright under              *)
(*  [ochans (g M) = []], so [CfgDisjunctionLocal] is not needed at all *)
(*  here: the first disjunct holds by construction, and                *)
(*  [completeness_gsum_step_gen] finishes on the bare sums --- with no      *)
(*  [tau_cont_nf] invariant, and with a tau-summand on the left        *)
(*  allowed.                                                           *)
(*                                                                     *)
(*  This is the configuration-level counterpart of                     *)
(*  [ax_below_NF_no_output]; the difference is that the recursion is   *)
(*  handed over to [completeness_gsum_step_gen] (measure [size] of the     *)
(*  right-hand sum) instead of being taken as a per-summand premise.   *)
(* ------------------------------------------------------------------ *)

Theorem completeness_cfg_no_output : forall (l : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> ochans ((g M) : proc) = [] ->
  ((msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
  (forall p' q', Static p' -> Static q' ->
     (size q' < size ((g N) : proc))%nat ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
  ax_pre (msgs l ‖ ((g M) : proc)) (msgs l ‖ ((g N) : proc)).
Proof.
  intros l M N HM HN Hoc Hsem IH.
  apply ax_par; [ apply ax_refl | ].
  apply completeness_gsum_step_gen; try assumption.
  - apply static_g. exact HM.
  - eapply msgs_cancel_no_output; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(*  Obstacle (4), cashed in: the SURPLUS is cancelled, not just bounded *)
(*                                                                     *)
(*  [bag_split_of_below] reads the inclusion of the two bags as a list  *)
(*  split, [l1 ≡ₚ l2 ++ d].  What follows turns that split into a       *)
(*  genuine cancellation: the common part [l2] is removed from BOTH     *)
(*  sides, the surplus [d] staying on the left.                         *)
(*                                                                     *)
(*  [msgs_cancel_no_output] is the case [d = []].  The extra work is    *)
(*  entirely in the drain phase: there the left carries [bag l2 ⊎ bag d] *)
(*  while the trace only emits [l2]'s worth, so the run does not end at *)
(*  [g M ▷ ∅] and [drain_forced_no_output] does not apply.  What does   *)
(*  is [VACCS_Forwarder.fw_drain_project]: the same run, with the       *)
(*  buffer emissions dropped, is a τ-run from the surplus alone —       *)
(*  reaching the very same state.                                       *)
(* ------------------------------------------------------------------ *)

Lemma MuteRun_of_ochans : forall (p : proc), Static p -> ochans p = [] -> MuteRun p.
Proof.
  intros p Hst Hoc r q Hw.
  destruct (outs r) as [|cv l0] eqn:E; [ reflexivity | exfalso ].
  destruct cv as (c,v).
  assert (Hin : In c (ochans p)).
  { eapply trace_out_in_ochans; [ exact Hst | exact Hw | rewrite E; left; reflexivity ]. }
  rewrite Hoc in Hin. exact Hin.
Qed.

Theorem msgs_cancel_surplus : forall (l d : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  ochans ((g M) : proc) = [] ->
  ((msgs (l ++ d) ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g N) : proc))) ->
  ((msgs d ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs nil ‖ ((g N) : proc))).
Proof.
  intros l d M N HM HN Hoc Hpre.
  destruct (msgs_accept (l ++ d) l (g M) (g N) Hpre) as (Hc1 & Hc2).
  apply msgs_sound. split.
  - intros s _. apply fw_converge_static. apply static_g. exact HN.
  - intros s y _ Hwy Hsty.
    assert (Hdrain : ((g N) ▷ bag l)
                       ⟹[map ActOut l] ((g N) ▷ (∅ : MO (ExtAct TypeOfActions)))).
    { replace (bag l) with (bag l ⊎ (∅ : MO (ExtAct TypeOfActions))) at 1
        by (apply gmultiset.gmultiset_disj_union_right_id).
      apply bag_wt_drain. }
    simpl in Hwy.
    assert (Hbig : ((g N) ▷ bag l) ⟹[map ActOut l ++ s] y)
      by (eapply wt_concat; [ exact Hdrain | exact Hwy ]).
    destruct (Hc2 (map ActOut l ++ s) y
                (fw_converge_static (map ActOut l ++ s) (g M) (bag (l ++ d))
                   (static_g M HM))
                Hbig Hsty)
      as (x & Hwx & Hstx & Hincl).
    destruct (wt_split _ _ _ _ Hwx) as (z & Hz1 & Hz2).
    assert (Hproj : (((g M) : proc) ▷ bag d) ⟹[[]] z).
    { eapply (fw_drain_project (map ActOut l) (((g M) : proc) ▷ bag (l ++ d)) z Hz1).
      - simpl. apply MuteRun_of_ochans; [ apply static_g; exact HM | exact Hoc ].
      - apply ins_map_out.
      - simpl. rewrite outs_map_out. rewrite bag_app. reflexivity. }
    exists x. split; [ | split; [ exact Hstx | exact Hincl ] ].
    simpl.
    replace s with (@nil (ExtAct TypeOfActions) ++ s) by reflexivity.
    eapply wt_concat; [ exact Hproj | exact Hz2 ].
Qed.

(** The two halves together: a comparison at *unequal* bags is a
    comparison at the **empty** bag, with the surplus carried on the
    left.  That is the shape the configuration machinery consumes, and
    it needs no stability hypothesis on either side beyond [g N] being
    τ-free.

    Note the surplus is genuinely non-empty in general —
    [VACCS_Bad.unstable_delivery_below_nil] puts a one-message bag below
    an empty one, the guard swallowing the message rather than emitting
    it — so the reverse inclusion is false and this really is the best
    one can ask for. *)

Corollary msgs_cancel_of_below : forall (l1 l2 : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  ochans ((g M) : proc) = [] ->
  ((msgs l1 ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))) ->
  exists d, Permutation l1 (l2 ++ d)
         /\ ((msgs d ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs nil ‖ ((g N) : proc))).
Proof.
  intros l1 l2 M N HM HN Hoc Hpre.
  destruct (bag_split_of_below l1 l2 M N HM HN Hoc Hpre) as (d & Hperm).
  exists d. split; [ exact Hperm | ].
  assert (Hcgr : (msgs (l2 ++ d) ‖ ((g M) : proc)) ≡* (msgs l1 ‖ ((g M) : proc))).
  { apply cgr_fullpar; [ | apply cgr_refl ].
    apply msgs_perm. apply Permutation_sym. exact Hperm. }
  assert (Hshift : (msgs (l2 ++ d) ‖ ((g M) : proc))
                     ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))).
  { intros t Ht. apply Hpre. apply (proj2 (must_i_cgr _ _ Hcgr)). exact Ht. }
  exact (msgs_cancel_surplus l2 d M N HM HN Hoc Hshift).
Qed.

(* ------------------------------------------------------------------ *)
(*  [ochans (g M) = []] REACHES THE DERIVATIONS                        *)
(*                                                                     *)
(*  [VACCS_Bad.no_output_below_nil] says a process that can never emit  *)
(*  is below [𝟘]; that is a *semantic* fact, and per this project's     *)
(*  own rule it is worth nothing until a derivation consumes it.        *)
(*  Here it does, for a **stable guarded sum**, and by the cheapest     *)
(*  route: peel the summands one at a time.                             *)
(*                                                                     *)
(*  Each summand of a stable sum is [①], [𝟘] or [c ? P], and each has   *)
(*  its own rule — [ax_success_l], [ax_cgr], [ax_drop_ochans].  Crucially *)
(*  all three carry a **residue**, which is exactly what lets them fire *)
(*  inside a sum: [ax_choice_stable] is unsound in VACCS               *)
(*  ([VACCS_ChoiceProbes.v]), so a rule that does not state its context *)
(*  could not be used here at all.                                      *)
(*                                                                     *)
(*  Note the induction is on the *summand list*, with no search and no  *)
(*  measure: [rebuild]'s trailing [𝟘] would make [length (summands M)]  *)
(*  stationary (the padding trap already recorded for [nacts]), but     *)
(*  peeling the list itself never meets it.                             *)
(* ------------------------------------------------------------------ *)

Lemma summands_nonempty : forall (M : gproc), summands M <> [].
Proof.
  induction M as [ | | c P | P | M1 IH1 M2 IH2 ]; simpl; try discriminate.
  intro He. apply app_eq_nil in He as (He1 & _). exact (IH1 He1).
Qed.

Lemma cgr_nil_choice_l : forall (R : gproc), g (((𝟘 : gproc) + R)) ≡* g R.
Proof.
  intro R. transitivity (g (R + (𝟘 : gproc))).
  - apply cgr_choice_com.
  - apply cgr_choice_nil.
Qed.

(** The peeling steps fire *in place*, on the head of the summand list —
    the position-generic [*_anywhere] form the rest of the development
    uses (via [pull_one]) is not needed here, because the induction walks
    the list itself instead of searching it. *)

(** Stability and the emission footprint both distribute over [summands]. *)

Lemma gStable_summands : forall M, gStable M -> Forall gStable (summands M).
Proof.
  induction M as [ | | c P | P | M1 IH1 M2 IH2 ]; intro Hs; simpl in *;
    try (repeat constructor; exact I).
  - contradiction.
  - destruct Hs as (Hs1 & Hs2). apply Forall_app. split; auto.
Qed.

Lemma gochans_summands : forall M, gochans M = [] ->
  Forall (fun a => gochans a = []) (summands M).
Proof.
  induction M as [ | | c P | P | M1 IH1 M2 IH2 ]; intro Ho; simpl in *;
    try (repeat constructor; exact Ho).
  - apply Forall_app. apply app_eq_nil in Ho as (Ho1 & Ho2). split; auto.
Qed.

(** The peeling itself: a **prefix** of mute stable summands is discarded,
    whatever the rest [r] is.  Below-[𝟘] is the case [r = []]; the general
    form is a *derivable restriction* of a stable sum to its non-mute
    summands — which is what [grestrict] and [ax_restrict] attempt with a
    [BadK] certificate, obtained here from a syntactic, decidable
    criterion instead. *)

Lemma ax_rebuild_drop : forall (l r : list gproc),
  Forall gStatic l -> Forall (fun a => summands a = [a]) l ->
  Forall gStable l -> Forall (fun a => gochans a = []) l ->
  ax_pre ((g (rebuild (l ++ r))) : proc) ((g (rebuild r)) : proc).
Proof.
  induction l as [|a l IH]; intros r HSt HLf HSb HOc; simpl.
  - apply ax_refl.
  - inversion HSt as [|? ? HSt1 HSt2]; subst.
    inversion HLf as [|? ? HLf1 HLf2]; subst.
    inversion HSb as [|? ? HSb1 HSb2]; subst.
    inversion HOc as [|? ? HOc1 HOc2]; subst.
    assert (IHl : ax_pre ((g (rebuild (l ++ r))) : proc) ((g (rebuild r)) : proc))
      by (apply IH; assumption).
    destruct a as [ | | c P | P | A B ].
    + (* ① : the only use of [ax_success_l]'s residue here *)
      eapply ax_trans; [ apply ax_success_l | ].
      eapply ax_trans; [ apply ax_cgr; apply cgr_nil_choice_l | ]. exact IHl.
    + eapply ax_trans; [ apply ax_cgr; apply cgr_nil_choice_l | ]. exact IHl.
    + eapply ax_trans; [ | exact IHl ].
      apply ax_drop_ochans.
      * inversion HSt1; assumption.
      * simpl in HOc1. intros d Hd. rewrite HOc1 in Hd. contradiction.
    + (* a 𝛕-summand is excluded by stability *)
      simpl in HSb1. contradiction.
    + (* a leaf is never a sum: both halves are non-empty *)
      exfalso. simpl in HLf1.
      assert (Hlen : length (summands A ++ summands B) = 1%nat)
        by (rewrite HLf1; reflexivity).
      rewrite length_app in Hlen.
      assert (HA := summands_nonempty A). assert (HB := summands_nonempty B).
      destruct (summands A); [ exact (HA eq_refl) | ].
      destruct (summands B); [ exact (HB eq_refl) | ].
      simpl in Hlen. lia.
Qed.

(** …and at an arbitrary position, the summands to discard being singled
    out by a permutation.  The two [Forall]s about [gStatic] and about
    leaves are *not* hypotheses: they are transported from [summands M]
    across the permutation. *)

Theorem ax_gsum_drop_mute : forall (M : gproc) (l r : list gproc),
  gStatic M -> Permutation (summands M) (l ++ r) ->
  Forall gStable l -> Forall (fun a => gochans a = []) l ->
  ax_pre ((g M) : proc) ((g (rebuild r)) : proc).
Proof.
  intros M l r HM Hperm HSb HOc.
  assert (HSt : Forall gStatic (l ++ r))
    by (apply perm_summands_gStatic with M; assumption).
  assert (HLf : Forall (fun a => summands a = [a]) (l ++ r)).
  { rewrite <- Hperm. apply summands_leaves. }
  apply Forall_app in HSt as (HSt1 & _).
  apply Forall_app in HLf as (HLf1 & _).
  eapply ax_trans; [ apply ax_cgr | ].
  - transitivity (g (rebuild (summands M))); [ apply summands_cgr | ].
    apply (rebuild_perm (summands M) (l ++ r)). exact Hperm.
  - apply ax_rebuild_drop; assumption.
Qed.

(** The [𝟘] case: discard *everything*. *)

Corollary ax_gsum_below_nil : forall (M : gproc),
  gStatic M -> gStable M -> ochans ((g M) : proc) = [] ->
  ax_pre ((g M) : proc) ((g (𝟘 : gproc)) : proc).
Proof.
  intros M HM HSb HOc.
  apply (ax_gsum_drop_mute M (summands M) []).
  - exact HM.
  - rewrite app_nil_r. reflexivity.
  - apply gStable_summands; exact HSb.
  - apply gochans_summands; exact HOc.
Qed.

(* ------------------------------------------------------------------ *)
(*  …AND AT THE LEVEL OF PROCESSES, ON THE ν-FREE FRAGMENT             *)
(*                                                                     *)
(*  Neither the stability nor the guarded-sum shape of                 *)
(*  [ax_gsum_below_nil] is essential — a [𝛕]-summand is peeled by      *)
(*  [ax_tau_step], and the other [proc] shapes have their own rules.   *)
(*  What genuinely blocks is the **restriction block**: [ochans (ν P)] *)
(*  can be empty while [ochans P] is not (the restricted channel never *)
(*  escapes), so [ax_res] has nothing smaller to recurse on.           *)
(*                                                                     *)
(*  [NoResD] excludes [ν] *everywhere*, not merely on the spine —      *)
(*  [VACCS_NormalForm.NoRes] is the spine-only version, and it is not  *)
(*  enough here because the recursion descends into a [𝛕]-summand's    *)
(*  continuation.                                                       *)
(* ------------------------------------------------------------------ *)

Fixpoint NoResD (p : proc) : Prop :=
match p with
| P ‖ Q => NoResD P /\ NoResD Q
| pr_var _ => True
| rec _ • P => NoResD P
| If _ Then P Else Q => NoResD P /\ NoResD Q
| _ ! _ • 𝟘 => True
| ν _ => False
| g M => gNoResD M
end
with gNoResD (M : gproc) : Prop :=
match M with
| gpr_success => True
| gpr_nil => True
| gpr_input _ P => NoResD P
| gpr_tau P => NoResD P
| gpr_choice M1 M2 => gNoResD M1 /\ gNoResD M2
end.

(** Only the [τ] case of the recursion needs [NoResD] transported along a
    transition, and there the target is a *subterm* — so no substitution
    lemma is required (an input's target would need one). *)

Lemma noresd_tau_target : forall (M : gproc) X,
  gNoResD M -> lts ((g M) : proc) τ X -> NoResD X.
Proof.
  induction M as [ | | c P | P | M1 IH1 M2 IH2 ]; intros X Hnr Hl;
    try (inversion Hl; fail).
  - inversion Hl; subst. exact Hnr.
  - simpl in Hnr. destruct Hnr as (Hn1 & Hn2). inversion Hl; subst.
    + eapply IH1; eassumption.
    + eapply IH2; eassumption.
Qed.

Theorem ax_below_nil_noresd : forall (p : proc),
  Static p -> NoResD p -> ochans p = [] ->
  ax_pre p ((g (𝟘 : gproc)) : proc).
Proof.
  intro p. induction p as [p IHp] using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hst Hnr Hoc. destruct p as [p1 p2|x|x p0|E p1 p2|c v|p0|M].
  - (* parallel: [ax_par], then [𝟘 ‖ 𝟘 ≡* 𝟘] *)
    inversion Hst; subst. simpl in Hnr, Hoc.
    destruct Hnr as (Hn1 & Hn2). apply app_eq_nil in Hoc as (Ho1 & Ho2).
    eapply ax_trans; [ apply ax_par | ].
    + apply (IHp p1 ltac:(simpl; lia)); assumption.
    + apply (IHp p2 ltac:(simpl; lia)); assumption.
    + apply ax_cgr. apply cgr_par_nil.
  - inversion Hst.
  - inversion Hst.
  - (* conditional: [Eval_Eq 0] never fails, so [≡*] one branch *)
    inversion Hst; subst. simpl in Hnr, Hoc.
    destruct Hnr as (Hn1 & Hn2). apply app_eq_nil in Hoc as (Ho1 & Ho2).
    destruct (Eval_Eq 0 E) as [[|]|] eqn:HE;
      [ | | exfalso; eapply Eval_Eq_0_not_none; exact HE ].
    + eapply ax_trans; [ apply ax_cgr; apply cgr_if_true; exact HE | ].
      apply (IHp p1 ltac:(simpl; lia)); assumption.
    + eapply ax_trans; [ apply ax_cgr; apply cgr_if_false; exact HE | ].
      apply (IHp p2 ltac:(simpl; lia)); assumption.
  - (* a message is excluded by the criterion itself *)
    simpl in Hoc. discriminate Hoc.
  - (* a restriction is excluded by [NoResD] — see the header *)
    simpl in Hnr. contradiction.
  - (* a guarded sum: stable, or peel its own [τ] *)
    destruct (lts_dec ((g M) : proc) τ) as [Hno|(X & HX)].
    + apply ax_gsum_below_nil; [ inversion Hst; assumption | | exact Hoc ].
      apply gStable_iff. apply no_lts_stable. exact Hno.
    + eapply ax_trans; [ apply ax_tau_step; exact HX | ].
      apply (IHp X).
      * unfold ltof. eapply Static_lts_decrease; [ exact Hst | exact HX ].
      * eapply Static_preserved_by_lts; [ exact Hst | exact HX ].
      * eapply noresd_tau_target; [ exact Hnr | exact HX ].
      * assert (Hsub := lts_ochans_target _ _ _ Hst HX).
        destruct (ochans X) as [|d l0] eqn:E; [ reflexivity | exfalso ].
        assert (Hin : In d (ochans ((g M) : proc)))
          by (apply Hsub; left; reflexivity).
        rewrite Hoc in Hin. exact Hin.
Qed.

(** …and the criterion need only hold *somewhere along an internal run*.

    [ochans p = []] is a strong request for a **configuration**: a pending
    message puts its own channel in the footprint.  But a configuration
    that consumes its bag reaches a state which is mute again, and
    [ax_tau_run] takes it there — so the syntactic criterion applies to
    the reduct instead of to the process.

    This is the shape [VACCS_Bad.unstable_delivery_below_nil] exhibits: a
    one-message bag below the empty one, the guard swallowing the message.
    There it is a hand-made [ax_tau_step]; here it is an instance. *)

Lemma NoResD_subst : forall p k X, NoResD p -> NoResD (subst_in_proc k X p)
with gNoResD_subst : forall M k X, gNoResD M -> gNoResD (subst_in_gproc k X M).
Proof.
  - destruct p as [P Q | i | x P | C P Q | c v | P | M ]; intros k X H; simpl in *.
    + destruct H as (H1 & H2). split; [ apply NoResD_subst | apply NoResD_subst ]; assumption.
    + exact I.
    + apply NoResD_subst. exact H.
    + destruct H as (H1 & H2). split; [ apply NoResD_subst | apply NoResD_subst ]; assumption.
    + exact I.
    + contradiction.
    + apply gNoResD_subst. exact H.
  - destruct M as [ | | c P | P | M1 M2 ]; intros k X H; simpl in *.
    + exact I.
    + exact I.
    + apply NoResD_subst. exact H.
    + apply NoResD_subst. exact H.
    + destruct H as (H1 & H2). split; [ apply gNoResD_subst | apply gNoResD_subst ]; assumption.
Qed.

Lemma noresd_lts_target : forall (p : proc) a q,
  Static p -> NoResD p -> lts p a q -> NoResD q.
Proof.
  intros p a q Hst Hnr Hl. revert Hst Hnr.
  induction Hl; intros Hst Hnr; simpl in *;
    try exact I; try contradiction; try assumption.
  - apply NoResD_subst. exact Hnr.
  - inversion Hst.
  - inversion Hst; subst. apply IHHl; tauto.
  - inversion Hst; subst. apply IHHl; tauto.
  - inversion Hst; subst. split; [ apply IHHl1 | apply IHHl2 ]; tauto.
  - inversion Hst; subst. split; [ apply IHHl2 | apply IHHl1 ]; tauto.
  - inversion Hst; subst. split; [ apply IHHl | ]; tauto.
  - inversion Hst; subst. split; [ | apply IHHl ]; tauto.
  - inversion Hst; subst.
    match goal with H : gStatic (p1 + p2) |- _ => inversion H; subst end.
    apply IHHl; [ constructor; assumption | tauto ].
  - inversion Hst; subst.
    match goal with H : gStatic (p1 + p2) |- _ => inversion H; subst end.
    apply IHHl; [ constructor; assumption | tauto ].
Qed.

Lemma noresd_wt_target : forall s (p q : proc),
  Static p -> NoResD p -> p ⟹[s] q -> NoResD q.
Proof.
  intros s p q Hst Hnr Hw. revert Hst Hnr.
  induction Hw as [x|s0 x y z Hl Hwt IH|mu s0 x y z Hl Hwt IH]; intros Hst Hnr.
  - exact Hnr.
  - apply IH.
    + eapply Static_preserved_by_lts; [ exact Hst | exact Hl ].
    + eapply noresd_lts_target; [ exact Hst | exact Hnr | exact Hl ].
  - apply IH.
    + eapply Static_preserved_by_lts; [ exact Hst | exact Hl ].
    + eapply noresd_lts_target; [ exact Hst | exact Hnr | exact Hl ].
Qed.

Theorem ax_below_nil_of_mute_reduct : forall (p x : proc),
  Static p -> NoResD p -> p ⟹[[]] x -> ochans x = [] ->
  ax_pre p ((g (𝟘 : gproc)) : proc).
Proof.
  intros p x Hst Hnr Hw Hoc.
  eapply ax_trans; [ apply ax_tau_run; exact Hw | ].
  apply ax_below_nil_noresd.
  - eapply Static_preserved_by_wt; [ exact Hst | exact Hw ].
  - eapply noresd_wt_target; [ exact Hst | exact Hnr | exact Hw ].
  - exact Hoc.
Qed.

(** So the criterion [ochans p = []] now has *four* consumers: the bag
    cancellation ([drain_forced_no_output], [msgs_cancel_no_output]),
    [VACCS_Bad.no_output_below_nil] semantically,
    [VACCS_Absorb.ochans_sub_Bad] as a [Bad] certificate — and, from
    here on, a **derivation** at every ν-free [Static] process. *)


(* ------------------------------------------------------------------ *)
(*  THE CONFIGURATION STEP AT *DIFFERENT* BAGS, DISCHARGED             *)
(*                                                                     *)
(*  [ax_below_split_from_certificate] reduces the unequal-bag step to   *)
(*  one certificate, [Settles (chans K) (g M ▷ (bag d ⊎ K))] — and the  *)
(*  comment there records that this is *exactly the residue*: it asks   *)
(*  the left to absorb the whole surplus.                               *)
(*                                                                     *)
(*  It is discharged here, and the argument is [surplus_settles_bag]'s  *)
(*  with the left buffer **shifted by [bag d]**: read the acceptance    *)
(*  condition at the trace [feed k] that loads [K].  The right settles  *)
(*  at [g N ▷ bag k] — stable, since [N] is τ-free and refuses [K] —    *)
(*  emitting exactly [chans K]; feeding is reversible                   *)
(*  ([fw_feed_inv_list]), so the left's matching run is a τ-run from    *)
(*  the shifted buffer.  Nothing here needs [ochans (g M) = []]: that   *)
(*  hypothesis is used only to *produce* the split, by                  *)
(*  [msgs_cancel_of_below].                                             *)
(* ------------------------------------------------------------------ *)

Theorem surplus_settles_split : forall (M N : gproc) (d k : list TypeOfActions),
  gStatic M -> gStatic N ->
  (forall p, ~ lts ((g N) : proc) τ p) ->
  (forall a, ActOut a ∈ bag k -> forall r, ~ lts ((g N) : proc) (ActExt (ActIn a)) r) ->
  ((msgs d ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs nil ‖ ((g N) : proc))) ->
  Settles (chans (bag k)) (((g M) : proc) ▷ (bag k ⊎ bag d)).
Proof.
  intros M N d k HM HN HstN Hnoc Hsem.
  assert (Hsty : (((g N) : proc) ▷ bag k) ↛).
  { assert (Hnostep : forall x, ~ ((((g N) : proc) ▷ bag k) ⟶ x)).
    { apply fw_stable_iff. split; [ exact HstN | ].
      intros a Hin q Hq. eapply Hnoc; [ exact Hin | exact Hq ]. }
    destruct (decide (lts_refuses (((g N) : proc) ▷ bag k) τ)) as [Hy|Hn]; [ exact Hy | ].
    exfalso. apply lts_refuses_spec1 in Hn as (z & Hz). eapply Hnostep. exact Hz. }
  assert (Hwq : (((g N) : proc) ▷ (∅ : MO (ExtAct TypeOfActions)))
                  ⟹[feed k] (((g N) : proc) ▷ bag k)).
  { replace (feed k) with (feed k ++ []) by (rewrite app_nil_r; reflexivity).
    apply fw_wt_feed_list.
    replace (bag k ⊎ (∅ : MO (ExtAct TypeOfActions))) with (bag k)
      by (symmetry; apply gmultiset.gmultiset_disj_union_right_id).
    apply wt_nil. }
  destruct (msgs_accept d nil (g M) (g N) Hsem) as (Hc1 & Hc2). simpl in Hc2.
  destruct (Hc2 (feed k) (((g N) : proc) ▷ bag k)
              (fw_converge_static (feed k) (g M) (bag d) (static_g M HM)) Hwq Hsty)
    as (x & Hwx & Hstx & Hincl).
  exists x. split.
  - pose proof (fw_feed_inv_list k (((g M) : proc) ▷ bag d) x Hwx) as H.
    simpl in H. exact H.
  - split; [ exact Hstx | ].
    intros dd w r Hr.
    assert (Hin : (Inputs dd) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR x))
      by (apply coR_abs_pair_iff; exists w, r; exact Hr).
    apply Hincl in Hin. apply coR_abs_pair_iff in Hin.
    eapply emits_gsum_chans. exact Hin.
Qed.

(** …in the form the theorem asks for: the buffer is an arbitrary
    [OutOnly] one, and "[N] refuses it" is read off the *mirror*'s
    stability ([mirror_refuses_of_N]). *)

Lemma cert_of_split : forall (d : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> (forall p, ~ lts ((g N) : proc) τ p) ->
  ((msgs d ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs nil ‖ ((g N) : proc))) ->
  forall K, OutOnly K ->
    ((g (mirrorN ((msgs d) ‖ ((g M) : proc)) N)) ▷ K) ↛ ->
    Settles (chans K) (((g M) : proc) ▷ (bag d ⊎ K)).
Proof.
  intros d M N HM HN HstN Hsem K Hout Hstm.
  destruct (outonly_bag K Hout) as (k & Hk). subst K.
  assert (Hnoc : forall a, ActOut a ∈ bag k ->
                   forall r, ~ lts ((g N) : proc) (ActExt (ActIn a)) r).
  { intros a Hin r Hr.
    assert (Hns : forall z, ~ ((g (mirrorN ((msgs d) ‖ ((g M) : proc)) N) ▷ bag k) ⟶ z))
      by (apply no_step_of_stable; exact Hstm).
    apply fw_stable_iff in Hns as (_ & Hrefuse).
    destruct a as (c,v).
    eapply (mirror_refuses_of_N _ N c v (Hrefuse (c,v) Hin)); exact Hr. }
  replace (bag d ⊎ bag k) with (bag k ⊎ bag d)
    by (apply (comm_L (@disj_union (MO (ExtAct TypeOfActions)) _))).
  apply (surplus_settles_split M N d k); assumption.
Qed.

(** * THE UNEQUAL-BAG STEP, FOR A MUTE LEFT-HAND SUM

    Everything meets here.  [msgs_cancel_of_below] produces the split
    [l1 ≡ₚ l2 ++ d] *and* the cancelled inequation; [cert_of_split] turns
    that inequation into the certificate; [ax_below_split_from_certificate]
    runs Phase A, Phase B and puts the surplus back into the bag.

    The only hypothesis left is the **recursion** — one call per input
    transition of [g N], at every sub-bag — which is the shape
    [VACCS_Descent.wrapped_premise_from_IH] discharges, with [domsim_wt]
    supplying the measure.  It is stated over *every* legal split, since
    [d] is produced by the theorem rather than supplied by the caller. *)

Theorem completeness_cfg_split_no_output :
  forall (l1 l2 : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  ochans ((g M) : proc) = [] ->
  (forall z, ~ lts ((g N) : proc) τ z) ->
  ((msgs l1 ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))) ->
  (forall d, Permutation l1 (l2 ++ d) ->
     forall c v Q' l', subbag l' l2 -> lts ((g N) : proc) (ActExt (ActIn (c,v))) Q' ->
       ax_pre (msgs l' ‖ ((c ! v • 𝟘) ‖ ((msgs d) ‖ ((g M) : proc))))
              (msgs l' ‖ Q')) ->
  ax_pre (msgs l1 ‖ ((g M) : proc)) (msgs l2 ‖ ((g N) : proc)).
Proof.
  intros l1 l2 M N HM HN Hoc HstN Hpre Hrec.
  destruct (msgs_cancel_of_below l1 l2 M N HM HN Hoc Hpre) as (d & Hperm & Hcut).
  assert (Hcgr : (msgs l1 ‖ ((g M) : proc)) ≡* (msgs (d ++ l2) ‖ ((g M) : proc))).
  { apply cgr_fullpar; [ | apply cgr_refl ].
    apply msgs_perm. transitivity (l2 ++ d); [ exact Hperm | apply Permutation_app_comm ]. }
  eapply ax_trans; [ apply ax_cgr; exact Hcgr | ].
  apply ax_below_split_from_certificate; try assumption.
  - apply cert_of_split; assumption.
  - apply Hrec. exact Hperm.
Qed.


(* ------------------------------------------------------------------ *)
(*  THE OTHER HALF: A RIGHT-HAND SIDE WITH A [τ], AT DIFFERENT BAGS     *)
(*                                                                     *)
(*  [cert_of_split] cannot serve here — its certificate needs the right *)
(*  to be genuinely *stable* at the loaded buffer.  [ax_glb_tau] can:   *)
(*  it takes the right apart instead of certifying the left.            *)
(*                                                                     *)
(*  Its existence premise is what [bag_incl_of_below] just made     *)
(*  available at different bags.  A guarded sum never emits             *)
(*  ([gsum_no_out]), so every emission of [msgs l2 ‖ g N] comes from    *)
(*  its bag; the inclusion [bag l2 ⊆ bag l1] then puts the same message *)
(*  in the left's bag, and the left emits it too.                       *)
(* ------------------------------------------------------------------ *)

Theorem ax_below_cfg_glb_split : forall (l1 l2 : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> ochans ((g M) : proc) = [] ->
  ((msgs l1 ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))) ->
  (exists q0, lts (msgs l2 ‖ ((g N) : proc)) τ q0) ->
  (forall q', lts (msgs l2 ‖ ((g N) : proc)) τ q' ->
     ax_pre (msgs l1 ‖ ((g M) : proc)) q') ->
  (forall c v q'', lts (msgs l2 ‖ ((g N) : proc)) (ActExt (ActIn (c,v))) q'' ->
     ax_pre (((c ! v • 𝟘) : proc) ‖ (msgs l1 ‖ ((g M) : proc))) q'') ->
  (forall c v l1' l2', Permutation l1 ((c,v) :: l1') -> Permutation l2 ((c,v) :: l2') ->
     ax_pre (msgs l1' ‖ ((g M) : proc)) (msgs l2' ‖ ((g N) : proc))) ->
  ax_pre (msgs l1 ‖ ((g M) : proc)) (msgs l2 ‖ ((g N) : proc)).
Proof.
  intros l1 l2 M N HM HN Hoc Hpre Hex Htau Hin Hrec.
  assert (Hsub := bag_incl_of_below l1 l2 M N HM HN Hoc Hpre).
  apply ax_glb_tau; [ exact Hex | exact Htau | exact Hin | | ].
  - intros c v q'' Hq''.
    destruct (cfg_out_inv l2 N c v q'' Hq'') as (l0 & Hperm & _).
    assert (Hmem : ActOut (c,v) ∈ bag l1).
    { eapply gmultiset.gmultiset_elem_of_subseteq; [ | exact Hsub ].
      rewrite (bag_perm l2 ((c,v) :: l0) Hperm). simpl.
      apply gmultiset.gmultiset_elem_of_disj_union. left.
      apply gmultiset_elem_of_singleton. reflexivity. }
    apply bag_elem in Hmem. apply in_split in Hmem as (u1 & u2 & Eu).
    assert (Hp1 : Permutation l1 ((c,v) :: (u1 ++ u2))).
    { rewrite Eu. symmetry. apply Permutation_middle. }
    destruct (cfg_out_of_perm l1 (u1 ++ u2) c v ((g M) : proc) Hp1) as (r & Hr & _).
    exists r. exact Hr.
  - intros c v p'' q'' Hp'' Hq''.
    destruct (cfg_out_inv l1 M c v p'' Hp'') as (l1' & Hp1 & Hcp).
    destruct (cfg_out_inv l2 N c v q'' Hq'') as (l2' & Hp2 & Hcq).
    eapply ax_trans; [ apply ax_cgr; exact Hcp | ].
    eapply ax_trans; [ apply (Hrec c v l1' l2' Hp1 Hp2) | ].
    apply ax_cgr_sym. exact Hcq.
Qed.

(* ------------------------------------------------------------------ *)
(*  THE MEASURE GLUE: [DomOk]                                          *)
(*                                                                     *)
(*  [completeness_from_step] hands the step an induction hypothesis at  *)
(*  [size q'] < [size q] for the **original** [q].  A step that works   *)
(*  on the *normal form* recurses on reducts of [NF n l N] instead, and *)
(*  normalisation is not size-decreasing — the level mismatch recorded  *)
(*  at [ax_below_stable_NF].                                            *)
(*                                                                     *)
(*  [domsim] closes exactly that gap, and [DomOk] is the shape in which *)
(*  it is consumed: a state is *admissible* when it is [⊢]-equal to a   *)
(*  strictly smaller [Static] one.  [domok_of_domsim] produces it for   *)
(*  every transition of a dominated process, and [ax_below_of_domok]    *)
(*  spends it — transporting the semantics onto the smaller witness by  *)
(*  [soundness_ax], applying the hypothesis there, and coming back      *)
(*  along the [⊢]-equality.                                             *)
(*                                                                     *)
(*  What is still missing to run [completeness_cfg_mute_dom] under      *)
(*  [completeness_from_step] is only the restatement of its own         *)
(*  recursive premise over [DomOk] instead of over [size], plus a       *)
(*  normal-form theorem that returns a [domsim] **and** [n = 0] on the  *)
(*  ν-free fragment ([normal_form_nores] gives the second, not the      *)
(*  first).                                                             *)
(* ------------------------------------------------------------------ *)

Definition DomOk (q0 q' : proc) : Prop :=
  exists r', Static r' /\ (size r' < size q0)%nat /\ ax_pre q' r' /\ ax_pre r' q'.

Lemma ax_below_of_domok : forall (q0 p q' : proc),
  Static p -> DomOk q0 q' ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' ->
  (forall p1 q1, Static p1 -> Static q1 -> (size q1 < size q0)%nat ->
     p1 ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q1 -> ax_pre p1 q1) ->
  ax_pre p q'.
Proof.
  intros q0 p q' Hp (r' & Hr' & Hlt & Hqr & Hrq) Hpre IH.
  eapply ax_trans; [ | exact Hrq ].
  apply IH; try assumption.
  intros t Ht. apply (soundness_ax _ _ Hqr). apply Hpre. exact Ht.
Qed.

Lemma domok_of_domsim : forall (q0 q : proc) a r,
  Static q0 -> domsim q0 q -> lts q a r -> DomOk q0 r.
Proof.
  intros q0 q a r Hst Hd Hl.
  destruct (ds_s Hd a r Hl) as (r' & Hr' & Hds).
  exists r'. split; [ | split; [ | split ] ].
  - eapply Static_preserved_by_lts; [ exact Hst | exact Hr' ].
  - eapply Static_lts_decrease; [ exact Hst | exact Hr' ].
  - exact (ds_r Hds).
  - exact (ds_l Hds).
Qed.


(** The two closures the restatement will need.

    [DomOk_cgr] because the output branch applies the hypothesis to
    [msgs l2' ‖ g N], which is only [≡*]-equal to the reduct; and
    [domok_of_domsim_wt] because the split branch applies it to
    [msgs l' ‖ Q'], reached by *emitting a sub-bag and then inputting* —
    a whole trace, not one step.  A trace carrying at least one action
    still shrinks a [Static] process ([wt_act_size_lt]), which is exactly
    why the [mu :: s] shape is the right hypothesis. *)

Lemma DomOk_cgr : forall (q0 q1 q2 : proc),
  DomOk q0 q1 -> q1 ≡* q2 -> DomOk q0 q2.
Proof.
  intros q0 q1 q2 (r' & Hr' & Hlt & Hqr & Hrq) Hc.
  exists r'. split; [ exact Hr' | ]. split; [ exact Hlt | ]. split.
  - eapply ax_trans; [ apply ax_cgr_sym; exact Hc | exact Hqr ].
  - eapply ax_trans; [ exact Hrq | apply ax_cgr; exact Hc ].
Qed.

Lemma domok_of_domsim_wt : forall (q0 q : proc) mu s r,
  Static q0 -> domsim q0 q -> q ⟹[mu :: s] r -> DomOk q0 r.
Proof.
  intros q0 q mu s r Hst Hd Hw.
  destruct (domsim_wt q (mu :: s) r Hw q0 Hd) as (r' & Hr' & Hds).
  exists r'. split; [ | split; [ | split ] ].
  - eapply Static_preserved_by_wt; [ exact Hst | exact Hr' ].
  - eapply wt_act_size_lt; [ exact Hst | exact Hr' ].
  - exact (ds_r Hds).
  - exact (ds_l Hds).
Qed.


(** The last technical piece: **emitting a sub-bag** is a run.

    [completeness_cfg_split_dom] applies its hypothesis at
    [msgs l' ‖ Q'] for a *sub-bag* [l'] — a state reached by emitting the
    surplus [u] and then inputting, not by a single step.  The transport
    is by [cgr_wt_transfer]: an emission leaves a [𝟘] behind, so each step
    lands only [≡*]-close to the next configuration, and the run has to be
    replayed across that congruence.  [cgr_lts_transfer] does one step;
    this is its [⟹] closure. *)

Lemma cgr_wt_transfer : forall s (p p' r : proc), p ≡* p' -> p ⟹[s] r ->
  exists r', p' ⟹[s] r' /\ r ≡* r'.
Proof.
  intros s p p' r Hc Hw. revert p' Hc.
  induction Hw as [x|s0 x y z Hl Hwt IH|mu s0 x y z Hl Hwt IH]; intros p' Hc.
  - exists p'. split; [ apply wt_nil | exact Hc ].
  - destruct (cgr_lts_transfer x p' τ y Hc Hl) as (y' & Hy' & Hcy).
    destruct (IH y' Hcy) as (r' & Hr' & Hcr).
    exists r'. split; [ eapply wt_tau; [ exact Hy' | exact Hr' ] | exact Hcr ].
  - destruct (cgr_lts_transfer x p' (ActExt mu) y Hc Hl) as (y' & Hy' & Hcy).
    destruct (IH y' Hcy) as (r' & Hr' & Hcr).
    exists r'. split; [ eapply wt_act; [ exact Hy' | exact Hr' ] | exact Hcr ].
Qed.

Lemma cfg_emit_prefix : forall (u l' : list TypeOfActions) (P : proc),
  exists r, (msgs (u ++ l') ‖ P) ⟹[map ActOut u] r /\ r ≡* (msgs l' ‖ P).
Proof.
  induction u as [|a u IH]; intros l' P; simpl.
  - exists (msgs l' ‖ P). split; [ apply wt_nil | reflexivity ].
  - destruct a as (c,v).
    destruct (cfg_out_of_perm ((c,v) :: (u ++ l')) (u ++ l') c v P
                (reflexivity _)) as (r0 & Hr0 & Hc0).
    destruct (IH l' P) as (r1 & Hr1 & Hc1).
    assert (Hc0' : (msgs (u ++ l') ‖ P) ≡* r0) by (symmetry; exact Hc0).
    destruct (cgr_wt_transfer (map ActOut u) (msgs (u ++ l') ‖ P) r0 r1 Hc0' Hr1)
      as (r2 & Hr2 & Hc2).
    exists r2. split.
    + eapply wt_act; [ exact Hr0 | exact Hr2 ].
    + etransitivity; [ symmetry; exact Hc2 | exact Hc1 ].
Qed.

Lemma domok_of_domsim_wt' : forall (q0 q : proc) s r,
  Static q0 -> domsim q0 q -> q ⟹[s] r -> s <> [] -> DomOk q0 r.
Proof.
  intros q0 q s r Hst Hd Hw Hs. destruct s as [|mu s0]; [ contradiction | ].
  eapply domok_of_domsim_wt; eassumption.
Qed.

Lemma cfg_reach_subbag : forall (l' l : list TypeOfActions) (P : proc),
  subbag l' l ->
  exists u r, (msgs l ‖ P) ⟹[map ActOut u] r /\ r ≡* (msgs l' ‖ P).
Proof.
  intros l' l P (u & Hp).
  destruct (cfg_emit_prefix u l' P) as (r0 & Hr0 & Hc0).
  assert (Hc : (msgs l ‖ P) ≡* (msgs (u ++ l') ‖ P)).
  { apply cgr_fullpar; [ apply msgs_perm; exact Hp | apply cgr_refl ]. }
  assert (Hc' : (msgs (u ++ l') ‖ P) ≡* (msgs l ‖ P)) by (symmetry; exact Hc).
  destruct (cgr_wt_transfer (map ActOut u) (msgs (u ++ l') ‖ P) (msgs l ‖ P) r0
              Hc' Hr0) as (r & Hr & Hcr).
  exists u, r. split; [ exact Hr | ].
  etransitivity; [ symmetry; exact Hcr | exact Hc0 ].
Qed.

(** …so the state [completeness_cfg_split_dom] recurses on really is
    admissible: it is [⊢]-equal to a strictly smaller reduct of the
    original process.  This is the last of the three [DomOk] facts the
    restatement needs. *)

Lemma domok_of_subbag_input : forall (q0 : proc) (l2 l' : list TypeOfActions)
    (N : gproc) c v Q',
  Static q0 -> domsim q0 (msgs l2 ‖ ((g N) : proc)) ->
  subbag l' l2 -> lts ((g N) : proc) (ActExt (ActIn (c,v))) Q' ->
  DomOk q0 (msgs l' ‖ Q').
Proof.
  intros q0 l2 l' N c v Q' Hst Hd Hsub Hin.
  destruct (cfg_reach_subbag l' l2 ((g N) : proc) Hsub) as (u & r & Hr & Hcr).
  assert (Hstep : lts (msgs l' ‖ ((g N) : proc)) (ActExt (ActIn (c,v)))
                      (msgs l' ‖ Q')) by (apply lts_parR; exact Hin).
  assert (Hcr' : (msgs l' ‖ ((g N) : proc)) ≡* r) by (symmetry; exact Hcr).
  destruct (cgr_lts_transfer _ r _ _ Hcr' Hstep) as (x & Hx & Hcx).
  assert (Hbig : (msgs l2 ‖ ((g N) : proc))
                   ⟹[map ActOut u ++ (ActIn (c,v) :: nil)] x).
  { eapply wt_concat; [ exact Hr | eapply wt_act; [ exact Hx | apply wt_nil ] ]. }
  eapply DomOk_cgr; [ | symmetry; exact Hcx ].
  eapply domok_of_domsim_wt'; [ exact Hst | exact Hd | exact Hbig | ].
  destruct u as [|a u0]; simpl; discriminate.
Qed.


(* ------------------------------------------------------------------ *)
(*  THE STEP, RESTATED OVER [DomOk] — and finally in the shape          *)
(*  [completeness_from_step] consumes                                   *)
(*                                                                     *)
(*  Same three theorems as before, with the recursive premise moved     *)
(*  from [size q'] below the *normal form* to: [q'] is [DomOk] for      *)
(*  the **original** right-hand side.  Each of the four places the      *)
(*  hypothesis is used has its own [DomOk] fact:                        *)
(*                                                                     *)
(*    τ- and input-reducts  → [domok_of_domsim]                         *)
(*    the output branch      → [DomOk_cgr] on [cfg_out_of_perm]'s target*)
(*    the split branch       → [domok_of_subbag_input]                  *)
(* ------------------------------------------------------------------ *)

(** The three theorems are stated over **two abstract predicates** — one
    per side — rather than over [DomOk] and over nothing:

      [LOk] the class the left-hand side is allowed to stay in, with the
            two closures the four recursive call sites need (add a bag,
            add one message), plus its base at [g M];
      [Ok]  the class the right-hand side's reducts land in.

    That is what lets the same proof serve both the unrestricted frame of
    [completeness_from_step] ([LOk := fun _ => True], [Ok := DomOk q0])
    and the **restricted recursion** further down ([LOk := MuteNF],
    [Ok := DomOkD q0]) without duplicating a line. *)

Theorem completeness_cfg_split_ok :
  forall (LOk Ok : proc -> Prop) (l1 l2 : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  ochans ((g M) : proc) = [] ->
  (forall z, ~ lts ((g N) : proc) τ z) ->
  (forall l p, LOk p -> LOk (msgs l ‖ p)) ->
  (forall (c : ChannelData) (v : ValueData) (p : proc),
     LOk p -> LOk (((c ! v • 𝟘) : proc) ‖ p)) ->
  LOk ((g M) : proc) ->
  (forall l' c v Q', subbag l' l2 ->
     lts ((g N) : proc) (ActExt (ActIn (c,v))) Q' -> Ok (msgs l' ‖ Q')) ->
  ((msgs l1 ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))) ->
  (forall p' q', Static p' -> LOk p' -> Static q' -> Ok q' ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
  ax_pre (msgs l1 ‖ ((g M) : proc)) (msgs l2 ‖ ((g N) : proc)).
Proof.
  intros LOk Ok l1 l2 M N HM HN Hoc HstN HLbag HLmsg HLbase HOkin Hpre IH.
  assert (Hnil : (msgs nil ‖ ((g N) : proc)) ≡* ((g N) : proc)).
  { simpl. etransitivity; [ apply cgr_par_com | apply cgr_par_nil ]. }
  apply completeness_cfg_split_no_output; try assumption.
  intros d Hperm c v Q' l' Hsub Hin.
  assert (Hcgr : (msgs (l2 ++ d) ‖ ((g M) : proc)) ≡* (msgs l1 ‖ ((g M) : proc))).
  { apply cgr_fullpar; [ | apply cgr_refl ].
    apply msgs_perm. apply Permutation_sym. exact Hperm. }
  assert (Hshift : (msgs (l2 ++ d) ‖ ((g M) : proc))
                     ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))).
  { intros t Ht. apply Hpre. apply (proj2 (must_i_cgr _ _ Hcgr)). exact Ht. }
  assert (Hcut := msgs_cancel_surplus l2 d M N HM HN Hoc Hshift).
  assert (Hcut' : (msgs d ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc)).
  { intros t Ht. apply (proj2 (must_i_cgr _ _ Hnil)). apply Hcut. exact Ht. }
  assert (Hsem : (((c ! v • 𝟘) : proc) ‖ (msgs d ‖ ((g M) : proc)))
                   ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ Q')
    by (eapply must_i_feed_below; [ exact Hcut' | exact Hin ]).
  apply IH.
  - constructor; [ apply msgs_Static | constructor ].
    + repeat constructor.
    + constructor; [ apply msgs_Static | apply static_g; exact HM ].
  - apply HLbag. apply HLmsg. apply HLbag. exact HLbase.
  - constructor; [ apply msgs_Static | ].
    eapply Static_preserved_by_lts; [ apply static_g; exact HN | exact Hin ].
  - apply (HOkin l' c v Q'); assumption.
  - apply must_i_par_compat_r. exact Hsem.
Qed.

Theorem completeness_cfg_glb_ok :
  forall (LOk Ok : proc -> Prop) (l1 l2 : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> ochans ((g M) : proc) = [] ->
  (forall l p, LOk p -> LOk (msgs l ‖ p)) ->
  (forall (c : ChannelData) (v : ValueData) (p : proc),
     LOk p -> LOk (((c ! v • 𝟘) : proc) ‖ p)) ->
  LOk ((g M) : proc) ->
  (forall a r, lts (msgs l2 ‖ ((g N) : proc)) a r -> Ok r) ->
  (forall q1 q2, Ok q1 -> q1 ≡* q2 -> Ok q2) ->
  (exists z, lts (msgs l2 ‖ ((g N) : proc)) τ z) ->
  ((msgs l1 ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))) ->
  (forall p' q', Static p' -> LOk p' -> Static q' -> Ok q' ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
  ax_pre (msgs l1 ‖ ((g M) : proc)) (msgs l2 ‖ ((g N) : proc)).
Proof.
  intros LOk Ok l1 l2 M N HM HN Hoc HLbag HLmsg HLbase HOk1 HOk2 Hex Hpre IH.
  assert (HStl : Static (msgs l1 ‖ ((g M) : proc)))
    by (constructor; [ apply msgs_Static | apply static_g; exact HM ]).
  assert (HStr : Static (msgs l2 ‖ ((g N) : proc)))
    by (constructor; [ apply msgs_Static | apply static_g; exact HN ]).
  apply ax_below_cfg_glb_split; try assumption.
  - intros q' Hq'. apply IH.
    + exact HStl.
    + apply HLbag. exact HLbase.
    + eapply Static_preserved_by_lts; [ exact HStr | exact Hq' ].
    + eapply HOk1. exact Hq'.
    + intros t Ht. eapply must_i_tau_below; [ exact Hq' | ]. apply Hpre. exact Ht.
  - intros c v q'' Hq''. apply IH.
    + constructor; [ repeat constructor | exact HStl ].
    + apply HLmsg. apply HLbag. exact HLbase.
    + eapply Static_preserved_by_lts; [ exact HStr | exact Hq'' ].
    + eapply HOk1. exact Hq''.
    + eapply must_i_feed_below; [ exact Hpre | exact Hq'' ].
  - intros c v l1' l2' Hp1 Hp2.
    destruct (msgs_cancel_of_below l1 l2 M N HM HN Hoc Hpre) as (d & Hdd & Hcut).
    assert (Hnil : (msgs nil ‖ ((g N) : proc)) ≡* ((g N) : proc)).
    { simpl. etransitivity; [ apply cgr_par_com | apply cgr_par_nil ]. }
    assert (Hcut' : (msgs d ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc)).
    { intros t Ht. apply (proj2 (must_i_cgr _ _ Hnil)). apply Hcut. exact Ht. }
    assert (Hsplit : Permutation l1' (l2' ++ d)).
    { apply (Permutation_cons_inv (a := (c,v))).
      etransitivity; [ symmetry; exact Hp1 | ].
      etransitivity; [ exact Hdd | ].
      etransitivity; [ apply Permutation_app_tail; exact Hp2 | reflexivity ]. }
    assert (Hcgr : (msgs l1' ‖ ((g M) : proc))
                     ≡* (msgs l2' ‖ (msgs d ‖ ((g M) : proc)))).
    { etransitivity; [ apply cgr_fullpar;
        [ apply msgs_perm; exact Hsplit | apply cgr_refl ] | ].
      etransitivity; [ apply cgr_fullpar; [ apply msgs_app | apply cgr_refl ] | ].
      apply cgr_par_assoc. }
    apply IH.
    + constructor; [ apply msgs_Static | apply static_g; exact HM ].
    + apply HLbag. exact HLbase.
    + constructor; [ apply msgs_Static | apply static_g; exact HN ].
    + destruct (cfg_out_of_perm l2 l2' c v ((g N) : proc) Hp2) as (r & Hr & Hcr).
      eapply HOk2; [ | exact Hcr ]. eapply HOk1. exact Hr.
    + intros t Ht.
      assert (Hw := must_i_par_compat_r (msgs l2') _ _ Hcut').
      apply Hw. apply (proj2 (must_i_cgr _ _ Hcgr)). exact Ht.
Qed.

Theorem completeness_cfg_mute_ok :
  forall (LOk Ok : proc -> Prop) (l1 l2 : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N -> ochans ((g M) : proc) = [] ->
  (forall l p, LOk p -> LOk (msgs l ‖ p)) ->
  (forall (c : ChannelData) (v : ValueData) (p : proc),
     LOk p -> LOk (((c ! v • 𝟘) : proc) ‖ p)) ->
  LOk ((g M) : proc) ->
  (forall a r, lts (msgs l2 ‖ ((g N) : proc)) a r -> Ok r) ->
  (forall q1 q2, Ok q1 -> q1 ≡* q2 -> Ok q2) ->
  (forall l' c v Q', subbag l' l2 ->
     lts ((g N) : proc) (ActExt (ActIn (c,v))) Q' -> Ok (msgs l' ‖ Q')) ->
  ((msgs l1 ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))) ->
  (forall p' q', Static p' -> LOk p' -> Static q' -> Ok q' ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
  ax_pre (msgs l1 ‖ ((g M) : proc)) (msgs l2 ‖ ((g N) : proc)).
Proof.
  intros LOk Ok l1 l2 M N HM HN Hoc HLbag HLmsg HLbase HOk1 HOk2 HOk3 Hpre IH.
  destruct (lts_dec (msgs l2 ‖ ((g N) : proc)) τ) as [Hno|Hyes].
  - apply (completeness_cfg_split_ok LOk Ok l1 l2 M N); try assumption.
    intros z Hz. eapply (Hno (msgs l2 ‖ z)). apply lts_parR. exact Hz.
  - apply (completeness_cfg_glb_ok LOk Ok l1 l2 M N); assumption.
Qed.

(** …and the unrestricted instance, which is what [completeness_step_mute]
    consumes: nothing is asked of the left ([LOk := fun _ => True]) and the
    right's reducts are measured by [DomOk]. *)

Corollary completeness_cfg_mute_dom :
  forall (q0 : proc) (l1 l2 : list TypeOfActions) (M N : gproc),
  Static q0 -> domsim q0 (msgs l2 ‖ ((g N) : proc)) ->
  gStatic M -> gStatic N -> ochans ((g M) : proc) = [] ->
  ((msgs l1 ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))) ->
  (forall p' q', Static p' -> Static q' -> DomOk q0 q' ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
  ax_pre (msgs l1 ‖ ((g M) : proc)) (msgs l2 ‖ ((g N) : proc)).
Proof.
  intros q0 l1 l2 M N Hq0 Hd HM HN Hoc Hpre IH.
  apply (completeness_cfg_mute_ok (fun _ => True) (DomOk q0) l1 l2 M N);
    try assumption; try (intros; exact I).
  - intros a r Hr. eapply domok_of_domsim; eassumption.
  - intros q1 q2 H1 H2. eapply DomOk_cgr; eassumption.
  - intros l' c v Q' Hsub Hin. eapply domok_of_subbag_input; eassumption.
  - intros p' q' Hp' _ Hq' Hok Hs. apply IH; assumption.
Qed.

(** * THE STEP, IN THE SHAPE THE OUTER RECURSION CONSUMES

    Everything lines up here.  [normal_form_nores_sim] turns the ν-free
    right-hand side into a **bare configuration** *and* hands over the
    [domsim] that measures its reducts against the **original** [q];
    [ax_below_of_domok] spends that measure; and what is left is exactly
    [completeness_from_step]'s hypothesis, restricted to a left-hand side
    that is a mute configuration.

    The left is *not* normalised: it is taken already in configuration
    form with [ochans (g M) = []].  Producing that from an arbitrary
    [Static p] is the remaining gap — and it is the residue this
    development has been circling since the [Harmless]/[Bad] family, not
    a missing piece of plumbing. *)

Theorem completeness_step_mute :
  forall (q : proc) (l1 : list TypeOfActions) (M : gproc),
  Static q -> NoRes q -> gStatic M -> ochans ((g M) : proc) = [] ->
  (msgs l1 ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
  ax_pre (msgs l1 ‖ ((g M) : proc)) q.
Proof.
  intros q l1 M Hq Hnr HM Hoc Hpre IH.
  destruct (normal_form_nores_sim q Hq Hnr) as (l2 & N & HN & Hd).
  eapply ax_trans; [ | exact (ds_r Hd) ].
  eapply completeness_cfg_mute_dom; try eassumption.
  - intros t Ht. apply (soundness_ax _ _ (ds_l Hd)). apply Hpre. exact Ht.
  - intros p' q' Hp' Hq' Hok Hpre'.
    eapply ax_below_of_domok; eassumption.
Qed.


(** * THE RESIDUE, NAMED ON THE LEFT-HAND SIDE: [MuteNF]

    [completeness_step_mute] takes its left already as a **mute
    configuration**.  Naming that property of [p] alone turns the step
    into exactly [completeness_from_step]'s hypothesis, conditional on
    one predicate:

        MuteNF p := p is ⊢-equal to some [msgs l ‖ g M] with
                    [ochans (g M) = []]

    i.e. *p normalises to a configuration whose guarded sum can never
    emit*.  [MuteNF_gsum] and [MuteNF_cfg] show it is not vacuous, and
    [VACCS_Bad.no_output_below_nil] says what it means semantically: such
    a [p], stripped of its bag, sits below [𝟘].

    That is the residue — the same one the [Harmless]/[Bad]/[BadK] family
    was built for and shown not to capture. *)

Definition MuteNF (p : proc) : Prop :=
  exists l M, gStatic M /\ ochans ((g M) : proc) = []
           /\ ax_pre p (msgs l ‖ ((g M) : proc))
           /\ ax_pre (msgs l ‖ ((g M) : proc)) p.

Lemma MuteNF_gsum : forall (M : gproc),
  gStatic M -> ochans ((g M) : proc) = [] -> MuteNF ((g M) : proc).
Proof.
  intros M HM Hoc. exists nil, M. split; [ exact HM | ]. split; [ exact Hoc | ].
  assert (Hc : ((g M) : proc) ≡* (msgs nil ‖ ((g M) : proc))).
  { simpl. symmetry. etransitivity; [ apply cgr_par_com | apply cgr_par_nil ]. }
  split; [ apply ax_cgr; exact Hc | apply ax_cgr_sym; exact Hc ].
Qed.

Lemma MuteNF_cfg : forall (l : list TypeOfActions) (M : gproc),
  gStatic M -> ochans ((g M) : proc) = [] -> MuteNF (msgs l ‖ ((g M) : proc)).
Proof.
  intros l M HM Hoc. exists l, M.
  split; [ exact HM | ]. split; [ exact Hoc | ]. split; apply ax_refl.
Qed.

Theorem completeness_step_of_mute_nf :
  forall (p q : proc),
  Static q -> NoRes q -> MuteNF p ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
  ax_pre p q.
Proof.
  intros p q Hq Hnr (l1 & M & HM & Hoc & Hpm & Hmp) Hpre IH.
  eapply ax_trans; [ exact Hpm | ].
  apply completeness_step_mute; try assumption.
  intros t Ht. apply Hpre. apply (soundness_ax _ _ Hmp). exact Ht.
Qed.


(** * A SYNTACTIC SUFFICIENT CONDITION FOR [MuteNF]

    [MuteNF] is the one hypothesis the whole configuration chain still
    rests on, and until now it could only be checked by hand.  Here is a
    criterion for it — the same [ochans p = []] that runs through the
    rest of the development:

        a ν-free [Static] process that can **never emit** normalises to a
        configuration with an **empty bag** and a mute guarded sum.

    The bag comes out empty for a good reason: a pending message is the
    only shape whose [ochans] is non-empty on its own, so the criterion
    excludes it outright, and every other case just recombines. *)

Lemma ochans_NewVar : forall p k, ochans (NewVar k p) = ochans p
with gochans_gNewVar : forall M k, gochans (gNewVar k M) = gochans M.
Proof.
  - destruct p as [P Q | i | x P | C P Q | c v | P | M ]; intro k; simpl.
    + f_equal; apply ochans_NewVar.
    + reflexivity.
    + apply ochans_NewVar.
    + f_equal; apply ochans_NewVar.
    + reflexivity.
    + f_equal. apply ochans_NewVar.
    + apply gochans_gNewVar.
  - destruct M as [ | | c P | P | M1 M2 ]; intro k; simpl.
    + reflexivity.
    + reflexivity.
    + apply ochans_NewVar.
    + apply ochans_NewVar.
    + f_equal; apply gochans_gNewVar.
Qed.

Lemma gochans_ext_nil : forall M N,
  gochans M = [] -> gochans N = [] -> gochans (ext M N) = [].
Proof.
  induction M as [ | | c P | P | M1 IH1 M2 IH2 ]; intros N HM HN; simpl in *.
  - reflexivity.
  - reflexivity.
  - rewrite HM. simpl. rewrite gochans_gNewVar. exact HN.
  - rewrite HM. simpl. exact HN.
  - apply app_eq_nil in HM as (H1 & H2). rewrite IH1, IH2; auto.
Qed.

Lemma gochans_ext_r_nil : forall N M,
  gochans N = [] -> gochans M = [] -> gochans (ext_r N M) = [].
Proof.
  induction N as [ | | c Q | Q | N1 IH1 N2 IH2 ]; intros M HN HM; simpl in *.
  - reflexivity.
  - reflexivity.
  - rewrite HN. rewrite gochans_gNewVar. rewrite HM. reflexivity.
  - rewrite HN. rewrite HM. reflexivity.
  - apply app_eq_nil in HN as (H1 & H2). rewrite IH1, IH2; auto.
Qed.

Theorem normal_form_nores_mute : forall p, Static p -> NoRes p -> ochans p = [] ->
  exists M, gStatic M /\ ochans ((g M) : proc) = []
         /\ domsim p (msgs nil ‖ ((g M) : proc)).
Proof.
  intro p. induction p as [p IHp] using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs Hnr Hoc. destruct p as [p1 p2|x|x p0|E p1 p2|c v|p0|M].
  - inversion Hs; subst. destruct Hnr as (Hn1 & Hn2).
    simpl in Hoc. apply app_eq_nil in Hoc as (Ho1 & Ho2).
    destruct (IHp p1 ltac:(simpl; lia) H1 Hn1 Ho1) as (M1 & HM1 & Hm1 & Hd1).
    destruct (IHp p2 ltac:(simpl; lia) H2 Hn2 Ho2) as (M2 & HM2 & Hm2 & Hd2).
    exists (ext M1 M2 + ext_r M2 M1).
    split; [ constructor; [ apply ext_gStatic | apply ext_r_gStatic ]; assumption | ].
    split.
    { simpl. simpl in Hm1, Hm2.
      rewrite (gochans_ext_nil M1 M2 Hm1 Hm2).
      rewrite (gochans_ext_r_nil M2 M1 Hm2 Hm1). reflexivity. }
    assert (Hc : ((msgs nil ‖ ((g M1) : proc)) ‖ (msgs nil ‖ ((g M2) : proc)))
                 ≡* (msgs nil ‖ (((g M1) : proc) ‖ ((g M2) : proc)))).
    { etransitivity; [ apply cgr_par_exchange | ].
      apply cgr_fullpar; [ symmetry; apply (msgs_app nil nil) | reflexivity ]. }
    eapply domsim_trans; [ apply domsim_par; [ exact Hd1 | exact Hd2 ] | ].
    eapply domsim_trans; [ apply domsim_cgr; exact Hc | ].
    apply domsim_par; [ apply domsim_refl | apply domsim_expansion ].
  - inversion Hs.
  - inversion Hs.
  - simpl in Hoc. apply app_eq_nil in Hoc as (Ho1 & Ho2).
    destruct (Eval_Eq 0 E) as [[|]|] eqn:HE;
      [ | | exfalso; eapply Eval_Eq_0_not_none; exact HE ].
    + inversion Hs; subst. destruct Hnr as (Hn1 & Hn2).
      destruct (IHp p1 ltac:(simpl; lia) H1 Hn1 Ho1) as (M & HM & Hm & Hd).
      exists M. split; [ exact HM | ]. split; [ exact Hm | ].
      eapply domsim_trans; [ apply domsim_cgr; apply cgr_if_true; exact HE | exact Hd ].
    + inversion Hs; subst. destruct Hnr as (Hn1 & Hn2).
      destruct (IHp p2 ltac:(simpl; lia) H3 Hn2 Ho2) as (M & HM & Hm & Hd).
      exists M. split; [ exact HM | ]. split; [ exact Hm | ].
      eapply domsim_trans; [ apply domsim_cgr; apply cgr_if_false; exact HE | exact Hd ].
  - (* a pending message is exactly what the criterion excludes *)
    simpl in Hoc. discriminate Hoc.
  - simpl in Hnr. contradiction.
  - inversion Hs; subst. exists M. split; [ assumption | ].
    split; [ exact Hoc | ]. simpl.
    apply domsim_cgr. etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ].
Qed.

Corollary MuteNF_of_mute : forall p, Static p -> NoRes p -> ochans p = [] -> MuteNF p.
Proof.
  intros p Hs Hnr Hoc.
  destruct (normal_form_nores_mute p Hs Hnr Hoc) as (M & HM & Hm & Hd).
  exists nil, M. split; [ exact HM | ]. split; [ exact Hm | ].
  split; [ exact (ds_l Hd) | exact (ds_r Hd) ].
Qed.


(** * THE LEFT-HAND CLASS IS STABLE UNDER THE RECURSION

    This matters more than it looks.  The four recursive calls of
    [completeness_cfg_mute_ok] all have a left-hand side of the shape
    "[msgs …] beside the original mute sum, possibly with one more
    message in front":

      [msgs l' ‖ ((c!v•𝟘) ‖ (msgs d ‖ g M))]   (split branch)
      [msgs l1 ‖ g M]                           (τ branch)
      [(c!v•𝟘) ‖ (msgs l1 ‖ g M)]               (input branch)
      [msgs l1' ‖ g M]                          (output branch)

    and [MuteSem_msg]/[MuteSem_bag] put every one of them back in the
    class.  So on the left the recursion never leaves it; the hypothesis
    is *self-propagating*.

    (The same two closures were first proved for [MuteNF]; they were
    deleted when [MuteSem] superseded it, since nothing consumed them any
    more — see the audit note in the plan.) *)

(** * THE RIGHT-HAND CLASS: [NoResD] SURVIVES NORMALISATION

    [MuteSem_msg]/[MuteSem_bag] close the recursion on the left.  On the
    right what has to survive is *deep* ν-freedom, because the reducts of
    a normal form are the continuations of its guards — and
    [VACCS_NormalForm.NoRes] only constrains the spine.

    [NoResD] does survive: it is preserved by every transition
    ([noresd_lts_target]), by substitution ([NoResD_subst]) and by the
    value shift, and the two constructions the normal form is built from
    propagate it exactly as [gochans_ext_nil] propagates [ochans]. *)

Lemma NoResD_msgs : forall (l : list TypeOfActions), NoResD (msgs l).
Proof.
  induction l as [|a l IH]; simpl; [ exact I | split; [ exact I | exact IH ] ].
Qed.

Lemma NoResD_NewVar : forall p k, NoResD p -> NoResD (NewVar k p)
with gNoResD_gNewVar : forall M k, gNoResD M -> gNoResD (gNewVar k M).
Proof.
  - destruct p as [P Q | i | x P | C P Q | c v | P | M ]; intros k H; simpl in *.
    + destruct H as (H1 & H2). split; [ apply NoResD_NewVar | apply NoResD_NewVar ];
        assumption.
    + exact I.
    + apply NoResD_NewVar. exact H.
    + destruct H as (H1 & H2). split; [ apply NoResD_NewVar | apply NoResD_NewVar ];
        assumption.
    + exact I.
    + contradiction.
    + apply gNoResD_gNewVar. exact H.
  - destruct M as [ | | c P | P | M1 M2 ]; intros k H; simpl in *.
    + exact I.
    + exact I.
    + apply NoResD_NewVar. exact H.
    + apply NoResD_NewVar. exact H.
    + destruct H as (H1 & H2). split; [ apply gNoResD_gNewVar | apply gNoResD_gNewVar ];
        assumption.
Qed.

Lemma gNoResD_ext : forall M N, gNoResD M -> gNoResD N -> gNoResD (ext M N).
Proof.
  induction M as [ | | c P | P | M1 IH1 M2 IH2 ]; intros N HM HN; simpl in *.
  - exact I.
  - exact I.
  - split; [ exact HM | apply gNoResD_gNewVar; exact HN ].
  - split; [ exact HM | exact HN ].
  - destruct HM as (H1 & H2). split; [ apply IH1 | apply IH2 ]; assumption.
Qed.

Lemma gNoResD_ext_r : forall N M, gNoResD N -> gNoResD M -> gNoResD (ext_r N M).
Proof.
  induction N as [ | | c Q | Q | N1 IH1 N2 IH2 ]; intros M HN HM; simpl in *.
  - exact I.
  - exact I.
  - split; [ apply gNoResD_gNewVar; exact HM | exact HN ].
  - split; [ exact HM | exact HN ].
  - destruct HN as (H1 & H2). split; [ apply IH1 | apply IH2 ]; assumption.
Qed.

(** …so the normal form of a deeply ν-free process has a deeply ν-free
    guarded sum, and every reduct of it is deeply ν-free again.  That is
    the right-hand half of the class the restricted recursion needs. *)

Theorem normal_form_deep : forall p, Static p -> NoResD p ->
  exists l M, gStatic M /\ gNoResD M /\ domsim p (msgs l ‖ ((g M) : proc)).
Proof.
  intro p. induction p as [p IHp] using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs Hnr. destruct p as [p1 p2|x|x p0|E p1 p2|c v|p0|M].
  - inversion Hs; subst. destruct Hnr as (Hn1 & Hn2).
    destruct (IHp p1 ltac:(simpl; lia) H1 Hn1) as (l1 & M1 & HM1 & Hd1 & Hs1).
    destruct (IHp p2 ltac:(simpl; lia) H2 Hn2) as (l2 & M2 & HM2 & Hd2 & Hs2).
    exists (l1 ++ l2), (ext M1 M2 + ext_r M2 M1).
    split; [ constructor; [ apply ext_gStatic | apply ext_r_gStatic ]; assumption | ].
    split; [ split; [ apply gNoResD_ext | apply gNoResD_ext_r ]; assumption | ].
    assert (Hc : ((msgs l1 ‖ ((g M1) : proc)) ‖ (msgs l2 ‖ ((g M2) : proc)))
                 ≡* (msgs (l1 ++ l2) ‖ (((g M1) : proc) ‖ ((g M2) : proc)))).
    { etransitivity; [ apply cgr_par_exchange | ].
      apply cgr_fullpar; [ symmetry; apply msgs_app | reflexivity ]. }
    eapply domsim_trans; [ apply domsim_par; [ exact Hs1 | exact Hs2 ] | ].
    eapply domsim_trans; [ apply domsim_cgr; exact Hc | ].
    apply domsim_par; [ apply domsim_refl | apply domsim_expansion ].
  - inversion Hs.
  - inversion Hs.
  - destruct (Eval_Eq 0 E) as [[|]|] eqn:HE;
      [ | | exfalso; eapply Eval_Eq_0_not_none; exact HE ].
    + inversion Hs; subst. destruct Hnr as (Hn1 & Hn2).
      destruct (IHp p1 ltac:(simpl; lia) H1 Hn1) as (l & M & HM & Hdd & Hd).
      exists l, M. split; [ exact HM | ]. split; [ exact Hdd | ].
      eapply domsim_trans; [ apply domsim_cgr; apply cgr_if_true; exact HE | exact Hd ].
    + inversion Hs; subst. destruct Hnr as (Hn1 & Hn2).
      destruct (IHp p2 ltac:(simpl; lia) H3 Hn2) as (l & M & HM & Hdd & Hd).
      exists l, M. split; [ exact HM | ]. split; [ exact Hdd | ].
      eapply domsim_trans; [ apply domsim_cgr; apply cgr_if_false; exact HE | exact Hd ].
  - exists [(c,v)], 𝟘. split; [ constructor | ]. split; [ exact I | ]. simpl.
    apply domsim_cgr. etransitivity; [ apply cgr_par_nil_rev | ].
    apply cgr_fullpar; [ apply cgr_par_nil_rev | reflexivity ].
  - simpl in Hnr. contradiction.
  - inversion Hs; subst. exists [], M. split; [ assumption | ].
    split; [ exact Hnr | ]. simpl.
    apply domsim_cgr. etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ].
Qed.


(** * THE LEFT-HAND CLASS, WEAKENED: [MuteSem]

    [MuteNF] asks for [⊢] in **both** directions between [p] and its mute
    configuration.  The recursion never needs that: it uses [⊢] one way —
    to move the goal onto the configuration — and the *semantics* the
    other way, to transport the hypothesis.  So the second conjunct can
    be a plain [⊑ₘᵤₛₜᵢ], which is strictly weaker (soundness turns any [⊢]
    into one).

    The widening is not cosmetic: **the copycat is in the class.**
    [ax_ccat_l] gives [⊢ ccat c ⊑ g 𝟘] and [must_i_ccat_r] gives
    [g 𝟘 ⊑ₘᵤₛₜᵢ ccat c]; what [MuteNF] would additionally require is the
    converse *derivation* [⊢ g 𝟘 ⊑ ccat c].  And the copycat is precisely
    the shape the syntactic criterion [MuteG] excludes — it is what makes
    VACCS's must-preorder coarser than VCCS's.

    It is not vacuous either.  [c ? (d ! v • 𝟘)] belongs to no such class:
    a mute configuration can only ever emit what its bag held from the
    start, so it would have to offer [d] straight away, and [d ? ①]
    separates the two. *)

Definition MuteSem (p : proc) : Prop :=
  exists l M, gStatic M /\ ochans ((g M) : proc) = []
           /\ ax_pre p (msgs l ‖ ((g M) : proc))
           /\ (msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ p.

Lemma MuteSem_of_MuteNF : forall p, MuteNF p -> MuteSem p.
Proof.
  intros p (l & M & HM & Hoc & Hpm & Hmp).
  exists l, M. split; [ exact HM | ]. split; [ exact Hoc | ].
  split; [ exact Hpm | ]. apply soundness_ax. exact Hmp.
Qed.

Lemma MuteSem_gsum : forall (M : gproc),
  gStatic M -> ochans ((g M) : proc) = [] -> MuteSem ((g M) : proc).
Proof.
  intros M HM Hoc. apply MuteSem_of_MuteNF. apply MuteNF_gsum; assumption.
Qed.

Lemma MuteSem_cfg : forall (l : list TypeOfActions) (M : gproc),
  gStatic M -> ochans ((g M) : proc) = [] -> MuteSem (msgs l ‖ ((g M) : proc)).
Proof.
  intros l M HM Hoc. apply MuteSem_of_MuteNF. apply MuteNF_cfg; assumption.
Qed.

Lemma MuteSem_msg : forall (c : ChannelData) (v : ValueData) (p : proc),
  MuteSem p -> MuteSem (((c ! v • 𝟘) : proc) ‖ p).
Proof.
  intros c v p (l & M & HM & Hoc & Hpm & Hmp).
  exists ((c,v) :: l), M. split; [ exact HM | ]. split; [ exact Hoc | ].
  assert (Hc : (((c ! v • 𝟘) : proc) ‖ (msgs l ‖ ((g M) : proc)))
                 ≡* (msgs ((c,v) :: l) ‖ ((g M) : proc))).
  { simpl. symmetry. apply cgr_par_assoc. }
  split.
  - eapply ax_trans; [ apply ax_par; [ apply ax_refl | exact Hpm ] | ].
    apply ax_cgr. exact Hc.
  - intros t Ht.
    apply (must_i_par_compat_r ((c ! v • 𝟘) : proc) _ _ Hmp).
    apply (proj1 (must_i_cgr _ _ Hc)). exact Ht.
Qed.

Lemma MuteSem_bag : forall (l : list TypeOfActions) (p : proc),
  MuteSem p -> MuteSem (msgs l ‖ p).
Proof.
  induction l as [|a l IH]; intros p Hp; simpl.
  - destruct Hp as (l0 & M & HM & Hoc & Hpm & Hmp).
    exists l0, M. split; [ exact HM | ]. split; [ exact Hoc | ].
    assert (Hc : (((g (𝟘 : gproc)) : proc) ‖ p) ≡* p).
    { etransitivity; [ apply cgr_par_com | apply cgr_par_nil ]. }
    split.
    + eapply ax_trans; [ apply ax_cgr; exact Hc | exact Hpm ].
    + intros t Ht. apply (proj1 (must_i_cgr _ _ Hc)). apply Hmp. exact Ht.
  - destruct a as (c,v).
    assert (Hrec : MuteSem (msgs l ‖ p)) by (apply IH; exact Hp).
    assert (Hm := MuteSem_msg c v (msgs l ‖ p) Hrec).
    destruct Hm as (l0 & M & HM & Hoc & Hpm & Hmp).
    exists l0, M. split; [ exact HM | ]. split; [ exact Hoc | ].
    assert (Hc : ((((c ! v • 𝟘) : proc) ‖ msgs l) ‖ p)
                   ≡* (((c ! v • 𝟘) : proc) ‖ (msgs l ‖ p)))
      by (apply cgr_par_assoc).
    split.
    + eapply ax_trans; [ apply ax_cgr; exact Hc | exact Hpm ].
    + intros t Ht. apply (proj1 (must_i_cgr _ _ Hc)). apply Hmp. exact Ht.
Qed.

(** * THE RESTRICTED RECURSION

    [completeness_from_step]'s frame is unrestricted: its recursive
    premise speaks about *every* pair at a smaller right-hand side, so it
    cannot carry the class the step actually preserves — [MuteNF] on the
    left, ν-freedom on the right.  Both closures are now proved
    ([MuteSem_msg]/[MuteSem_bag] one side, [normal_form_deep] and
    [noresd_lts_target] the other), so the recursion can be built
    directly on [size q], **restricted to the class**.

    [DomOkD] is [DomOk] with the witness additionally deeply ν-free.
    That costs nothing: the witness is a reduct of the *original*
    right-hand side, and [NoResD] travels along transitions
    ([noresd_lts_target]) and along runs ([noresd_wt_target]). *)

Definition DomOkD (q0 q' : proc) : Prop :=
  exists r', Static r' /\ NoResD r' /\ (size r' < size q0)%nat
             /\ ax_pre q' r' /\ ax_pre r' q'.

Lemma domokd_of_domsim : forall (q0 q : proc) a r,
  Static q0 -> NoResD q0 -> domsim q0 q -> lts q a r -> DomOkD q0 r.
Proof.
  intros q0 q a r Hst Hnr Hd Hl.
  destruct (ds_s Hd a r Hl) as (r' & Hr' & Hds).
  exists r'. split; [ | split; [ | split; [ | split ] ] ].
  - eapply Static_preserved_by_lts; [ exact Hst | exact Hr' ].
  - eapply noresd_lts_target; [ exact Hst | exact Hnr | exact Hr' ].
  - eapply Static_lts_decrease; [ exact Hst | exact Hr' ].
  - exact (ds_r Hds).
  - exact (ds_l Hds).
Qed.

Lemma DomOkD_cgr : forall (q0 q1 q2 : proc),
  DomOkD q0 q1 -> q1 ≡* q2 -> DomOkD q0 q2.
Proof.
  intros q0 q1 q2 (r' & Hr' & Hnr & Hlt & Hqr & Hrq) Hc.
  exists r'. split; [ exact Hr' | ]. split; [ exact Hnr | ].
  split; [ exact Hlt | ]. split.
  - eapply ax_trans; [ apply ax_cgr_sym; exact Hc | exact Hqr ].
  - eapply ax_trans; [ exact Hrq | apply ax_cgr; exact Hc ].
Qed.

Lemma domokd_of_domsim_wt : forall (q0 q : proc) mu s r,
  Static q0 -> NoResD q0 -> domsim q0 q -> q ⟹[mu :: s] r -> DomOkD q0 r.
Proof.
  intros q0 q mu s r Hst Hnr Hd Hw.
  destruct (domsim_wt q (mu :: s) r Hw q0 Hd) as (r' & Hr' & Hds).
  exists r'. split; [ | split; [ | split; [ | split ] ] ].
  - eapply Static_preserved_by_wt; [ exact Hst | exact Hr' ].
  - eapply noresd_wt_target; [ exact Hst | exact Hnr | exact Hr' ].
  - eapply wt_act_size_lt; [ exact Hst | exact Hr' ].
  - exact (ds_r Hds).
  - exact (ds_l Hds).
Qed.

Lemma domokd_of_domsim_wt' : forall (q0 q : proc) s r,
  Static q0 -> NoResD q0 -> domsim q0 q -> q ⟹[s] r -> s <> [] -> DomOkD q0 r.
Proof.
  intros q0 q s r Hst Hnr Hd Hw Hs. destruct s as [|mu s0]; [ contradiction | ].
  eapply domokd_of_domsim_wt; eassumption.
Qed.

Lemma domokd_of_subbag_input : forall (q0 : proc) (l2 l' : list TypeOfActions)
    (N : gproc) c v Q',
  Static q0 -> NoResD q0 -> domsim q0 (msgs l2 ‖ ((g N) : proc)) ->
  subbag l' l2 -> lts ((g N) : proc) (ActExt (ActIn (c,v))) Q' ->
  DomOkD q0 (msgs l' ‖ Q').
Proof.
  intros q0 l2 l' N c v Q' Hst Hnr Hd Hsub Hin.
  destruct (cfg_reach_subbag l' l2 ((g N) : proc) Hsub) as (u & r & Hr & Hcr).
  assert (Hstep : lts (msgs l' ‖ ((g N) : proc)) (ActExt (ActIn (c,v)))
                      (msgs l' ‖ Q')) by (apply lts_parR; exact Hin).
  assert (Hcr' : (msgs l' ‖ ((g N) : proc)) ≡* r) by (symmetry; exact Hcr).
  destruct (cgr_lts_transfer _ r _ _ Hcr' Hstep) as (x & Hx & Hcx).
  assert (Hbig : (msgs l2 ‖ ((g N) : proc))
                   ⟹[map ActOut u ++ (ActIn (c,v) :: nil)] x).
  { eapply wt_concat; [ exact Hr | eapply wt_act; [ exact Hx | apply wt_nil ] ]. }
  eapply DomOkD_cgr; [ | symmetry; exact Hcx ].
  eapply domokd_of_domsim_wt';
    [ exact Hst | exact Hnr | exact Hd | exact Hbig | ].
  destruct u as [|a u0]; simpl; discriminate.
Qed.

(** The step, in the restricted frame.  Compare [completeness_step_mute]:
    the recursive premise now *gets* [MuteNF p'] and [NoResD q'] as well,
    and the proof *supplies* them at the four call sites — the left ones
    from [MuteSem_gsum]/[MuteSem_msg]/[MuteSem_bag], the right ones from
    [normal_form_deep]'s [gNoResD N] carried through [DomOkD]. *)

Theorem completeness_step_deep :
  forall (q : proc) (l1 : list TypeOfActions) (M : gproc),
  Static q -> NoResD q -> gStatic M -> ochans ((g M) : proc) = [] ->
  (msgs l1 ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  (forall p' q', Static p' -> MuteSem p' -> Static q' -> NoResD q' ->
     (size q' < size q)%nat -> p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
  ax_pre (msgs l1 ‖ ((g M) : proc)) q.
Proof.
  intros q l1 M Hq Hnr HM Hoc Hpre IH.
  destruct (normal_form_deep q Hq Hnr) as (l2 & N & HN & HNd & Hd).
  eapply ax_trans; [ | exact (ds_r Hd) ].
  apply (completeness_cfg_mute_ok MuteSem (DomOkD q) l1 l2 M N); try assumption.
  - intros l p Hp. apply MuteSem_bag. exact Hp.
  - intros c v p Hp. apply MuteSem_msg. exact Hp.
  - apply MuteSem_gsum; assumption.
  - intros a r Hr. eapply domokd_of_domsim; eassumption.
  - intros q1 q2 H1 H2. eapply DomOkD_cgr; eassumption.
  - intros l' c v Q' Hsub Hin. eapply domokd_of_subbag_input; eassumption.
  - intros t Ht. apply (soundness_ax _ _ (ds_l Hd)). apply Hpre. exact Ht.
  - intros p' q' Hp' Hlp' Hq' (r' & Hr' & Hnrr & Hlt & Hqr & Hrq) Hs.
    eapply ax_trans; [ | exact Hrq ].
    apply IH; try assumption.
    intros t Ht. apply (soundness_ax _ _ Hqr). apply Hs. exact Ht.
Qed.

(** …and the recursion itself, on [size q], **inside the class**. *)

Theorem completeness_deep :
  forall (q p : proc), Static q -> NoResD q -> Static p -> MuteSem p ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intro q. induction q as [q IHq] using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros p Hq Hnr Hp Hm Hpre.
  destruct Hm as (l1 & M & HM & Hoc & Hpm & Hmp).
  eapply ax_trans; [ exact Hpm | ].
  apply completeness_step_deep; try assumption.
  - intros t Ht. apply Hpre. apply Hmp. exact Ht.
  - intros p' q' Hsp' Hmp' Hsq' Hnq' Hlt Hs.
    apply (IHq q' Hlt p' Hsq' Hnq' Hsp' Hmp' Hs).
Qed.

(** The usable form: **a mute configuration below any deeply ν-free
    [Static] process is derivably below it** — no side condition, no
    induction hypothesis to supply. *)

Corollary completeness_deep_cfg :
  forall (l : list TypeOfActions) (M : gproc) (q : proc),
  Static q -> NoResD q -> gStatic M -> ochans ((g M) : proc) = [] ->
  (msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  ax_pre (msgs l ‖ ((g M) : proc)) q.
Proof.
  intros l M q Hq Hnr HM Hoc Hpre.
  apply completeness_deep; try assumption.
  - constructor; [ apply msgs_Static | apply static_g; exact HM ].
  - apply MuteSem_cfg; assumption.
Qed.

Lemma NoResD_NoRes : forall p, NoResD p -> NoRes p.
Proof.
  induction p as [p1 IH1 p2 IH2 | i | x P IH | C P IH1 Q IH2 | c v | P IH | M];
    intros H; simpl in *; try exact I.
  - destruct H as (H1 & H2). split; [ apply IH1 | apply IH2 ]; assumption.
  - apply IH. exact H.
  - destruct H as (H1 & H2). split; [ apply IH1 | apply IH2 ]; assumption.
  - contradiction.
Qed.

(** …and its process-level reading, where both sides are given as plain
    [Static] terms: a ν-free process that can never emit is derivably
    below any ν-free process it is semantically below. *)

Corollary completeness_mute_deep :
  forall (p q : proc), Static p -> Static q -> NoResD p -> NoResD q ->
  ochans p = [] -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros p q Hp Hq Hnp Hnq Hoc Hpre.
  apply completeness_deep; try assumption.
  apply MuteSem_of_MuteNF.
  apply MuteNF_of_mute; try assumption.
  apply NoResD_NoRes. exact Hnp.
Qed.


(** * WIDENING THE LEFT-HAND CLASS: [MuteG]

    [MuteNF_of_mute] asks [ochans p = []] — the *whole* process mute.
    That is stricter than [completeness_deep_cfg] needs: what has to be
    mute is the **guarded sum** of the normal form, not the bag.  A
    pending message contributes to the bag and never to the sum, so

        MuteG (c ! v • 𝟘) = True

    while [ochans (c ! v • 𝟘) = [c]].  [MuteG] is the resulting criterion
    — syntactic, decidable, and strictly more permissive: it admits every
    configuration with pending messages, which is the shape the left-hand
    side actually has. *)

Fixpoint MuteG (p : proc) : Prop :=
match p with
| P ‖ Q => MuteG P /\ MuteG Q
| pr_var _ => True
| rec _ • P => MuteG P
| If _ Then P Else Q => MuteG P /\ MuteG Q
| _ ! _ • 𝟘 => True
| ν P => MuteG P
| g M => gochans M = []
end.

Lemma MuteG_of_mute : forall p, NoResD p -> ochans p = [] -> MuteG p.
Proof.
  induction p as [p1 IH1 p2 IH2 | i | x P IH | C P IH1 Q IH2 | c v | P IH | M];
    intros Hnr Hoc; simpl in *; try exact I.
  - apply app_eq_nil in Hoc as (H1 & H2). destruct Hnr as (Hn1 & Hn2).
    split; [ apply IH1 | apply IH2 ]; assumption.
  - apply IH; assumption.
  - apply app_eq_nil in Hoc as (H1 & H2). destruct Hnr as (Hn1 & Hn2).
    split; [ apply IH1 | apply IH2 ]; assumption.
  - contradiction.
  - exact Hoc.
Qed.

(** …and the normal form carries the three invariants at once: [gStatic],
    deep ν-freedom, and mutity of the sum.  Same proof as
    [normal_form_deep] with one more conjunct, the [‖] case going through
    [gochans_ext_nil]/[gochans_ext_r_nil] exactly as
    [normal_form_nores_mute] does. *)

Theorem normal_form_deep_mute : forall p, Static p -> NoResD p -> MuteG p ->
  exists l M, gStatic M /\ gNoResD M /\ ochans ((g M) : proc) = []
           /\ domsim p (msgs l ‖ ((g M) : proc)).
Proof.
  intro p. induction p as [p IHp] using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs Hnr Hmu. destruct p as [p1 p2|x|x p0|E p1 p2|c v|p0|M].
  - inversion Hs; subst. destruct Hnr as (Hn1 & Hn2).
    destruct Hmu as (Hu1 & Hu2).
    destruct (IHp p1 ltac:(simpl; lia) H1 Hn1 Hu1)
      as (l1 & M1 & HM1 & Hd1 & Hm1 & Hs1).
    destruct (IHp p2 ltac:(simpl; lia) H2 Hn2 Hu2)
      as (l2 & M2 & HM2 & Hd2 & Hm2 & Hs2).
    exists (l1 ++ l2), (ext M1 M2 + ext_r M2 M1).
    split; [ constructor; [ apply ext_gStatic | apply ext_r_gStatic ]; assumption | ].
    split; [ split; [ apply gNoResD_ext | apply gNoResD_ext_r ]; assumption | ].
    split.
    { simpl. simpl in Hm1, Hm2.
      rewrite (gochans_ext_nil M1 M2 Hm1 Hm2).
      rewrite (gochans_ext_r_nil M2 M1 Hm2 Hm1). reflexivity. }
    assert (Hc : ((msgs l1 ‖ ((g M1) : proc)) ‖ (msgs l2 ‖ ((g M2) : proc)))
                 ≡* (msgs (l1 ++ l2) ‖ (((g M1) : proc) ‖ ((g M2) : proc)))).
    { etransitivity; [ apply cgr_par_exchange | ].
      apply cgr_fullpar; [ symmetry; apply msgs_app | reflexivity ]. }
    eapply domsim_trans; [ apply domsim_par; [ exact Hs1 | exact Hs2 ] | ].
    eapply domsim_trans; [ apply domsim_cgr; exact Hc | ].
    apply domsim_par; [ apply domsim_refl | apply domsim_expansion ].
  - inversion Hs.
  - inversion Hs.
  - destruct (Eval_Eq 0 E) as [[|]|] eqn:HE;
      [ | | exfalso; eapply Eval_Eq_0_not_none; exact HE ].
    + inversion Hs; subst. destruct Hnr as (Hn1 & Hn2). destruct Hmu as (Hu1 & Hu2).
      destruct (IHp p1 ltac:(simpl; lia) H1 Hn1 Hu1) as (l & M & HM & Hdd & Hm & Hd).
      exists l, M. split; [ exact HM | ]. split; [ exact Hdd | ].
      split; [ exact Hm | ].
      eapply domsim_trans; [ apply domsim_cgr; apply cgr_if_true; exact HE | exact Hd ].
    + inversion Hs; subst. destruct Hnr as (Hn1 & Hn2). destruct Hmu as (Hu1 & Hu2).
      destruct (IHp p2 ltac:(simpl; lia) H3 Hn2 Hu2) as (l & M & HM & Hdd & Hm & Hd).
      exists l, M. split; [ exact HM | ]. split; [ exact Hdd | ].
      split; [ exact Hm | ].
      eapply domsim_trans; [ apply domsim_cgr; apply cgr_if_false; exact HE | exact Hd ].
  - exists [(c,v)], 𝟘. split; [ constructor | ]. split; [ exact I | ].
    split; [ reflexivity | ]. simpl.
    apply domsim_cgr. etransitivity; [ apply cgr_par_nil_rev | ].
    apply cgr_fullpar; [ apply cgr_par_nil_rev | reflexivity ].
  - simpl in Hnr. contradiction.
  - inversion Hs; subst. exists [], M. split; [ assumption | ].
    split; [ exact Hnr | ]. split; [ exact Hmu | ]. simpl.
    apply domsim_cgr. etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ].
Qed.

Corollary MuteNF_of_muteG : forall p,
  Static p -> NoResD p -> MuteG p -> MuteNF p.
Proof.
  intros p Hs Hnr Hmu.
  destruct (normal_form_deep_mute p Hs Hnr Hmu) as (l & M & HM & _ & Hoc & Hd).
  exists l, M. split; [ exact HM | ]. split; [ exact Hoc | ].
  split; [ exact (ds_l Hd) | exact (ds_r Hd) ].
Qed.

(** ** Completeness on the fragment, at the process level

    Both sides plain [Static] terms; the left's guarded sums mute, both
    sides deeply ν-free.  [completeness_mute_deep] is the instance at
    [ochans p = []], which [MuteG_of_mute] shows is strictly stronger. *)

Theorem completeness_muteG : forall (p q : proc),
  Static p -> Static q -> NoResD p -> NoResD q -> MuteG p ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros p q Hp Hq Hnp Hnq Hmu Hpre.
  apply completeness_deep; try assumption.
  apply MuteSem_of_MuteNF. apply MuteNF_of_muteG; assumption.
Qed.

(** [MuteSem] transports along the *same* asymmetric pair it is defined
    by — [⊢] one way, the semantics the other — so any process squeezed
    that way against a member is itself a member. *)

Lemma MuteSem_transport : forall (p q : proc),
  ax_pre q p -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> MuteSem p -> MuteSem q.
Proof.
  intros p q Hqp Hpq (l & M & HM & Hoc & Hpm & Hmp).
  exists l, M. split; [ exact HM | ]. split; [ exact Hoc | ].
  split.
  - eapply ax_trans; [ exact Hqp | exact Hpm ].
  - intros t Ht. apply Hpq. apply Hmp. exact Ht.
Qed.

(** …and it is **closed under parallel composition**.  Both halves are
    the expansion law read in its two directions: [ax_expansion_l] for
    the derivation, [must_i_expansion_r] for the semantics — and mutity
    survives because [gochans_ext_nil]/[gochans_ext_r_nil] say the
    expansion of two mute sums is mute.

    So a mute process beside any number of copycats is in the class. *)

Lemma MuteSem_par : forall (p q : proc),
  MuteSem p -> MuteSem q -> MuteSem (p ‖ q).
Proof.
  intros p q (lp & Mp & HMp & Hop & Hpm & Hmp) (lq & Mq & HMq & Hoq & Hqm & Hmq).
  exists (lp ++ lq), (ext Mp Mq + ext_r Mq Mp).
  split; [ constructor; [ apply ext_gStatic | apply ext_r_gStatic ]; assumption | ].
  split.
  { simpl. simpl in Hop, Hoq.
    rewrite (gochans_ext_nil Mp Mq Hop Hoq).
    rewrite (gochans_ext_r_nil Mq Mp Hoq Hop). reflexivity. }
  assert (Hc : ((msgs lp ‖ ((g Mp) : proc)) ‖ (msgs lq ‖ ((g Mq) : proc)))
               ≡* (msgs (lp ++ lq) ‖ (((g Mp) : proc) ‖ ((g Mq) : proc)))).
  { etransitivity; [ apply cgr_par_exchange | ].
    apply cgr_fullpar; [ symmetry; apply msgs_app | reflexivity ]. }
  split.
  - eapply ax_trans; [ apply ax_par; [ exact Hpm | exact Hqm ] | ].
    eapply ax_trans; [ apply ax_cgr; exact Hc | ].
    apply ax_par; [ apply ax_refl | apply ax_expansion_l ].
  - intros t Ht.
    apply (must_i_par_compat2 _ _ _ _ Hmp Hmq).
    apply (proj1 (must_i_cgr _ _ Hc)).
    apply (must_i_par_compat_r (msgs (lp ++ lq)) _ _ (must_i_expansion_r Mp Mq)).
    exact Ht.
Qed.

(** Two consequences of [MuteSem_transport], both by [ax_cgr]: the class
    is stable under structural congruence, and under a conditional
    ([Eval_Eq 0] never fails, so a conditional is congruent to a
    branch). *)

Lemma MuteSem_cgr : forall (p q : proc), p ≡* q -> MuteSem q -> MuteSem p.
Proof.
  intros p q Hc Hq. eapply MuteSem_transport; [ | | exact Hq ].
  - apply ax_cgr. exact Hc.
  - exact (proj1 (must_i_cgr _ _ Hc)).
Qed.

Lemma MuteSem_if : forall E (p q : proc),
  MuteSem p -> MuteSem q -> MuteSem (If E Then p Else q).
Proof.
  intros E p q Hp Hq.
  destruct (Eval_Eq 0 E) as [[|]|] eqn:HE;
    [ | | exfalso; eapply Eval_Eq_0_not_none; exact HE ].
  - eapply MuteSem_cgr; [ apply cgr_if_true; exact HE | exact Hp ].
  - eapply MuteSem_cgr; [ apply cgr_if_false; exact HE | exact Hq ].
Qed.

(** The class is genuinely wider than the syntactic criterion: the
    **copycat** is in it, and [MuteG] rejects it (its guard's
    continuation emits, on its own channel).  [ax_ccat_l] supplies the
    [⊢] half, [must_i_ccat_r] the semantic half — and the *converse*
    derivation [⊢ g 𝟘 ⊑ ccat c], which [MuteNF] would need, is not used
    anywhere. *)

Lemma MuteSem_ccat : forall c, MuteSem (ccat c).
Proof.
  intro c. exists [], 𝟘. split; [ constructor | ]. split; [ reflexivity | ].
  assert (Hc : (msgs nil ‖ ((g (𝟘 : gproc)) : proc)) ≡* ((g (𝟘 : gproc)) : proc)).
  { simpl. etransitivity; [ apply cgr_par_com | apply cgr_par_nil ]. }
  split.
  - eapply ax_trans; [ apply ax_ccat_l | apply ax_cgr_sym; exact Hc ].
  - intros t Ht. apply (must_i_ccat_r c).
    apply (proj2 (must_i_cgr _ _ Hc)). exact Ht.
Qed.

(** * THE RIGHT-HAND CLASS, WEAKENED TOO: [ResFree]

    Deep ν-freedom is asked of the right because [normal_form_deep] has
    to return a **bare configuration** for the matching machinery, and
    because [NoResD] is what survives the reducts.  But the top level
    only ever needs *some* deeply ν-free process that the right is
    [⊢]-equal to — the recursion then runs there. *)

Definition ResFree (q : proc) : Prop :=
  exists q', Static q' /\ NoResD q' /\ ax_pre q q' /\ ax_pre q' q.

Lemma ResFree_of_NoResD : forall q, Static q -> NoResD q -> ResFree q.
Proof.
  intros q Hq Hnr. exists q. split; [ exact Hq | ]. split; [ exact Hnr | ].
  split; apply ax_refl.
Qed.

(** It is strictly weaker: [ax_res_normalize_l]/[_r] retire a ν over a
    guarded sum, so e.g. [ν (g 𝟘)] is [ResFree] and not [NoResD].

    It does **not** retire ν in general, and it is worth being precise
    about why: [resg] pushes the ν into each guard's *continuation*
    ([resg (c ? p) = c' ? (ν p)]), so one application makes the spine
    ν-free and leaves ν's underneath.  Eliminating them all needs the
    construction re-applied inside continuations — a fuelled recursion on
    [size] — and, on top of that, a treatment of a **message under a ν**
    ([ν ((bvar 0) ! v • 𝟘 ‖ g M)]), which no law of the system moves. *)

Lemma ResFree_res_nil : ResFree (ν ((g (𝟘 : gproc)) : proc)).
Proof.
  exists ((g (𝟘 : gproc)) : proc). split; [ repeat constructor | ].
  split; [ exact I | ].
  split; [ apply (ax_res_normalize_l 𝟘) | apply (ax_res_normalize_r 𝟘) ].
Qed.

(** Completeness on the class, at the process level.  Note what is *not*
    asked: nothing about [p] beyond [MuteSem], in particular no ν-freedom
    — [p] enters only through its mute configuration. *)

Corollary completeness_muteSem : forall (p q : proc),
  Static p -> Static q -> NoResD q -> MuteSem p ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros p q Hp Hq Hnq Hmu Hpre. apply completeness_deep; assumption.
Qed.

(** [ResFree] is closed under parallel composition — [ax_par] on both
    sides, and [NoResD] of a product is [NoResD] of the factors. *)

Lemma ResFree_par : forall (p q : proc), ResFree p -> ResFree q -> ResFree (p ‖ q).
Proof.
  intros p q (p' & Hsp & Hnp & H1 & H2) (q' & Hsq & Hnq & H3 & H4).
  exists (p' ‖ q'). split; [ constructor; assumption | ].
  split; [ split; assumption | ].
  split; apply ax_par; assumption.
Qed.

(** * A ν CASE BEYOND [resg]: THE CLOSED HANDSHAKE

    [resg] retires a ν over a guarded sum by pushing it into the guards'
    continuations, so it never removes ν outright.  There is a second,
    independent way in, and it is [ax_glb_tau]: a process whose *whole*
    behaviour is one deterministic internal step is [⊢]-equal to a bare
    [𝛕]-guard, **in both directions** — [ax_tau_step] one way, and
    [ax_glb_tau] the other, its output and input premises being vacuous.

    That is exactly the shape of a ν-block containing a closed
    handshake, [ν ((bvar 0) ! v • 𝟘 ‖ g ((bvar 0) ? P))]: the message
    cannot escape (its channel is the restricted one) and cannot be
    supplied from outside, so the only thing that can happen is the
    delivery.  It is the case no law of the system moves — and here it
    is, moved. *)

Lemma ax_tau_only_below : forall (q X Y : proc),
  lts q τ X ->
  (forall a z, lts q (ActExt a) z -> False) ->
  ax_pre X Y ->
  ax_pre q ((g ((𝛕 • Y) : gproc)) : proc).
Proof.
  intros q X Y Hl Hnoext HXY. apply ax_glb_tau.
  - exists Y. apply lts_tau.
  - intros q' Hq'. inversion Hq'; subst.
    eapply ax_trans; [ apply ax_tau_step; exact Hl | exact HXY ].
  - intros c v q'' Hq''. inversion Hq''.
  - intros c v q'' Hq''. inversion Hq''.
  - intros c v p'' q'' Hp'' Hq''. inversion Hq''.
Qed.

Lemma ax_tau_only_above : forall (q X Y : proc),
  lts q τ X ->
  (forall z, lts q τ z -> z = X) ->
  (forall a z, lts q (ActExt a) z -> False) ->
  ax_pre Y X ->
  ax_pre ((g ((𝛕 • Y) : gproc)) : proc) q.
Proof.
  intros q X Y Hl Hdet Hnoext HYX. apply ax_glb_tau.
  - exists X. exact Hl.
  - intros q' Hq'. rewrite (Hdet q' Hq').
    eapply ax_trans; [ apply ax_tau_step; apply lts_tau | exact HYX ].
  - intros c v q'' Hq''. exfalso. eapply Hnoext. exact Hq''.
  - intros c v q'' Hq''. exfalso. eapply Hnoext. exact Hq''.
  - intros c v p'' q'' Hp'' Hq''. exfalso. eapply Hnoext. exact Hq''.
Qed.

Lemma ResFree_tau_only : forall (q X : proc),
  lts q τ X ->
  (forall z, lts q τ z -> z = X) ->
  (forall a z, lts q (ActExt a) z -> False) ->
  ResFree X -> ResFree q.
Proof.
  intros q X Hl Hdet Hnoext (X' & HsX' & HnX' & HXX' & HX'X).
  exists ((g ((𝛕 • X') : gproc)) : proc).
  split; [ apply static_g; constructor; exact HsX' | ].
  split; [ exact HnX' | ].
  split.
  - eapply ax_tau_only_below; eassumption.
  - eapply ax_tau_only_above; eassumption.
Qed.

(** …and the instance, machine-checked: the **closed handshake**.  Its
    only transition is the delivery — the message cannot escape (its
    channel is the restricted one, and [VarC_action_add 1] never produces
    [bvar 0]) and the guard cannot be fed from outside — so [ν] comes off
    it, which [resg] alone never does. *)

Lemma ResFree_handshake : forall (P : proc) (v : ValueData),
  ResFree (ν (((g (𝟘 : gproc)) : proc) ‖ (subst_in_proc 0 v P))) ->
  ResFree (ν ((((bvar 0) ! v • 𝟘) : proc)
               ‖ ((g (((bvar 0) ? P) : gproc)) : proc))).
Proof.
  intros P v HX.
  eapply ResFree_tau_only; [ | | | exact HX ].
  - apply lts_res_tau. eapply lts_comL; [ apply lts_output | apply lts_input ].
  - intros z Hz. inversion Hz; subst. inversion H0; subst.
    + inversion H2; subst. inversion H3; subst. reflexivity.
    + inversion H2.
    + inversion H4.
    + inversion H4.
  - intros a z Hz. inversion Hz; subst. inversion H1; subst.
    + inversion H4; subst. destruct a as [[c0 v0]|[c0 v0]]; simpl in *.
      * discriminate.
      * injection H as H H'. destruct c0 as [j|c1]; simpl in H; discriminate.
    + inversion H4; subst. destruct a as [[c0 v1]|[c0 v1]]; simpl in *.
      * injection H as H H'. destruct c0 as [j|c1]; simpl in H; discriminate.
      * discriminate.
Qed.

(** …and the deterministic hypothesis is not needed either.  A process
    with **no visible transition at all** is [⊢]-equal to the *internal
    choice of its τ-reducts* — [ax_ichoice_glb] and [ax_tau_step] one
    way, [ax_glb_tau] and [ax_ichoice_below] the other.  So a closed ν
    block is retired whatever its internal branching, provided its
    reducts are.

    The reducts are collected as a **list** through [lts_set], which the
    VACCS instance exposes as a [gset] — no choice principle is needed,
    and [resfree_list] turns "every reduct is [ResFree]" into an actual
    list of ν-free counterparts (an elimination of [Prop]-existentials
    into a [Prop] goal, so no sort violation). *)

Lemma ichoice_NoResD : forall (L : list proc),
  Forall NoResD L -> gNoResD (ichoice L).
Proof.
  induction L as [|p L IH]; intros Hall.
  { exact I. }
  inversion Hall as [|? ? Hp Hrest]; subst.
  destruct L as [|p2 L2]; simpl.
  { split; exact Hp. }
  split; [ exact Hp | apply IH; exact Hrest ].
Qed.

Lemma resfree_list : forall (L : list proc),
  (forall x, In x L -> ResFree x) ->
  exists L', (forall x', In x' L' -> Static x' /\ NoResD x')
          /\ (forall x, In x L -> exists x', In x' L' /\ ax_pre x x' /\ ax_pre x' x)
          /\ (forall x', In x' L' -> exists x, In x L /\ ax_pre x x' /\ ax_pre x' x)
          /\ (L <> nil -> L' <> nil).
Proof.
  induction L as [|x L IH]; intro Hall.
  { exists nil. split; [ contradiction | ]. split; [ contradiction | ].
    split; [ contradiction | ]. intro Hne. contradiction. }
  destruct (Hall x (or_introl eq_refl)) as (x' & Hsx' & Hnx' & H1 & H2).
  destruct (IH (fun y Hy => Hall y (or_intror Hy))) as (L' & Hst & Hfw & Hbw & _).
  exists (x' :: L').
  split; [ intros z [Hz|Hz]; [ subst; split; assumption | apply Hst; exact Hz ] | ].
  split.
  { intros y [Hy|Hy].
    { subst. exists x'. split; [ left; reflexivity | split; assumption ]. }
    destruct (Hfw y Hy) as (y' & Hy' & Ha & Hb).
    exists y'. split; [ right; exact Hy' | split; assumption ]. }
  split.
  { intros z [Hz|Hz].
    { subst. exists x. split; [ left; reflexivity | split; assumption ]. }
    destruct (Hbw z Hz) as (y & Hy & Ha & Hb).
    exists y. split; [ right; exact Hy | split; assumption ]. }
  intro Hne. discriminate.
Qed.

Lemma ResFree_tau_closed : forall (q : proc),
  (exists z, lts q τ z) ->
  (forall a z, lts q (ActExt a) z -> False) ->
  (forall x, lts q τ x -> ResFree x) ->
  ResFree q.
Proof.
  intros q (z0 & Hz0) Hnoext Hres.
  assert (Hne : tau_list q <> nil).
  { intro He. assert (Hin : In z0 (tau_list q)) by (apply tau_list_spec; exact Hz0).
    rewrite He in Hin. contradiction. }
  destruct (resfree_list (tau_list q)
              (fun x Hx => Hres x (proj1 (tau_list_spec q x) Hx)))
    as (L' & Hst & Hfw & Hbw & Hne').
  exists ((g (ichoice L')) : proc).
  split.
  { apply static_g. apply ichoice_gStatic. apply Forall_forall.
    intros z Hz. apply Hst. exact Hz. }
  split.
  { apply ichoice_NoResD. apply Forall_forall.
    intros z Hz. apply Hst. exact Hz. }
  split.
  { apply ax_ichoice_glb; [ apply Hne'; exact Hne | ].
    intros y Hy. destruct (Hbw y Hy) as (x & Hx & Ha & Hb).
    eapply ax_trans; [ apply ax_tau_step; apply tau_list_spec; exact Hx | exact Ha ]. }
  apply ax_glb_tau.
  { exists z0. exact Hz0. }
  { intros q' Hq'.
    assert (Hin : In q' (tau_list q)) by (apply tau_list_spec; exact Hq').
    destruct (Hfw q' Hin) as (y' & Hy' & Ha & Hb).
    eapply ax_trans; [ apply ax_ichoice_below; exact Hy' | exact Hb ]. }
  { intros c v q'' Hq''. exfalso. eapply Hnoext. exact Hq''. }
  { intros c v q'' Hq''. exfalso. eapply Hnoext. exact Hq''. }
  { intros c v p'' q'' Hp'' Hq''. exfalso. eapply Hnoext. exact Hq''. }
Qed.

(** The two remaining structural closures, both by [ax_cgr]: a
    conditional is congruent to the branch [Eval_Eq 0] selects (it never
    fails — [Eval_Eq_0_not_none]), and a restriction on a channel the
    body does not use is vacuous ([cgr_res_newvarc]). *)

Lemma ResFree_if : forall E (p q : proc),
  ResFree p -> ResFree q -> ResFree (If E Then p Else q).
Proof.
  intros E p q Hp Hq.
  destruct (Eval_Eq 0 E) as [[|]|] eqn:HE;
    [ | | exfalso; eapply Eval_Eq_0_not_none; exact HE ].
  - destruct Hp as (p' & Hs & Hn & H1 & H2). exists p'.
    split; [ exact Hs | ]. split; [ exact Hn | ].
    assert (Hc : (If E Then p Else q) ≡* p) by (apply cgr_if_true; exact HE).
    split; [ eapply ax_trans; [ apply ax_cgr; exact Hc | exact H1 ]
           | eapply ax_trans; [ exact H2 | apply ax_cgr_sym; exact Hc ] ].
  - destruct Hq as (q' & Hs & Hn & H1 & H2). exists q'.
    split; [ exact Hs | ]. split; [ exact Hn | ].
    assert (Hc : (If E Then p Else q) ≡* q) by (apply cgr_if_false; exact HE).
    split; [ eapply ax_trans; [ apply ax_cgr; exact Hc | exact H1 ]
           | eapply ax_trans; [ exact H2 | apply ax_cgr_sym; exact Hc ] ].
Qed.

Lemma ResFree_res_unused : forall (p : proc),
  ResFree p -> ResFree (ν (NewVarC 0 p)).
Proof.
  intros p (p' & Hs & Hn & H1 & H2). exists p'.
  split; [ exact Hs | ]. split; [ exact Hn | ].
  assert (Hc : ν (NewVarC 0 p) ≡* p) by apply cgr_res_newvarc.
  split; [ eapply ax_trans; [ apply ax_cgr; exact Hc | exact H1 ]
         | eapply ax_trans; [ exact H2 | apply ax_cgr_sym; exact Hc ] ].
Qed.

Lemma ResFree_cgr : forall (p q : proc), p ≡* q -> ResFree q -> ResFree p.
Proof.
  intros p q Hc (q' & Hs & Hn & H1 & H2). exists q'.
  split; [ exact Hs | ]. split; [ exact Hn | ].
  split; [ eapply ax_trans; [ apply ax_cgr; exact Hc | exact H1 ]
         | eapply ax_trans; [ exact H2 | apply ax_cgr_sym; exact Hc ] ].
Qed.

(** A fully closed instance, end to end: the handshake whose continuation
    is [𝟘].  Its residue [ν (𝟘 ‖ 𝟘)] has *no transition at all*, which
    neither [ResFree_tau_only] nor [ResFree_tau_closed] covers — but it
    is structurally congruent to [ν (g 𝟘)], which [resg] retires
    ([ResFree_res_nil]).  So the ν comes off the whole term, with nothing
    assumed. *)

Lemma ResFree_handshake_nil : forall (v : ValueData),
  ResFree (ν ((((bvar 0) ! v • 𝟘) : proc)
               ‖ ((g (((bvar 0) ? ((g (𝟘 : gproc)) : proc)) : gproc)) : proc))).
Proof.
  intro v. apply ResFree_handshake.
  eapply ResFree_cgr; [ | apply ResFree_res_nil ].
  apply cgr_res. apply cgr_par_nil.
Qed.

(** * WHY THE LAST ν CASE IS NOT PLUMBING

    What is left is a block with **both** visible and internal actions,
    e.g. [ν (g M)] where [M] guards a non-restricted channel.  The route
    is [resg], which turns it into a guarded sum whose guards carry
    [ν P] as continuations, and then rewriting those continuations in
    place — [ax_choice_tau] for a [𝛕]-guard, [ax_choice_input_ctx] for an
    input.

    The input is where it stops, and the obstruction is already on record
    in this development.  [ax_input] is the **omega rule**: it consumes
    one *open* continuation, so retiring the ν under an input guard needs
    a single open [Q] with [⊢ ν (P ^ v) ≂ Q ^ v] **at every [v]** — a
    *uniform* family.  Building [Q] means normalising [ν P] open, and
    normalisation is **not** substitution-equivariant:
    [VACCS_NormalForm.if_open_branch_depends_on_value] machine-checks
    that [Eval_Eq 0] picks a different branch of a conditional once a
    value is substituted, so no [normal_form_open] exists.

    [dom_u]/[sd_u] give uniform *transition* families, which is what made
    [normal_form_strong_u] possible; they do **not** give uniform
    [⊢]-equalities, and that is exactly the half needed here. *)

(** The top-level statement the two weakenings deliver: [Static] on both
    sides, [MuteSem] on the left, [ResFree] on the right. *)

Corollary completeness_resfree : forall (p q : proc),
  Static p -> Static q -> ResFree q -> MuteSem p ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros p q Hp Hq (q' & Hq' & Hnq' & Hqq' & Hq'q) Hmu Hpre.
  eapply ax_trans; [ | exact Hq'q ].
  apply completeness_muteSem; try assumption.
  intros t Ht. apply (soundness_ax _ _ Hqq'). apply Hpre. exact Ht.
Qed.

(** * A NEW ROUTE: THE RIGHT'S OUTPUTS ARE **WEAKLY** MATCHED ON THE LEFT

    The bag layer is the whole residue: Phase A ([ax_phaseA_direct] with
    [bigsum_certificate]) and the bare-sum step
    ([completeness_gsum_step_gen]) need **no** mutity — it enters only in
    [bag_incl_of_below] and [msgs_cancel_surplus], i.e. in relating the
    two bags.

    And [bag_incl_of_below]'s hypothesis is too strong for a reason worth
    naming: a left that emits only *after* a τ, like [g (𝛕 • (c!v•𝟘))],
    sits below [c!v•𝟘] while carrying an empty bag, so the *syntactic*
    inclusion [bag l2 ⊆ bag l1] genuinely fails.  What does not fail is
    the **weak** form:

        if [q] can emit on [c], so can [p], after some internal steps.

    That is proved here, and constructively, in its contrapositive form:
    "never weakly emits on [c]" travels **up** the preorder.

    The probe is the smallest one that sees an output: [𝛕•① + c?𝟘].  Its
    own τ makes [ex] free and reaches [①], so a server passes it exactly
    when it never offers [c] — an offer would trigger [com] and leave the
    server against the dead client [𝟘], which nothing survives
    ([no_client_nil]). *)

Lemma no_client_nil : forall (x : proc), Static x ->
  ~ (x must_pass ((g (𝟘 : gproc)) : proc)).
Proof.
  intros x Hst. assert (Ht := Static_terminate x Hst). revert Hst.
  induction Ht as [x Hstep IH]. intros Hst Hm.
  inversion Hm; subst.
  { inversion H. }
  destruct ex as (y & Hy). inversion Hy; subst.
  - eapply IH; [ exact l | | apply pt; exact l ].
    eapply Static_preserved_by_lts; [ exact Hst | exact l ].
  - inversion l.
  - inversion l2.
Qed.

Definition NoWeakOut (c : ChannelData) (p : proc) : Prop :=
  forall p1, p ⟹[[]] p1 -> forall w r, ~ lts p1 (ActExt (ActOut (c,w))) r.

Definition TSink (c : ChannelData) : proc :=
  g (((𝛕 • ((g (① : gproc)) : proc)) + (c ? ((g (𝟘 : gproc)) : proc))) : gproc).

Lemma TSink_not_good : forall c, ~ good_VACCS (TSink c).
Proof.
  intros c H. inversion H; subst. inversion H1. inversion H1.
  all: inversion H0.
Qed.

Lemma no_weak_out_passes : forall (p : proc) c,
  Static p -> NoWeakOut c p -> p must_pass (TSink c).
Proof.
  intros p c Hst. assert (Ht := Static_terminate p Hst). revert Hst.
  induction Ht as [p Hstep IH]. intros Hst Hnw.
  apply m_step.
  - apply TSink_not_good.
  - eexists. apply ParRight. apply lts_choiceL. apply lts_tau.
  - intros p' Hp'. apply IH.
    + exact Hp'.
    + eapply Static_preserved_by_lts; [ exact Hst | exact Hp' ].
    + intros p1 Hp1 w r Hr. eapply Hnw; [ | exact Hr ].
      eapply wt_tau; [ exact Hp' | exact Hp1 ].
  - intros t' Ht'. inversion Ht'; subst.
    + inversion H3; subst. apply m_now. constructor.
    + inversion H3.
  - intros p' t' mu1 mu2 Hdual Hp' Ht'. exfalso.
    inversion Ht'; subst.
    + inversion H3.
    + inversion H3; subst.
      destruct mu1 as [a1|a1]; simpl in Hdual; try contradiction.
      eapply Hnw; [ apply wt_nil | ]. subst a1. exact Hp'.
Qed.

Theorem below_preserves_no_weak_out : forall (p q : proc) c,
  Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> NoWeakOut c p -> NoWeakOut c q.
Proof.
  intros p q c Hp Hq Hpre Hnw q1 Hq1 w r Hr.
  assert (Hm : q must_pass (TSink c))
    by (apply Hpre; apply no_weak_out_passes; assumption).
  assert (Hm1 : q1 must_pass (TSink c))
    by (eapply must_preserved_by_weak_nil_srv; eassumption).
  assert (Ht : lts (TSink c) (ActExt (ActIn (c,w)))
                   (subst_in_proc 0 w ((g (𝟘 : gproc)) : proc)))
    by (apply lts_choiceR; apply lts_input).
  inversion Hm1; subst.
  - eapply TSink_not_good. exact H.
  - assert (Hcon := com r _ (ActOut (c,w)) (ActIn (c,w)) eq_refl Hr Ht).
    simpl in Hcon. eapply no_client_nil; [ | exact Hcon ].
    eapply Static_preserved_by_lts; [ | exact Hr ].
    eapply Static_preserved_by_wt; [ exact Hq | exact Hq1 ].
Qed.

(** …and the result is usable **forwards**, not only as a contrapositive.

    [below_preserves_no_weak_out] is stated the way it is because
    [¬ NoWeakOut] is a negated ∀ and gives no witness constructively.  The
    witness is recovered by *deciding* [NoWeakOut] on the [Static]
    fragment: "does this state emit on [c]" is decidable
    ([emits_on_dec], via the finite multiset of pending outputs), the
    τ-reducts form a **list** ([tau_list]), and a finite family of
    disjunctions collapses to one ([list_disj]).  Termination
    ([Static_terminate]) makes the recursion well-founded.

        weak_out_of_below : p ⊑ₘᵤₛₜᵢ q -> q ⟶[(c,v)!] q' ->
          ∃ p1, p ⟹[[]] p1 ∧ emits_on c p1

    This is the correct mutity-free replacement for [bag_incl_of_below]'s
    first half, and it is exactly the shape a weak-output rule's existence
    premise needs. *)

Lemma list_disj : forall {X : Type} (L : list X) (A B : X -> Prop),
  (forall x, In x L -> A x \/ B x) ->
  (forall x, In x L -> A x) \/ (exists x, In x L /\ B x).
Proof.
  induction L as [|x L IH]; intros A B Hall.
  { left. intros y Hy. contradiction. }
  destruct (Hall x (or_introl eq_refl)) as [Hx|Hx].
  - destruct (IH A B (fun y Hy => Hall y (or_intror Hy))) as [Hl|(y & Hy & Hb)].
    + left. intros y [Hy|Hy]; [ subst; exact Hx | apply Hl; exact Hy ].
    + right. exists y. split; [ right; exact Hy | exact Hb ].
  - right. exists x. split; [ left; reflexivity | exact Hx ].
Qed.

Lemma weak_out_dec : forall (p : proc) c, Static p ->
  NoWeakOut c p \/ (exists p1, p ⟹[[]] p1 /\ emits_on c p1).
Proof.
  intros p c Hst. assert (Ht := Static_terminate p Hst). revert Hst.
  induction Ht as [p Hstep IH]. intros Hst.
  destruct (emits_on_dec c p) as [He|He].
  { right. exists p. split; [ apply wt_nil | exact He ]. }
  assert (Hall : forall x, In x (tau_list p) ->
    NoWeakOut c x \/ (exists p1, x ⟹[[]] p1 /\ emits_on c p1)).
  { intros x Hx. apply IH.
    - apply tau_list_spec. exact Hx.
    - eapply Static_preserved_by_lts; [ exact Hst | apply tau_list_spec; exact Hx ]. }
  destruct (list_disj (tau_list p) _ _ Hall) as [Hno|(x & Hx & p1 & Hp1 & He1)].
  - left. intros p2 Hp2 w r Hr. inversion Hp2; subst.
    + apply He. exists w, r. exact Hr.
    + eapply (Hno q); [ apply tau_list_spec; exact l | exact w0 | exact Hr ].
  - right. exists p1. split; [ | exact He1 ].
    eapply wt_tau; [ apply tau_list_spec; exact Hx | exact Hp1 ].
Qed.

Theorem weak_out_of_below : forall (p q : proc) c v q',
  Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  lts q (ActExt (ActOut (c,v))) q' ->
  exists p1, p ⟹[[]] p1 /\ emits_on c p1.
Proof.
  intros p q c v q' Hp Hq Hpre Hout.
  destruct (weak_out_dec p c Hp) as [Hnw|Hyes]; [ | exact Hyes ].
  exfalso. eapply (below_preserves_no_weak_out p q c Hp Hq Hpre Hnw q).
  - apply wt_nil.
  - exact Hout.
Qed.

(** * THE FIFTH PREMISE, FIXED: COMPARE THE RESIDUES **COLLECTIVELY**

    The output premise of a weak-output [glb] rule was stated
    per-residue — [⊢ p'' ⊑ q''] for each emission residue — and that is
    *not* semantically implied: [must] does not travel backwards along the
    server's τ's, so knowing that **one** residue passes a test says
    nothing about [p] itself, and [p ⊑ q] cannot be invoked.

    What **is** implied is the *collective* statement: whenever **all** of
    [p]'s emission residues on [c] pass a test, so does every residue of
    [q].  That is the conjunction — i.e. the internal choice of the
    residues — and it is exactly the shape [ax_ichoice_glb] consumes.

    The probe that sees it is [𝛕•① + c?(NewVar 0 t)]: its own τ makes
    [ex] free and reaches [①], so the *only* obligation it imposes on a
    server is [com] at [c] — "every emission on [c], from every
    τ-reachable state, leaves a residue that passes [t]".  Shifting [t]
    by [NewVar] makes the caught continuation independent of the value
    received, so one probe covers every value at once
    ([NewVar_subst_cancel]). *)

Definition TCatch (c : ChannelData) (t : proc) : proc :=
  g (((𝛕 • ((g (① : gproc)) : proc)) + (c ? (NewVar 0 t))) : gproc).

Lemma TCatch_not_good : forall c t, ~ good_VACCS (TCatch c t).
Proof.
  intros c t H. inversion H; subst. inversion H1. inversion H1.
  all: inversion H0.
Qed.

Lemma catch_passes : forall (p : proc) c t,
  Static p ->
  (forall p1 w p'', p ⟹[[]] p1 -> lts p1 (ActExt (ActOut (c,w))) p'' ->
     p'' must_pass t) ->
  p must_pass (TCatch c t).
Proof.
  intros p c t Hst. assert (Ht := Static_terminate p Hst). revert Hst.
  induction Ht as [p Hstep IH]. intros Hst Hall.
  apply m_step.
  - apply TCatch_not_good.
  - eexists. apply ParRight. apply lts_choiceL. apply lts_tau.
  - intros p' Hp'. apply IH.
    + exact Hp'.
    + eapply Static_preserved_by_lts; [ exact Hst | exact Hp' ].
    + intros p1 w p'' Hp1 Ho. eapply Hall; [ | exact Ho ].
      eapply wt_tau; [ exact Hp' | exact Hp1 ].
  - intros t2 Ht2. inversion Ht2; subst.
    + inversion H3; subst. apply m_now. constructor.
    + inversion H3.
  - intros p' t2 mu1 mu2 Hdual Hp' Ht2.
    inversion Ht2; subst.
    + inversion H3.
    + inversion H3; subst.
      destruct mu1 as [a1|a1]; simpl in Hdual; try contradiction.
      subst a1. rewrite NewVar_subst_cancel.
      eapply Hall; [ apply wt_nil | exact Hp' ].
Qed.

Theorem residues_below : forall (p q : proc) c v q' t,
  Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  lts q (ActExt (ActOut (c,v))) q' ->
  (forall p1 w p'', p ⟹[[]] p1 -> lts p1 (ActExt (ActOut (c,w))) p'' ->
     p'' must_pass t) ->
  q' must_pass t.
Proof.
  intros p q c v q' t Hp Hq Hpre Hout Hall.
  assert (Hm : q must_pass (TCatch c t))
    by (apply Hpre; apply catch_passes; assumption).
  assert (Ht2 : lts (TCatch c t) (ActExt (ActIn (c,v))) (subst_in_proc 0 v (NewVar 0 t)))
    by (apply lts_choiceR; apply lts_input).
  inversion Hm; subst.
  - exfalso. eapply TCatch_not_good. exact H.
  - assert (Hcon := com q' _ (ActOut (c,v)) (ActIn (c,v)) eq_refl Hout Ht2).
    rewrite NewVar_subst_cancel in Hcon. exact Hcon.
Qed.

(** * ENUMERATING THE RESIDUES

    The last thing a weak-output rule needs is the **list** of emission
    residues, so that [ichoice] can turn [residues_below]'s conjunction
    into a process.  Two computations, both by fuel on [size] — not on
    [terminate], which lives in [Prop] and forbids large elimination:

    - [VACCS_Residues.reach_list] closes [tau_list] under iteration.
      Each τ strictly shrinks a [Static] process ([Static_lts_decrease]),
      so [S (size p)] steps of fuel suffice;
    - [out_vals] reads the values a state can emit on a channel off its
      **finite** multiset of pending outputs ([lts_oba_mo]) — the same
      finiteness [emits_on_dec] rests on — and [res_at] takes the
      residues at each of them from [lts_set]. *)

Definition out_vals (c : ChannelData) (u : proc) : list ValueData :=
  flat_map (fun eta => match eta with
      | ActOut (d,w) => if bool_decide (d = c) then [w] else []
      | _ => [] end) (elements (lts_oba_mo u)).

Definition res_at (c : ChannelData) (u : proc) : list proc :=
  flat_map (fun w => elements (lts_set u (ActExt (ActOut (c,w))))) (out_vals c u).

Definition res_list (n : nat) (c : ChannelData) (p : proc) : list proc :=
  flat_map (res_at c) (reach_list n p).

Lemma out_vals_complete : forall c u w r,
  lts u (ActExt (ActOut (c,w))) r -> In w (out_vals c u).
Proof.
  intros c u w r Hl.
  assert (Hnb : non_blocking (ActOut (c,w))).
  { unfold non_blocking. simpl. unfold non_blocking_output.
    exists (c ▷ w). reflexivity. }
  pose proof (lts_oba_mo_spec_bis1 u (ActOut (c,w)) r Hnb Hl) as Hmem.
  unfold out_vals. apply in_flat_map. exists (ActOut (c,w)). split.
  - apply list_elem_of_In. apply gmultiset_elem_of_elements. exact Hmem.
  - rewrite bool_decide_eq_true_2 by reflexivity. left. reflexivity.
Qed.

Lemma res_list_complete : forall n p c, Static p -> (size p < n)%nat ->
  forall p1 w r, p ⟹[[]] p1 -> lts p1 (ActExt (ActOut (c,w))) r ->
  In r (res_list n c p).
Proof.
  intros n p c Hst Hsz p1 w r Hp1 Hr.
  apply in_flat_map. exists p1. split.
  - eapply reach_list_complete; eassumption.
  - apply in_flat_map. exists w. split.
    + eapply out_vals_complete. exact Hr.
    + apply list_elem_of_In. apply elem_of_elements.
      apply lts_set_spec1. exact Hr.
Qed.

Lemma res_list_sound : forall n p c r, In r (res_list n c p) ->
  exists p1 w, p ⟹[[]] p1 /\ lts p1 (ActExt (ActOut (c,w))) r.
Proof.
  intros n p c r Hin. apply in_flat_map in Hin as (p1 & Hp1 & Hr).
  apply in_flat_map in Hr as (w & Hw & Hr).
  exists p1, w. split.
  - eapply reach_list_sound. exact Hp1.
  - apply lts_set_spec0. apply elem_of_elements. apply list_elem_of_In. exact Hr.
Qed.

(** * THE n-ARY JOIN — and the value-selectivity obstruction

    [ichoice] turns [residues_below]'s conjunction into a process only if
    "all members pass [t]" gives "[ichoice L] passes [t]" — that is
    [VACCS_Residues.ichoice_must], which lives upstream with [ichoice]
    itself. *)


(** * THE VALUE-SELECTIVE PROBE

    The comparison of residues has to be made **at one value**: in the
    [com]-output case the client offers [(c,v)?] for a *single* [v], so
    [must p t0] only ever yields residues at that [v].  [TCatch]'s caught
    continuation is deliberately value-independent, so a selective probe
    is needed —

      [c ? (If (bvar 0 == v0) Then t Else ①)]

    — and the calculus looks at first as if it pushed back:
    [Eval_Eq 0 (bvar i == cst t)] is [Some false] *unconditionally*
    ([VACCS.Eval_Eq]).  It does not.  The guard is evaluated only **after**
    the input has substituted the received value, and [Eval_Eq 0] is in
    fact **total and exact** on [ValueData]: it decides syntactic equality
    in every case, [bvar i == bvar i'] included ([eval_eq_true],
    [eval_eq_refl]).  So the probe works at an arbitrary value, not only a
    constant one.

    The one piece of bookkeeping is that [v0] sits inside the guard's
    scope: it is stored shifted, as [NewVar_in_Data 0 v0], and the input's
    own substitution brings it back ([subst_NewVar_in_Data_cancel]).  This
    is the value-level twin of what [NewVar_subst_cancel] does for the
    caught continuation. *)

Lemma subst_NewVar_in_Data_cancel : forall (X Y : ValueData),
  subst_Data 0 X (NewVar_in_Data 0 Y) = Y.
Proof.
  intros X Y. destruct Y as [v|i]; simpl; [ reflexivity | ].
  destruct (decide (0 < S i)) as [_|Hn]; [ | lia ].
  simpl. destruct (decide (S i = 0)) as [E|_]; [ discriminate | ].
  destruct (decide (S i < 0)) as [E|_]; [ lia | ]. reflexivity.
Qed.

Lemma eval_eq_refl : forall (Y : ValueData), Eval_Eq 0 (Y == Y) = Some true.
Proof.
  intros [v|i]; simpl.
  - destruct (decide (v = v)); [ reflexivity | contradiction ].
  - destruct (decide (i = i)); [ reflexivity | contradiction ].
Qed.

Lemma eval_eq_true : forall (w u : ValueData),
  Eval_Eq 0 (w == u) = Some true -> w = u.
Proof.
  intros [v|i] [v'|j] H; simpl in H.
  - destruct (decide (v = v')); [ subst; reflexivity | discriminate ].
  - discriminate.
  - discriminate.
  - destruct (decide (i = j)); [ subst; reflexivity | ].
    destruct (decide (0 <= i)); [ | lia ].
    destruct (decide (0 <= j)); [ discriminate | lia ].
Qed.

Definition TCatchD (c : ChannelData) (v0 : ValueData) (t : proc) : proc :=
  g ((( 𝛕 • ((g (① : gproc)) : proc))
      + (c ? (If ((bvar 0) == (NewVar_in_Data 0 v0))
              Then (NewVar 0 t) Else ((g (① : gproc)) : proc)))) : gproc).

Lemma TCatchD_not_good : forall c v0 t, ~ good_VACCS (TCatchD c v0 t).
Proof.
  intros c v0 t H. inversion H; subst. inversion H1. inversion H1.
  all: inversion H0.
Qed.

(** A [Static] process passes [TCatchD c v0 t] as soon as every residue of
    an emission on [c] **at the value [v0]** passes [t].  Emissions at
    other values impose nothing: there the guard evaluates to [false] and
    the client is congruent to [g ①], which is good, so [m_now] closes
    the obligation. *)

Lemma catch_d_passes : forall (p : proc) c (v0 : ValueData) t,
  Static p ->
  (forall p1 p'', p ⟹[[]] p1 ->
     lts p1 (ActExt (ActOut (c, v0))) p'' -> p'' must_pass t) ->
  p must_pass (TCatchD c v0 t).
Proof.
  intros p c v0 t Hst. assert (Ht := Static_terminate p Hst). revert Hst.
  induction Ht as [p Hstep IH]. intros Hst Hall.
  apply m_step.
  - apply TCatchD_not_good.
  - eexists. apply ParRight. apply lts_choiceL. apply lts_tau.
  - intros p' Hp'. apply IH.
    + exact Hp'.
    + eapply Static_preserved_by_lts; [ exact Hst | exact Hp' ].
    + intros p1 p'' Hp1 Ho. eapply Hall; [ | exact Ho ].
      eapply wt_tau; [ exact Hp' | exact Hp1 ].
  - intros t2 Ht2. inversion Ht2; subst.
    + inversion H3; subst. apply m_now. constructor.
    + inversion H3.
  - intros p' t2 mu1 mu2 Hdual Hp' Ht2.
    inversion Ht2; subst.
    + inversion H3.
    + inversion H3; subst.
      destruct mu1 as [a1|a1]; simpl in Hdual; try contradiction.
      subst a1. simpl. rewrite subst_NewVar_in_Data_cancel.
      destruct (Eval_Eq 0 (v == v0)) as [[|]|] eqn:HE.
      * eapply must_eq_client; [ symmetry; apply cgr_if_true; exact HE | ].
        rewrite NewVar_subst_cancel.
        assert (Hv : v = v0) by (eapply eval_eq_true; exact HE).
        subst v. eapply Hall; [ apply wt_nil | exact Hp' ].
      * eapply must_eq_client; [ symmetry; apply cgr_if_false; exact HE | ].
        apply m_now. constructor.
      * exfalso. eapply Eval_Eq_0_not_none. exact HE.
Qed.

(** The fixed-value residue comparison, at an **arbitrary** value. *)

Theorem residues_below_d : forall (p q : proc) c (v0 : ValueData) q' t,
  Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  lts q (ActExt (ActOut (c, v0))) q' ->
  (forall p1 p'', p ⟹[[]] p1 ->
     lts p1 (ActExt (ActOut (c, v0))) p'' -> p'' must_pass t) ->
  q' must_pass t.
Proof.
  intros p q c v0 q' t Hp Hq Hpre Hout Hall.
  assert (Hm : q must_pass (TCatchD c v0 t))
    by (apply Hpre; apply catch_d_passes; assumption).
  assert (Ht2 : lts (TCatchD c v0 t) (ActExt (ActIn (c, v0)))
                    (subst_in_proc 0 v0
                       (If ((bvar 0) == (NewVar_in_Data 0 v0))
                        Then (NewVar 0 t) Else ((g (① : gproc)) : proc))))
    by (apply lts_choiceR; apply lts_input).
  inversion Hm; subst.
  - exfalso. eapply TCatchD_not_good. exact H.
  - assert (Hcon := com q' _ (ActOut (c, v0)) (ActIn (c, v0))
                        eq_refl Hout Ht2).
    simpl in Hcon. rewrite subst_NewVar_in_Data_cancel in Hcon.
    eapply must_eq_client in Hcon; [ | apply cgr_if_true; apply eval_eq_refl ].
    rewrite NewVar_subst_cancel in Hcon. exact Hcon.
Qed.

(** ** The payoff: the residues, taken COLLECTIVELY, are below every residue
       of the right-hand side

    This is the output premise of the weak-emission [glb] rule, in semantic
    form, and it needs nothing beyond [Static] on both sides and the
    preorder itself.  The internal choice is what makes the conjunction a
    process: [VACCS_Residues.lts_ichoice] places it below each of its
    members, so a test it passes is passed by every residue of [p], and
    [residues_below_d] then hands that to the residue of [q]. *)

Theorem ichoice_residues_below : forall (p q : proc) c (v : ValueData) q' n,
  Static p -> Static q -> (size p < n)%nat ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  lts q (ActExt (ActOut (c, v))) q' ->
  (g (ichoice (res_list_v n c v p))) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q'.
Proof.
  intros p q c v q' n Hp Hq Hn Hpre Hout t Ht.
  apply (residues_below_d p q c v q' t Hp Hq Hpre Hout).
  intros p1 p'' Hp1 Ho.
  assert (Hin : In p'' (res_list_v n c v p))
    by (eapply res_list_v_complete; eassumption).
  assert (Hb : (g (ichoice (res_list_v n c v p))) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ p'')
    by (apply must_i_tau_below; apply lts_ichoice; exact Hin).
  apply Hb. exact Ht.
Qed.

(** ** The non-emptiness side condition of the weak-emission glb law

    It never rules out a valid instance: were the residue list empty,
    [residues_below_d]'s hypothesis would be vacuous, so [q'] would pass
    **every** test — [g 𝟘] included, which no [Static] process does
    ([no_client_nil]).

    It cannot be *used* inside a rule (its hypothesis is the very
    inequation the rule concludes), but it says the premise is exactly
    what the semantics already forces. *)

Lemma res_list_v_nonempty : forall (p q : proc) c (v : ValueData) q' n,
  Static p -> Static q -> (size p < n)%nat ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  lts q (ActExt (ActOut (c, v))) q' ->
  res_list_v n c v p <> nil.
Proof.
  intros p q c v q' n Hp Hq Hn Hpre Hout Hnil.
  assert (Hq' : Static q') by (eapply Static_preserved_by_lts; [ exact Hq | exact Hout ]).
  eapply (no_client_nil q' Hq').
  apply (residues_below_d p q c v q' ((g (𝟘 : gproc)) : proc) Hp Hq Hpre Hout).
  intros p1 p'' Hp1 Ho.
  assert (Hin : In p'' (res_list_v n c v p))
    by (eapply res_list_v_complete; eassumption).
  rewrite Hnil in Hin. inversion Hin.
Qed.

(** ** [ax_glb_weak] in use: the non-emptiness premise, discharged

    The consumer of the rule, and what it buys over [ax_glb_tau]: **no
    premise at all about the left-hand side emitting**.  [ax_glb_tau]
    requires a *strong* emission of [p] to match each emission of [q],
    which [glb_output_premise_not_semantic] shows is not implied by the
    preorder; here the corresponding premise is the non-emptiness of the
    residue list, and the preorder implies it outright. *)

Theorem ax_glb_weak_of_sem : forall (p q : proc) n,
  Static p -> Static q -> (size p < n)%nat ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  (exists q0, lts q τ q0) ->
  (forall q', lts q τ q' -> ax_pre p q') ->
  (forall c v q'', lts q (ActExt (ActIn (c,v))) q'' ->
     ax_pre (((c ! v • 𝟘) : proc) ‖ p) q'') ->
  (forall c v q'', lts q (ActExt (ActOut (c, v))) q'' ->
     ax_pre (g (ichoice (res_list_v n c v p))) q'') ->
  ax_pre p q.
Proof.
  intros p q n Hp Hq Hn Hpre Hex Htau Hin Hout.
  apply (ax_glb_weak p q n); try assumption.
  intros c v q'' Hq''. eapply res_list_v_nonempty; eassumption.
Qed.

Lemma res_list_v_Static : forall n c v (p : proc), Static p ->
  Forall Static (res_list_v n c v p).
Proof.
  intros n c v p Hst. apply Forall_forall. intros x Hx.
  apply res_list_v_sound in Hx as (p1 & Hp1 & Ho).
  eapply Static_preserved_by_lts;
    [ eapply Static_preserved_by_wt; [ exact Hst | exact Hp1 ] | exact Ho ].
Qed.

(** ** A COMPLETENESS STEP FOR ANY RIGHT-HAND SIDE WITH A [τ]

    And with **no condition on either side**.  Compare what the
    development had before:

    - [ax_below_cfg_glb_split] takes the right apart the same way, but it
      discharges [ax_glb_tau]'s *strong* output premise through
      [bag_incl_of_below], which needs the left to be **mute**
      ([ochans (g M) = []]) *and* to be a configuration [msgs l ‖ g M];
    - [completeness_gsum_step_gen] has no mutity requirement but needs the
      right to be a **guarded sum**, where the output premises are vacuous
      ([gsum_no_out]).

    Here neither is needed.  Every premise of [ax_glb_weak_of_sem] is
    discharged from the preorder alone, at a **strictly smaller
    right-hand side** ([Static_lts_decrease]):

    - the τ premise by [must_i_tau_below] (a server's own [τ] only ever
      decreases it), so [p ⊑ₘᵤₛₜᵢ q ⊑ₘᵤₛₜᵢ q'];
    - the input premise by [must_i_feed_below] — the asynchronous reading,
      where the left keeps the message *pending* rather than consuming it;
    - the output premise by [ichoice_residues_below], the collective
      comparison of the weak residues. *)

Theorem completeness_step_glb_weak : forall (p q : proc),
  Static p -> Static q ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  (exists q0, lts q τ q0) ->
  (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
  ax_pre p q.
Proof.
  intros p q Hp Hq Hpre Hex HR.
  apply (ax_glb_weak_of_sem p q (S (size p))); try assumption.
  - lia.
  - intros q' Hq'. apply HR.
    + exact Hp.
    + eapply Static_preserved_by_lts; [ exact Hq | exact Hq' ].
    + eapply Static_lts_decrease; [ exact Hq | exact Hq' ].
    + intros t Ht. eapply must_i_tau_below; [ exact Hq' | ]. apply Hpre. exact Ht.
  - intros c v q'' Hq''. apply HR.
    + repeat constructor. exact Hp.
    + eapply Static_preserved_by_lts; [ exact Hq | exact Hq'' ].
    + eapply Static_lts_decrease; [ exact Hq | exact Hq'' ].
    + eapply must_i_feed_below; [ exact Hpre | exact Hq'' ].
  - intros c v q'' Hq''. apply HR.
    + apply static_g. apply ichoice_gStatic. apply res_list_v_Static. exact Hp.
    + eapply Static_preserved_by_lts; [ exact Hq | exact Hq'' ].
    + eapply Static_lts_decrease; [ exact Hq | exact Hq'' ].
    + eapply ichoice_residues_below; try eassumption. lia.
Qed.

(** ** …so the step reduces to a STABLE right-hand side

    "Does [q] have a [τ]?" is decidable ([VACCS_Absorb.lts_dec]) and the
    unstable branch is closed outright, so the completeness step needs
    only the **stable** right-hand side — the case where [ax_glb_weak] has
    nothing to take apart and the mirror / Phase A machinery takes over,
    which is why that machinery still asks the right to be a guarded
    sum. *)

Theorem completeness_step_of_stable_case : forall (p q : proc),
  Static p -> Static q ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
  ((forall z, ~ lts q τ z) -> ax_pre p q) ->
  ax_pre p q.
Proof.
  intros p q Hp Hq Hpre HR Hstable.
  destruct (lts_dec q τ) as [Hno | (z & Hz)].
  - apply Hstable. exact Hno.
  - eapply completeness_step_glb_weak; try eassumption. exists z. exact Hz.
Qed.

(** ** COMPLETENESS REDUCES TO THE STABLE RIGHT-HAND SIDE

    Unconditionally.  Every other shape of right-hand side — a
    configuration whose bag can be delivered, an internal choice, a mixed
    sum, anything at all with an internal move — is handled by
    [ax_glb_weak], and the recursion it needs is exactly the one
    [completeness_from_step] provides. *)

Theorem completeness_of_stable_step :
  (forall p q, Static p -> Static q -> (forall z, ~ lts q τ z) ->
     p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
     (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
        p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
     ax_pre p q) ->
  forall p q, Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros Hstep. apply completeness_from_step.
  intros p q Hp Hq Hpre HR.
  eapply completeness_step_of_stable_case; try eassumption.
  intros Hno. eapply Hstep; eassumption.
Qed.

(** ** …and the stable case may be assumed AT A NORMAL FORM

    [domsim] carries stability across: the normal form's transitions are
    matched by the original's ([ds_s]), so a τ-stable process has a
    τ-stable normal form.  And [ds_r] transports the conclusion back.

    So the remaining case is not merely "the right-hand side is stable"
    but "the right-hand side is a **stable forwarder state**
    [Ѵⁿ (msgs l ‖ g M)]" — the shape the mirror / Phase A machinery is
    written for.  Note the recursion is still measured by [size q] for the
    *original* [q], which is what [domsim] exists to bridge ([DomOk]). *)

Lemma domsim_stable : forall (p q : proc), domsim p q ->
  (forall z, ~ lts p τ z) -> (forall z, ~ lts q τ z).
Proof.
  intros p q Hs Hst z Hz.
  destruct (ds_s Hs τ z Hz) as (r' & Hl & _). eapply Hst. exact Hl.
Qed.

Theorem completeness_of_stable_NF_step :
  (forall (p q : proc) n l M, Static p -> Static q -> gStatic M ->
     domsim q (NF n l M) ->
     (forall z, ~ lts (NF n l M) τ z) ->
     p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
     (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
        p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
     ax_pre p (NF n l M)) ->
  forall p q, Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros Hstep. apply completeness_of_stable_step.
  intros p q Hp Hq Hno Hpre HR.
  destruct (normal_form_strong_sim q Hq) as (n & l & M & HM & Hsim).
  eapply ax_trans; [ | exact (ds_r Hsim) ].
  eapply Hstep; try eassumption.
  eapply domsim_stable; [ exact Hsim | exact Hno ].
Qed.


(** ** THE RESTRICTION BLOCK IS NOT AN OBSTACLE WHEN THE BAG IS EMPTY

    [resg] pushes a [ν] into the guards of a **guarded sum**, and with an
    empty bag the body of the restriction *is* one — [msgs [] ‖ g M] is
    [g M] up to [ax_nil_par].  So the whole block comes off, one [ν] at a
    time, and what is left is a bare guarded sum.

    The measure follows for free: [domsim_resg] is a *literal* transition
    correspondence, so [domsim_NF_nil] composes with the normal form's own
    simulation and the reducts are still measured against the original
    [q]. *)

Fixpoint resgn (n : nat) (M : gproc) : gproc :=
match n with
| 0 => M
| S n' => resg (resgn n' M)
end.

Lemma resgn_gStatic : forall n M, gStatic M -> gStatic (resgn n M).
Proof.
  induction n as [|n IH]; intros M HM; simpl; [ exact HM | ].
  apply resg_gStatic. apply IH. exact HM.
Qed.

Lemma domsim_resgn : forall n M,
  domsim (Ѵ n ((g M) : proc)) ((g (resgn n M)) : proc).
Proof.
  induction n as [|n IH]; intro M; simpl.
  - apply domsim_refl.
  - eapply domsim_trans; [ apply domsim_res; apply IH | apply domsim_resg ].
Qed.

Lemma domsim_NF_nil : forall n M, domsim (NF n [] M) ((g (resgn n M)) : proc).
Proof.
  intros n M. unfold NF.
  eapply domsim_trans; [ | apply domsim_resgn ].
  apply domsim_res_n. apply domsim_cgr. apply cgr_symm. apply ax_nil_par.
Qed.

(** The stable case at a bare guarded sum, with the measure routed through
    [domsim]: the recursive premise is about a reduct of [g M], while the
    induction hypothesis is at [size q] for the **original** [q], and
    [ds_s] hands back a genuine reduct of [q] with a [⊢]-equal target. *)

Lemma stable_bare_gsum_of_domsim : forall (p q : proc) (M : gproc),
  Static p -> Static q -> gStatic M ->
  domsim q ((g M) : proc) ->
  (forall z, ~ lts ((g M) : proc) τ z) ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
  ax_pre p ((g M) : proc).
Proof.
  intros p q M Hp Hq HM Hsim Hno Hpre HR.
  assert (HsemM : p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g M) : proc)).
  { intros t Ht. apply (soundness_ax _ _ (ds_l Hsim)). apply Hpre. exact Ht. }
  apply ax_below_stable_gsum_gen; try assumption.
  intros c v Q' Hl.
  destruct (ds_s Hsim _ _ Hl) as (r' & Hr' & Hd).
  eapply ax_trans; [ | exact (ds_l Hd) ].
  apply HR.
  - constructor; [ constructor | exact Hp ].
  - eapply Static_preserved_by_lts; [ exact Hq | exact Hr' ].
  - eapply Static_lts_decrease; [ exact Hq | exact Hr' ].
  - eapply must_i_feed_below; [ exact Hpre | exact Hr' ].
Qed.

Lemma stable_NF_empty_bag : forall (p q : proc) n (M : gproc),
  Static p -> Static q -> gStatic M ->
  domsim q (NF n [] M) ->
  (forall z, ~ lts (NF n [] M) τ z) ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
  ax_pre p (NF n [] M).
Proof.
  intros p q n M Hp Hq HM Hsim Hno Hpre HR.
  assert (Hdn := domsim_NF_nil n M).
  assert (Hd : domsim q ((g (resgn n M)) : proc))
    by (eapply domsim_trans; [ exact Hsim | exact Hdn ]).
  assert (Hst : forall z, ~ lts ((g (resgn n M)) : proc) τ z)
    by (eapply domsim_stable; [ exact Hdn | exact Hno ]).
  eapply ax_trans; [ | exact (ds_r Hdn) ].
  eapply stable_bare_gsum_of_domsim; try eassumption.
  apply resgn_gStatic. exact HM.
Qed.

(** ** COMPLETENESS REDUCES TO A STABLE RIGHT-HAND SIDE CARRYING A MESSAGE

    The restriction block is gone from the statement: with an empty bag it
    is removed by [resg], whatever its depth.  So the single remaining
    case is a **pending message** on the right — the one thing a VACCS
    normal form has that a guarded sum cannot express, an output being an
    atomic message and never a guard. *)

Theorem completeness_of_stable_bag_step :
  (forall (p q : proc) n l M, Static p -> Static q -> gStatic M ->
     domsim q (NF n l M) ->
     (forall z, ~ lts (NF n l M) τ z) ->
     l <> [] ->
     p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
     (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
        p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
     ax_pre p (NF n l M)) ->
  forall p q, Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros Hstep. apply completeness_of_stable_NF_step.
  intros p q n l M Hp Hq HM Hsim Hno Hpre HR.
  destruct l as [|a l'].
  - eapply stable_NF_empty_bag; eassumption.
  - apply (Hstep p q n (a :: l') M); try assumption. discriminate.
Qed.

(** ** A τ-STABLE LEFT MUST CARRY THE RIGHT'S MESSAGES

    The remaining case has a right-hand side that **emits**, and message
    rigidity ([nil_not_below_msg_gen]) says the left must be able to emit
    too.  [weak_out_of_below] gives that only *weakly* and only at the
    channel; [res_list_v_nonempty] sharpens it to the exact **value**, and
    when the left is τ-stable a weak emission is a strong one
    ([wt_nil_stable]).  [TransitionShapeForOutputSimplified] then splits
    the left as the message beside its residue — asynchrony again: a
    process that emits *is* the message in parallel with what is left.

    This is the bridge the bagged stable case needs without assuming the
    left ν-free: iterated over the right's bag it should give
    [p ≡* msgs l ‖ p0], which is the shape [ax_below_stable_sum_cfg]
    consumes.  The iteration needs one more ingredient — the residues at a
    fixed [(c,v)] are unique up to [≡*], which is VACCS's output
    determinacy — and is not done here. *)

Lemma stable_left_extract : forall (p q : proc) c (v : ValueData) q',
  Static p -> Static q -> (forall z, ~ lts p τ z) ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  lts q (ActExt (ActOut (c,v))) q' ->
  exists p'', lts p (ActExt (ActOut (c,v))) p''
           /\ p ≡* (((c ! v • 𝟘) : proc) ‖ p'').
Proof.
  intros p q c v q' Hp Hq Hst Hpre Hout.
  assert (Hne : res_list_v (S (size p)) c v p <> nil)
    by (eapply res_list_v_nonempty; try eassumption; lia).
  destruct (res_list_v (S (size p)) c v p) as [|x L] eqn:E; [ contradiction | ].
  assert (Hin : In x (res_list_v (S (size p)) c v p)) by (rewrite E; left; reflexivity).
  apply res_list_v_sound in Hin as (p1 & Hp1 & Ho).
  assert (Hpp : p1 = p)
    by (eapply wt_nil_stable; [ apply no_lts_stable; exact Hst | exact Hp1 ]).
  subst p1. exists x. split; [ exact Ho | ].
  apply TransitionShapeForOutputSimplified. exact Ho.
Qed.

(** ** A τ-STABLE LEFT DECOMPOSES AS THE RIGHT'S BAG BESIDE A RESIDUE

    [stable_left_extract] peels one message; iterating it over the right's
    whole bag gives [p ≡* msgs l ‖ p0] — and, crucially, the **cancelled**
    semantics [p0 ⊑ₘᵤₛₜᵢ Q] for free, so no drain argument and no
    [msgs_cancel] is needed.

    The per-step transfer is [stable_residue_below]: on a τ-stable left
    the residues of a given emission are unique up to [≡*] — that is
    VACCS's **output determinacy** ([OBA_with_FB_Third_Axiom]) — so the
    internal choice of the residue list, which [ichoice_residues_below]
    places below the right's residue, is [⊢]-above the single residue
    [p''] ([ax_ichoice_glb] fed by [ax_cgr_sym]).  Without determinacy one
    would only know that *some* residue works, which is the usual ∀∃ gap;
    here the calculus closes it. *)

Lemma res_list_v_stable_uniq : forall n c (v : ValueData) (p p'' : proc),
  (forall z, ~ lts p τ z) ->
  lts p (ActExt (ActOut (c,v))) p'' ->
  forall x, In x (res_list_v n c v p) -> x ≡* p''.
Proof.
  intros n c v p p'' Hst Ho x Hx.
  apply res_list_v_sound in Hx as (p1 & Hp1 & Hx).
  assert (Hpp : p1 = p)
    by (eapply wt_nil_stable; [ apply no_lts_stable; exact Hst | exact Hp1 ]).
  subst p1. eapply OBA_with_FB_Third_Axiom; [ exact Hx | exact Ho ].
Qed.

Lemma stable_residue_below : forall (p q : proc) c (v : ValueData) q' p'',
  Static p -> Static q -> (forall z, ~ lts p τ z) ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  lts q (ActExt (ActOut (c,v))) q' ->
  lts p (ActExt (ActOut (c,v))) p'' ->
  p'' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q'.
Proof.
  intros p q c v q' p'' Hp Hq Hst Hpre Hoq Hop.
  assert (Hne : res_list_v (S (size p)) c v p <> nil)
    by (eapply res_list_v_nonempty; try eassumption; lia).
  assert (Hb : (g (ichoice (res_list_v (S (size p)) c v p))) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q')
    by (eapply ichoice_residues_below; try eassumption; lia).
  assert (Hax : ax_pre p'' (g (ichoice (res_list_v (S (size p)) c v p))))
    by (apply ax_ichoice_glb; [ exact Hne | intros y Hy; apply ax_cgr_sym;
          eapply res_list_v_stable_uniq; [ exact Hst | exact Hop | exact Hy ] ]).
  intros t Ht. apply Hb. apply (soundness_ax _ _ Hax). exact Ht.
Qed.

Lemma stable_left_decompose : forall (l : list TypeOfActions) (p Q : proc),
  Static p -> Static Q -> (forall z, ~ lts p τ z) ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ Q) ->
  exists p0, Static p0 /\ (forall z, ~ lts p0 τ z)
          /\ p ≡* (msgs l ‖ p0) /\ p0 ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ Q.
Proof.
  induction l as [|a l0 IH]; intros p Q Hp HQ Hst Hpre.
  - exists p. split; [ exact Hp | ]. split; [ exact Hst | ].
    split; [ apply ax_nil_par | ].
    intros t Ht. apply (proj1 (must_i_cgr Q (msgs [] ‖ Q) (ax_nil_par Q))).
    apply Hpre. exact Ht.
  - destruct a as (c,v).
    assert (HsQ : Static (msgs ((c,v) :: l0) ‖ Q))
      by (constructor; [ apply msgs_Static | exact HQ ]).
    assert (Hstep : lts (msgs ((c,v) :: l0) ‖ Q) (ActExt (ActOut (c,v)))
                        (((g (𝟘 : gproc) : proc) ‖ msgs l0) ‖ Q)).
    { simpl. apply lts_parL. apply lts_parL. apply lts_output. }
    destruct (stable_left_extract p (msgs ((c,v) :: l0) ‖ Q) c v _
                Hp HsQ Hst Hpre Hstep) as (p'' & Hop & Hcp).
    assert (Hsp'' : Static p'')
      by (eapply Static_preserved_by_lts; [ exact Hp | exact Hop ]).
    assert (Hst'' : forall z, ~ lts p'' τ z).
    { intros z Hz.
      assert (Hz2 : lts (((c ! v • 𝟘) : proc) ‖ p'') τ (((c ! v • 𝟘) : proc) ‖ z))
        by (apply lts_parR; exact Hz).
      destruct (cgr_lts_transfer _ p τ _ (cgr_symm _ _ _ Hcp) Hz2) as (y & Hy & _).
      eapply Hst. exact Hy. }
    assert (Hbelow : p'' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l0 ‖ Q)).
    { assert (Hb1 : p'' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (((g (𝟘 : gproc) : proc) ‖ msgs l0) ‖ Q))
        by (exact (stable_residue_below p (msgs ((c,v) :: l0) ‖ Q) c v
                     (((g (𝟘 : gproc) : proc) ‖ msgs l0) ‖ Q) p''
                     Hp HsQ Hst Hpre Hstep Hop)).
      intros t Ht.
      apply (proj1 (must_i_cgr (msgs l0 ‖ Q) (((g (𝟘 : gproc) : proc) ‖ msgs l0) ‖ Q)
                     (cgr_fullpar _ _ _ _ _ (ax_nil_par (msgs l0)) (cgr_refl _ Q)))).
      apply Hb1. exact Ht. }
    destruct (IH p'' Q Hsp'' HQ Hst'' Hbelow) as (p0 & Hs0 & Hst0 & Hc0 & Hb0).
    exists p0. split; [ exact Hs0 | ]. split; [ exact Hst0 | ].
    split; [ | exact Hb0 ].
    etransitivity; [ exact Hcp | ].
    etransitivity;
      [ apply (cgr_fullpar _ _ _ _ _ (cgr_refl _ ((c ! v • 𝟘) : proc)) Hc0) | ].
    simpl. apply cgr_par_assoc_rev.
Qed.

(** Hence the bagged stable case for a **τ-stable left**, with nothing
    else asked of it — no ν-freeness, no normal form, no bag of its own
    known in advance.  The decomposition supplies both the common bag and
    the cancelled semantics Phase A needs. *)

Theorem stable_bag_stable_left : forall (p q : proc) (l : list TypeOfActions) (M : gproc),
  Static p -> Static q -> gStatic M ->
  domsim q (msgs l ‖ ((g M) : proc)) ->
  (forall z, ~ lts (msgs l ‖ ((g M) : proc)) τ z) ->
  (forall z, ~ lts p τ z) ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
  ax_pre p (msgs l ‖ ((g M) : proc)).
Proof.
  intros p q l M Hp Hq HM Hsim Hno Hstp Hpre HR.
  assert (HstM : forall z, ~ lts ((g M) : proc) τ z).
  { intros z Hz. eapply (Hno (msgs l ‖ z)). apply lts_parR. exact Hz. }
  assert (Hsem : p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g M) : proc))).
  { intros t Ht. apply (soundness_ax _ _ (ds_l Hsim)). apply Hpre. exact Ht. }
  destruct (stable_left_decompose l p ((g M) : proc) Hp (static_g M HM) Hstp Hsem)
    as (p0 & Hs0 & Hst0 & Hc0 & Hb0).
  eapply ax_trans; [ apply ax_cgr; exact Hc0 | ].
  apply ax_below_stable_sum_cfg; [ exact HstM | | ].
  - apply phaseA_of_empty_bag_sem; [ exact Hs0 | exact HM | exact HstM | exact Hb0 ].
  - intros c v Q' l' Hsub Hin.
    eapply (ax_below_of_domok q).
    + constructor; [ apply msgs_Static | ].
      constructor; [ constructor | exact Hs0 ].
    + eapply domok_of_subbag_input; eassumption.
    + apply must_i_par_compat_r.
      eapply must_i_feed_below; [ exact Hb0 | exact Hin ].
    + exact HR.
Qed.

(** ** THE RESIDUE

    Completeness now needs only the step where the right-hand side is a
    **stable normal form carrying a message** and, on top of that, either
    a **restriction block** or an **unstable left**.  Everything else —
    every unstable right, every guarded-sum right, every stable right
    without a bag, and every stable right with a bag facing a τ-stable
    left — is closed.

    That statement was once a theorem of its own here, with an arbitrary
    left.  It is subsumed by [completeness_of_hard_NF_step] below, which
    hands the step a *normal form* on the left as well and is therefore
    the weaker obligation; the bare version had no consumer left and is
    gone. *)

(** ** THE LEFT-UNSTABLE CASE: the slice where the ∀∃ gap degenerates

    The obstruction is that [p ⊑ₘᵤₛₜᵢ q] constrains only the *conjunction*
    of [p]'s τ-successors — for [p = 𝛕•A + 𝛕•B] roughly
    [passes(p) = passes(A) ∩ passes(B)] — so no single successor need be
    below [q] ([tau_successor_cannot_be_chosen]).

    It degenerates exactly when the branching is **confluent to a least
    successor**: if [p] has no external transition and some [p0] is below
    every τ-successor, then [p0 ⊑ₘᵤₛₜᵢ p] — that is [must_i_glb_tau] read
    with [p] on the *right*, its output and input premises being vacuous —
    and with [must_i_tau_below] the two are must-equivalent.  The
    derivation is then one [ax_tau_step].

    The intended instance is a **deterministic** left, and in particular
    [ichoice [x]], whose two summands lead to the same state; that is why
    [ichoice] at a singleton was defined as [𝛕•x + 𝛕•x] in the first
    place. *)

Lemma left_tau_collapse : forall (p p0 : proc),
  (exists z, lts p τ z) ->
  (forall a z, ~ lts p (ActExt a) z) ->
  (forall q', lts p τ q' -> p0 ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q') ->
  p0 ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ p.
Proof.
  intros p p0 Hex Hnoext Hall.
  apply must_i_glb_tau; try assumption.
  - intros a q'' Hl. eapply Hnoext. exact Hl.
  - intros c v q'' Hl. exfalso. eapply Hnoext. exact Hl.
Qed.

Theorem completeness_step_left_collapse : forall (p q p0 : proc),
  (forall a z, ~ lts p (ActExt a) z) ->
  lts p τ p0 ->
  (forall q', lts p τ q' -> p0 ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q') ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  (p0 ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p0 q) ->
  ax_pre p q.
Proof.
  intros p q p0 Hnoext Hp0 Hall Hpre HR.
  eapply ax_trans; [ apply ax_tau_step; exact Hp0 | ].
  apply HR. intros t Ht. apply Hpre.
  apply (left_tau_collapse p p0 (ex_intro _ p0 Hp0) Hnoext Hall). exact Ht.
Qed.

Corollary completeness_step_left_det : forall (p q p0 : proc),
  (forall a z, ~ lts p (ActExt a) z) ->
  lts p τ p0 ->
  (forall q', lts p τ q' -> q' = p0) ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  (p0 ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p0 q) ->
  ax_pre p q.
Proof.
  intros p q p0 Hnoext Hp0 Huniq Hpre HR.
  eapply completeness_step_left_collapse; try eassumption.
  intros q' Hq'. rewrite (Huniq q' Hq'). intros t Ht. exact Ht.
Qed.

(** The instance, and the non-vacuity witness: the singleton internal
    choice collapses to its member. *)

Lemma ichoice_singleton_no_ext : forall (x : proc) a z,
  ~ lts (g (ichoice [x])) (ActExt a) z.
Proof.
  intros x a z Hl. simpl in Hl. inversion Hl; subst; inversion H3.
Qed.

Lemma ichoice_singleton_tau_inv : forall (x : proc) z,
  lts (g (ichoice [x])) τ z -> z = x.
Proof.
  intros x z Hl. simpl in Hl. inversion Hl; subst; inversion H3; subst; reflexivity.
Qed.

Corollary ax_ichoice_singleton_step : forall (x q : proc),
  x ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre x q -> ax_pre (g (ichoice [x])) q.
Proof.
  intros x q Hsem Hax.
  eapply (completeness_step_left_det _ _ x).
  - apply ichoice_singleton_no_ext.
  - simpl. apply lts_choiceL. apply lts_tau.
  - apply ichoice_singleton_tau_inv.
  - intros t Ht. apply Hsem. eapply must_i_tau_below; [ | exact Ht ].
    simpl. apply lts_choiceL. apply lts_tau.
  - intros _. exact Hax.
Qed.

(** ** …AND IN GENERAL: AN UNSTABLE LEFT *IS* AN INTERNAL CHOICE

    Drop the confluence assumption and the collapse still says something,
    because the target it collapses to may be chosen to be the internal
    choice of **all** the τ-successors:

    - [ax_ichoice_below] puts [ichoice (tau_list p)] below each successor,
      which is exactly [left_tau_collapse]'s premise, so
      [ichoice (tau_list p) ⊑ₘᵤₛₜᵢ p];
    - [ax_ichoice_of_taus] gives the derivation the other way,
      [⊢ p ⊑ ichoice (tau_list p)].

    Together: a [p] with a [τ] and no external transition is
    **must-equivalent to the internal choice of its τ-successors**, and
    the goal [⊢ p ⊑ q] may be replaced by [⊢ ichoice (tau_list p) ⊑ q]
    with its semantic side established.  The replacement costs nothing in
    the recursion, which measures the right-hand side only.

    So the left-unstable case reduces to a left that is *literally* an
    internal choice — the shape [ax_share_in], [ax_convex] and
    [ax_int_glb] are written for.  What is still missing is the driver
    that consumes it: the VACCS analogue of VCCS's [ax_M_below], which
    walks the ⊕-tree on the left.  Every rule it would use is in the
    system; nothing drives them from the left yet. *)

Lemma tau_list_nonempty : forall p, (exists z, lts p τ z) -> tau_list p <> nil.
Proof.
  intros p (z & Hz) Hnil.
  assert (Hin : In z (tau_list p)) by (apply tau_list_spec; exact Hz).
  rewrite Hnil in Hin. inversion Hin.
Qed.

Lemma left_ichoice_below : forall (p : proc),
  (exists z, lts p τ z) ->
  (forall a z, ~ lts p (ActExt a) z) ->
  (g (ichoice (tau_list p))) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ p.
Proof.
  intros p Hex Hnoext.
  apply left_tau_collapse; try assumption.
  intros q' Hq'.
  apply (soundness_ax _ _ (ax_ichoice_below (tau_list p) q'
           (proj2 (tau_list_spec p q') Hq'))).
Qed.

Lemma ax_left_ichoice : forall (p : proc),
  (exists z, lts p τ z) -> ax_pre p (g (ichoice (tau_list p))).
Proof.
  intros p Hex. apply ax_ichoice_of_taus.
  - apply tau_list_nonempty. exact Hex.
  - intros x Hx. eapply wt_tau; [ apply tau_list_spec; exact Hx | apply wt_nil ].
Qed.

Corollary left_ichoice_eq : forall (p : proc),
  (exists z, lts p τ z) ->
  (forall a z, ~ lts p (ActExt a) z) ->
  (p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g (ichoice (tau_list p))))
  /\ ((g (ichoice (tau_list p))) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ p).
Proof.
  intros p Hex Hnoext. split.
  - apply (soundness_ax _ _ (ax_left_ichoice p Hex)).
  - apply left_ichoice_below; assumption.
Qed.

Theorem completeness_step_left_ichoice : forall (p q : proc),
  (exists z, lts p τ z) ->
  (forall a z, ~ lts p (ActExt a) z) ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  ((g (ichoice (tau_list p))) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
     ax_pre (g (ichoice (tau_list p))) q) ->
  ax_pre p q.
Proof.
  intros p q Hex Hnoext Hpre HR.
  eapply ax_trans; [ apply ax_left_ichoice; exact Hex | ].
  apply HR. intros t Ht. apply Hpre.
  apply (left_ichoice_below p Hex Hnoext). exact Ht.
Qed.

(** ** …AND THE LEFT MAY BE ASSUMED TO BE A NORMAL FORM TOO

    [completeness_of_stable_NF_step] puts the *right* into normal form,
    at the cost of a [domsim] — because the recursion measures the right
    and the reducts of the normal form must be measured against the
    original [q].

    On the left it is far cheaper: nothing measures the left, so plain
    [normal_form] suffices.  [ax_trans] moves the goal onto the normal
    form, and [soundness_ax] transports the hypothesis back.

    One care is needed, and it is why the case split is redone here
    rather than reused: [⊢ p ≂ NF n1 l1 M1] does **not** transport
    "[p] has a τ" (a normal form may be stable where [p] is not —
    [g (𝛕•𝟘 + 𝛕•𝟘) ≂ₘᵤₛₜᵢ 𝟘]).  So the τ-stability test is taken on the
    normal form itself, and its stable branch is closed by
    [stable_bag_stable_left], which asks nothing of the left beyond
    stability. *)

Theorem completeness_of_hard_NF_step :
  (forall (q : proc) n1 l1 M1 n l M, Static q ->
     gStatic M1 -> gStatic M ->
     domsim q (NF n l M) ->
     (forall z, ~ lts (NF n l M) τ z) ->
     l <> [] ->
     (n <> 0%nat \/ (exists z, lts (NF n1 l1 M1) τ z)) ->
     (NF n1 l1 M1) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
     (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
        p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
     ax_pre (NF n1 l1 M1) (NF n l M)) ->
  forall p q, Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros Hstep. apply completeness_of_stable_bag_step.
  intros p q n l M Hp Hq HM Hsim Hno Hne Hpre HR.
  destruct (normal_form p Hp) as (n1 & l1 & M1 & HM1 & Hp1 & Hp2).
  assert (Hs1 : Static (NF n1 l1 M1)) by (apply Static_NF; exact HM1).
  assert (Hsem1 : (NF n1 l1 M1) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q).
  { intros t Ht. apply Hpre. apply (soundness_ax _ _ Hp2). exact Ht. }
  eapply ax_trans; [ exact Hp1 | ].
  destruct n as [|n'].
  - destruct (lts_dec (NF n1 l1 M1) τ) as [Hst | (z & Hz)].
    + assert (Heq : NF 0%nat l M = (msgs l ‖ ((g M) : proc))) by reflexivity.
      rewrite Heq. rewrite Heq in Hsim, Hno.
      apply (stable_bag_stable_left (NF n1 l1 M1) q l M); assumption.
    + apply (Hstep q n1 l1 M1 0%nat l M); try assumption.
      right. exists z. exact Hz.
  - apply (Hstep q n1 l1 M1 (S n') l M); try assumption.
    left. discriminate.
Qed.

(** ** THE RESTRICTION BLOCK GOES WHEN NO MESSAGE IS TRAPPED

    [stable_NF_empty_bag] removes the block when the bag is *empty*.
    With a bag it cannot, in general: a message on the just-restricted
    channel neither escapes ([VarC_action_add 1] never produces
    [bvar 0]) nor can be supplied from outside, and it is **not**
    removable either — a visible transition may re-expose the restricted
    channel, so [ν ((bvar 0 ! v • 𝟘) ‖ (c ? (bvar 0 ? ①)))] is not
    [ν (c ? (bvar 0 ? ①))].

    But that is the *trapped* case only.  A message whose channel
    survives the block is pulled straight out by scope extrusion, and
    what is left is [Ѵⁿ (g M)], which [resgn] flattens
    ([domsim_resgn]).  So an **untrapped** bag reduces the block to
    nothing, and the reduction carries the measure because every step is
    a [domsim].

    "Untrapped" is decided by [untrappedB]: a channel survives [n]
    binders when it is a constant or a [bvar i] with [n ≤ i], and
    [untrappedB_inv] then reads the bag back as a shift of a smaller one
    — which is exactly the shape [cgr_res_scope_n] consumes, so no
    inverse-shift construction is needed. *)

Definition untrappedC (n : nat) (c : ChannelData) : bool :=
  match c with cst _ => true | bvar i => Nat.leb n i end.

Definition untrappedB (n : nat) (l : list (ChannelData * ValueData)) : bool :=
  forallb (fun cv => untrappedC n (fst cv)) l.

Lemma iter_shift_bvar : forall n j,
  Nat.iter n (NewVar_in_ChannelData 0) (bvar j) = bvar (n + j).
Proof.
  induction n as [|n IH]; intro j; simpl; [ reflexivity | ].
  rewrite IH. simpl. reflexivity.
Qed.

Lemma iter_shift_cst : forall n a,
  Nat.iter n (NewVar_in_ChannelData 0) (cst a) = cst a.
Proof.
  induction n as [|n IH]; intro a; simpl; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma untrappedC_inv : forall n c, untrappedC n c = true ->
  exists c0, Nat.iter n (NewVar_in_ChannelData 0) c0 = c.
Proof.
  intros n [j|a] H.
  - simpl in H. exists (cst j). apply iter_shift_cst.
  - simpl in H. apply Nat.leb_le in H.
    exists (bvar (a - n)). rewrite iter_shift_bvar. f_equal. lia.
Qed.

Lemma untrappedB_inv : forall n l, untrappedB n l = true ->
  exists l0, l = map (shiftCn 0 n) l0.
Proof.
  intros n. induction l as [|cv l IH]; intro H.
  - exists []. reflexivity.
  - simpl in H. apply andb_prop in H as (H1 & H2).
    destruct (untrappedC_inv n (fst cv) H1) as (c0 & Hc0).
    destruct (IH H2) as (l0 & Hl0).
    exists ((c0, snd cv) :: l0). simpl. rewrite <- Hl0.
    unfold shiftCn. simpl. rewrite Hc0. destruct cv. reflexivity.
Qed.

Lemma untrappedC_shift : forall n c0,
  untrappedC n (Nat.iter n (NewVar_in_ChannelData 0) c0) = true.
Proof.
  intros n [j|a].
  - rewrite iter_shift_cst. reflexivity.
  - rewrite iter_shift_bvar. simpl. apply Nat.leb_le. lia.
Qed.

Lemma untrappedB_shift : forall n l0, untrappedB n (map (shiftCn 0 n) l0) = true.
Proof.
  intros n. induction l0 as [|cv l0 IH]; simpl; [ reflexivity | ].
  apply andb_true_intro. split; [ | exact IH ].
  unfold shiftCn. simpl. apply untrappedC_shift.
Qed.

(** Scope extrusion, read backwards: an untrapped bag comes out of the
    block, leaving [Ѵⁿ (g M)] behind. *)

Lemma NF_extrude : forall n l0 M,
  NF n (map (shiftCn 0 n) l0) M ≡* (msgs l0 ‖ (Ѵ n ((g M) : proc))).
Proof.
  intros n l0 M. unfold NF.
  rewrite <- NewVarCn_msgs.
  etransitivity; [ apply cgr_res_n; apply cgr_par_com | ].
  etransitivity; [ | apply cgr_par_com ].
  symmetry. apply cgr_res_scope_n.
Qed.

Lemma domsim_NF_extrude : forall n l0 M,
  domsim (NF n (map (shiftCn 0 n) l0) M) (NF 0%nat l0 (resgn n M)).
Proof.
  intros n l0 M.
  eapply domsim_trans; [ apply domsim_cgr; apply NF_extrude | ].
  unfold NF. simpl.
  apply domsim_par; [ apply domsim_refl | apply domsim_resgn ].
Qed.

(** So the residue's restriction block is only ever in the way when the
    bag really is trapped. *)

Theorem completeness_of_trapped_NF_step :
  (forall (q : proc) n1 l1 M1 n l M, Static q ->
     gStatic M1 -> gStatic M ->
     domsim q (NF n l M) ->
     (forall z, ~ lts (NF n l M) τ z) ->
     l <> [] ->
     (n <> 0%nat \/ (exists z, lts (NF n1 l1 M1) τ z)) ->
     (n <> 0%nat -> untrappedB n l = false) ->
     (NF n1 l1 M1) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
     (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
        p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
     ax_pre (NF n1 l1 M1) (NF n l M)) ->
  forall p q, Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros Hstep. apply completeness_of_hard_NF_step.
  intros q n1 l1 M1 n l M Hq HM1 HM Hsim Hno Hne Hdisj Hsem HR.
  destruct (untrappedB n l) eqn:Hu.
  - destruct (untrappedB_inv n l Hu) as (l0 & Hl0). subst l.
    assert (Hd : domsim (NF n (map (shiftCn 0 n) l0) M) (NF 0%nat l0 (resgn n M)))
      by apply domsim_NF_extrude.
    assert (HR0 : gStatic (resgn n M)) by (apply resgn_gStatic; exact HM).
    assert (Hs0 : domsim q (NF 0%nat l0 (resgn n M)))
      by (eapply domsim_trans; [ exact Hsim | exact Hd ]).
    assert (Hno0 : forall z, ~ lts (NF 0%nat l0 (resgn n M)) τ z)
      by (eapply domsim_stable; [ exact Hd | exact Hno ]).
    assert (Hne0 : l0 <> []) by (intro Hc; subst l0; apply Hne; reflexivity).
    eapply ax_trans; [ | apply (ds_r Hd) ].
    destruct (lts_dec (NF n1 l1 M1) τ) as [Hst | (z & Hz)].
    + apply (stable_bag_stable_left (NF n1 l1 M1) q l0 (resgn n M));
        try assumption.
      apply Static_NF; exact HM1.
    + apply (Hstep q n1 l1 M1 0%nat l0 (resgn n M)); try assumption.
      * right. exists z. exact Hz.
      * intro Hc. exfalso. apply Hc. reflexivity.
  - apply (Hstep q n1 l1 M1 n l M); try assumption. intro. exact Hu.
Qed.

(** The criterion is neither vacuous nor trivial: [bvar 1] survives one
    binder and comes out of the block, [bvar 0] does not. *)

Lemma untrapped_shift_one : forall (v : ValueData),
  [((bvar 1) : ChannelData, v)] = map (shiftCn 0 1) [((bvar 0) : ChannelData, v)].
Proof. intro v. simpl. unfold shiftCn. simpl. reflexivity. Qed.

Example untrapped_criterion_fires : forall (v : ValueData) (M : gproc),
  untrappedB 1 [((bvar 1) : ChannelData, v)] = true
  /\ domsim (NF 1%nat [((bvar 1) : ChannelData, v)] M)
            (NF 0%nat [((bvar 0) : ChannelData, v)] (resg M)).
Proof.
  intros v M. split; [ reflexivity | ].
  rewrite (untrapped_shift_one v).
  apply (domsim_NF_extrude 1%nat [((bvar 0) : ChannelData, v)] M).
Qed.

Example untrapped_criterion_bites : forall (v : ValueData),
  untrappedB 1 [((bvar 0) : ChannelData, v)] = false.
Proof. intro v. reflexivity. Qed.

(** ** …AND THE LEFT'S BLOCK GOES THE SAME WAY

    The left is extruded exactly as the right was, and the τ-existence
    disjunct — which does *not* transport along [⊢] — costs nothing here
    because the case split is simply **redone after** the extrusion:
    when [n ≠ 0] the disjunct is the left one and no test is needed; when
    [n = 0] the right is already [msgs l ‖ g M], so a stable extruded
    left is closed by [stable_bag_stable_left] and an unstable one feeds
    the step. *)

Theorem completeness_of_trapped_both_step :
  (forall (q : proc) n1 l1 M1 n l M, Static q ->
     gStatic M1 -> gStatic M ->
     domsim q (NF n l M) ->
     (forall z, ~ lts (NF n l M) τ z) ->
     l <> [] ->
     (n <> 0%nat \/ (exists z, lts (NF n1 l1 M1) τ z)) ->
     (n <> 0%nat -> untrappedB n l = false) ->
     (n1 <> 0%nat -> untrappedB n1 l1 = false) ->
     (NF n1 l1 M1) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
     (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
        p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
     ax_pre (NF n1 l1 M1) (NF n l M)) ->
  forall p q, Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros Hstep. apply completeness_of_trapped_NF_step.
  intros q n1 l1 M1 n l M Hq HM1 HM Hsim Hno Hne Hdisj Htr Hsem HR.
  destruct (untrappedB n1 l1) eqn:Hu1.
  - destruct (untrappedB_inv n1 l1 Hu1) as (l1' & Hl1). subst l1.
    assert (Hd1 : domsim (NF n1 (map (shiftCn 0 n1) l1') M1)
                         (NF 0%nat l1' (resgn n1 M1)))
      by apply domsim_NF_extrude.
    assert (HRg : gStatic (resgn n1 M1)) by (apply resgn_gStatic; exact HM1).
    assert (HsL : Static (NF 0%nat l1' (resgn n1 M1))) by (apply Static_NF; exact HRg).
    assert (HsemL : (NF 0%nat l1' (resgn n1 M1)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q).
    { intros t Ht. apply Hsem. apply (soundness_ax _ _ (ds_r Hd1)). exact Ht. }
    eapply ax_trans; [ apply (ds_l Hd1) | ].
    destruct n as [|n'].
    + assert (Heq : NF 0%nat l M = (msgs l ‖ ((g M) : proc))) by reflexivity.
      destruct (lts_dec (NF 0%nat l1' (resgn n1 M1)) τ) as [Hst | (z & Hz)].
      * rewrite Heq. rewrite Heq in Hsim, Hno.
        apply (stable_bag_stable_left (NF 0%nat l1' (resgn n1 M1)) q l M);
          assumption.
      * apply (Hstep q 0%nat l1' (resgn n1 M1) 0%nat l M); try assumption.
        -- right. exists z. exact Hz.
        -- intro Hc. exfalso. apply Hc. reflexivity.
    + apply (Hstep q 0%nat l1' (resgn n1 M1) (S n') l M); try assumption.
      * left. discriminate.
      * intro Hc. exfalso. apply Hc. reflexivity.
  - apply (Hstep q n1 l1 M1 n l M); try assumption. intro. exact Hu1.
Qed.

(** ** …AND A MUTE LEFT IS ALREADY DONE

    When both blocks are gone the two sides are bare configurations, and
    the case where the left's guarded sum can **never emit along any run**
    ([ochans (g M1) = []]) is exactly [completeness_cfg_mute_dom], proved
    long ago and until now not wired into this chain.  Its recursive
    premise is over [DomOk], and [ax_below_of_domok] converts the
    [size]-indexed one this chain carries.

    Note the criterion is on the **sum** only: the left's own pending
    messages are allowed, since they go to the bag and never to [M1]. *)

Theorem completeness_of_emitting_left_step :
  (forall (q : proc) n1 l1 M1 n l M, Static q ->
     gStatic M1 -> gStatic M ->
     domsim q (NF n l M) ->
     (forall z, ~ lts (NF n l M) τ z) ->
     l <> [] ->
     (n <> 0%nat \/ (exists z, lts (NF n1 l1 M1) τ z)) ->
     (n <> 0%nat -> untrappedB n l = false) ->
     (n1 <> 0%nat -> untrappedB n1 l1 = false) ->
     (n = 0%nat -> n1 = 0%nat -> ochans ((g M1) : proc) <> []) ->
     (NF n1 l1 M1) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
     (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
        p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
     ax_pre (NF n1 l1 M1) (NF n l M)) ->
  forall p q, Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros Hstep. apply completeness_of_trapped_both_step.
  intros q n1 l1 M1 n l M Hq HM1 HM Hsim Hno Hne Hdisj Htr Htr1 Hsem HR.
  destruct n as [|n']; [ destruct n1 as [|n1'] | ].
  - destruct (ochans ((g M1) : proc)) eqn:Hoc.
    + assert (Heq : NF 0%nat l M = (msgs l ‖ ((g M) : proc))) by reflexivity.
      assert (Heq1 : NF 0%nat l1 M1 = (msgs l1 ‖ ((g M1) : proc))) by reflexivity.
      rewrite Heq, Heq1.
      assert (Hsem2 : (msgs l1 ‖ ((g M1) : proc))
                        ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g M) : proc))).
      { intros t Ht. apply (soundness_ax _ _ (ds_l Hsim)). apply Hsem. exact Ht. }
      rewrite Heq in Hsim.
      apply (completeness_cfg_mute_dom q l1 l M1 M); try assumption.
      intros p' q' Hp' Hq' Hok Hs.
      eapply ax_below_of_domok; eassumption.
    + apply (Hstep q 0%nat l1 M1 0%nat l M); try assumption.
      intros _ _. rewrite Hoc. discriminate.
  - apply (Hstep q (S n1') l1 M1 0%nat l M); try assumption.
    intros _ Hc. discriminate.
  - apply (Hstep q n1 l1 M1 (S n') l M); try assumption.
    intro Hc. discriminate.
Qed.

(** ** THE RESIDUE, AS A SINGLE NAMED OBLIGATION

    Everything above is a chain of reductions; [HardResidue] is what it
    all bottoms out on, and [completeness_of_residue] is the statement
    that nothing else is missing. *)

Definition HardResidue : Prop :=
  forall (q : proc) n1 l1 M1 n l M, Static q ->
     gStatic M1 -> gStatic M ->
     domsim q (NF n l M) ->
     (forall z, ~ lts (NF n l M) τ z) ->
     l <> [] ->
     (n <> 0%nat \/ (exists z, lts (NF n1 l1 M1) τ z)) ->
     (n <> 0%nat -> untrappedB n l = false) ->
     (n1 <> 0%nat -> untrappedB n1 l1 = false) ->
     (n = 0%nat -> n1 = 0%nat -> ochans ((g M1) : proc) <> []) ->
     (NF n1 l1 M1) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
     (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
        p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> ax_pre p' q') ->
     ax_pre (NF n1 l1 M1) (NF n l M).

Theorem completeness_of_residue : HardResidue ->
  forall p q, Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof. exact completeness_of_emitting_left_step. Qed.

(** What the semantics does give about the residue's unstable left: the
    right's bag is non-empty, so the right emits, and a left below it
    must be able to emit too — **weakly**, which is exactly where the
    τ-stable case ([stable_left_extract]) and the unstable one part
    company, weak emission being strong only for a stable process. *)

Lemma residue_left_weak_emits : forall (p : proc) l M c v,
  Static p -> gStatic M -> In (c,v) l ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g M) : proc)) ->
  exists p1, p ⟹[[]] p1 /\ emits_on c p1.
Proof.
  intros p M0 M c v Hp HM Hin Hpre.
  apply in_split in Hin as (l1 & l2 & Hl).
  assert (Hperm : Permutation M0 ((c,v) :: (l1 ++ l2))).
  { rewrite Hl. symmetry. apply Permutation_middle. }
  destruct (cfg_out_of_perm M0 (l1 ++ l2) c v ((g M) : proc) Hperm) as (r & Hr & _).
  eapply weak_out_of_below; [ exact Hp | | exact Hpre | exact Hr ].
  apply Static_NF with (n := 0%nat) (l := M0) (M := M). exact HM.
Qed.

(** ** THE POOLING LAW, LIFTED TO A WHOLE BAG

    [ax_share_msg] pools two branches of an internal choice at **one**
    shared pending message.  Iterated over a message list it says that
    the **whole bag** factors out of a binary internal choice:

      (msgs l ‖ X) ⊕ (msgs l ‖ Y)  ≂  msgs l ‖ (X ⊕ Y)

    so an internal choice of two configurations **at a common bag** is a
    configuration whose process is an internal choice.  That is the shape
    the left-hand side of the residue would have to be brought into, and
    it is the first pooling law of this development that operates on the
    message layer rather than inside a guarded sum.

    The reverse direction is derivable from [ax_int_glb] and
    [ax_tau_step], so the two are must-equivalent ([share_msgs_eq]). *)

Lemma ax_choice_tau2 : forall (p1 p2 q1 q2 : proc),
  ax_pre p1 q1 -> ax_pre p2 q2 ->
  ax_pre (g ((𝛕 • p1) + (𝛕 • p2))) (g ((𝛕 • q1) + (𝛕 • q2))).
Proof.
  intros p1 p2 q1 q2 H1 H2.
  eapply ax_trans; [ apply (ax_choice_tau p1 q1 (𝛕 • p2) H1) | ].
  eapply ax_trans; [ apply ax_cgr; apply cgr_choice_com | ].
  eapply ax_trans; [ apply (ax_choice_tau p2 q2 (𝛕 • q1) H2) | ].
  apply ax_cgr. apply cgr_choice_com.
Qed.

Lemma ax_share_msgs : forall (l : list TypeOfActions) (X Y : proc),
  ax_pre (g ((𝛕 • (msgs l ‖ X)) + (𝛕 • (msgs l ‖ Y))))
         (msgs l ‖ ((g ((𝛕 • X) + (𝛕 • Y))) : proc)).
Proof.
  induction l as [|cv l IH]; intros X Y; simpl.
  - eapply ax_trans;
      [ apply ax_choice_tau2; apply ax_cgr; apply cgr_nil_par_l | ].
    apply ax_cgr_sym. apply cgr_nil_par_l.
  - destruct cv as (c, v).
    eapply ax_trans;
      [ apply ax_choice_tau2; apply ax_cgr; apply cgr_par_assoc | ].
    eapply ax_trans; [ apply ax_share_msg | ].
    eapply ax_trans; [ apply ax_par; [ apply ax_refl | apply IH ] | ].
    apply ax_cgr. apply cgr_par_assoc_rev.
Qed.

Corollary ax_share_msgs_rev : forall (l : list TypeOfActions) (X Y : proc),
  ax_pre (msgs l ‖ ((g ((𝛕 • X) + (𝛕 • Y))) : proc))
         (g ((𝛕 • (msgs l ‖ X)) + (𝛕 • (msgs l ‖ Y)))).
Proof.
  intros l X Y. apply ax_int_glb.
  - apply ax_par;
      [ apply ax_refl | apply ax_tau_step; apply lts_choiceL; apply lts_tau ].
  - apply ax_par;
      [ apply ax_refl | apply ax_tau_step; apply lts_choiceR; apply lts_tau ].
Qed.

Corollary share_msgs_eq : forall (l : list TypeOfActions) (X Y : proc),
  (g ((𝛕 • (msgs l ‖ X)) + (𝛕 • (msgs l ‖ Y))))
    ≂ₘᵤₛₜᵢ (msgs l ‖ ((g ((𝛕 • X) + (𝛕 • Y))) : proc)).
Proof.
  intros l X Y. split; apply soundness_ax;
    [ apply ax_share_msgs_rev | apply ax_share_msgs ].
Qed.

(** ** THE POOLING LAW, n-ARY — AND THE CONFIGURATION-LEVEL DECOMPOSITION

    Iterating [ax_share_msgs] over an [ichoice] gives the n-ary form: an
    internal choice of **any number** of configurations at a common bag is
    the configuration whose process is the internal choice of their
    processes.  The step from the binary law is one [ax_tau_flatten_r] to
    expose the tail as a τ-guard, [ax_choice_tau2] to rewrite it by the
    induction hypothesis, then the binary law and [ax_tau_flatten_l] back.

    The converse is derivable from [ax_ichoice_glb] and [ax_ichoice_below]
    over [ax_par], as at the binary level. *)

Lemma ax_share_msgs_ichoice : forall (l : list TypeOfActions) (L : list proc),
  L <> nil ->
  ax_pre (g (ichoice (map (fun x => msgs l ‖ x) L)))
         (msgs l ‖ ((g (ichoice L)) : proc)).
Proof.
  intros l L. induction L as [|x L IH]; intro Hne; [ contradiction | ].
  destruct L as [|y L'].
  - simpl. apply ax_share_msgs.
  - assert (Hne' : (y :: L') <> nil) by discriminate.
    assert (HAT : gAllTau (ichoice (map (fun x => msgs l ‖ x) (y :: L'))))
      by (apply ichoice_gAllTau; discriminate).
    assert (HAT' : gAllTau (ichoice (y :: L')))
      by (apply ichoice_gAllTau; exact Hne').
    simpl map. simpl ichoice.
    eapply ax_trans; [ apply ax_tau_flatten_r; exact HAT | ].
    eapply ax_trans;
      [ apply ax_choice_tau2; [ apply ax_refl | apply IH; exact Hne' ] | ].
    eapply ax_trans; [ apply ax_share_msgs | ].
    apply ax_par; [ apply ax_refl | apply ax_tau_flatten_l; exact HAT' ].
Qed.

Lemma ax_share_msgs_ichoice_rev : forall (l : list TypeOfActions) (L : list proc),
  L <> nil ->
  ax_pre (msgs l ‖ ((g (ichoice L)) : proc))
         (g (ichoice (map (fun x => msgs l ‖ x) L))).
Proof.
  intros l L Hne. apply ax_ichoice_glb.
  - destruct L as [|x L]; [ contradiction | discriminate ].
  - intros p Hin. apply in_map_iff in Hin as (x & <- & Hx).
    apply ax_par; [ apply ax_refl | apply ax_ichoice_below; exact Hx ].
Qed.

(** And here is what it buys.  A configuration whose **process has no
    external offer of its own** — everything visible about it is its bag
    — is, by [left_ichoice_eq], must-equivalent to the internal choice of
    that process's τ-branches; the n-ary law then carries the bag through
    and turns the **whole configuration** into the internal choice of the
    configurations at those branches, derivably in the useful direction
    and semantically both ways.

    That is the configuration-level counterpart of VCCS's leaf
    decomposition, and it is the first time the left-hand side of a
    completeness step is broken into branches *with its bag carried
    along*.  A guarded sum that is all-τ is the intended instance
    ([completeness_step_cfg_alltau]), but nothing in the argument needs
    the process to be a sum. *)

Lemma ax_cfg_noext_ichoice : forall (l : list TypeOfActions) (p : proc),
  (exists z, lts p τ z) ->
  (forall a z, ~ lts p (ActExt a) z) ->
  ax_pre (msgs l ‖ p)
         (g (ichoice (map (fun x => msgs l ‖ x) (tau_list p)))).
Proof.
  intros l p Hex Hnoext.
  eapply ax_trans;
    [ apply ax_par; [ apply ax_refl | apply ax_left_ichoice; exact Hex ] | ].
  apply ax_share_msgs_ichoice_rev. apply tau_list_nonempty. exact Hex.
Qed.

Lemma cfg_noext_ichoice_below : forall (l : list TypeOfActions) (p : proc),
  (exists z, lts p τ z) ->
  (forall a z, ~ lts p (ActExt a) z) ->
  (g (ichoice (map (fun x => msgs l ‖ x) (tau_list p))))
    ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ p).
Proof.
  intros l p Hex Hnoext t Ht.
  apply (must_i_par_compat_r (msgs l) _ _ (left_ichoice_below p Hex Hnoext)).
  apply (soundness_ax _ _
          (ax_share_msgs_ichoice l (tau_list p) (tau_list_nonempty _ Hex))).
  exact Ht.
Qed.

Theorem completeness_step_cfg_noext :
  forall (l : list TypeOfActions) (p q : proc),
  (exists z, lts p τ z) ->
  (forall a z, ~ lts p (ActExt a) z) ->
  (msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  ((g (ichoice (map (fun x => msgs l ‖ x) (tau_list p)))) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
   ax_pre (g (ichoice (map (fun x => msgs l ‖ x) (tau_list p)))) q) ->
  ax_pre (msgs l ‖ p) q.
Proof.
  intros l p q Hex Hnoext Hpre HR.
  eapply ax_trans; [ apply ax_cfg_noext_ichoice; assumption | ].
  apply HR. intros t Ht. apply Hpre.
  apply (cfg_noext_ichoice_below l p Hex Hnoext). exact Ht.
Qed.

(** The intended instance: an all-τ guarded sum. *)

Corollary completeness_step_cfg_alltau :
  forall (l : list TypeOfActions) (M : gproc) (q : proc),
  gAllTau M ->
  (msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  ((g (ichoice (map (fun x => msgs l ‖ x) (tau_list ((g M) : proc)))))
     ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
   ax_pre (g (ichoice (map (fun x => msgs l ‖ x) (tau_list ((g M) : proc))))) q) ->
  ax_pre (msgs l ‖ ((g M) : proc)) q.
Proof.
  intros l M q HAT.
  apply completeness_step_cfg_noext.
  - apply gAllTau_has_tau; exact HAT.
  - intros a z Hl. eapply gAllTau_no_ext; [ exact HAT | exact Hl ].
Qed.

(** * THE LEAF LAYER — union closure of the acceptance family

    Ported from VCCS's [CompletenessAx.v], where it is the first stage of
    [ax_M_below].  [leaves] reads the stable leaves off a [tau_nf] tree,
    [leafsum] is their **external** sum, and the two facts that matter are

    - [leaves_below] — every leaf is derivably *above* the tree, one
      [ax_int_l]/[ax_int_r] per level; this is how a matching argument
      discards the leaves it does not need;
    - [ax_leafsum] — the tree is derivably below the external sum of all
      its leaves, i.e. **union closure** of the acceptance family, and it
      is where [ax_int_below_ext] earns its keep.

    The port is mechanical apart from two VACCS-specific simplifications:
    [ax_cgr] carries no [Static] side condition, and [ax_int_l]/[ax_int_r]
    none either, so every [apply ax_cgr; [ … | … ]] loses its first
    branch.  The [⊕]-congruence step still needs [ax_choice_tau] *twice*
    with a commutation in between — the rule only ever rewrites the
    leftmost summand. *)

Fixpoint leaves (M : gproc) : list gproc :=
  if gStableB M then [M]
  else match M with
       | (𝛕 • (g A)) + (𝛕 • (g B)) => leaves A ++ leaves B
       | _ => [M]
       end.

Lemma leaves_eq : forall M, leaves M =
  if gStableB M then [M]
  else match M with
       | (𝛕 • (g A)) + (𝛕 • (g B)) => leaves A ++ leaves B
       | _ => [M]
       end.
Proof. intro M. destruct M; reflexivity. Qed.

Lemma gStatic_tau_choice : forall M1 M2,
  gStatic ((𝛕 • ((g M1) : proc)) + (𝛕 • ((g M2) : proc))) -> gStatic M1 /\ gStatic M2.
Proof.
  intros M1 M2 H. inversion H; subst.
  match goal with HA : gStatic (𝛕 • ((g M1) : proc)) |- _ => inversion HA; subst end.
  match goal with HB : gStatic (𝛕 • ((g M2) : proc)) |- _ => inversion HB; subst end.
  match goal with HA : Static ((g M1) : proc) |- _ => inversion HA; subst end.
  match goal with HB : Static ((g M2) : proc) |- _ => inversion HB; subst end.
  split; assumption.
Qed.

Lemma leaves_gStatic : forall M, gStatic M -> Forall gStatic (leaves M).
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  intro HM. rewrite leaves_eq.
  destruct (gStableB M) eqn:E; [constructor; [exact HM | constructor] |].
  destruct M; try (constructor; [exact HM | constructor]).
  destruct M1; try (constructor; [exact HM | constructor]).
  destruct p; try (constructor; [exact HM | constructor]).
  destruct M2; try (constructor; [exact HM | constructor]).
  destruct p; try (constructor; [exact HM | constructor]).
  destruct (gStatic_tau_choice _ _ HM) as (Hg1 & Hg2).
  apply Forall_app. split.
  - apply IH; [simpl; lia | assumption].
  - apply IH; [simpl; lia | assumption].
Qed.

Lemma leaves_stable : forall M, tau_nf M -> Forall gStable (leaves M).
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  intro HM. rewrite leaves_eq.
  destruct (gStableB M) eqn:E.
  - constructor; [apply gStableB_spec; exact E | constructor].
  - inversion HM as [? Hs | A B HA HB]; subst.
    + exfalso. apply gStableB_spec in Hs. rewrite Hs in E. discriminate E.
    + simpl. apply Forall_app. split.
      * apply IH; [simpl; lia | exact HA].
      * apply IH; [simpl; lia | exact HB].
Qed.

Lemma leaves_below : forall M, gStatic M -> tau_nf M ->
  forall A, In A (leaves M) -> ax_pre ((g M) : proc) ((g A) : proc).
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  intros HgM HM A Hin. rewrite leaves_eq in Hin.
  destruct (gStableB M) eqn:E.
  - destruct Hin as [<- | []]. apply ax_refl.
  - inversion HM as [? Hs | M1 M2 H1 H2]; subst.
    + exfalso. apply gStableB_spec in Hs. rewrite Hs in E. discriminate E.
    + destruct (gStatic_tau_choice M1 M2 HgM) as (Hgs1 & Hgs2).
      simpl in Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      * eapply ax_trans;
          [apply ax_int_l | apply IH; [simpl; lia | exact Hgs1 | exact H1 | exact Hin]].
      * eapply ax_trans;
          [apply ax_int_r | apply IH; [simpl; lia | exact Hgs2 | exact H2 | exact Hin]].
Qed.

Definition leafsum (M : gproc) : gproc := rebuild (leaves M).

Lemma leafsum_gStatic : forall M, gStatic M -> gStatic (leafsum M).
Proof. intros M HM. apply rebuild_gStatic. apply leaves_gStatic. exact HM. Qed.

Lemma ax_leafsum : forall M, gStatic M -> tau_nf M ->
  ax_pre ((g M) : proc) ((g (leafsum M)) : proc).
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  intros HMst HM. unfold leafsum. rewrite leaves_eq.
  destruct (gStableB M) eqn:E.
  - simpl. apply ax_cgr. apply cgr_choice_nil_rev.
  - inversion HM as [? Hs | M1 M2 H1 H2]; subst.
    + exfalso. apply gStableB_spec in Hs. rewrite Hs in E. discriminate E.
    + destruct (gStatic_tau_choice M1 M2 HMst) as (Hg1 & Hg2).
      assert (Hl1 : ax_pre ((g M1) : proc) ((g (leafsum M1)) : proc))
        by (apply IH; [simpl; lia | exact Hg1 | exact H1]).
      assert (Hl2 : ax_pre ((g M2) : proc) ((g (leafsum M2)) : proc))
        by (apply IH; [simpl; lia | exact Hg2 | exact H2]).
      eapply ax_trans;
        [apply (ax_choice_tau ((g M1) : proc) ((g (leafsum M1)) : proc)
                  (𝛕 • ((g M2) : proc))); exact Hl1 |].
      eapply ax_trans;
        [apply ax_cgr with
           (q := g ((𝛕 • ((g M2) : proc)) + (𝛕 • ((g (leafsum M1)) : proc))));
         apply cgr_choice_com |].
      eapply ax_trans;
        [apply (ax_choice_tau ((g M2) : proc) ((g (leafsum M2)) : proc)
                  (𝛕 • ((g (leafsum M1)) : proc))); exact Hl2 |].
      eapply ax_trans; [apply ax_int_below_ext |].
      apply ax_cgr.
      transitivity ((g (leafsum M1 + leafsum M2)) : proc);
        [apply cgr_choice_com | ].
      symmetry. apply rebuild_app.
Qed.

(** Union closure lifts to a configuration for free: [ax_par] carries it
    under the bag, no sharing law needed — the bag is untouched. *)

Corollary ax_cfg_leafsum : forall (l : list TypeOfActions) (M : gproc),
  gStatic M -> tau_nf M ->
  ax_pre (msgs l ‖ ((g M) : proc)) (msgs l ‖ ((g (leafsum M)) : proc)).
Proof.
  intros l M HM Hnf.
  apply ax_par; [ apply ax_refl | apply ax_leafsum; assumption ].
Qed.

(** ** …AND THE LEAVES ARE EXACTLY THE INTERNALLY-REACHABLE STABLE STATES

    [leaves_below] is the derivational reading; these two are the
    semantic one, and together they pin [⟹[[]]] down on a [tau_nf]
    completely: every leaf is reached by internal moves alone, and every
    stable state so reached **is** a leaf.  That is what turns the
    anonymous witness a behavioural condition hands back into a leaf the
    derivation can name.

    [wt_cons_stable] is the companion for a visible action: a stable
    process's run over [μ :: s] must *start* with its [μ]-step. *)

Lemma wt_cons_stable : forall (p r : proc) (mu : ExtAct TypeOfActions)
    (s : trace (ExtAct TypeOfActions)),
  (forall z, ~ lts p τ z) -> p ⟹[mu :: s] r ->
  exists q, lts p (ActExt mu) q /\ q ⟹[s] r.
Proof.
  intros p r mu s Hst Hwt. inversion Hwt; subst.
  - exfalso. eapply Hst. eassumption.
  - eexists. split; eassumption.
Qed.

Lemma leaves_reach : forall M, tau_nf M ->
  forall A, In A (leaves M) -> ((g M) : proc) ⟹[[]] ((g A) : proc).
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  intros HM A Hin. rewrite leaves_eq in Hin.
  destruct (gStableB M) eqn:E.
  - destruct Hin as [<- | []]. apply wt_nil.
  - inversion HM as [? Hs | M1 M2 H1 H2]; subst.
    + exfalso. apply gStableB_spec in Hs. rewrite Hs in E. discriminate E.
    + simpl in Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      * eapply wt_tau; [apply lts_choiceL; apply lts_tau |].
        apply IH; [simpl; lia | exact H1 | exact Hin].
      * eapply wt_tau; [apply lts_choiceR; apply lts_tau |].
        apply IH; [simpl; lia | exact H2 | exact Hin].
Qed.

Lemma leaves_wt_stable : forall M, tau_nf M ->
  forall r, ((g M) : proc) ⟹[[]] r -> (forall z, ~ lts r τ z) ->
  exists A, In A (leaves M) /\ r = ((g A) : proc).
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  intros HM r Hwt Hst.
  inversion HM as [? Hs | M1 M2 H1 H2]; subst.
  - exists M. split.
    + rewrite leaves_eq. rewrite (proj2 (gStableB_spec M) Hs). left. reflexivity.
    + apply (wt_nil_stable ((g M) : proc) r);
        [ apply (proj2 (gStable_iff M) Hs) | exact Hwt ].
  - assert (E : gStableB ((𝛕 • ((g M1) : proc)) + (𝛕 • ((g M2) : proc))) = false)
      by reflexivity.
    rewrite leaves_eq. rewrite E.
    inversion Hwt; subst.
    + exfalso. eapply Hst. apply lts_choiceL. apply lts_tau.
    + inversion l; subst.
      * inversion H5; subst.
        destruct (IH M1 ltac:(simpl; lia) H1 r w Hst) as (A & Hin & Heq).
        exists A. split; [ apply in_app_iff; left; exact Hin | exact Heq ].
      * inversion H5; subst.
        destruct (IH M2 ltac:(simpl; lia) H2 r w Hst) as (A & Hin & Heq).
        exists A. split; [ apply in_app_iff; right; exact Hin | exact Heq ].
Qed.

(** * [ax_M_below] FOR VACCS — three lines, where VCCS needs forty lemmas

    VCCS's [ax_M_below] builds, from a [tau_nf] left-hand side, a
    **stable canonical** sum derivably above it, and to do so it carries a
    whole association-list apparatus ([kguard], [build], [kmem],
    [kcollapse], [kshare_iter], [ax_build_align], …) because its keys are
    [(channel, option value)] — an output guard carries a value, so
    merging same-key guards and aligning two key lists is real work.

    In VACCS there is **no output guard**, so a key is a plain channel,
    and the collapse of same-channel guards is exactly [canonicalize]
    ([VACCS_Canonical.v]), proved long ago for [Bad]'s sake.  Composing it
    with the leaf layer gives the whole theorem:

      [ax_leafsum]   : the tree is below the external sum of its leaves
      [canonicalize] : and that sum collapses to a canonical one,
                       pooling the continuations at each channel into an
                       internal choice — which *is* the acceptance-tree
                       uniformity condition.

    Note what this is and is not.  It is the **union-closure** step: [B]
    passes strictly more tests than [g M], so it cannot on its own carry
    a completeness hypothesis across — that is what [ax_convex] is for,
    exactly as in VCCS. *)

Lemma rebuild_gStable : forall l, Forall gStable l -> gStable (rebuild l).
Proof.
  induction l as [|a l IH]; intro H; simpl; [ exact I | ].
  inversion H; subst. split; [ assumption | apply IH; assumption ].
Qed.

Lemma leafsum_gStable : forall M, tau_nf M -> gStable (leafsum M).
Proof.
  intros M HM. apply rebuild_gStable. apply leaves_stable. exact HM.
Qed.

Theorem ax_M_below : forall M, gStatic M -> tau_nf M ->
  exists B, gStatic B /\ gStable B /\ canonical B /\ ax_pre ((g M) : proc) ((g B) : proc).
Proof.
  intros M HM Hnf.
  destruct (canonicalize (leafsum M) (leafsum_gStatic M HM))
    as (B & HBst & HBstable & HBcan & HB).
  exists B. split; [ exact HBst | ].
  split; [ apply HBstable; apply leafsum_gStable; exact Hnf | ].
  split; [ exact HBcan | ].
  eapply ax_trans; [ apply ax_leafsum; assumption | exact HB ].
Qed.

(** …and it lifts to a configuration by [ax_par], the bag being
    untouched. *)

Corollary ax_cfg_M_below : forall (l : list TypeOfActions) (M : gproc),
  gStatic M -> tau_nf M ->
  exists B, gStatic B /\ gStable B /\ canonical B /\
    ax_pre (msgs l ‖ ((g M) : proc)) (msgs l ‖ ((g B) : proc)).
Proof.
  intros l M HM Hnf.
  destruct (ax_M_below M HM Hnf) as (B & HBst & HBstable & HBcan & HB).
  exists B. repeat split; try assumption.
  apply ax_par; [ apply ax_refl | exact HB ].
Qed.

(** * CONVEXITY AT AN ARBITRARY SUMMAND SPLIT

    [ax_convex]'s literal shape demands the middle term be syntactically
    [(X + Y) + Z] with the same [X] as the first branch.  In practice all
    that is ever known is a **permutation** of summands, so this is the
    usable form; [split_by]-style bookkeeping is not needed here because
    the caller supplies the split.

    [leafsum_split] is the glue: a leaf's own summands sit inside
    [leafsum M]'s, with a definite remainder — exactly the [Permutation]
    hypothesis [ax_convex_anywhere] consumes. *)

Lemma summands_rebuild_perm : forall l l', Permutation l l' ->
  Permutation (summands (rebuild l)) (summands (rebuild l')).
Proof.
  intros l l' Hp. induction Hp; simpl.
  - reflexivity.
  - apply Permutation_app_head. exact IHHp.
  - repeat rewrite app_assoc. apply Permutation_app_tail.
    apply Permutation_app_comm.
  - etransitivity; eassumption.
Qed.

Theorem ax_convex_anywhere : forall (W A : gproc) (Y Z : list gproc),
  gStatic A -> Forall gStatic Y -> Forall gStatic Z ->
  Permutation (summands W) (summands A ++ (Y ++ Z)) ->
  ax_pre (g ((𝛕 • ((g A) : proc)) + (𝛕 • ((g W) : proc))))
         (g (A + rebuild Y)).
Proof.
  intros W A Y Z HA HY HZ Hperm.
  assert (Hcgr : ((g W) : proc) ≡* ((g ((A + rebuild Y) + rebuild Z)) : proc)).
  { transitivity ((g (rebuild (summands W))) : proc); [apply summands_cgr |].
    transitivity ((g (rebuild (summands A ++ (Y ++ Z)))) : proc);
      [apply rebuild_perm; exact Hperm |].
    transitivity ((g (rebuild (summands A) + rebuild (Y ++ Z))) : proc);
      [apply rebuild_app |].
    transitivity ((g (A + rebuild (Y ++ Z))) : proc).
    - apply cgr_choice. symmetry. apply summands_cgr.
    - transitivity ((g (A + (rebuild Y + rebuild Z))) : proc).
      + apply cgr_fullchoice; [reflexivity | apply rebuild_app].
      + apply cgr_choice_assoc_rev. }
  eapply ax_trans;
    [ apply ax_cgr with
        (q := g ((𝛕 • ((g A) : proc))
               + (𝛕 • ((g ((A + rebuild Y) + rebuild Z)) : proc))))
    | apply ax_convex ].
  apply cgr_fullchoice; [reflexivity | apply cgr_tau; exact Hcgr].
Qed.

Lemma leafsum_split : forall M A, gStatic M -> In A (leaves M) ->
  exists R, Permutation (summands (leafsum M)) (summands A ++ R) /\ Forall gStatic R.
Proof.
  intros M A HM Hin.
  apply in_split in Hin as (k1 & k2 & Hk).
  assert (Hp : Permutation (leaves M) (A :: (k1 ++ k2)))
    by (rewrite Hk; symmetry; apply Permutation_middle).
  assert (Hst : Forall gStatic (A :: (k1 ++ k2))).
  { eapply Permutation_Forall; [exact Hp | apply leaves_gStatic; exact HM]. }
  inversion Hst as [|? ? _ Hk']; subst.
  exists (summands (rebuild (k1 ++ k2))). split.
  - unfold leafsum. etransitivity; [apply summands_rebuild_perm; exact Hp | reflexivity].
  - apply summands_gStatic. apply rebuild_gStatic. exact Hk'.
Qed.

(** And the payoff, which is the shape the matching wants: **a normal
    form is derivably below its chosen leaf enlarged by any
    sub-collection of the other leaves' summands.**  Union closure
    ([ax_leafsum]) goes up to *all* the leaves, [leaves_below] goes down
    to *one*, [ax_int_glb] holds both at once, and [ax_convex] lands on
    anything in between — which is exactly the convex closure of the
    acceptance family, and exactly why [ax_convex] had to be a rule. *)

Theorem ax_leaf_convex : forall (M A : gproc) (Y Z : list gproc),
  gStatic M -> tau_nf M -> In A (leaves M) ->
  Forall gStatic Y -> Forall gStatic Z ->
  Permutation (summands (leafsum M)) (summands A ++ (Y ++ Z)) ->
  ax_pre ((g M) : proc) ((g (A + rebuild Y)) : proc).
Proof.
  intros M A Y Z HM Hnf Hin HY HZ Hperm.
  assert (HA : gStatic A).
  { pose proof (leaves_gStatic M HM) as HF.
    rewrite Forall_forall in HF. apply HF. exact Hin. }
  eapply ax_trans;
    [ apply (ax_int_glb ((g M) : proc) ((g A) : proc) ((g (leafsum M)) : proc));
      [ apply leaves_below; assumption | apply ax_leafsum; assumption ] | ].
  apply (ax_convex_anywhere (leafsum M) A Y Z); assumption.
Qed.

(** The form a caller actually wants: **here is the remainder, keep any
    part of it**.  [leafsum_split] produces the remainder, the caller
    chooses the split, and the [gStatic] side conditions come along the
    permutation. *)

Corollary ax_leaf_convex_rest : forall (M A : gproc),
  gStatic M -> tau_nf M -> In A (leaves M) ->
  exists R, Forall gStatic R /\
    forall (Y Z : list gproc), Permutation R (Y ++ Z) ->
      ax_pre ((g M) : proc) ((g (A + rebuild Y)) : proc).
Proof.
  intros M A HM Hnf Hin.
  destruct (leafsum_split M A HM Hin) as (R & Hperm & HR).
  exists R. split; [ exact HR | ].
  intros Y Z Hsplit.
  assert (HYZ : Forall gStatic (Y ++ Z))
    by (eapply Permutation_Forall; [ exact Hsplit | exact HR ]).
  apply Forall_app in HYZ as (HY & HZ).
  apply (ax_leaf_convex M A Y Z HM Hnf Hin HY HZ).
  etransitivity; [ exact Hperm | ].
  apply Permutation_app_head. exact Hsplit.
Qed.

Corollary ax_cfg_leaf_convex_rest : forall (l : list TypeOfActions) (M A : gproc),
  gStatic M -> tau_nf M -> In A (leaves M) ->
  exists R, Forall gStatic R /\
    forall (Y Z : list gproc), Permutation R (Y ++ Z) ->
      ax_pre (msgs l ‖ ((g M) : proc)) (msgs l ‖ ((g (A + rebuild Y)) : proc)).
Proof.
  intros l M A HM Hnf Hin.
  destruct (ax_leaf_convex_rest M A HM Hnf Hin) as (R & HR & Hall).
  exists R. split; [ exact HR | ].
  intros Y Z Hsplit.
  apply ax_par; [ apply ax_refl | apply (Hall Y Z Hsplit) ].
Qed.

(** * A DELIMITATION: THE TWO BAGS NEED NOT BE RELATED AT ALL

    [bag_incl_of_below] gives [bag l ⊆ bag l1] under the **mute**
    criterion [ochans (g M1) = []], and the whole [msgs_cancel] family
    rests on it.  The criterion is not slack: without it the right's bag
    can be strictly larger, because the left's *process* may supply the
    missing message.

    The witness is already in the file — [glb_output_premise_not_semantic]'s
    example, read as two configurations:

      left  = msgs []      ‖ g (𝛕 • (c!v•𝟘))     (bag empty)
      right = msgs [(c,v)] ‖ g 𝟘                 (bag one message, and stable)

    The left is below the right ([must_i_tau_below]: a server's own τ is
    already a [⊑ₘᵤₛₜᵢ]-step), the right configuration is τ-stable, and yet
    [bag [(c,v)] ⊄ bag []].

    So for the residue — where the left is unstable and [ochans (g M1) ≠ []]
    by [completeness_of_emitting_left_step] — **no bag-cancellation
    argument can apply**, and the blocker is not the shape of the left's
    [⊕]-tree but the bag itself.  Note the instance is nevertheless
    derivable, by [ax_tau_step] onto the single τ-successor; it is the
    *choice* of that successor that does not generalise
    ([tau_successor_cannot_be_chosen]). *)

Lemma msgs_nil_par_stable : forall (l : list TypeOfActions) (z : proc),
  ~ lts (msgs l ‖ ((g (𝟘 : gproc)) : proc)) τ z.
Proof.
  intros l z Hz. inversion Hz; subst;
    try (eapply msgs_no_tau; eassumption);
    try (match goal with H : lts ((g (𝟘 : gproc)) : proc) _ _ |- _ =>
           eapply nil_no_lts; exact H end).
Qed.

Theorem bag_incl_fails_without_mute : forall (c : ChannelData) (v : ValueData),
  ((msgs (@nil TypeOfActions)) ‖ ((g (𝛕 • ((c ! v • 𝟘) : proc))) : proc))
    ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((msgs [(c,v)]) ‖ ((g (𝟘 : gproc)) : proc))
  /\ (forall z, ~ lts ((msgs [(c,v)]) ‖ ((g (𝟘 : gproc)) : proc)) τ z)
  /\ ~ (bag [(c,v)] ⊆ bag (@nil TypeOfActions)).
Proof.
  intros c v.
  assert (Hr : ((msgs [(c,v)]) ‖ ((g (𝟘 : gproc)) : proc)) ≡* ((c ! v • 𝟘) : proc)).
  { simpl. etransitivity; [ apply cgr_par_nil | apply cgr_par_nil ]. }
  assert (Hl : ((msgs (@nil TypeOfActions)) ‖ ((g (𝛕 • ((c ! v • 𝟘) : proc))) : proc))
                 ≡* ((g (𝛕 • ((c ! v • 𝟘) : proc))) : proc))
    by apply cgr_nil_par_l.
  split; [ | split ].
  - intros t Ht.
    apply (proj1 (must_i_cgr _ _ Hr)).
    eapply must_i_tau_below; [ apply lts_tau | ].
    apply (proj2 (must_i_cgr _ _ Hl)). exact Ht.
  - apply msgs_nil_par_stable.
  - intro Hsub.
    assert (Hm : ActOut (c,v) ∈ bag [(c,v)]).
    { simpl. apply gmultiset.gmultiset_elem_of_disj_union. left.
      apply gmultiset_elem_of_singleton. reflexivity. }
    assert (Hm2 : ActOut (c,v) ∈ bag (@nil TypeOfActions))
      by (eapply gmultiset_elem_of_subseteq; eassumption).
    simpl in Hm2. eapply gmultiset_not_elem_of_empty. exact Hm2.
Qed.

(** * THE TWO SPECIES OF τ OF A CONFIGURATION, NAMED

    This is the structural fact behind every negative result about the
    residue, and it is worth having machine-checked rather than repeated
    in prose.  A configuration's internal moves are of exactly two kinds:

    - the **sum's own** τ — a [𝛕]-branch — which leaves the bag intact;
    - a **delivery** — a message of the bag meeting a guard — which
      consumes it, so the bag is strictly smaller.

    [ax_share_msg] and its n-ary form pool the first species, because a
    common bag can be factored out of an internal choice.  They cannot
    touch the second: two deliveries land at *different* bags, so there
    is no common bag to factor.

    And no syntactic law can repair that.  In a guarded sum the
    τ-branches are **syntactic**, so [ax_tau_sep], [ax_tau_flatten] and
    [ax_share_in] can reshuffle them; in a configuration they are
    **emergent** — a delivery is a message meeting a guard, not a summand
    — so there is nothing to rewrite.  Encoding a delivery as a
    [𝛕]-summand of the sum fails for the same reason the whole message
    layer is rigid: such a summand keeps the bag, while the delivery
    consumes it, and "adding a message back is invisible" is refuted
    ([nil_not_below_msg_gen]). *)

Lemma cfg_tau_species : forall (l : list TypeOfActions) (M : gproc) (z : proc),
  lts (msgs l ‖ ((g M) : proc)) τ z ->
  (exists K, lts ((g M) : proc) τ K /\ z = (msgs l ‖ K))
  \/ (exists c v l0 K, Permutation l ((c,v) :: l0)
        /\ lts ((g M) : proc) (ActExt (ActIn (c,v))) K
        /\ z ≡* (msgs l0 ‖ K)).
Proof.
  intros l M z Hz. inversion Hz; subst;
    try (exfalso; eapply msgs_no_tau; eassumption);
    try (exfalso;
         match goal with H : lts ((g M) : proc) (ActExt (ActOut _)) _ |- _ =>
           eapply gsum_no_out; exact H end);
    try (left; eexists; split; [ eassumption | reflexivity ]).
  right.
  match goal with H : lts (msgs l) (ActExt _) _ |- _ =>
    destruct (msgs_lts_inv l _ _ H) as (c0 & v0 & l0 & Heq & Hperm & Hcgr) end.
  inversion Heq; subst.
  exists c0, v0, l0, q2. repeat split; try assumption.
  apply cgr_fullpar; [ exact Hcgr | reflexivity ].
Qed.

(** * PAR LE FORWARDER : LE SAC PASSE DANS LE TEST

    The forwarder's reading of a configuration is [p ▷ bag l] — a process
    beside a **buffer** — and [fw_msg_swap] says a buffered message may
    sit on either side of the barrier.  Syntactically that is
    [must_msg_swap], and iterated over a whole bag it gives

      (msgs l ‖ p) must_pass e  <->  p must_pass (msgs l ‖ e)

    so a configuration's bag can always be **moved into the test**.

    Read at the preorder, this is the sharpest statement of the
    cancellation problem this development has:

      msgs l ‖ p ⊑ₘᵤₛₜᵢ msgs l' ‖ q
        <->  ∀e, p passes (msgs l ‖ e) -> q passes (msgs l' ‖ e)

    — the two sides are compared on *different* tests, each carrying its
    own bag.  At a **common** bag it degenerates to "[p ⊑ₘᵤₛₜᵢ q]
    restricted to the tests that carry the bag", so cancelling the bag is
    exactly extending that restricted preorder to all tests; and
    [bag_incl_fails_without_mute] shows the extension is not free.

    Nothing here is new semantics — it is the same fact as
    [msgs_buffer_iff] — but it is the first time the residue is written
    with the bags on the **test** side, where the delivery is the
    forwarder's primitive step rather than an emergent one
    ([cfg_tau_species]). *)

Lemma must_msgs_swap : forall (l : list TypeOfActions) (p e : proc),
  ((msgs l ‖ p) must_pass e) <-> (p must_pass (msgs l ‖ e)).
Proof.
  induction l as [|cv l IH]; intros p e; simpl.
  - split; intro Hm.
    + eapply must_eq_client; [ apply cgr_symm; apply cgr_nil_par_l | ].
      apply (proj2 (must_i_cgr _ _ (cgr_nil_par_l p))). exact Hm.
    + apply (proj1 (must_i_cgr _ _ (cgr_nil_par_l p))).
      eapply must_eq_client; [ apply cgr_nil_par_l | exact Hm ].
  - destruct cv as (c, v).
    assert (Hc : ((((c ! v • 𝟘) : proc) ‖ msgs l) ‖ p)
                   ≡* ((msgs l ‖ p) ‖ ((c ! v • 𝟘) : proc))).
    { etransitivity; [ apply cgr_par_assoc | apply cgr_par_com ]. }
    assert (Hd : (msgs l ‖ (((c ! v • 𝟘) : proc) ‖ e))
                   ≡* ((((c ! v • 𝟘) : proc) ‖ msgs l) ‖ e)).
    { etransitivity; [ apply cgr_par_assoc_rev | ].
      apply cgr_fullpar; [ apply cgr_par_com | reflexivity ]. }
    split; intro Hm.
    + assert (Hs : ((msgs l ‖ p) ‖ ((c ! v • 𝟘) : proc)) must_pass e)
        by (apply (proj2 (must_i_cgr _ _ Hc)); exact Hm).
      apply (proj1 (must_msg_swap c v (msgs l ‖ p) e)) in Hs.
      apply IH in Hs.
      eapply must_eq_client; [ exact Hd | exact Hs ].
    + assert (Hs : p must_pass (msgs l ‖ (((c ! v • 𝟘) : proc) ‖ e)))
        by (eapply must_eq_client; [ apply cgr_symm; exact Hd | exact Hm ]).
      apply IH in Hs.
      apply (proj2 (must_msg_swap c v (msgs l ‖ p) e)) in Hs.
      apply (proj1 (must_i_cgr _ _ Hc)). exact Hs.
Qed.

Corollary msgs_below_tests : forall (l l' : list TypeOfActions) (p q : proc),
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ q))
  <-> (forall e, p must_pass (msgs l ‖ e) -> q must_pass (msgs l' ‖ e)).
Proof.
  intros l l' p q. unfold ctx_pre. split.
  - intros Hpre e He.
    apply (proj1 (must_msgs_swap l' q e)). apply Hpre.
    apply (proj2 (must_msgs_swap l p e)). exact He.
  - intros H t Ht.
    apply (proj2 (must_msgs_swap l' q t)). apply H.
    apply (proj1 (must_msgs_swap l p t)). exact Ht.
Qed.

(** At a common bag: cancelling it *is* extending a restricted preorder
    to all tests. *)

Corollary msgs_cancel_is_extension : forall (l : list TypeOfActions) (p q : proc),
  ((msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ q))
  <-> (forall e, p must_pass (msgs l ‖ e) -> q must_pass (msgs l ‖ e)).
Proof. intros l p q. apply msgs_below_tests. Qed.

(* ===================================================================== *)
(** * A COMPLETENESS SCHEMA, AND WHAT IT ISOLATES

    Every reduction of the chain above narrows the open case to a
    right-hand side that is **stable with a non-empty bag**
    ([HardResidue]).  Turned around, that says the bag is the *whole*
    difficulty — and the schema below is the exact statement of it.

    Two of the three cases a completeness step must handle are already
    closed **unconditionally**:

    - [q] has a τ — [ax_glb_weak_of_sem] takes it apart, its output
      premises fed by [ichoice_residues_below];
    - [q] is a bare guarded sum — [ax_below_stable_gsum_gen].

    So completeness holds outright on **any** class of right-hand sides
    that is closed under transitions and whose *stable* members are
    [⊢]-equal to a bare guarded sum.  Nothing else is needed, and the
    left-hand side is never constrained.

    That is the honest position: the residue is not a missing lemma about
    [p], it is the single question of whether a stable [q] can be brought
    to a bare guarded sum — i.e. whether its bag can be emptied. *)

Theorem completeness_of_gsum_class :
  forall (Ok : proc -> Prop),
    (forall x a y, Static x -> Ok x -> lts x a y -> Ok y) ->
    (forall x, Static x -> Ok x -> (forall z, ~ lts x τ z) ->
       exists M, gStatic M /\ domsim x ((g M) : proc)) ->
    forall (n : nat) (q p : proc), (size q < n)%nat ->
    Static p -> Static q -> Ok q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros Ok Hcl Hgs.
  induction n as [ | n IH ]; intros q p Hn Hp Hq Hok Hpre; [ lia | ].
  destruct (lts_dec q τ) as [Hno | (q0 & Hq0)].
  - destruct (Hgs q Hq Hok Hno) as (M & HM & Hd).
    assert (HnoM : forall z, ~ lts ((g M) : proc) τ z)
      by (eapply domsim_stable; eassumption).
    assert (HsemM : p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g M) : proc)).
    { intros t Ht. apply (soundness_ax _ _ (ds_l Hd)). apply Hpre. exact Ht. }
    eapply ax_trans; [ | exact (ds_r Hd) ].
    apply ax_below_stable_gsum_gen; try assumption.
    intros c v Q' Hl.
    destruct (ds_s Hd _ _ Hl) as (r' & Hr' & Hdr).
    eapply ax_trans; [ | exact (ds_l Hdr) ].
    eapply IH.
    + assert (size r' < size q)%nat by (eapply Static_lts_decrease; eassumption). lia.
    + constructor; [ constructor | exact Hp ].
    + eapply Static_preserved_by_lts; [ exact Hq | exact Hr' ].
    + eapply Hcl; eassumption.
    + eapply must_i_feed_below; [ exact Hpre | exact Hr' ].
  - apply (ax_glb_weak_of_sem p q (S (size p))); try assumption.
    + lia.
    + exists q0. exact Hq0.
    + intros q' Hq'. eapply IH.
      * assert (size q' < size q)%nat by (eapply Static_lts_decrease; eassumption). lia.
      * exact Hp.
      * eapply Static_preserved_by_lts; [ exact Hq | exact Hq' ].
      * eapply Hcl; eassumption.
      * intros t Ht. eapply must_i_tau_below; [ exact Hq' | ]. apply Hpre. exact Ht.
    + intros c v q'' Hq''. eapply IH.
      * assert (size q'' < size q)%nat by (eapply Static_lts_decrease; eassumption). lia.
      * repeat constructor. exact Hp.
      * eapply Static_preserved_by_lts; [ exact Hq | exact Hq'' ].
      * eapply Hcl; eassumption.
      * eapply must_i_feed_below; [ exact Hpre | exact Hq'' ].
    + intros c v q'' Hq''. eapply IH.
      * assert (size q'' < size q)%nat by (eapply Static_lts_decrease; eassumption). lia.
      * apply static_g. apply ichoice_gStatic. apply res_list_v_Static. exact Hp.
      * eapply Static_preserved_by_lts; [ exact Hq | exact Hq'' ].
      * eapply Hcl; eassumption.
      * eapply ichoice_residues_below; try eassumption. lia.
Qed.

(** ** The instance: a right-hand side that never sits on a message

    [NoStableEmit q] says no **stable** state reachable from [q] can
    emit.  It is exactly what makes the bag of the normal form empty: a
    stable [msgs l ‖ g M] with [l ≠ []] does emit ([cfg_out_of_perm]),
    and [domsim] hands that emission back to [q].

    It is closed under transitions by construction (reachability), and —
    this is [gsum_class_no_stable_emit] below — it is *exactly* the
    schema's reach: **every** class the schema accepts is contained in
    it.  So this is not one instance among others, and there is no
    cleverer one to look for. *)

Definition NoStableEmit (q : proc) : Prop :=
  forall s x, q ⟹[s] x -> (forall z, ~ lts x τ z) ->
    forall c v r, ~ lts x (ActExt (ActOut (c,v))) r.

Lemma NoStableEmit_lts : forall x a y, NoStableEmit x -> lts x a y -> NoStableEmit y.
Proof.
  intros x a y H Hl s z Hw Hst c v r Hout.
  destruct a as [ mu | ].
  - eapply (H (mu :: s) z); [ eapply wt_act; eassumption | exact Hst | exact Hout ].
  - eapply (H s z); [ eapply wt_tau; eassumption | exact Hst | exact Hout ].
Qed.

Lemma NoStableEmit_gsum : forall q, Static q -> NoResD q -> NoStableEmit q ->
  (forall z, ~ lts q τ z) -> exists M, gStatic M /\ domsim q ((g M) : proc).
Proof.
  intros q Hq Hnr Hns Hno.
  destruct (normal_form_nores_sim q Hq (NoResD_NoRes _ Hnr)) as (l & M & HM & Hd).
  destruct l as [ | a l' ].
  - exists M. split; [ exact HM | ].
    eapply domsim_trans; [ exact Hd | apply domsim_cgr; simpl; apply cgr_nil_par_l ].
  - exfalso. destruct a as (c, v).
    destruct (cfg_out_of_perm ((c ▷ v) :: l') l' c v ((g M) : proc)
                (Permutation_refl _)) as (r & Hout & _).
    destruct (ds_s Hd _ _ Hout) as (r' & Hr' & _).
    eapply (Hns [] q (wt_nil q) Hno c v r'). exact Hr'.
Qed.

Theorem completeness_no_stable_emit : forall (p q : proc),
  Static p -> Static q -> NoResD q -> NoStableEmit q ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros p q Hp Hq Hnr Hns Hpre.
  apply (completeness_of_gsum_class (fun x => NoResD x /\ NoStableEmit x)
           ltac:(intros x a y Hst (H1 & H2) Hl; split;
                 [ eapply noresd_lts_target; eassumption
                 | eapply NoStableEmit_lts; eassumption ])
           ltac:(intros x Hst (H1 & H2) Hno; eapply NoStableEmit_gsum; eassumption)
           (S (size q)) q p); try assumption.
  - lia.
  - split; assumption.
Qed.

(** ** The schema's reach is *exactly* [NoStableEmit] — and it stops there

    The two conditions the schema asks of a class force it: a stable
    member is [domsim]-equal to a bare guarded sum, that sum is stable
    too ([domsim_stable]) and a guarded sum never emits ([gsum_no_out]),
    so it can never emit weakly either; [below_preserves_no_weak_out]
    carries that back to the member.

    Together with [completeness_no_stable_emit] — which shows the class
    [NoResD ∩ NoStableEmit] *is* accepted — the schema's power is pinned
    between the two: no instance can reach beyond [NoStableEmit]. *)

Lemma gsum_class_no_stable_emit :
  forall (Ok : proc -> Prop),
    (forall x a y, Static x -> Ok x -> lts x a y -> Ok y) ->
    (forall x, Static x -> Ok x -> (forall z, ~ lts x τ z) ->
       exists M, gStatic M /\ domsim x ((g M) : proc)) ->
    forall q, Static q -> Ok q -> NoStableEmit q.
Proof.
  intros Ok Hcl Hgs q Hq Hok.
  assert (Haux : forall s0 (y z : proc), y ⟹[s0] z -> Static y -> Ok y ->
                   Static z /\ Ok z).
  { intros s0 y z Hy. induction Hy; intros Hsy Hoy.
    - split; assumption.
    - apply IHHy; [ eapply Static_preserved_by_lts | eapply Hcl ]; eassumption.
    - apply IHHy; [ eapply Static_preserved_by_lts | eapply Hcl ]; eassumption. }
  intros s x Hw Hst c v r Hout.
  destruct (Haux s q x Hw Hq Hok) as (Hsx & Hokx).
  destruct (Hgs x Hsx Hokx Hst) as (M & HM & Hd).
  assert (HnoM : forall z, ~ lts ((g M) : proc) τ z)
    by (eapply domsim_stable; eassumption).
  assert (HnwM : NoWeakOut c ((g M) : proc)).
  { intros p1 Hp1 w r' Hl.
    assert (p1 = ((g M) : proc)) as Heq
      by (eapply wt_nil_stable; [ apply no_lts_stable; exact HnoM | exact Hp1 ]).
    subst p1. eapply gsum_no_out; eassumption. }
  assert (HnwX : NoWeakOut c x).
  { eapply below_preserves_no_weak_out;
      [ apply static_g; exact HM | exact Hsx
      | apply (soundness_ax _ _ (ds_r Hd)) | exact HnwM ]. }
  eapply (HnwX x (wt_nil x) v r). exact Hout.
Qed.

(** …and the open case is provably out of range.

    [HardResidue]'s right-hand side is a **stable** configuration with a
    **non-empty** bag.  Such a state emits, and it is stable, so it
    violates [NoStableEmit] outright — hence no class the schema accepts
    can ever contain it.  The schema is therefore exhausted, and closing
    the residue needs a genuinely different mechanism, not a better
    class. *)

Lemma stable_bag_not_no_stable_emit : forall l (P : proc),
  l <> [] -> (forall z, ~ lts ((msgs l) ‖ P) τ z) ->
  ~ NoStableEmit ((msgs l) ‖ P).
Proof.
  intros l P Hl Hst Hns.
  destruct l as [ | (c,v) l0 ]; [ contradiction | ].
  destruct (cfg_out_of_perm ((c ▷ v) :: l0) l0 c v P (Permutation_refl _))
    as (r & Hout & _).
  eapply (Hns [] ((msgs ((c ▷ v) :: l0)) ‖ P) (wt_nil _) Hst c v r).
  exact Hout.
Qed.

Corollary gsum_class_misses_hard_residue :
  forall (Ok : proc -> Prop),
    (forall x a y, Static x -> Ok x -> lts x a y -> Ok y) ->
    (forall x, Static x -> Ok x -> (forall z, ~ lts x τ z) ->
       exists M, gStatic M /\ domsim x ((g M) : proc)) ->
    forall l (P : proc), l <> [] -> Static ((msgs l) ‖ P) ->
      (forall z, ~ lts ((msgs l) ‖ P) τ z) ->
      ~ Ok ((msgs l) ‖ P).
Proof.
  intros Ok Hcl Hgs l P Hl Hs Hst Hok.
  eapply stable_bag_not_no_stable_emit; try eassumption.
  eapply gsum_class_no_stable_emit; eassumption.
Qed.

(** ** …and the syntactic form

    [ochans q = []] — "q can never emit along any run" — is decidable,
    and it implies the semantic criterion outright. *)

Lemma mute_NoStableEmit : forall q, Static q -> ochans q = [] -> NoStableEmit q.
Proof.
  intros q Hq Hoc s x Hw Hst c v r Hout.
  assert (Hsx : Static x) by (eapply Static_preserved_by_wt; eassumption).
  assert (Hin : In c (ochans x))
    by (eapply lts_ochans_out; [ exact Hsx | exact Hout | reflexivity ]).
  assert (Hin2 : In c (ochans q)) by (eapply wt_ochans; eassumption).
  rewrite Hoc in Hin2. contradiction.
Qed.

Theorem completeness_no_output_right : forall (p q : proc),
  Static p -> Static q -> NoResD q -> ochans q = [] ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q.
Proof.
  intros p q Hp Hq Hnr Hoc Hpre.
  eapply completeness_no_stable_emit; try eassumption.
  apply mute_NoStableEmit; assumption.
Qed.

Corollary must_iff_ax_pre_no_output : forall (p q : proc),
  Static p -> Static q -> NoResD q -> ochans q = [] ->
  (ax_pre p q <-> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q).
Proof.
  intros p q Hp Hq Hnr Hoc. split.
  - apply soundness_ax.
  - apply completeness_no_output_right; assumption.
Qed.

(** ** The instance that matters: [𝟘]

    [VACCS_Bad.below_nil_iff] reads [p ⊑ₘᵤₛₜᵢ 𝟘] as "p passes no τ-stuck,
    non-good client", and the whole [Harmless] / [Bad] / [BadK] line of
    work consists of **sufficient** conditions for deriving it — each one
    provably incomplete ([VACCS_DropProbes.no_Bad_target],
    [bad_not_closed_under_par], and the two ∀∃ counterexamples).

    They are all subsumed: below [𝟘] the preorder and the proof system
    coincide **exactly**, for every [Static p], with no side condition at
    all. *)

Corollary ax_of_below_nil : forall (p : proc),
  Static p -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc) -> ax_pre p ((g 𝟘) : proc).
Proof.
  intros p Hp Hpre.
  apply completeness_no_output_right; try assumption.
  - apply static_g. constructor.
  - simpl. exact I.
  - reflexivity.
Qed.

Corollary must_iff_ax_below_nil : forall (p : proc), Static p ->
  (ax_pre p ((g 𝟘) : proc) <-> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc)).
Proof.
  intros p Hp. split; [ apply soundness_ax | apply ax_of_below_nil; assumption ].
Qed.

(* ===================================================================== *)
(** * DEUX SONDES SUR LE RÉSIDU

    [HardResidue] compare deux configurations, la droite **stable** à sac
    **non vide**.  Les deux résultats qui suivent disent, l'un ce que la
    stabilité de la droite donne, l'autre que la classe n'est pas vide de
    cas dérivables. *)

(** ** La droite stable ne touche jamais son propre sac

    Un message du sac et une garde de la somme sur son canal se
    synchronisent en un [τ] de la configuration.  Donc, pour une
    configuration **stable**, la somme **refuse** tout canal du sac : le
    sac ne peut y être consommé que par le *client*.

    Lu du côté des tests ([msgs_below_tests]), cela dit que le sac de la
    droite est du **mobilier de client** — il n'interagit avec [g M] à
    aucun moment de la comparaison.  C'est la caractérisation exacte de
    la stabilité d'une configuration, et c'est ce qu'un argument
    d'appariement consommerait. *)

Lemma msgs_emits : forall l c v, In (c ▷ v) l ->
  exists r, lts (msgs l) ((c ▷ v)!) r.
Proof.
  induction l as [ | (d,w) l0 IH ]; intros c v Hin; [ contradiction | ].
  simpl in Hin. destruct Hin as [Heq | Hin].
  - injection Heq; intros; subst.
    exists (((g (𝟘 : gproc)) : proc) ‖ msgs l0). simpl.
    apply lts_parL. apply lts_output.
  - destruct (IH c v Hin) as (r & Hr).
    exists ((d ! w • 𝟘) ‖ r). simpl.
    apply lts_parR. exact Hr.
Qed.

Lemma stable_cfg_refuses_bag : forall l (M : gproc) c v,
  (forall z, ~ lts ((msgs l) ‖ ((g M) : proc)) τ z) ->
  In (c ▷ v) l ->
  forall K, ~ lts ((g M) : proc) ((c ▷ v)?) K.
Proof.
  intros l M c v Hst Hin K Hk.
  destruct (msgs_emits l c v Hin) as (r & Hr).
  eapply (Hst (r ‖ K)). eapply lts_comL; eassumption.
Qed.

(** ** …et le résidu contient des instances DÉRIVABLES

    Contrôle de non-vacuité, dans la discipline du dossier : une instance
    qui remplit **toutes** les conditions de [HardResidue] — gauche
    instable (la délivrance du message dans le copycat), somme gauche qui
    peut émettre ([ochans (ccat c) = [c]]), droite stable à sac non
    vide — et dont l'inéquation est **dérivable**, ici parce que la
    gauche se décompose et que [ax_ccat_l] traite le facteur.

    Cela ne ferme rien : le résidu est difficile *en général*, pas sur
    chaque instance.  Mais cela dit que la classe n'est pas un artefact
    de la réduction — elle est habitée, et par des cas que le système
    atteint. *)

Theorem residue_instance_derivable : forall (c : ChannelData) (v : ValueData),
     (exists z, lts ((c ! v • 𝟘) ‖ ccat c) τ z)
  /\ ochans (ccat c) <> []
  /\ (forall z, ~ lts (msgs [(c ▷ v)]) τ z)
  /\ ((c ! v • 𝟘) ‖ ccat c) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs [(c ▷ v)])
  /\ ax_pre ((c ! v • 𝟘) ‖ ccat c) (msgs [(c ▷ v)]).
Proof.
  intros c v. split; [ | split; [ | split; [ | split ]]].
  - unfold ccat. eexists. eapply lts_comL; [ apply lts_output | apply lts_input ].
  - simpl. discriminate.
  - intros z Hz. simpl in Hz.
    inversion Hz; subst; try (inversion H3; fail); try (inversion H4; fail);
      inversion H2.
  - assert (Hc : ((c ! v • 𝟘) : proc) ≡* (msgs [(c ▷ v)]))
      by (simpl; apply cgr_symm; apply cgr_par_nil).
    intros t Ht.
    apply (proj2 (must_i_cgr _ _ Hc)).
    apply (proj2 (ccat_delivery_equiv c v)). exact Ht.
  - eapply ax_trans.
    + apply (ax_par (c ! v • 𝟘) (c ! v • 𝟘) (ccat c) ((g (𝟘 : gproc)) : proc));
        [ apply ax_refl | apply ax_ccat_l ].
    + apply ax_cgr. simpl. apply cgr_refl.
Qed.

End VACCS_Matching.
