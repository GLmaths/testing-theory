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
  SetLTSConstruction FiniteImageLTS Lts_Finite_Output_Chain VACCS_GlbStable.

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
  (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((ext M (c ? (c ! (bvar 0) • 𝟘))) + fwdg c M)).
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
  (forall v, ((g M) ‖ (c ! v • 𝟘)) ᴠᴀᴄᴄꜱ⊑ₐₓ (Q ^ v)) ->
  (g (fwdg c M)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (c ? Q)).
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
  (forall v, (c ! v • 𝟘) ᴠᴀᴄᴄꜱ⊑ₐₓ (Q ^ v)) -> (g 𝟘) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (c ? Q)).
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
          (∀ v, ((c!v•𝟘) ‖ g M) ⊑ₘᵤₛₜᵢ Q^v -> ((c!v•𝟘) ‖ g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (Q^v)) ->
          g M ⊑ₘᵤₛₜᵢ g (c ? Q) -> (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (c ? Q))

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
  (forall v, ((g M) ‖ (c ! v • 𝟘)) ᴠᴀᴄᴄꜱ⊑ₐₓ (Q ^ v)) ->
  (g ((c ? A) + (fwdg c M))) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (c ? Q)).
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
  (g (((c ? A) + (fwdg c M)) + R)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((fwdg c M) + R)).
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
  (g ((ext M N) + ((fwdg c M0) + R))) ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((fwdg c M0) + R)).
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
  (forall v, ((g M) ‖ (c ! v • 𝟘)) ᴠᴀᴄᴄꜱ⊑ₐₓ (Q ^ v)) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (c ? Q)).
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
             ((c ! v • 𝟘) ‖ (g M)) ᴠᴀᴄᴄꜱ⊑ₐₓ (Q ^ v)) ->
  (g M) ⊑ₘᵤₛₜᵢ (g (c ? Q)) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (c ? Q)).
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

    - **Phase A** (shape): [(g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (mirrorN M N))], where [mirrorN M N]
      is [N] with every continuation replaced by the mirror one.  This is
      where the copycats are introduced and [M]'s own guards absorbed, and
      it is the only part still open in general ([ax_phaseA_one_channel]
      settles it when everything lives on a single channel).
    - **Phase B** (match): [(g (mirrorN M N)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g N)], summand by summand.

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
  | gpr_input c Q => forall v, ((g M) ‖ (c ! v • 𝟘)) ᴠᴀᴄᴄꜱ⊑ₐₓ (Q ^ v)
  | gpr_tau _ => False
  | gpr_choice N1 N2 => mirror_ok M N1 /\ mirror_ok M N2
  end.

Lemma ax_mirrorN_match : forall (M N : gproc), mirror_ok M N ->
  forall (R : gproc), (g ((mirrorN M N) + R)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (N + R)).
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
  (forall c v Q', lts (g N) (ActExt (ActIn (c,v))) Q' -> ((g M) ‖ (c ! v • 𝟘)) ᴠᴀᴄᴄꜱ⊑ₐₓ Q') ->
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
     ((c ! v • 𝟘) ‖ (g M)) ⊑ₘᵤₛₜᵢ Q' -> ((c ! v • 𝟘) ‖ (g M)) ᴠᴀᴄᴄꜱ⊑ₐₓ Q') ->
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
  (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (mirrorN M N)) ->
  (g M) ⊑ₘᵤₛₜᵢ (g N) ->
  (forall c v Q', lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ((c ! v • 𝟘) ‖ (g M)) ⊑ₘᵤₛₜᵢ Q' -> ((c ! v • 𝟘) ‖ (g M)) ᴠᴀᴄᴄꜱ⊑ₐₓ Q') ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g N).
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
  gInputsOn c M -> (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (fwdg c M)).
Proof.
  intros c M Hin.
  eapply ax_trans; [ apply (ax_fwd_intro c M) | ].
  eapply ax_trans; [ apply ax_cgr; apply cgr_fullchoice;
                     [ apply cgr_refl | apply cgr_symm; apply cgr_choice_nil ] | ].
  eapply ax_trans; [ apply (ax_ext_absorb c M Hin (c ? (c ! (bvar 0) • 𝟘)) M 𝟘) | ].
  apply ax_cgr. apply cgr_choice_nil.
Qed.

Corollary ax_phaseA_single_summand : forall (c : ChannelData) (M : gproc) (Q : proc),
  gInputsOn c M -> (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (mirrorN M (c ? Q))).
Proof. intros c M Q Hin. simpl. apply ax_phaseA_one_channel. exact Hin. Qed.

(** * Reaching the mirror in one step, on all channels at once

    [ax_fwd_intro] adds one copycat.  Adding one per channel and expanding
    the [k]-fold parallel product would be painful — but it is unnecessary,
    because a whole **sum** of copycat guards is invisible too
    ([must_i_nil_below_copycats], the generalised [ax_ccat_r]).  So:

        guardsN N  :=  N with every continuation replaced by the copycat
                       (and [①]/[𝟘] by [𝟘])

    is a [gCopycats] sum, [(g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g M ‖ g (guardsN N))] is one [ax_par],
    and [ax_expansion_l] flattens that in a single step.  The point that
    makes it fit exactly:

        ext_r (guardsN N) M  =  mirrorN M N        (definitionally)

    — the expansion's *right* component **is** the mirror.  So

        ax_mirror_reach : (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (ext M (guardsN N) + mirrorN M N))

    with no side condition beyond [N] being stable.

    ** What this leaves

    Exactly one obligation, and it is purely syntactic:

        (g (ext M (guardsN N) + mirrorN M N)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (mirrorN M N))

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
  (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((ext M (guardsN N)) + (mirrorN M N))).
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
  (g ((ext M (guardsN N)) + (mirrorN M N))) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (mirrorN M N)) ->
  (g M) ⊑ₘᵤₛₜᵢ (g N) ->
  (forall c v Q', lts (g N) (ActExt (ActIn (c,v))) Q' ->
     ((c ! v • 𝟘) ‖ (g M)) ⊑ₘᵤₛₜᵢ Q' -> ((c ! v • 𝟘) ‖ (g M)) ᴠᴀᴄᴄꜱ⊑ₐₓ Q') ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g N).
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
  (g ((ext M G) + ((mirrorN M0 N) + R))) ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((mirrorN M0 N) + R)).
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
  (g ((ext M (guardsN N)) + (mirrorN M N))) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (mirrorN M N)).
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
     ((c ! v • 𝟘) ‖ (g M)) ⊑ₘᵤₛₜᵢ Q' -> ((c ! v • 𝟘) ‖ (g M)) ᴠᴀᴄᴄꜱ⊑ₐₓ Q') ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g N).
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
  ((g M) ⊑ₘᵤₛₜᵢ (g N1) -> (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g N1)) ->
  ((g M) ⊑ₘᵤₛₜᵢ (g N2) -> (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g N2)) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((𝛕 • (g N1)) + (𝛕 • (g N2)))).
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
      ((c ! v • 𝟘) ‖ (g M)) ⊑ₘᵤₛₜᵢ Q' -> ((c ! v • 𝟘) ‖ (g M)) ᴠᴀᴄᴄꜱ⊑ₐₓ Q') ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g N).
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
  (p ⊑ₘᵤₛₜᵢ (g N1) -> p ᴠᴀᴄᴄꜱ⊑ₐₓ (g N1)) ->
  (p ⊑ₘᵤₛₜᵢ (g N2) -> p ᴠᴀᴄᴄꜱ⊑ₐₓ (g N2)) ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((𝛕 • (g N1)) + (𝛕 • (g N2)))).
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
  (p ⊑ₘᵤₛₜᵢ (g ((rebuild r) + Y)) -> p ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((rebuild r) + Y))) ->
  (p ⊑ₘᵤₛₜᵢ (g Y) -> p ᴠᴀᴄᴄꜱ⊑ₐₓ (g Y)) ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M).
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
  (p ⊑ₘᵤₛₜᵢ (g ((rebuild r) + Y)) -> p ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((rebuild r) + Y))) ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M).
Proof.
  intros p M Y r HS Hall Hperm Hsem H1.
  destruct (ax_tau_flatten_anywhere M Y r HS Hall Hperm) as [Ha Hb].
  eapply ax_trans; [ | exact Hb ].
  apply H1. intros t Hm. apply (soundness_ax _ _ Ha). apply Hsem. exact Hm.
Qed.

(** * The inner driver: any guarded sum reduces to its stable case

    The two peeling steps are iterated exactly as [tau_flatten_all] and
    [tau_separate] iterate their rewrites — same searches, same measures,
    same invariants — but driving the *goal* [p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M)] instead of
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
  (forall (L : gproc), gStatic L -> gStable L -> p ⊑ₘᵤₛₜᵢ (g L) -> p ᴠᴀᴄᴄꜱ⊑ₐₓ (g L)) ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M).
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
  (forall (L : gproc), gStatic L -> gStable L -> p ⊑ₘᵤₛₜᵢ (g L) -> p ᴠᴀᴄᴄꜱ⊑ₐₓ (g L)) ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M).
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
      p ⊑ₘᵤₛₜᵢ (g M') -> p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M')) ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M).
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
  (forall (L : gproc), gStatic L -> gStable L -> p ⊑ₘᵤₛₜᵢ (g L) -> p ᴠᴀᴄᴄꜱ⊑ₐₓ (g L)) ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ (g M).
Proof.
  intros M HM Hnf p Hsem Hstab.
  eapply (ax_below_flatten_drive (tau_weight (summands M)) M HM (le_n _) Hnf p Hsem).
  intros M' HM' Hok' Hs'.
  exact (ax_below_mixed (ntaus (summands M')) M' HM' (le_n _) Hok' p Hs' Hstab).
Qed.




Definition InvR (M0 : proc) (L : gproc) : Prop :=
  (forall c v Q, lts (g L) (ActExt (ActIn (c,v))) Q -> M0 ⟹[[ActIn (c,v)]] Q)
  /\ (forall Y, In (𝛕 • (g Y)) (summands L) -> M0 ⟹[[]] (g Y)).







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

        (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (grestrict N M))          (ax_restrict, certificate)
        (g (grestrict N M)) ᴠᴀᴄᴄꜱ⊑ₐₓ (g N)          (ax_below_stable_sum_full)

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






(** Phase A at a configuration, from the certificate for [g M] alone. *)



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
    `p ᴠᴀᴄᴄꜱ⊑ₐₓ p'`, so composing it with `p' ᴠᴀᴄᴄꜱ⊑ₐₓ q` yields `p ᴠᴀᴄᴄꜱ⊑ₐₓ q` — sound,
    and it is how the copycat example
    `(c!v•𝟘) ‖ ((c?(c!v•𝟘)) + (d?(e!y•𝟘))) ⊑ (c!v•𝟘) ‖ 𝟘` is derived.  But
    the semantic side condition `p' ⊑ₘᵤₛₜᵢ q` does **not** follow from
    `p ⊑ₘᵤₛₜᵢ q`: a reduct passes at least what `p` passes, so this is an
    *up*-move, legitimate only when the chosen reduct happens to stay
    below `q`.  With several delivery branches, different branches may be
    needed for different stable states of `q` — the same ∀∃ alternation
    that defeated [Harmless] and [Bad]. *)


Lemma ax_below_via_reduct : forall (p p' q : proc),
  p ⟹[[]] p' -> p' ᴠᴀᴄᴄꜱ⊑ₐₓ q -> p ᴠᴀᴄᴄꜱ⊑ₐₓ q.
Proof. intros p p' q Hw H. eapply ax_trans; [ apply ax_tau_run; exact Hw | exact H ]. Qed.

Theorem ax_config_leaf : forall (p : proc), Static p ->
  exists p', p ⟹[[]] p' /\ p' ↛ /\ p ᴠᴀᴄᴄꜱ⊑ₐₓ p' /\ Static p'.
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
  (forall p, In p l -> q ᴠᴀᴄᴄꜱ⊑ₐₓ p) -> q ᴠᴀᴄᴄꜱ⊑ₐₓ (g (ichoice l)).
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
  (g (ichoice l)) ᴠᴀᴄᴄꜱ⊑ₐₓ p.
Proof. intros l p Hin. apply ax_tau_step. apply lts_ichoice. exact Hin. Qed.


Lemma ax_restrict_keep : forall (M M' : gproc), gStatic M -> gStatic M' ->
  (forall al q, lts (g M') al q -> lts (g M) al q) ->
  (forall c v p, lts (g M) (ActExt (ActIn (c,v))) p ->
                 exists w q, lts (g M') (ActExt (ActIn (c,w))) q) ->
  (forall p, ~ lts (g M) τ p) ->
  (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g M').
Proof.
  intros M M' HM HM' Hsub Hoff HstM. apply ax_glb_settle.
  - intros l Hl. apply Settles_gsum_stable. apply stable_of_no_step.
    apply fw_stable_iff. split; [ exact HstM | ].
    intros a Ha q Hq. destruct a as (c,v). apply bag_elem in Ha.
    apply (Hl c v Ha). destruct (Hoff c v q Hq) as (w & r & Hr). exists w, r. exact Hr.
  - intros X HX. exfalso. eapply HstM. apply Hsub. eapply summand_lts; [ exact HX | apply lts_tau ].
  - intros c Q HQ v. apply ax_deliver. apply Hsub. eapply summand_lts; [ exact HQ | apply lts_input ].
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
  ((g ((A + R) + (B + R))) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g ((A + B) + R)) : proc).
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
  ((g ((c ? ((g ((𝛕 • P) + (𝛕 • Q))) : proc)) + R)) : proc)
    ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (((c ? P) + (c ? Q)) + R)) : proc).
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
  (g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (mirrorN M (N + M))).
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
        p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> p' ᴠᴀᴄᴄꜱ⊑ₐₓ q') ->
     p ᴠᴀᴄᴄꜱ⊑ₐₓ q) ->
  forall p q, Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> p ᴠᴀᴄᴄꜱ⊑ₐₓ q.
Proof.
  intro Hstep.
  assert (H : forall n q, (size q <= n)%nat ->
                forall p, Static p -> Static q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> p ᴠᴀᴄᴄꜱ⊑ₐₓ q).
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
  (msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ g (mirrorN M (N + M))).
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

(** ** …and at the level of [⊢]

    [ax_choice_input_bag] is itself a rule of the system: a summand's
    continuation may be rewritten **beside a message bag**, provided the
    rewrite is derivable at every sub-bag — and the sub-bags are exactly
    the states [domsim_wt] measures. *)

(** Pooling two **same-channel** guards is free at a bag: the law is a
    closed inequation, so [ax_par] carries it into any context.  This is
    what merges the delivery-branches a bag creates *at one channel*;
    nothing in the rule set merges branches at *different* channels, which
    is the open part of the unstable case
    ([VACCS_DropProbes.tau_successor_cannot_be_chosen] and
    [VACCS_DropProbes.ax_PC_below_nil] delimit it). *)

Lemma ax_choice_tau2 : forall (p1 p2 q1 q2 : proc),
  p1 ᴠᴀᴄᴄꜱ⊑ₐₓ q1 -> p2 ᴠᴀᴄᴄꜱ⊑ₐₓ q2 ->
  (g ((𝛕 • p1) + (𝛕 • p2))) ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((𝛕 • q1) + (𝛕 • q2))).
Proof.
  intros p1 p2 q1 q2 H1 H2.
  eapply ax_trans; [ apply (ax_choice_tau p1 q1 (𝛕 • p2) H1) | ].
  eapply ax_trans; [ apply ax_cgr; apply cgr_choice_com | ].
  eapply ax_trans; [ apply (ax_choice_tau p2 q2 (𝛕 • q1) H2) | ].
  apply ax_cgr. apply cgr_choice_com.
Qed.

Lemma ax_share_msgs : forall (l : list TypeOfActions) (X Y : proc),
  (g ((𝛕 • (msgs l ‖ X)) + (𝛕 • (msgs l ‖ Y))))
    ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ ((g ((𝛕 • X) + (𝛕 • Y))) : proc)).
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

(** The greatest lower bound, likewise at a bag: the bare rule
    [ax_int_glb] builds the internal choice of the two configurations, and
    [ax_share_msgs] factors the common bag out of it. *)
Lemma ax_int_glb_bag : forall (l : list TypeOfActions) (p q1 q2 : proc),
  (forall l', subbag l' l -> (msgs l' ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l' ‖ q1)) ->
  (forall l', subbag l' l -> (msgs l' ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l' ‖ q2)) ->
  (msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ g ((𝛕 • q1) + (𝛕 • q2))).
Proof.
  intros l p q1 q2 H1 H2.
  eapply ax_trans;
    [ apply ax_int_glb; [ apply (H1 l (subbag_refl l)) | apply (H2 l (subbag_refl l)) ]
    | apply ax_share_msgs ].
Qed.

(** ** Phase B, and the stable case, AT A CONFIGURATION

    The whole chain now lifts, and the point of lifting it is the shape of
    the **recursive premise**: it comes out as
    [(msgs l' ‖ ((c!v•𝟘) ‖ g M)) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l' ‖ Q')] — *wrapped*, at every
    sub-bag [l'] — which is exactly what [VACCS_Descent.
    wrapped_premise_from_IH] discharges, and the sub-bags are exactly the
    states [domsim_wt] measures.  Compare [ax_below_stable_NF], whose
    premise is bare and therefore unmeasurable.

    Phase A stays bare: it is a [⊢]-statement about the two sums with no
    premise of its own, so one [ax_par] carries it into the context. *)

Lemma ax_par_bag : forall (l : list TypeOfActions) (X Y : proc),
  X ᴠᴀᴄᴄꜱ⊑ₐₓ Y -> (msgs l ‖ X) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ Y).
Proof. intros l X Y H. apply ax_par; [ apply ax_refl | exact H ]. Qed.







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








(** ** The τ-layer, at a configuration

    The two drivers lift as mechanically as Phase B did.  Everything is
    phrased with two abbreviations, both **monotone in the bag** (a
    sub-bag of a sub-bag is a sub-bag), which is what lets the recursive
    calls be made at the *outer* bag and used at the inner ones. *)

Definition BagSem (l : list TypeOfActions) (p : proc) (X : gproc) : Prop :=
  forall l', subbag l' l -> (msgs l' ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l' ‖ g X).

Definition BagBelow (l : list TypeOfActions) (p : proc) (X : gproc) : Prop :=
  forall l', subbag l' l -> (msgs l' ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l' ‖ g X).

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
  In x L -> x ᴠᴀᴄᴄꜱ⊑ₐₓ q -> (g (ichoice L)) ᴠᴀᴄᴄꜱ⊑ₐₓ q.
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
  (forall x, In x L -> p ⟹[[]] x) -> p ᴠᴀᴄᴄꜱ⊑ₐₓ (g (ichoice L)).
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
  r ᴠᴀᴄᴄꜱ⊑ₐₓ (g (ichoice_cfg L)).
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
  (msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ (g (ichoice_cfg L)).
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

Lemma cfg_deliver_step_p : forall (l l0 : list TypeOfActions) c v (p pc : proc),
  Permutation l ((c,v) :: l0) ->
  lts p (ActExt (ActIn (c,v))) pc ->
  exists r, lts (msgs l ‖ p) τ r /\ r ≡* (msgs l0 ‖ pc).
Proof.
  intros l l0 c v p pc Hperm Hin.
  assert (Hc : msgs l ‖ p ≡* (msgs ((c,v) :: l0)) ‖ p)
    by (apply cgr_fullpar; [ apply msgs_perm; exact Hperm | apply cgr_refl ]).
  assert (Hstep : lts ((msgs ((c,v) :: l0)) ‖ p) τ (((g 𝟘) ‖ msgs l0) ‖ pc)).
  { simpl. eapply lts_comL; [ apply lts_parL; apply lts_output | exact Hin ]. }
  destruct (Congruence_Respects_Transition (msgs l ‖ p) (((g 𝟘) ‖ msgs l0) ‖ pc) τ
              (ex_intro _ _ (conj Hc Hstep))) as (r & Hr & Hcr).
  exists r. split; [ exact Hr | ].
  eapply cgr_trans; [ exact Hcr | ].
  apply cgr_fullpar; [ | apply cgr_refl ].
  etransitivity; [ apply cgr_par_com | apply cgr_par_nil ].
Qed.

Theorem ax_below_cfg_descend_p : forall (l l0 : list TypeOfActions) c v
    (p pc q : proc),
  Permutation l ((c,v) :: l0) ->
  lts p (ActExt (ActIn (c,v))) pc ->
  (msgs l0 ‖ pc) ᴠᴀᴄᴄꜱ⊑ₐₓ q ->
  (msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ q.
Proof.
  intros l l0 c v p pc q Hperm Hin Hax.
  destruct (cfg_deliver_step_p l l0 c v p pc Hperm Hin) as (r & Hr & Hcr).
  eapply ax_trans; [ apply ax_tau_step; exact Hr | ].
  eapply ax_trans; [ apply ax_cgr; exact Hcr | exact Hax ].
Qed.

(** Les versions à somme gardée en sont les instances : rien dans la
    preuve n'inspecte la forme du processus. *)

Lemma cfg_deliver_step : forall (l l0 : list TypeOfActions) c v (M : gproc) (Mc : proc),
  Permutation l ((c,v) :: l0) ->
  lts (g M) (ActExt (ActIn (c,v))) Mc ->
  exists r, lts (msgs l ‖ g M) τ r /\ r ≡* (msgs l0 ‖ Mc).
Proof. intros l l0 c v M Mc. apply cfg_deliver_step_p. Qed.

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
  (msgs l0 ‖ Mc) ᴠᴀᴄᴄꜱ⊑ₐₓ q ->
  (msgs l ‖ g M) ᴠᴀᴄᴄꜱ⊑ₐₓ q.
Proof. intros l l0 c v M Mc q. apply ax_below_cfg_descend_p. Qed.

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


Theorem ax_below_stable_gsum_gen : forall (P : proc) (N : gproc),
  Static P -> gStatic N -> (forall z, ~ lts ((g N) : proc) τ z) ->
  P ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g N) : proc) ->
  (forall c v Q', lts ((g N) : proc) (ActExt (ActIn (c,v))) Q' ->
     (((c ! v • 𝟘) : proc) ‖ P) ᴠᴀᴄᴄꜱ⊑ₐₓ Q') ->
  P ᴠᴀᴄᴄꜱ⊑ₐₓ ((g N) : proc).
Proof.
  intros P N HP HN HstN Hsem Hrec. apply ax_glb_settle.
  - intros l Hl.
    apply (certificate_N_refuses P N HP HN HstN Hsem (bag l) (outonly_of_bag l)).
    intros a Ha r Hr. destruct a as (c,v). apply bag_elem in Ha.
    apply (Hl c v Ha). exists v, r. exact Hr.
  - intros X HX. exfalso. eapply HstN. eapply summand_lts; [ exact HX | apply lts_tau ].
  - intros c Q HQ v. apply Hrec. eapply summand_lts; [ exact HQ | apply lts_input ].
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
     (NF n l1 M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (NF n l2 N) -> (NF n l1 M) ᴠᴀᴄᴄꜱ⊑ₐₓ (NF n l2 N)) ->
  forall n1 l1 M n2 l2 N, gStatic M -> gStatic N ->
    (NF n1 l1 M) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (NF n2 l2 N) -> (NF n1 l1 M) ᴠᴀᴄᴄꜱ⊑ₐₓ (NF n2 l2 N).
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

(** ** …et il suffit de le vérifier sur les canaux DU SAC

    L'inversion ne consulte le critère qu'au canal de la **première
    entrée** du run.  Avec la prémisse [bag (ins r) ⊆ bag l] — que
    [VACCS_NormalForm.fw_conservation_bounded] fournit dès que la trace
    du forwarder n'a pas d'entrée — cette entrée est forcément un message
    que le sac tenait, donc le critère n'a rien à dire des autres
    canaux.

    Gain : une somme dont une garde **hors du sac** rend son message
    n'est plus rejetée.  [VACCS_DropProbes.MSelf] est exactement cela, et
    son sac s'annule bel et bien. *)



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






(** Et l'inclusion est **stricte** : une somme qui porte un [𝛕]-sommant
    émettant sur une voie **étrangère au sac** échoue à [ochans _ = []]
    et satisfait le critère relatif. *)

Lemma no_output_bag_criterion_is_weaker :
  forall (c d : ChannelData) (vv uu : ValueData), c <> d ->
  ochans ((g ((c ? ((g 𝟘) : proc)) + (𝛕 • ((d ! vv • 𝟘) : proc)))) : proc) <> []
  /\ (forall c' u', In (c',u') [(c,uu)] ->
        ~ In c' (ochans ((g ((c ? ((g 𝟘) : proc)) + (𝛕 • ((d ! vv • 𝟘) : proc)))) : proc))).
Proof.
  intros c d vv uu Hcd. split.
  - simpl. discriminate.
  - intros c' u' Hin Hoc. simpl in Hin. destruct Hin as [He|[]].
    injection He as He1 He2. subst c' u'.
    simpl in Hoc. destruct Hoc as [He|[]]. congruence.
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





(** Énoncé au type **générique** à dessein : à [MO (ExtAct TypeOfActions)]
    les deux élaborations de [⊎] que le développement transporte sont
    convertibles sans être syntaxiquement égales, et [rewrite] rate.  Même
    précaution que pour [VACCS_NormalForm.disj_union_cancel_empty]. *)

(** …et la version qui tolère un troisième terme à gauche, pourvu qu'il
    ne rencontre pas [Z].  C'est ce qui permet de relativiser au sac le
    critère d'émission : le membre gauche du bilan porte alors les
    sorties **propres** du processus, et il suffit qu'elles évitent les
    voies du sac visé. *)


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

(** Le critère n'a jamais eu besoin d'interdire **toute** émission de la
    gauche : il suffit que ses émissions évitent les voies du **sac de
    droite**.  Les messages du processus sur d'autres voies ne peuvent
    pas rembourser ce que la trace de vidange réclame, donc ils ne
    faussent pas l'inclusion. *)


(** ** L'inclusion des deux sacs, SANS AUCUN CRITÈRE

    Vider le sac de droite et suivre à gauche donne, par le bilan de
    [fw_conservation], une inclusion inconditionnelle : *le sac de droite
    tient dans celui de gauche **augmenté de ce que le processus gauche a
    émis** le long du run projeté*.  Autrement dit, chaque message que la
    droite détient, la gauche le détient déjà ou sait le produire.

    C'est la forme générale ; le critère relatif au sac en est le cas où
    ces émissions évitent les voies du sac de droite. *)

Theorem bag_incl_of_below_emit : forall (l1 l2 : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  ((msgs l1 ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))) ->
  exists r q, ((g M) : proc) ⟹[r] q /\ bag l2 ⊆ bag l1 ⊎ bag (outs r).
Proof.
  intros l1 l2 M N HM HN Hpre.
  destruct (msgs_accept l1 l2 (g M) (g N) Hpre) as (Hc1 & Hc2).
  assert (Hdrain : (((g N) : proc) ▷ bag l2)
                     ⟹[map ActOut l2] (((g N) : proc) ▷ (∅ : MO (ExtAct TypeOfActions)))).
  { replace (bag l2) with (bag l2 ⊎ (∅ : MO (ExtAct TypeOfActions))) at 1
      by (apply gmultiset.gmultiset_disj_union_right_id).
    apply bag_wt_drain. }
  destruct (fw_stable_reach ((g N) : proc) (∅ : MO (ExtAct TypeOfActions))
              (static_g N HN)) as (yy & Hwy & Hsty).
  assert (Hbig : (((g N) : proc) ▷ bag l2) ⟹[map ActOut l2] yy).
  { replace (map ActOut l2) with (map ActOut l2 ++ (@nil (ExtAct TypeOfActions)))
      by (rewrite app_nil_r; reflexivity).
    eapply wt_concat; [ exact Hdrain | exact Hwy ]. }
  destruct (Hc2 (map ActOut l2) yy
              (fw_converge_static (map ActOut l2) (g M) (bag l1) (static_g M HM))
              Hbig Hsty)
    as (x & Hwx & Hstx & Hincl).
  destruct (fw_conservation _ _ _ Hwx) as (r & Hr & Hbal). simpl in Hbal.
  rewrite ins_map_out in Hbal. rewrite outs_map_out in Hbal. simpl in Hbal.
  exists r, x.1. split; [ exact Hr | ]. multiset_solver.
Qed.


(** Lu à l'envers, le terme correcteur dit *quand* le sac de droite peut
    déborder : uniquement si le processus gauche **émet**. *)

Theorem emit_of_bag_incl_failure : forall (l1 l2 : list TypeOfActions) (M N : gproc),
  gStatic M -> gStatic N ->
  ((msgs l1 ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))) ->
  ~ (bag l2 ⊆ bag l1) ->
  exists r q, ((g M) : proc) ⟹[r] q /\ outs r <> [].
Proof.
  intros l1 l2 M N HM HN Hpre Hno.
  destruct (bag_incl_of_below_emit l1 l2 M N HM HN Hpre) as (r & q & Hr & Hsub).
  exists r, q. split; [ exact Hr | ].
  intro Ho. apply Hno. rewrite Ho in Hsub. simpl in Hsub. multiset_solver.
Qed.

(** ** ★ QUAND LA SOMME DROITE EST τ-LIBRE, LE BILAN EST UNE ÉGALITÉ

    Le cas du résidu : la droite y est **stable**, donc sa somme est
    τ-libre.  Alors l'état que la droite atteint après vidange est
    [g N ▷ ∅], qui **n'émet rien du tout** (une somme gardée n'émet
    jamais, [gsum_no_out], et le buffer est vide).  La condition
    d'acceptation force donc l'état gauche à n'émettre rien non plus —
    ni par son processus, ni par son buffer, qui est donc **vide**.

    Le bilan de [fw_conservation_bounded] devient alors une **égalité** :

        bag l1 ⊎ bag (outs r) = bag l2 ⊎ bag (ins r)

    « ce que la gauche avait plus ce qu'elle a produit = ce que la droite
    avait plus ce qu'elle a consommé ».  C'est nettement plus fort que
    l'inclusion, et c'est disponible sans aucun critère. *)

Theorem bag_balance_of_taufree_right : forall (l1 l2 : list TypeOfActions)
    (p : proc) (N : gproc),
  Static p -> gStatic N ->
  (forall z, ~ lts ((g N) : proc) τ z) ->
  ((msgs l1 ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))) ->
  exists r q, p ⟹[r] q
           /\ (forall c v z, ~ lts q (ActExt (ActOut (c,v))) z)
           /\ (forall z, ~ lts q τ z)
           /\ bag (ins r) ⊆ bag l1
           /\ bag l1 ⊎ bag (outs r) = bag l2 ⊎ bag (ins r).
Proof.
  intros l1 l2 p N Hp HN HstN Hpre.
  destruct (msgs_accept l1 l2 p (g N) Hpre) as (Hc1 & Hc2).
  assert (Hdrain : (((g N) : proc) ▷ bag l2)
                     ⟹[map ActOut l2] (((g N) : proc) ▷ (∅ : MO (ExtAct TypeOfActions)))).
  { replace (bag l2) with (bag l2 ⊎ (∅ : MO (ExtAct TypeOfActions))) at 1
      by (apply gmultiset.gmultiset_disj_union_right_id).
    apply bag_wt_drain. }
  assert (Hsty : (((g N) : proc) ▷ (∅ : MO (ExtAct TypeOfActions))) ↛).
  { apply stable_of_no_step. intros z Hz.
    destruct (fw_tau_shape _ _ _ Hz) as [(p' & Hp' & _)|(a & p' & m' & Hm & _ & _)].
    - eapply HstN. exact Hp'.
    - simpl in Hm. multiset_solver. }
  destruct (Hc2 (map ActOut l2) _
              (fw_converge_static (map ActOut l2) p (bag l1) Hp)
              Hdrain Hsty)
    as (x & Hwx & Hstx & Hincl).
  destruct x as (px,mx).
  assert (Hnoemit : forall d w z, ~ ((px ▷ mx) ⟶[ActOut (d,w)] z)).
  { intros d w z Hz.
    assert (Habs : (Inputs d) ∈ ⌈ 𝝳ᴠᴀᴄᴄꜱ ∘ Φᴠᴀᴄᴄꜱ ⌉ (coR (px ▷ mx)))
      by (apply coR_abs_pair_iff; exists w, z; exact Hz).
    apply Hincl in Habs.
    apply coR_abs_pair_iff in Habs as (w' & r' & Hr').
    destruct (proj1 (fw_emits_iff ((g N) : proc) (∅ : MO (ExtAct TypeOfActions)) (d,w'))
                (ex_intro _ r' Hr')) as [(p' & Hp')|Hin].
    - eapply gsum_no_out. exact Hp'.
    - eapply gmultiset_not_elem_of_empty. exact Hin. }
  assert (Hbuf : mx = (∅ : MO (ExtAct TypeOfActions))).
  { destruct (decide (mx = (∅ : MO (ExtAct TypeOfActions)))) as [E|E]; [ exact E | exfalso ].
    apply gmultiset_choose in E as (zz & Hzz).
    assert (Hoo : OutOnly mx)
      by (eapply (OutOnly_wt _ _ (px,mx)); [ exact Hwx | simpl; apply outonly_of_bag ]).
    destruct (Hoo zz Hzz) as ((d,w) & Ezz). subst zz.
    destruct (proj2 (fw_emits_iff px mx (d,w)) (or_intror Hzz)) as (y & Hy).
    eapply Hnoemit. exact Hy. }
  destruct (fw_conservation_bounded _ _ _ Hwx) as (r & Hr & Hbal & Hsub).
  simpl in Hbal, Hsub, Hr. rewrite ins_map_out in Hbal, Hsub.
  rewrite outs_map_out in Hbal. rewrite Hbuf in Hbal, Hsub.
  exists r, px. split; [ exact Hr | ]. split.
  - intros c v z Hz. eapply (Hnoemit c v (z, mx)). apply ParLeft. exact Hz.
  - split.
    + intros z Hz. pose proof (no_step_of_stable (px ▷ mx) Hstx (z, mx)) as Hns.
      apply Hns. apply ParLeft. exact Hz.
    + split; [ multiset_solver | multiset_solver ].
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
(*  is [VACCS_Forwarder.fw_drain_project_on]: the same run, with the       *)
(*  buffer emissions dropped, is a τ-run from the surplus alone —       *)
(*  reaching the very same state.                                       *)


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

(** The peeling itself: a **prefix** of summands meeting [DropOk] is
    discarded, whatever the rest [r] is.  Below-[𝟘] is the case [r = []];
    the general form is a *derivable restriction* of a sum to its
    non-droppable summands — ce que [grestrict] et [ax_restrict]
    cherchent à faire avec un certificat [BadK], obtenu ici par un
    critère syntaxique et décidable. *)

(** ** ★ LE PELAGE, AU CRITÈRE [ochans] PAR GARDE

    Le pelage « muet » que ce bloc remplace exigeait [gochans a = []] de
    chaque sommant pelé, ce qui exclut le **copycat** — dont la continuation émet, précisément
    sur la voie de sa propre garde.  Or [ax_drop_ochans] n'a jamais
    demandé le silence : il suffit que la continuation n'émette **que
    sur la voie de sa garde**.

    [DropOk] est ce critère, et il exclut au passage les [𝛕]-sommants et
    les sous-sommes, ce qui rend inutiles les hypothèses de stabilité et
    de feuille que portait la version précédente. *)

Definition DropOk (a : gproc) : Prop :=
  match a with
  | gpr_success => True
  | gpr_nil => True
  | gpr_input c P => forall d, In d (ochans P) -> d = c
  | gpr_tau _ => False
  | gpr_choice _ _ => False
  end.

(** Et l'instance qui motive le critère : une somme de **copycats** est
    dérivablement sous [𝟘], ce que le pelage muet ne pouvait pas dire. *)

Lemma gCopycats_DropOk : forall M, gCopycats M -> Forall DropOk (summands M).
Proof.
  induction M as [ | | c P | P | M1 IH1 M2 IH2 ]; intro HM; simpl in *.
  - repeat constructor.
  - repeat constructor.
  - repeat constructor. subst P. simpl. intros d [He|[]]. congruence.
  - contradiction.
  - destruct HM as (H1 & H2). apply Forall_app. split; [ apply IH1 | apply IH2 ];
      assumption.
Qed.

(** Le critère muet en est un cas particulier : une garde silencieuse
    n'émet sur aucune voie, donc *a fortiori* pas hors de la sienne. *)

Lemma DropOk_of_mute : forall (aa : gproc),
  summands aa = [aa] -> gStable aa -> gochans aa = [] -> DropOk aa.
Proof.
  intros aa Hlf Hsb Ho. destruct aa as [ | | c P | P | A B ]; simpl in *.
  - exact I.
  - exact I.
  - intros d Hd. rewrite Ho in Hd. contradiction.
  - contradiction.
  - exfalso.
    assert (Hlen : length (summands A ++ summands B) = 1%nat)
      by (rewrite Hlf; reflexivity).
    rewrite length_app in Hlen.
    assert (HA := summands_nonempty A). assert (HB := summands_nonempty B).
    destruct (summands A); [ exact (HA eq_refl) | ].
    destruct (summands B); [ exact (HB eq_refl) | ].
    simpl in Hlen. lia.
Qed.


(** ** ★ UNE GARDE COPYCAT SUR UNE VOIE DU SAC : LA DESCENTE SUFFIT

    La délivrance d'un message du sac dans une garde **copycat** rend ce
    message aussitôt — et le choix gardé **s'engage**, donc tout le reste
    de la somme disparaît.  L'état atteint est donc `≡*` au **sac nu**,
    et [ax_below_cfg_descend] ferme le but sans aucune hypothèse
    sémantique ni appel récursif.

    C'est le seul endroit du développement où l'engagement du choix
    gardé — la source de presque tous les résultats négatifs — joue **en
    faveur** de la dérivation. *)

Definition ccatg (k : ChannelData) : gproc := k ? (k ! (bvar 0) • 𝟘).

Lemma ccatg_gStatic : forall k, gStatic (ccatg k).
Proof. intro k. unfold ccatg. repeat constructor. Qed.

Lemma ccatg_lts_in : forall (c : ChannelData) (u : ValueData),
  lts ((g (ccatg c)) : proc) (ActExt (ActIn (c,u))) ((c ! u • 𝟘) : proc).
Proof.
  intros c u. unfold ccatg.
  assert (E : subst_in_proc 0 u (((c ! (bvar 0) • 𝟘)) : proc) = ((c ! u • 𝟘) : proc))
    by reflexivity.
  rewrite <- E. apply lts_input.
Qed.

(** La forme générale : il suffit que la garde **rende** le message.  Le
    résidu [K] de cette ré-émission remplace alors toute la somme, et il
    est un réduit de réduit de [g M] — donc **strictement plus petit**,
    ce qu'aucune autre route de ce développement n'offre du côté gauche. *)

Lemma cgr_swap_out : forall (A B C : proc),
  (A ‖ (B ‖ C)) ≡* ((B ‖ A) ‖ C).
Proof.
  intros A B C.
  transitivity ((A ‖ B) ‖ C).
  - symmetry. apply cgr_par_assoc.
  - apply cgr_fullpar; [ apply cgr_par_com | apply cgr_refl ].
Qed.

(* ------------------------------------------------------------------ *)
(*  LE REJEU D'UN RUN DU PROCESSUS À L'INTÉRIEUR D'UNE CONFIGURATION    *)
(*                                                                     *)
(*  Les deux descentes ci-dessus traitent un renvoi précédé de pas      *)
(*  INTERNES.  L'écart restant était le renvoi précédé d'autres         *)
(*  DÉLIVRANCES : le run projeté par [fw_conservation_bounded] peut     *)
(*  consommer plusieurs messages du sac avant de rendre le premier.     *)
(*                                                                     *)
(*  Le théorème général le couvre : *tout* run du processus se rejoue   *)
(*  à l'intérieur de la configuration, le sac servant ses entrées et    *)
(*  absorbant ses sorties.  Trois pas, un par constructeur de [wt] :    *)
(*  un [τ] passe par [lts_parR], une entrée par la délivrance           *)
(*  ([ax_below_cfg_descend_p]), une sortie par [≡*] seul — un processus *)
(*  qui émet EST le message à côté de son résidu                        *)
(*  ([TransitionShapeForOutputSimplified]), donc le message rejoint le  *)
(*  sac sans qu'aucune transition ne soit requise.                      *)
(*                                                                     *)
(*  La seule hypothèse est que le sac initial contienne de quoi servir  *)
(*  toutes les entrées : les sorties ne font qu'ajouter, donc           *)
(*  l'invariant se maintient.                                          *)
(* ------------------------------------------------------------------ *)


Theorem ax_cfg_replay : forall (r : trace (ExtAct TypeOfActions)) (p q : proc),
  p ⟹[r] q ->
  forall (l : list TypeOfActions), bag (ins r) ⊆ bag l ->
  exists lf, bag lf ⊎ bag (ins r) = bag l ⊎ bag (outs r)
          /\ (msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs lf ‖ q).
Proof.
  intros r p q Hw. induction Hw as [x | s x y z Hl Hwt IH | mu s x y z Hl Hwt IH];
    intros l Hsub.
  - exists l. split; [ reflexivity | apply ax_refl ].
  - destruct (IH l Hsub) as (lf & Hbal & Hax).
    exists lf. split; [ exact Hbal | ].
    eapply ax_trans; [ | exact Hax ].
    apply ax_tau_step. apply lts_parR. exact Hl.
  - destruct mu as [[c v]|[c v]].
    + simpl in Hsub |- *.
      assert (Hin : In (c,v) l).
      { apply bag_elem. eapply gmultiset_elem_of_subseteq; [ | exact Hsub ].
        apply gmultiset_elem_of_disj_union. left.
        apply gmultiset_elem_of_singleton. reflexivity. }
      apply in_split in Hin as (l1 & l2 & Heq).
      assert (Hperm : Permutation l ((c,v) :: (l1 ++ l2))).
      { rewrite Heq. symmetry. apply Permutation_middle. }
      assert (Hbl : bag l = {[+ ActOut (c,v) +]} ⊎ bag (l1 ++ l2)).
      { rewrite (bag_perm _ _ Hperm). reflexivity. }
      assert (Hsub0 : bag (ins s) ⊆ bag (l1 ++ l2)).
      { rewrite Hbl in Hsub. multiset_solver. }
      destruct (IH (l1 ++ l2) Hsub0) as (lf & Hbal & Hax).
      exists lf. split.
      * rewrite Hbl. multiset_solver.
      * eapply ax_below_cfg_descend_p; [ exact Hperm | exact Hl | exact Hax ].
    + simpl in Hsub |- *.
      assert (Hsub1 : bag (ins s) ⊆ bag ((c,v) :: l)) by (simpl; multiset_solver).
      destruct (IH ((c,v) :: l) Hsub1) as (lf & Hbal & Hax).
      exists lf. split.
      * simpl in Hbal. multiset_solver.
      * eapply ax_trans; [ | exact Hax ].
        apply ax_cgr.
        transitivity (msgs l ‖ (((c ! v • 𝟘) : proc) ‖ y)).
        -- apply cgr_fullpar; [ apply cgr_refl | ].
           apply (TransitionShapeForOutputSimplified _ _ _ _ Hl).
        -- simpl. apply cgr_swap_out.
Qed.

(** …et quand le run **rend exactement ce qu'il a pris**, le sac est
    restitué et la configuration passe sous son propre résidu.  C'est la
    forme générale dont [cfg_return_below_residue_w] est le cas d'un
    seul message rendu tout de suite après un τ-run. *)

Corollary ax_cfg_replay_balanced : forall (r : trace (ExtAct TypeOfActions))
    (p q : proc) (l : list TypeOfActions),
  p ⟹[r] q -> bag (ins r) ⊆ bag l -> bag (outs r) = bag (ins r) ->
  (msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ q).
Proof.
  intros r p q l Hw Hsub Hbal.
  destruct (ax_cfg_replay r p q Hw l Hsub) as (lf & Heq & Hax).
  rewrite Hbal in Heq.
  assert (Hlf : bag lf = bag l) by multiset_solver.
  eapply ax_trans; [ exact Hax | ].
  apply ax_cgr. apply cgr_fullpar; [ | apply cgr_refl ].
  apply bag_msgs_eq. exact Hlf.
Qed.

(** ** ★ LE REJEU ATTERRIT SUR LE SAC DE DROITE

    Les deux résultats se composent exactement.  Le bilan
    ([bag_balance_of_taufree_right]) donne un run [r] du processus gauche
    avec [bag l1 ⊎ bag (outs r) = bag l2 ⊎ bag (ins r)] ; le rejeu
    ([ax_cfg_replay]) le joue dans la configuration et atterrit au sac
    [lf] avec [bag lf ⊎ bag (ins r) = bag l1 ⊎ bag (outs r)].  Les deux
    équations donnent **[bag lf = bag l2]**.

    Autrement dit : *pour une somme droite τ-libre, la configuration
    gauche est dérivablement sous une configuration **au sac de droite**,
    dont le processus n'émet rien.*  Les deux sacs, que rien ne reliait
    sans critère, sont ainsi **égalisés** par une dérivation.

    Ce que cela ne donne pas : le rejeu **monte** dans le préordre, donc
    l'hypothèse sémantique ne se transporte pas sur [msgs l2 ‖ q].  C'est
    l'obstruction structurelle habituelle, et elle est intacte. *)

Corollary ax_replay_to_right_bag : forall (l1 l2 : list TypeOfActions)
    (p : proc) (N : gproc),
  Static p -> gStatic N ->
  (forall z, ~ lts ((g N) : proc) τ z) ->
  ((msgs l1 ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l2 ‖ ((g N) : proc))) ->
  exists q, (forall c v z, ~ lts q (ActExt (ActOut (c,v))) z)
         /\ (forall z, ~ lts q τ z)
         /\ (msgs l1 ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l2 ‖ q).
Proof.
  intros l1 l2 p N Hp HN HstN Hpre.
  destruct (bag_balance_of_taufree_right l1 l2 p N Hp HN HstN Hpre)
    as (r & q & Hr & Hno & Hst & Hsub & Hbal).
  destruct (ax_cfg_replay r p q Hr l1 Hsub) as (lf & Hlf & Hax).
  exists q. split; [ exact Hno | ]. split; [ exact Hst | ].
  eapply ax_trans; [ exact Hax | ].
  apply ax_cgr. apply cgr_fullpar; [ | apply cgr_refl ].
  apply bag_msgs_eq. multiset_solver.
Qed.

(** ** LES DESCENTES EN SONT DES INSTANCES

    Un renvoi est un run à deux actions — l'entrée, puis la sortie, avec
    des pas internes entre les deux ([wt_push_nil_left]) — et il est
    **équilibré** : ce qui est pris est exactement ce qui est rendu.
    Toute la famille de descentes se dérive donc du rejeu. *)

Theorem cfg_return_below_residue_w :
  forall (l l0 : list TypeOfActions) (c : ChannelData) (u : ValueData)
         (M : gproc) (Mc Mc' K : proc),
    Permutation l ((c,u) :: l0) ->
    lts ((g M) : proc) (ActExt (ActIn (c,u))) Mc ->
    (Mc ⟹[[]] Mc') ->
    lts Mc' (ActExt (ActOut (c,u))) K ->
    (msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ K).
Proof.
  intros l l0 c u M Mc Mc' K Hperm Hin Hw Hout.
  eapply (ax_cfg_replay_balanced [ActIn (c,u); ActOut (c,u)]).
  - eapply wt_act; [ exact Hin | ].
    eapply wt_push_nil_left; [ exact Hw | ].
    eapply wt_act; [ exact Hout | apply wt_nil ].
  - simpl. rewrite (bag_perm _ _ Hperm). simpl. multiset_solver.
  - simpl. reflexivity.
Qed.

Theorem ax_below_cfg_descend_wreturn :
  forall (l l0 : list TypeOfActions) (c : ChannelData) (u : ValueData)
         (M : gproc) (Mc Mc' K q : proc),
    Permutation l ((c,u) :: l0) ->
    lts ((g M) : proc) (ActExt (ActIn (c,u))) Mc ->
    (Mc ⟹[[]] Mc') ->
    lts Mc' (ActExt (ActOut (c,u))) K ->
    (msgs l ‖ K) ᴠᴀᴄᴄꜱ⊑ₐₓ q ->
    (msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₐₓ q.
Proof.
  intros l l0 c u M Mc Mc' K q Hperm Hin Hw Hout Hax.
  eapply ax_trans; [ | exact Hax ].
  eapply cfg_return_below_residue_w;
    [ exact Hperm | exact Hin | exact Hw | exact Hout ].
Qed.

(** Et le renvoi *immédiat* est le cas [wt_nil]. *)

Theorem ax_below_cfg_descend_return :
  forall (l l0 : list TypeOfActions) (c : ChannelData) (u : ValueData)
         (M : gproc) (Mc K q : proc),
    Permutation l ((c,u) :: l0) ->
    lts ((g M) : proc) (ActExt (ActIn (c,u))) Mc ->
    lts Mc (ActExt (ActOut (c,u))) K ->
    (msgs l ‖ K) ᴠᴀᴄᴄꜱ⊑ₐₓ q ->
    (msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₐₓ q.
Proof.
  intros l l0 c u M Mc K q Hperm Hin Hout Hax.
  eapply ax_below_cfg_descend_wreturn;
    [ exact Hperm | exact Hin | apply wt_nil | exact Hout | exact Hax ].
Qed.

Theorem cfg_return_below_residue :
  forall (l l0 : list TypeOfActions) (c : ChannelData) (u : ValueData)
         (M : gproc) (Mc K : proc),
    Permutation l ((c,u) :: l0) ->
    lts ((g M) : proc) (ActExt (ActIn (c,u))) Mc ->
    lts Mc (ActExt (ActOut (c,u))) K ->
    (msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ K).
Proof.
  intros l l0 c u M Mc K Hperm Hin Hout.
  eapply cfg_return_below_residue_w;
    [ exact Hperm | exact Hin | apply wt_nil | exact Hout ].
Qed.

(** …et le cas copycat en est l'instance [K := 𝟘], sans plus aucune
    hypothèse de staticité. *)

Theorem cfg_copycat_guard_below_bag :
  forall (l l0 : list TypeOfActions) (c : ChannelData) (u : ValueData)
         (M : gproc) (r : list gproc),
    Permutation l ((c,u) :: l0) ->
    Permutation (summands M) ((ccatg c) :: r) ->
    (msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ ((g (𝟘 : gproc)) : proc)).
Proof.
  intros l l0 c u M r Hperm Hsum.
  eapply cfg_return_below_residue; [ exact Hperm | | apply lts_output ].
  eapply summand_lts; [ rewrite Hsum; left; reflexivity | apply ccatg_lts_in ].
Qed.

(** The [𝟘] case: discard *everything*. *)

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
  exists r', Static r' /\ (size r' < size q0)%nat /\ q' ᴠᴀᴄᴄꜱ⊑ₐₓ r' /\ r' ᴠᴀᴄᴄꜱ⊑ₐₓ q'.

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

Lemma domok_of_domsim_wt' : forall (q0 q : proc) s r,
  Static q0 -> domsim q0 q -> q ⟹[s] r -> s <> [] -> DomOk q0 r.
Proof.
  intros q0 q s r Hst Hd Hw Hs. destruct s as [|mu s0]; [ contradiction | ].
  eapply domok_of_domsim_wt; eassumption.
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

(** * THE LEFT-HAND CLASS, WEAKENED: [MuteSem]

    [MuteNF] asks for [⊢] in **both** directions between [p] and its mute
    configuration.  The recursion never needs that: it uses [⊢] one way —
    to move the goal onto the configuration — and the *semantics* the
    other way, to transport the hypothesis.  So the second conjunct can
    be a plain [⊑ₘᵤₛₜᵢ], which is strictly weaker (soundness turns any [⊢]
    into one).

    The widening is not cosmetic: **the copycat is in the class.**
    [ax_ccat_l] gives [(ccat c) ᴠᴀᴄᴄꜱ⊑ₐₓ (g 𝟘)] and [must_i_ccat_r] gives
    [g 𝟘 ⊑ₘᵤₛₜᵢ ccat c]; what [MuteNF] would additionally require is the
    converse *derivation* [(g 𝟘) ᴠᴀᴄᴄꜱ⊑ₐₓ (ccat c)].  And the copycat is precisely
    the shape the syntactic criterion [MuteG] excludes — it is what makes
    VACCS's must-preorder coarser than VCCS's.

    It is not vacuous either.  [c ? (d ! v • 𝟘)] belongs to no such class:
    a mute configuration can only ever emit what its bag held from the
    start, so it would have to offer [d] straight away, and [d ? ①]
    separates the two. *)

Definition MuteSem (p : proc) : Prop :=
  exists l M, gStatic M /\ ochans ((g M) : proc) = []
           /\ p ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ ((g M) : proc))
           /\ (msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ p.

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
             /\ q' ᴠᴀᴄᴄꜱ⊑ₐₓ r' /\ r' ᴠᴀᴄᴄꜱ⊑ₐₓ q'.

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

(** [MuteSem] transports along the *same* asymmetric pair it is defined
    by — [⊢] one way, the semantics the other — so any process squeezed
    that way against a member is itself a member. *)

Lemma MuteSem_transport : forall (p q : proc),
  q ᴠᴀᴄᴄꜱ⊑ₐₓ p -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> MuteSem p -> MuteSem q.
Proof.
  intros p q Hqp Hpq (l & M & HM & Hoc & Hpm & Hmp).
  exists l, M. split; [ exact HM | ]. split; [ exact Hoc | ].
  split.
  - eapply ax_trans; [ exact Hqp | exact Hpm ].
  - intros t Ht. apply Hpq. apply Hmp. exact Ht.
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

(** * THE RIGHT-HAND CLASS, WEAKENED TOO: [ResFree]

    Deep ν-freedom is asked of the right because [normal_form_deep] has
    to return a **bare configuration** for the matching machinery, and
    because [NoResD] is what survives the reducts.  But the top level
    only ever needs *some* deeply ν-free process that the right is
    [⊢]-equal to — the recursion then runs there. *)

Definition ResFree (q : proc) : Prop :=
  exists q', Static q' /\ NoResD q' /\ q ᴠᴀᴄᴄꜱ⊑ₐₓ q' /\ q' ᴠᴀᴄᴄꜱ⊑ₐₓ q.

(** [ResFree] is closed under parallel composition — [ax_par] on both
    sides, and [NoResD] of a product is [NoResD] of the factors. *)

Lemma ResFree_par : forall (p q : proc), ResFree p -> ResFree q -> ResFree (p ‖ q).
Proof.
  intros p q (p' & Hsp & Hnp & H1 & H2) (q' & Hsq & Hnq & H3 & H4).
  exists (p' ‖ q'). split; [ constructor; assumption | ].
  split; [ split; assumption | ].
  split; apply ax_par; assumption.
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

(** * WHY THE LAST ν CASE IS NOT PLUMBING

    What is left is a block with **both** visible and internal actions,
    e.g. [ν (g M)] where [M] guards a non-restricted channel.  The route
    is [resg], which turns it into a guarded sum whose guards carry
    [ν P] as continuations, and then rewriting those continuations in
    place — [ax_choice_tau] for a [𝛕]-guard, [ax_choice_input_bag] for an
    input.

    The input is where it stops, and the obstruction is already on record
    in this development.  [ax_input] is the **omega rule**: it consumes
    one *open* continuation, so retiring the ν under an input guard needs
    a single open [Q] with [(ν (P ^ v)) ᴠᴀᴄᴄꜱ≂ₐₓ (Q ^ v)] **at every [v]** — a
    *uniform* family.  Building [Q] means normalising [ν P] open, and
    normalisation is **not** substitution-equivariant:
    [VACCS_NormalForm.if_open_branch_depends_on_value] machine-checks
    that [Eval_Eq 0] picks a different branch of a conditional once a
    value is substituted, so no [normal_form_open] exists.

    [dom_u]/[sd_u] give uniform *transition* families, which is what made
    [normal_form_strong_u] possible; they do **not** give uniform
    [⊢]-equalities, and that is exactly the half needed here. *)

(** * A NEW ROUTE: THE RIGHT'S OUTPUTS ARE **WEAKLY** MATCHED ON THE LEFT

    The bag layer is the whole residue: Phase A ([ax_phaseA_direct] with
    [bigsum_certificate]) and the bare-sum step
    ([completeness_gsum_step_gen]) need **no** mutity — it enters only in
    [bag_incl_of_below_disj] and [msgs_cancel_surplus_disj], i.e. in
    relating the two bags.

    And even the bag-relative criterion is too strong for a reason worth
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

    This is the correct criterion-free replacement for
    [bag_incl_of_below_disj]'s first half, and it is exactly the shape a weak-output rule's existence
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
    per-residue — [p'' ᴠᴀᴄᴄꜱ⊑ₐₓ q''] for each emission residue — and that is
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

Lemma res_list_v_Static : forall n c v (p : proc), Static p ->
  Forall Static (res_list_v n c v p).
Proof.
  intros n c v p Hst. apply Forall_forall. intros x Hx.
  apply res_list_v_sound in Hx as (p1 & Hp1 & Ho).
  eapply Static_preserved_by_lts;
    [ eapply Static_preserved_by_wt; [ exact Hst | exact Hp1 ] | exact Ho ].
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
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> p' ᴠᴀᴄᴄꜱ⊑ₐₓ q') ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ ((g M) : proc).
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
  (p0 ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> p0 ᴠᴀᴄᴄꜱ⊑ₐₓ q) ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ q.
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
  (p0 ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> p0 ᴠᴀᴄᴄꜱ⊑ₐₓ q) ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ q.
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
  x ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> x ᴠᴀᴄᴄꜱ⊑ₐₓ q -> (g (ichoice [x])) ᴠᴀᴄᴄꜱ⊑ₐₓ q.
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
      [p ᴠᴀᴄᴄꜱ⊑ₐₓ (ichoice (tau_list p))].

    Together: a [p] with a [τ] and no external transition is
    **must-equivalent to the internal choice of its τ-successors**, and
    the goal [p ᴠᴀᴄᴄꜱ⊑ₐₓ q] may be replaced by [(ichoice (tau_list p)) ᴠᴀᴄᴄꜱ⊑ₐₓ q]
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
  (exists z, lts p τ z) -> p ᴠᴀᴄᴄꜱ⊑ₐₓ (g (ichoice (tau_list p))).
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
     (g (ichoice (tau_list p))) ᴠᴀᴄᴄꜱ⊑ₐₓ q) ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ q.
Proof.
  intros p q Hex Hnoext Hpre HR.
  eapply ax_trans; [ apply ax_left_ichoice; exact Hex | ].
  apply HR. intros t Ht. apply Hpre.
  apply (left_ichoice_below p Hex Hnoext). exact Ht.
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

(** ** …AND A MUTE LEFT IS ALREADY DONE

    When both blocks are gone the two sides are bare configurations, and
    the case where the left's guarded sum can **never emit along any run**
    ([ochans (g M1) = []]) is exactly [completeness_cfg_mute_dom], proved
    long ago and until now not wired into this chain.  Its recursive
    premise is over [DomOk], and [ax_below_of_domok] converts the
    [size]-indexed one this chain carries.

    Note the criterion is on the **sum** only: the left's own pending
    messages are allowed, since they go to the bag and never to [M1]. *)


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

Corollary ax_share_msgs_rev : forall (l : list TypeOfActions) (X Y : proc),
  (msgs l ‖ ((g ((𝛕 • X) + (𝛕 • Y))) : proc))
    ᴠᴀᴄᴄꜱ⊑ₐₓ (g ((𝛕 • (msgs l ‖ X)) + (𝛕 • (msgs l ‖ Y)))).
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
  (g (ichoice (map (fun x => msgs l ‖ x) L)))
    ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ ((g (ichoice L)) : proc)).
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
  (msgs l ‖ ((g (ichoice L)) : proc))
    ᴠᴀᴄᴄꜱ⊑ₐₓ (g (ichoice (map (fun x => msgs l ‖ x) L))).
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
  (msgs l ‖ p)
    ᴠᴀᴄᴄꜱ⊑ₐₓ (g (ichoice (map (fun x => msgs l ‖ x) (tau_list p)))).
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
   (g (ichoice (map (fun x => msgs l ‖ x) (tau_list p)))) ᴠᴀᴄᴄꜱ⊑ₐₓ q) ->
  (msgs l ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ q.
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
   (g (ichoice (map (fun x => msgs l ‖ x) (tau_list ((g M) : proc))))) ᴠᴀᴄᴄꜱ⊑ₐₓ q) ->
  (msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₐₓ q.
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
  forall A, In A (leaves M) -> ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g A) : proc).
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
  ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (leafsum M)) : proc).
Proof.
  induction M as (M & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ gsize Nat.lt_wf_0)).
  intros HMst HM. unfold leafsum. rewrite leaves_eq.
  destruct (gStableB M) eqn:E.
  - simpl. apply ax_cgr. apply cgr_choice_nil_rev.
  - inversion HM as [? Hs | M1 M2 H1 H2]; subst.
    + exfalso. apply gStableB_spec in Hs. rewrite Hs in E. discriminate E.
    + destruct (gStatic_tau_choice M1 M2 HMst) as (Hg1 & Hg2).
      assert (Hl1 : ((g M1) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (leafsum M1)) : proc))
        by (apply IH; [simpl; lia | exact Hg1 | exact H1]).
      assert (Hl2 : ((g M2) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (leafsum M2)) : proc))
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
  (msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ ((g (leafsum M)) : proc)).
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
  exists B, gStatic B /\ gStable B /\ canonical B /\ ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g B) : proc).
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
    (msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ ((g B) : proc)).
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
  (g ((𝛕 • ((g A) : proc)) + (𝛕 • ((g W) : proc))))
    ᴠᴀᴄᴄꜱ⊑ₐₓ (g (A + rebuild Y)).
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
  ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (A + rebuild Y)) : proc).
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
      ((g M) : proc) ᴠᴀᴄᴄꜱ⊑ₐₓ ((g (A + rebuild Y)) : proc).
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
      (msgs l ‖ ((g M) : proc)) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ ((g (A + rebuild Y)) : proc)).
Proof.
  intros l M A HM Hnf Hin.
  destruct (ax_leaf_convex_rest M A HM Hnf Hin) as (R & HR & Hall).
  exists R. split; [ exact HR | ].
  intros Y Z Hsplit.
  apply ax_par; [ apply ax_refl | apply (Hall Y Z Hsplit) ].
Qed.

(** * A DELIMITATION: THE TWO BAGS NEED NOT BE RELATED AT ALL

    [bag_incl_of_below_disj] gives [bag l ⊆ bag l1] under the bag-relative
    criterion (the left's emissions avoid the right bag's channels), and
    the whole [msgs_cancel] family rests on it.  The criterion is not
    slack: without it the right's bag
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

(** …et le témoin **exerce** le terme correcteur : l'inclusion y échoue,
    donc [emit_of_bag_incl_failure] impose au processus gauche d'émettre —
    ce qu'il fait, après son [𝛕]. *)

Corollary bag_incl_correction_is_needed : forall (c : ChannelData) (v : ValueData),
  exists r q, ((g (𝛕 • ((c ! v • 𝟘) : proc))) : proc) ⟹[r] q /\ outs r <> [].
Proof.
  intros c v.
  destruct (bag_incl_fails_without_mute c v) as (Hpre & _ & Hno).
  eapply (emit_of_bag_incl_failure (@nil TypeOfActions) [(c,v)]
            (𝛕 • ((c ! v • 𝟘) : proc)) (𝟘 : gproc));
    [ repeat constructor | constructor | exact Hpre | exact Hno ].
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

(** ** LE REJEU EST UN τ-RUN DE LA CONFIGURATION — donc un pas qui MONTE

    [ax_cfg_replay] rejoue un run du processus à l'intérieur de la
    configuration.  Le fait structurel qui explique *pourquoi* ce rejeu
    ne peut jamais fermer le but est que ce rejeu est, au niveau du LTS,
    un simple **τ-run de la configuration** (à [≡*] près) :

    - un [τ] du processus est un [τ] de la configuration ([lts_parR]) ;
    - une entrée est une **délivrance**, donc encore un [τ]
      ([cfg_deliver_step_p]) ;
    - et une sortie ne coûte **aucune** transition : un processus qui
      émet EST le message à côté de son résidu
      ([TransitionShapeForOutputSimplified]), donc le message rejoint le
      sac par [≡*] seul.

    Conséquence : l'état atteint est un τ-successeur, donc il passe
    *plus* de tests que la configuration de départ ([must_i_tau_below]).
    Le rejeu est un pas qui **monte** dans le préordre, et
    [tau_successor_cannot_be_chosen] interdit de choisir un
    τ-successeur en général — c'est l'explication uniforme du fait que
    ni [ax_cfg_replay] ni [ax_replay_to_right_bag] ne transportent
    l'hypothèse sémantique sur leur cible. *)

Theorem cfg_replay_tau_run : forall (r : trace (ExtAct TypeOfActions)) (p q : proc),
  p ⟹[r] q ->
  forall (l : list TypeOfActions), bag (ins r) ⊆ bag l ->
  exists lf z, bag lf ⊎ bag (ins r) = bag l ⊎ bag (outs r)
            /\ (msgs l ‖ p) ⟹[[]] z
            /\ z ≡* (msgs lf ‖ q).
Proof.
  intros r p q Hw. induction Hw as [x | s x y z Hl Hwt IH | mu s x y z Hl Hwt IH];
    intros l Hsub.
  - exists l, (msgs l ‖ x).
    split; [ reflexivity | split; [ apply wt_nil | apply cgr_refl ]].
  - destruct (IH l Hsub) as (lf & w & Hbal & Hrun & Hc).
    exists lf, w. split; [ exact Hbal | split; [ | exact Hc ]].
    assert (Hstep : lts (msgs l ‖ x) τ (msgs l ‖ y)) by (apply lts_parR; exact Hl).
    eapply wt_tau; [ exact Hstep | exact Hrun ].
  - destruct mu as [[c v]|[c v]].
    + simpl in Hsub |- *.
      assert (Hin : In (c,v) l).
      { apply bag_elem. eapply gmultiset_elem_of_subseteq; [ | exact Hsub ].
        apply gmultiset_elem_of_disj_union. left.
        apply gmultiset_elem_of_singleton. reflexivity. }
      apply in_split in Hin as (l1 & l2 & Heq).
      assert (Hperm : Permutation l ((c,v) :: (l1 ++ l2))).
      { rewrite Heq. symmetry. apply Permutation_middle. }
      assert (Hbl : bag l = {[+ ActOut (c,v) +]} ⊎ bag (l1 ++ l2)).
      { rewrite (bag_perm _ _ Hperm). reflexivity. }
      assert (Hsub0 : bag (ins s) ⊆ bag (l1 ++ l2)).
      { rewrite Hbl in Hsub. multiset_solver. }
      destruct (IH (l1 ++ l2) Hsub0) as (lf & w & Hbal & Hrun & Hc).
      destruct (cfg_deliver_step_p l (l1 ++ l2) c v x y Hperm Hl) as (rr & Hrr & Hcrr).
      destruct (cgr_wt_transfer [] _ rr _ (cgr_symm _ _ _ Hcrr) Hrun) as (w' & Hw' & Hcw').
      exists lf, w'. split; [ rewrite Hbl; multiset_solver | split ].
      * eapply wt_tau; [ exact Hrr | exact Hw' ].
      * transitivity w; [ apply cgr_symm; exact Hcw' | exact Hc ].
    + simpl in Hsub |- *.
      assert (Hsub1 : bag (ins s) ⊆ bag ((c,v) :: l)) by (simpl; multiset_solver).
      destruct (IH ((c,v) :: l) Hsub1) as (lf & w & Hbal & Hrun & Hc).
      assert (Hcg : (msgs l ‖ x) ≡* (msgs ((c,v) :: l) ‖ y)).
      { transitivity (msgs l ‖ (((c ! v • 𝟘) : proc) ‖ y)).
        - apply cgr_fullpar; [ apply cgr_refl | ].
          apply (TransitionShapeForOutputSimplified _ _ _ _ Hl).
        - simpl. apply cgr_swap_out. }
      destruct (cgr_wt_transfer [] _ (msgs l ‖ x) _ (cgr_symm _ _ _ Hcg) Hrun)
        as (w' & Hw' & Hcw').
      exists lf, w'. split; [ simpl in Hbal; multiset_solver | split ].
      * exact Hw'.
      * transitivity w; [ apply cgr_symm; exact Hcw' | exact Hc ].
Qed.

(** Et pour un run **équilibré**, le sac est restitué : la configuration
    τ-atteint (à [≡*] près) son propre résidu.  C'est la lecture LTS de
    [ax_cfg_replay_balanced], et elle dit exactement pourquoi cette
    dérivation ne se compose pas avec l'hypothèse sémantique. *)

Corollary cfg_replay_balanced_tau : forall (r : trace (ExtAct TypeOfActions))
    (p q : proc) (l : list TypeOfActions),
  p ⟹[r] q -> bag (ins r) ⊆ bag l -> bag (outs r) = bag (ins r) ->
  exists z, (msgs l ‖ p) ⟹[[]] z /\ z ≡* (msgs l ‖ q).
Proof.
  intros r p q l Hw Hsub Hbal.
  destruct (cfg_replay_tau_run r p q Hw l Hsub) as (lf & z & Heq & Hrun & Hc).
  rewrite Hbal in Heq.
  assert (Hlf : bag lf = bag l) by multiset_solver.
  exists z. split; [ exact Hrun | ].
  transitivity (msgs lf ‖ q); [ exact Hc | ].
  apply cgr_fullpar; [ | apply cgr_refl ].
  apply bag_msgs_eq. exact Hlf.
Qed.

(** ** ★ LE RÉSIDU SE RAMÈNE À CHOISIR UN RÉSIDU D'ÉMISSION

    Le rejeu ([ax_cfg_replay]) est un pas qui **monte**
    ([cfg_replay_tau_run]), donc il ne compose pas avec l'hypothèse
    sémantique.  Il existe pourtant une descente qui, elle, fait
    décroître **le sac de droite** — et c'est la seule route du
    développement qui décroisse du côté de la cible sans rien supposer
    de la forme du membre gauche.

    Le pas est élémentaire : un τ-run est un pas vers le haut
    ([ax_tau_run]), et un processus qui émet **est** le message à côté
    de son résidu ([TransitionShapeForOutputSimplified]).  Donc si l'un
    des résidus d'émission faible du membre gauche, remis à côté de son
    message, est sous la cible, le membre gauche l'est aussi. *)

Theorem ax_below_of_out_residue : forall (p p1 p'' q : proc) c v,
  p ⟹[[]] p1 -> lts p1 (ActExt (ActOut (c,v))) p'' ->
  ((c ! v • 𝟘) ‖ p'') ᴠᴀᴄᴄꜱ⊑ₐₓ q ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ q.
Proof.
  intros p p1 p'' q c v Hrun Hout Hax.
  eapply ax_trans; [ apply ax_tau_run; exact Hrun | ].
  eapply ax_trans; [ | exact Hax ].
  apply ax_cgr. apply (TransitionShapeForOutputSimplified _ _ _ _ Hout).
Qed.

(** Lu à une configuration : le message émis rejoint le **sac de la
    cible**, donc la comparaison se poursuit à un sac strictement plus
    petit. *)

Corollary ax_below_cfg_of_out_residue :
  forall (l l0 : list TypeOfActions) c v (p p1 p'' Q : proc),
  Permutation l ((c,v) :: l0) ->
  p ⟹[[]] p1 -> lts p1 (ActExt (ActOut (c,v))) p'' ->
  p'' ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l0 ‖ Q) ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ Q).
Proof.
  intros l l0 c v p p1 p'' Q Hperm Hrun Hout Hax.
  eapply ax_below_of_out_residue; [ exact Hrun | exact Hout | ].
  eapply ax_trans.
  - apply (ax_par ((c ! v • 𝟘)) ((c ! v • 𝟘)) p'' (msgs l0 ‖ Q));
      [ apply ax_refl | exact Hax ].
  - apply ax_cgr.
    transitivity (msgs ((c,v) :: l0) ‖ Q).
    + simpl. symmetry. apply cgr_par_assoc.
    + apply cgr_fullpar; [ | apply cgr_refl ].
      apply msgs_perm. symmetry. exact Hperm.
Qed.

(** …et la prémisse récursive de [HardResidue] décharge le pas restant :
    le résidu de la cible est atteint par une **transition** de la forme
    normale, donc [domsim] le mesure contre le [q] d'origine.  Il ne
    reste donc, du cas à sac non vide, que le **choix** d'un résidu
    d'émission faible du membre gauche. *)

Theorem ax_below_cfg_of_out_choice :
  forall (q p : proc) (l l0 : list TypeOfActions) c v (M : gproc),
    Static q -> Static p -> gStatic M ->
    domsim q (msgs l ‖ ((g M) : proc)) ->
    Permutation l ((c,v) :: l0) ->
    (exists p1 p'', p ⟹[[]] p1
                 /\ lts p1 (ActExt (ActOut (c,v))) p''
                 /\ p'' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l0 ‖ ((g M) : proc))) ->
    (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
       p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> p' ᴠᴀᴄᴄꜱ⊑ₐₓ q') ->
    p ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ ((g M) : proc)).
Proof.
  intros q p l l0 c v M Hq Hp HM Hdom Hperm (p1 & p'' & Hrun & Hout & Hsem) HR.
  destruct (cfg_out_of_perm l l0 c v ((g M) : proc) Hperm) as (r0 & Hr0 & Hc0).
  destruct (ds_s Hdom _ _ Hr0) as (r & Hlr & Hdr).
  assert (Hsr : Static r) by (eapply Static_preserved_by_lts; [ exact Hq | exact Hlr ]).
  assert (Hlt : (size r < size q)%nat)
    by (eapply Static_lts_decrease; [ exact Hq | exact Hlr ]).
  assert (Hp1 : Static p1) by (eapply Static_preserved_by_wt; [ exact Hp | exact Hrun ]).
  assert (Hp2 : Static p'') by (eapply Static_preserved_by_lts; [ exact Hp1 | exact Hout ]).
  assert (Hsem2 : p'' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ r).
  { intros t Ht. apply (soundness_ax _ _ (ds_r Hdr)).
    apply (proj1 (must_i_cgr _ _ Hc0)). apply Hsem. exact Ht. }
  assert (Hax : p'' ᴠᴀᴄᴄꜱ⊑ₐₓ r) by (apply HR; assumption).
  eapply ax_below_cfg_of_out_residue;
    [ exact Hperm | exact Hrun | exact Hout | ].
  eapply ax_trans; [ exact Hax | ].
  eapply ax_trans; [ exact (ds_l Hdr) | apply ax_cgr; exact Hc0 ].
Qed.

(** Le principe de choix correspondant, sous sa forme la plus nette.  La
    sémantique donne bien que le membre gauche **émet faiblement** ce que
    la cible émet ([weak_out_of_below], [res_list_v_nonempty]), et que le
    **choix interne de tous** ses résidus est sous le résidu de la cible
    ([ichoice_residues_below]) ; ce qu'elle ne donne pas est qu'**un**
    résidu le soit — l'alternation ∀∃ habituelle, ici sous sa forme la
    plus petite : elle ne porte plus sur un état témoin quelconque mais
    sur un résidu d'émission, à un sac strictement plus petit.

    Noter que les contre-exemples du dossier ne la réfutent pas : ils
    interdisent de choisir un **τ-successeur**
    ([tau_successor_cannot_be_chosen], [no_delivery_is_reversible]), pas
    un résidu d'émission.  Sur [MCert] — le témoin de la branche
    [SelfRetBag] — le bon choix existe et c'est celui que
    [cfg_copycat_guard_below_bag] emprunte : délivrer le message dans la
    garde copycat, qui le rend, puis l'émettre ; le résidu est [𝟘]. *)

Definition OutChoice : Prop :=
  forall (p : proc) (l l0 : list TypeOfActions) c v (M : gproc),
    Static p -> gStatic M -> Permutation l ((c,v) :: l0) ->
    p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g M) : proc)) ->
    exists p1 p'', p ⟹[[]] p1
                /\ lts p1 (ActExt (ActOut (c,v))) p''
                /\ p'' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l0 ‖ ((g M) : proc)).

Corollary ax_below_cfg_of_OutChoice : OutChoice ->
  forall (q p : proc) (l : list TypeOfActions) c v l0 (M : gproc),
    Static q -> Static p -> gStatic M ->
    domsim q (msgs l ‖ ((g M) : proc)) ->
    Permutation l ((c,v) :: l0) ->
    p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g M) : proc)) ->
    (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
       p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> p' ᴠᴀᴄᴄꜱ⊑ₐₓ q') ->
    p ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ ((g M) : proc)).
Proof.
  intros HC q p l c v l0 M Hq Hp HM Hdom Hperm Hsem HR.
  eapply ax_below_cfg_of_out_choice;
    [ exact Hq | exact Hp | exact HM | exact Hdom | exact Hperm | | exact HR ].
  apply (HC p l l0 c v M Hp HM Hperm Hsem).
Qed.

(** ** UN MESSAGE EN ATTENTE REND SOURD À SA PROPRE VOIE

    Un processus **τ-bloqué** qui peut émettre sur [c] refuse toute
    entrée sur [c] : sinon le message et la garde se synchroniseraient.
    C'est immédiat une fois l'asynchronie utilisée — un processus qui
    émet **est** le message à côté de son résidu
    ([TransitionShapeForOutputSimplified]) — et il faut y ajouter la
    généricité en valeur des entrées ([lts_in_value_swap]) : le message
    porte [w], la garde offre [v], et elles ne se rencontrent que parce
    qu'une garde d'entrée reçoit **à toute valeur**. *)

Lemma stuck_emit_refuses_in : forall (u u' z : proc) c w v,
  (forall x, ~ lts u τ x) ->
  lts u (ActExt (ActOut (c,w))) u' ->
  ~ lts u (ActExt (ActIn (c,v))) z.
Proof.
  intros u u' z c w v Hst Hout Hin.
  assert (Hc : u ≡* (((c ! w • 𝟘) : proc) ‖ u'))
    by (apply (TransitionShapeForOutputSimplified _ _ _ _ Hout)).
  destruct (cgr_lts_transfer u _ _ _ Hc Hin) as (z' & Hz' & _).
  inversion Hz'; subst.
  - inversion H3.
  - destruct (lts_in_value_swap u' _ q2 H3 c v w eq_refl) as (q3 & Hq3).
    assert (Htau : lts (((c ! w • 𝟘) : proc) ‖ u') τ
                       (((g (𝟘 : gproc)) : proc) ‖ q3))
      by (eapply lts_comL; [ apply lts_output | exact Hq3 ]).
    destruct (cgr_lts_transfer _ u _ _ (cgr_symm _ _ _ Hc) Htau) as (x & Hx & _).
    eapply Hst. exact Hx.
Qed.

(** Lu à une configuration : un client **τ-bloqué qui porte un message
    sur [c] refuse [c]**, à toute valeur.  Comparer
    [stable_cfg_refuses_bag], qui dit la même chose de la *composante
    processus* d'une somme gardée ; celle-ci porte sur la configuration
    entière, avec un processus quelconque, et à toute valeur.

    C'est la raison structurelle pour laquelle les tentatives de
    contre-exemple **à l'intérieur du résidu** échouent : [MeetsBag]
    force la somme gauche à émettre sur une voie du **sac de droite**,
    et un client τ-bloqué qui porte déjà ce message ne peut pas le
    recevoir — l'émission ne lui sert donc à rien.  (C'est ce qui a fait
    capoter la variante de [out_choice_is_false] où l'on tentait de
    rendre les continuations de [P1]/[P2] émettrices sur la voie du sac
    pour satisfaire [MeetsBag].) *)

Corollary stuck_cfg_refuses_bag_in :
  forall (l : list TypeOfActions) (P : proc) c w v z,
  (forall x, ~ lts (msgs l ‖ P) τ x) -> In (c,w) l ->
  ~ lts (msgs l ‖ P) (ActExt (ActIn (c,v))) z.
Proof.
  intros l P c w v z Hst Hin.
  apply in_split in Hin as (l1 & l2 & Heq).
  assert (Hperm : Permutation l ((c,w) :: (l1 ++ l2))).
  { rewrite Heq. symmetry. apply Permutation_middle. }
  destruct (cfg_out_of_perm l (l1 ++ l2) c w P Hperm) as (r0 & Hr0 & _).
  eapply stuck_emit_refuses_in; [ exact Hst | exact Hr0 ].
Qed.

(** ** ★★ LE RÉSIDU SE RAMÈNE À UNE COMPARAISON **NUE**

    Les deux outils de cette session se composent.  Le bilan
    ([bag_balance_of_taufree_right]) donne un run du processus gauche au
    bout duquel il est **τ-stable et non émetteur**, les deux sacs étant
    équilibrés ; le rejeu ([ax_cfg_replay]) joue ce run *à l'intérieur de
    la configuration* et y atterrit — **au sac de droite**, par
    cancellation du bilan ([ax_replay_to_right_bag]).

    Il ne reste alors qu'à comparer ce résidu [qq] à la somme droite
    **nue** : la précongruence de [‖] ([ax_par]) remet le sac des deux
    côtés d'un coup.  Autrement dit :

      qq ᴠᴀᴄᴄꜱ⊑ₐₓ (g M)   ⟹   (msgs l1 ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ g M)

    et la cible y est une **somme gardée nue**, forme pour laquelle
    [completeness_gsum_step_gen] est close.  Le sac disparaît donc des
    deux côtés, et le membre gauche perd toute structure : c'est la forme
    la plus resserrée du résidu obtenue.

    **Ce n'est pas une route, et il faut le dire.**  Le [qq] produit est
    le témoin que [bhv_pre_cond2] rend à la trace de vidange — un témoin
    **existentiel**, qu'on ne choisit pas — et
    [VACCS_DropProbes.no_drain_witness_for_OCp] montre qu'il peut
    n'exister **aucun** bon témoin : sur [OCp] les deux états atteints
    par la vidange sont [𝟘 ‖ P1] et [𝟘 ‖ P2], dont aucun n'est sous [𝟘],
    alors que l'inéquation est dérivable (par [ax_share_msg]).

    Ce que le théorème dit, et qui reste vrai : **le sac et la structure
    disparaissent** du résidu dès qu'un bon témoin existe.  Ce qu'il ne
    dit pas, c'est qu'il en existe un. *)

Theorem residue_reduces_to_bare :
  forall (l1 l : list TypeOfActions) (p : proc) (M : gproc),
  Static p -> gStatic M ->
  (forall z, ~ lts ((g M) : proc) τ z) ->
  (msgs l1 ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (msgs l ‖ ((g M) : proc)) ->
  exists qq,
    (forall c v z, ~ lts qq (ActExt (ActOut (c,v))) z)
    /\ (forall z, ~ lts qq τ z)
    /\ (qq ᴠᴀᴄᴄꜱ⊑ₐₓ ((g M) : proc) ->
        (msgs l1 ‖ p) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs l ‖ ((g M) : proc))).
Proof.
  intros l1 l p M Hp HM Htau Hsem.
  destruct (ax_replay_to_right_bag l1 l p M Hp HM Htau Hsem)
    as (qq & Hno & Hnt & Hax).
  exists qq. split; [ exact Hno | split; [ exact Hnt | ] ].
  intros Hqq. eapply ax_trans; [ exact Hax | ].
  apply (ax_par (msgs l) (msgs l) qq ((g M) : proc));
    [ apply ax_refl | exact Hqq ].
Qed.

(** ** THE EMITTING RIGHT-HAND SIDE, CLOSED BY POOLING

    [out_choice_is_false] refutes choosing ONE weak output residue of the
    left ([OutChoice]).  What the semantics does give, freely, is the
    INTERNAL CHOICE of *all* of them ([ichoice_residues_below]) — and
    that is enough, because [ax_share_msg] factors the emitted message
    out of a choice.  The chain:

      p ᴠᴀᴄᴄꜱ⊑ₐₓ (⊕ᵢ (msgs [(c,v)] ‖ rᵢ))     ax_ichoice_glb + ax_below_of_out_residue
           ⊑ msgs [(c,v)] ‖ ⊕ᵢ rᵢ        ax_share_msgs_ichoice   ← the pooling law
           ⊑ msgs [(c,v)] ‖ q''          ax_par + the recursive call
           ≂ q                            ax_cgr, since a process that emits
                                          IS the message beside its residue
                                          ([TransitionShapeForOutputSimplified])

    Every step but the third is unconditional; the third recurses at
    [q''], a strict reduct of [q].  This is the route the file's negative
    results kept pointing at — pooling, never descent. *)

Lemma ax_msg_bag_one : forall (c : ChannelData) (v : ValueData) (r : proc),
  ((c ! v • 𝟘) ‖ r) ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs [(c, v)] ‖ r).
Proof.
  intros c v r. simpl. apply ax_cgr.
  apply cgr_fullpar; [ apply cgr_symm; apply cgr_par_nil | reflexivity ].
Qed.

Theorem ax_below_of_out_pool : forall (p q q'' : proc) (c : ChannelData) (v : ValueData) n,
  Static p -> Static q -> (size p < n)%nat ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  lts q (ActExt (ActOut (c,v))) q'' ->
  (g (ichoice (res_list_v n c v p))) ᴠᴀᴄᴄꜱ⊑ₐₓ q'' ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ q.
Proof.
  intros p q q'' c v n Hp Hq Hn Hpre Hout Hrec.
  assert (Hne : res_list_v n c v p <> nil) by (eapply res_list_v_nonempty; eassumption).
  assert (H1 : p ᴠᴀᴄᴄꜱ⊑ₐₓ (g (ichoice (map (fun x => msgs [(c,v)] ‖ x) (res_list_v n c v p))))).
  { apply ax_ichoice_glb.
    - destruct (res_list_v n c v p); [ contradiction | simpl; discriminate ].
    - intros y Hy. apply in_map_iff in Hy. destruct Hy as (r & Heq & Hr). subst y.
      destruct (res_list_v_sound n p c v r Hr) as (p1 & Hrun & Ho).
      eapply ax_below_of_out_residue; [ exact Hrun | exact Ho | ].
      apply ax_msg_bag_one. }
  assert (H2 : (g (ichoice (map (fun x => msgs [(c,v)] ‖ x) (res_list_v n c v p))))
                 ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs [(c,v)] ‖ ((g (ichoice (res_list_v n c v p))) : proc)))
    by (apply ax_share_msgs_ichoice; exact Hne).
  assert (H3 : (msgs [(c,v)] ‖ ((g (ichoice (res_list_v n c v p))) : proc))
                 ᴠᴀᴄᴄꜱ⊑ₐₓ (msgs [(c,v)] ‖ q''))
    by (apply ax_par; [ apply ax_refl | exact Hrec ]).
  assert (H4 : (msgs [(c,v)] ‖ q'') ᴠᴀᴄᴄꜱ⊑ₐₓ q).
  { apply ax_cgr. simpl.
    etransitivity; [ apply cgr_fullpar; [ apply cgr_par_nil | reflexivity ] | ].
    apply cgr_symm. apply TransitionShapeForOutputSimplified. exact Hout. }
  eapply ax_trans; [ exact H1 | ].
  eapply ax_trans; [ exact H2 | ].
  eapply ax_trans; [ exact H3 | exact H4 ].
Qed.

(** …and the recursive premise is discharged by the outer induction on
    [size q]: the residue [q''] is a reduct of [q] ([Static_lts_decrease]),
    and the left-hand side of the call is [Static] ([res_list_v_Static]).
    So a right-hand side that EMITS needs no side condition at all. *)
Theorem completeness_step_out_emit : forall (p q : proc) (c : ChannelData) (v : ValueData) q'',
  Static p -> Static q ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> lts q (ActExt (ActOut (c,v))) q'' ->
  (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> p' ᴠᴀᴄᴄꜱ⊑ₐₓ q') ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ q.
Proof.
  intros p q c v q'' Hp Hq Hpre Hout HIH.
  assert (Hq'' : Static q'') by (eapply Static_preserved_by_lts; [ exact Hq | exact Hout ]).
  assert (Hlt : (size q'' < size q)%nat) by (eapply Static_lts_decrease; [ exact Hq | exact Hout ]).
  assert (Hst : Static ((g (ichoice (res_list_v (S (size p)) c v p))) : proc))
    by (apply static_g; apply ichoice_gStatic; apply res_list_v_Static; exact Hp).
  assert (Hsem : (g (ichoice (res_list_v (S (size p)) c v p))) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q'')
    by (eapply ichoice_residues_below; [ exact Hp | exact Hq | lia | exact Hpre | exact Hout ]).
  apply (ax_below_of_out_pool p q q'' c v (S (size p)));
    [ exact Hp | exact Hq | lia | exact Hpre | exact Hout | ].
  apply HIH; [ exact Hst | exact Hq'' | exact Hlt | exact Hsem ].
Qed.

(** "Does this process emit at all?" is decidable, because its pending
    outputs form a FINITE multiset ([lts_oba_mo]) — the same finiteness
    [emits_on_dec] rests on, read at the trivial channel set. *)
Lemma emits_any_dec : forall (u : proc),
  (exists c (v : ValueData) q, lts u (ActExt (ActOut (c,v))) q)
  \/ (forall c (v : ValueData) q, ~ lts u (ActExt (ActOut (c,v))) q).
Proof.
  intros u.
  destruct (emits_in_set_dec (fun _ => True) (fun c => or_introl I) u)
    as [ (c & _ & v & q & Hl) | Hno ].
  - left. exists c, v, q. exact Hl.
  - right. intros c v q Hl. eapply (Hno c I). exists v, q. exact Hl.
Qed.

(** ** …AND THE RESIDUE BECOMES A TRAPPED MESSAGE UNDER A BLOCK

    [domsim] carries both stability ([domsim_stable]) and muteness
    ([domsim_mute]) from [q] to its normal form, so the case left by
    [completeness_of_mute_stable_step] may be assumed AT a normal form
    [NF n l M].  There:

    - [l = []] is already closed — [stable_NF_empty_bag] takes the whole
      restriction block off with [resgn], leaving a bare guarded sum;
    - [l <> []] forces [n <> 0] ([residue_needs_a_trapped_block]), i.e.
      the bag sits under a RESTRICTION BLOCK and its messages are
      TRAPPED: they cannot escape ([VarC_action_add 1] never yields
      [bvar 0]), cannot be supplied from outside, and cannot be deleted
      either ([VACCS_DropProbes.trapped_message_is_not_deletable]).

    So the residue is exactly that, and — unlike [HardResidue] — it puts
    **no condition whatever on the left-hand side**. *)
Lemma domsim_mute : forall (p q : proc), domsim p q ->
  (forall c (v : ValueData) z, ~ lts p (ActExt (ActOut (c,v))) z) ->
  (forall c (v : ValueData) z, ~ lts q (ActExt (ActOut (c,v))) z).
Proof.
  intros p q Hs Hmu c v z Hz.
  destruct (ds_s Hs (ActExt (ActOut (c,v))) z Hz) as (r' & Hl & _). eapply Hmu. exact Hl.
Qed.




(** *** The control: a TRAPPED message no guard can consume IS deletable

    Contrast [VACCS_DropProbes.trapped_message_is_not_deletable], where
    a SIBLING guard on the restricted channel can consume the message,
    so the configuration has a [τ] and the two sides are separated.
    Here nothing can consume it: the emission never escapes the block
    ([VarC_action_add 1] never yields [bvar 0]) and there is no guard at
    all, so **neither side has any transition whatever** and
    [ax_same_lts] identifies them in both directions.

    The message is rigid in general ([msg_not_below_nil],
    [nil_not_below_msg_gen]), so this is a fact the rest of the system
    does not reach: [ax_par] would need the message itself to be below
    [𝟘], and no congruence drops it. *)

Lemma msg_nil_lts_inv : forall (c : ChannelData) (v : ValueData) al z,
  lts ((c ! v • 𝟘) ‖ ((g (𝟘 : gproc)) : proc)) al z -> al = ActExt (ActOut (c,v)).
Proof.
  intros c v al z Hz. inversion Hz; subst;
    try (exfalso; eapply nil_no_lts; eassumption);
    inversion H3; subst; reflexivity.
Qed.

Lemma res_trapped_no_lts : forall (v : ValueData) al z,
  ~ lts (ν (((bvar 0) ! v • 𝟘) ‖ ((g (𝟘 : gproc)) : proc))) al z.
Proof.
  intros v al z Hz. inversion Hz; subst.
  - assert (Hc := msg_nil_lts_inv (bvar 0) v (ActExt (VarC_action_add 1 μ)) p' H0).
    injection Hc as Hc. destruct μ as [(d,w)|(d,w)]; simpl in Hc; try discriminate Hc.
    injection Hc as Hc1 Hc2. destruct d; simpl in Hc1; discriminate Hc1.
  - assert (Hc := msg_nil_lts_inv (bvar 0) v τ p' H0). discriminate Hc.
Qed.

Lemma res_nil_no_lts : forall al z, ~ lts (ν ((g (𝟘 : gproc)) : proc)) al z.
Proof.
  intros al z Hz. inversion Hz; subst; eapply nil_no_lts; eassumption.
Qed.

Theorem ax_trapped_msg_deletable : forall (v : ValueData),
  (ν (((bvar 0) ! v • 𝟘) ‖ ((g (𝟘 : gproc)) : proc)))
    ᴠᴀᴄᴄꜱ⊑ₐₓ (ν ((g (𝟘 : gproc)) : proc))
  /\ (ν ((g (𝟘 : gproc)) : proc))
       ᴠᴀᴄᴄꜱ⊑ₐₓ (ν (((bvar 0) ! v • 𝟘) ‖ ((g (𝟘 : gproc)) : proc))).
Proof.
  intro v. split; apply ax_same_lts;
    try (repeat constructor);
    try (intros al z Hz; exfalso; eapply res_trapped_no_lts; exact Hz);
    try (intros al z Hz; exfalso; eapply res_nil_no_lts; exact Hz).
Qed.

(** * ★ COMPLETENESS FOR VACCS

    A right-hand side that does not emit is, up to [domsim], a BARE
    GUARDED SUM.  Under the restriction block of its normal form
    [Ѵⁿ (msgs l ‖ g M)] the bag never emits, so every transition is an
    input of [M] or a delivery of a message of the bag into [M]; the
    guarded sum [saturate l M] below lists both kinds as summands and has
    exactly the same transitions ([ax_same_lts]), and [resgn] removes the
    block.  A bare guarded sum is then closed by [ax_glb_tau] if it has a
    [τ] and by the stable case otherwise.

    No new rule: [ax_same_lts] is derived from [ax_settle_sim], and
    [resgn] from [ax_res_normalize]. *)

(** ** Inverting a transition under a block of restrictions

    [lts_res_ext_n] and [lts_res_tau_n] ([VACCS_Instance.v]) build such
    transitions; this is the missing inversion, and it is what lets the
    two sides be compared under the block rather than inside it — inside,
    the bag emits and the two are NOT equivalent. *)

Lemma VarC_action_add_revert : forall k n mu,
  VarC_action_add (k + n) mu = VarC_action_add k (VarC_action_add n mu).
Proof.
  intros k n mu. destruct mu as [(c,v)|(c,v)]; simpl; f_equal; f_equal;
    apply VarC_add_revert_def.
Qed.

Lemma lts_res_n_shape : forall n (p : proc) al z, lts (Ѵ n p) al z ->
  exists p', z = Ѵ n p' /\
    match al with
    | τ => lts p τ p'
    | ActExt mu => lts p (ActExt (VarC_action_add n mu)) p'
    end.
Proof.
  induction n as [|n IH]; intros p al z Hz.
  - exists z. split; [ reflexivity | ].
    destruct al as [mu|]; [ rewrite VarC_add_zero_ext | ]; exact Hz.
  - simpl in Hz. inversion Hz; subst.
    + destruct (IH p (ActExt (VarC_action_add 1 μ)) p' H0) as (p'' & Heq & Hl).
      exists p''. split; [ simpl; rewrite Heq; reflexivity | ].
      assert (Hr : VarC_action_add (S n) μ = VarC_action_add n (VarC_action_add 1 μ)).
      { replace (S n) with ((n + 1)%nat) by lia. apply VarC_action_add_revert. }
      rewrite Hr. exact Hl.
    + destruct (IH p τ p' H0) as (p'' & Heq & Hl).
      exists p''. split; [ simpl; rewrite Heq; reflexivity | ]. exact Hl.
Qed.

(** ** Pushing the bag into the continuations

    [bagify l M] is [M] with the bag prefixed to every continuation.  The
    value binder of an input guard sits between the bag and the
    continuation, so the bag is shifted by [NewVar 0] and the
    substitution of the received value puts it back
    ([NewVar_subst_cancel]) — which is why the targets coincide exactly
    rather than up to [≡*]. *)

Fixpoint bagify (l : list TypeOfActions) (M : gproc) : gproc :=
match M with
| gpr_success => gpr_success
| gpr_nil => gpr_nil
| gpr_input c P => gpr_input c ((NewVar 0 (msgs l)) ‖ P)
| gpr_tau p => gpr_tau ((msgs l) ‖ p)
| gpr_choice M1 M2 => gpr_choice (bagify l M1) (bagify l M2)
end.

Lemma bagify_lts_fwd : forall l (M : gproc) al y,
  lts ((g M) : proc) al y -> lts ((g (bagify l M)) : proc) al (msgs l ‖ y).
Proof.
  intros l M. induction M as [ | | c P | p | M1 IH1 M2 IH2 ]; intros al y Hy;
    simpl; try (inversion Hy; fail).
  - inversion Hy; subst. simpl.
    assert (Hc : subst_in_proc 0 v ((NewVar 0 (msgs l)) ‖ P)
                 = (msgs l ‖ subst_in_proc 0 v P)).
    { simpl. f_equal. apply NewVar_subst_cancel. }
    rewrite <- Hc. apply lts_input.
  - inversion Hy; subst. apply lts_tau.
  - inversion Hy; subst.
    + apply lts_choiceL. apply IH1. exact H3.
    + apply lts_choiceR. apply IH2. exact H3.
Qed.

Lemma bagify_lts_bwd : forall l (M : gproc) al z,
  lts ((g (bagify l M)) : proc) al z ->
  exists y, z = (msgs l ‖ y) /\ lts ((g M) : proc) al y.
Proof.
  intros l M. induction M as [ | | c P | p | M1 IH1 M2 IH2 ]; intros al z Hz;
    simpl in Hz; try (inversion Hz; fail).
  - inversion Hz; subst. exists (subst_in_proc 0 v P). split.
    + simpl. f_equal. apply NewVar_subst_cancel.
    + apply lts_input.
  - inversion Hz; subst. exists p. split; [ reflexivity | apply lts_tau ].
  - inversion Hz; subst.
    + destruct (IH1 al z H3) as (y & Heq & Hl). exists y. split;
        [ exact Heq | apply lts_choiceL; exact Hl ].
    + destruct (IH2 al z H3) as (y & Heq & Hl). exists y. split;
        [ exact Heq | apply lts_choiceR; exact Hl ].
Qed.

Lemma bagify_gStatic : forall l (M : gproc), gStatic M -> gStatic (bagify l M).
Proof.
  intros l M. induction M as [ | | c P | p | M1 IH1 M2 IH2 ]; intro HM;
    simpl; try constructor.
  - inversion HM; subst. constructor.
    + apply Static_NewVar. apply msgs_Static.
    + exact H0.
  - inversion HM; subst. constructor; [ apply msgs_Static | exact H0 ].
  - inversion HM; subst. apply IH1. exact H1.
  - inversion HM; subst. apply IH2. exact H2.
Qed.

(** ** A mute normal form IS a bare guarded sum

    Under the restriction block of a mute normal form, the bag never
    emits, so every transition is either an input of [M] or a delivery
    of a message of the bag into [M].  [saturate l M] lists both as
    summands of one guarded sum — [bagify l M] for the inputs (the bag
    pushed into each continuation) and one [𝛕]-summand per possible
    delivery — and has literally the same transitions.  [resgn] then
    removes the block, so the right-hand side is a bare guarded sum and
    [ax_glb_tau] / the stable case close it. *)

Fixpoint msg_outs (l : list (ChannelData * ValueData)) : list ((ChannelData * ValueData) * proc) :=
match l with
| [] => []
| cv :: l' => (cv, ((g 𝟘 : proc) ‖ msgs l'))
               :: map (fun x => (fst x, ((cv.1 ! cv.2 • 𝟘) ‖ snd x))) (msg_outs l')
end.

Lemma msg_outs_fwd : forall l c v B,
  lts (msgs l) (ActExt (ActOut (c,v))) B -> In ((c,v), B) (msg_outs l).
Proof.
  induction l as [|cv l IH]; intros c v B H; simpl in H.
  - inversion H.
  - inversion H; subst.
    + left. match goal with HH : lts (_ ! _ • 𝟘) _ _ |- _ => inversion HH; subst end.
      destruct cv; reflexivity.
    + right. apply in_map_iff.
      match goal with HH : lts (msgs l) _ ?q2 |- _ =>
        exists ((c,v), q2); split; [ reflexivity | apply IH; exact HH ] end.
Qed.

Lemma msg_outs_bwd : forall l a B,
  In (a, B) (msg_outs l) -> lts (msgs l) (ActExt (ActOut a)) B.
Proof.
  induction l as [|cv l IH]; intros a B H; simpl in H.
  - contradiction.
  - destruct H as [H|H].
    + injection H as <- <-. destruct cv as (c,v). simpl. apply lts_parL. apply lts_output.
    + apply in_map_iff in H as ((a',B') & Heq & Hin). simpl in Heq. injection Heq as <- <-.
      simpl. apply lts_parR. apply IH. exact Hin.
Qed.

Fixpoint deliv1 (a : ChannelData * ValueData) (B : proc) (M : gproc) : gproc :=
match M with
| gpr_input c P => if Data_dec c a.1 then gpr_tau (B ‖ subst_in_proc 0 a.2 P) else gpr_nil
| gpr_choice M1 M2 => gpr_choice (deliv1 a B M1) (deliv1 a B M2)
| _ => gpr_nil
end.

Fixpoint delivs (os : list ((ChannelData * ValueData) * proc)) (M : gproc) : gproc :=
match os with
| [] => gpr_nil
| x :: os' => gpr_choice (deliv1 x.1 x.2 M) (delivs os' M)
end.

Definition saturate (l : list (ChannelData * ValueData)) (M : gproc) : gproc :=
  gpr_choice (bagify l M) (delivs (msg_outs l) M).

Lemma deliv1_lts_bwd : forall a B M al z,
  lts ((g (deliv1 a B M)) : proc) al z ->
  al = τ /\ exists R, lts ((g M) : proc) (ActExt (ActIn a)) R /\ z = (B ‖ R).
Proof.
  intros (c,v) B M. induction M as [ | | c' P | P | M1 IH1 M2 IH2 ]; intros al z Hz;
    simpl in Hz; try (inversion Hz; fail).
  - destruct (Data_dec c' c) as [->|Hne]; [ | inversion Hz ].
    inversion Hz; subst. split; [ reflexivity | ].
    exists (subst_in_proc 0 v P). split; [ apply lts_input | reflexivity ].
  - inversion Hz; subst.
    + destruct (IH1 _ _ H3) as (-> & R & HR & ->). split; [ reflexivity | ].
      exists R. split; [ apply lts_choiceL; exact HR | reflexivity ].
    + destruct (IH2 _ _ H3) as (-> & R & HR & ->). split; [ reflexivity | ].
      exists R. split; [ apply lts_choiceR; exact HR | reflexivity ].
Qed.

Lemma deliv1_lts_fwd : forall a B M R,
  lts ((g M) : proc) (ActExt (ActIn a)) R -> lts ((g (deliv1 a B M)) : proc) τ (B ‖ R).
Proof.
  intros (c,v) B M. induction M as [ | | c' P | P | M1 IH1 M2 IH2 ]; intros R HR;
    simpl; try (inversion HR; fail).
  - inversion HR; subst. simpl. destruct (Data_dec c c) as [_|Hne]; [ apply lts_tau | congruence ].
  - inversion HR; subst.
    + apply lts_choiceL. apply IH1. exact H3.
    + apply lts_choiceR. apply IH2. exact H3.
Qed.

Lemma delivs_lts_bwd : forall os M al z,
  lts ((g (delivs os M)) : proc) al z ->
  al = τ /\ exists a B R, In (a,B) os /\ lts ((g M) : proc) (ActExt (ActIn a)) R /\ z = (B ‖ R).
Proof.
  induction os as [|x os IH]; intros M al z Hz; simpl in Hz; [ inversion Hz | ].
  inversion Hz; subst.
  - destruct (deliv1_lts_bwd _ _ _ _ _ H3) as (-> & R & HR & ->). split; [ reflexivity | ].
    exists x.1, x.2, R. split; [ left; destruct x; reflexivity | split; [ exact HR | reflexivity ] ].
  - destruct (IH _ _ _ H3) as (-> & a & B & R & Hin & HR & ->). split; [ reflexivity | ].
    exists a, B, R. split; [ right; exact Hin | split; [ exact HR | reflexivity ] ].
Qed.

Lemma delivs_lts_fwd : forall os M a B R,
  In (a,B) os -> lts ((g M) : proc) (ActExt (ActIn a)) R ->
  lts ((g (delivs os M)) : proc) τ (B ‖ R).
Proof.
  induction os as [|x os IH]; intros M a B R Hin HR; simpl in Hin; [ contradiction | simpl ].
  destruct Hin as [Hx|Hin].
  - subst x. apply lts_choiceL. apply deliv1_lts_fwd. exact HR.
  - apply lts_choiceR. eapply IH; eassumption.
Qed.

Lemma saturate_body_bwd : forall l M al z,
  lts ((g (saturate l M)) : proc) al z -> lts (msgs l ‖ ((g M) : proc)) al z.
Proof.
  intros l M al z Hz. unfold saturate in Hz. inversion Hz; subst.
  - destruct (bagify_lts_bwd l M _ _ H3) as (y & -> & Hy). apply lts_parR. exact Hy.
  - destruct (delivs_lts_bwd _ _ _ _ H3) as (-> & (c,v) & B & R & Hin & HR & ->).
    eapply lts_comL; [ apply msg_outs_bwd; exact Hin | exact HR ].
Qed.

Lemma saturate_body_fwd : forall l M al z,
  lts (msgs l ‖ ((g M) : proc)) al z ->
  (exists d w, al = ActExt (ActOut (d,w))) \/ lts ((g (saturate l M)) : proc) al z.
Proof.
  intros l M al z Hz. inversion Hz; subst.
  - right. unfold saturate. apply lts_choiceR.
    eapply delivs_lts_fwd; [ apply msg_outs_fwd; exact H1 | exact H4 ].
  - exfalso. match goal with HH : lts (msgs l) ((_ ▷ _) ?) _ |- _ =>
      eapply msgs_no_input; exact HH end.
  - match goal with HH : lts (msgs l) _ _ |- _ => rename HH into Hm end.
    destruct al as [mu|].
    + destruct (msgs_lts_inv l mu _ Hm) as (c0 & v0 & l0 & -> & _ & _).
      left. exists c0, v0. reflexivity.
    + exfalso. eapply msgs_no_tau. exact Hm.
  - right. unfold saturate. apply lts_choiceL. apply bagify_lts_fwd.
    match goal with HH : lts (g M) _ _ |- _ => exact HH end.
Qed.

Lemma trapped_saturate_lts_bwd : forall n l (M : gproc) al z,
  lts (Ѵ n (((g (saturate l M)) : proc))) al z ->
  lts (Ѵ n (msgs l ‖ ((g M) : proc))) al z.
Proof.
  intros n l M al z Hz.
  destruct (lts_res_n_shape n _ al z Hz) as (z' & Heq & Hl). subst z.
  destruct al as [mu|].
  - apply lts_res_ext_n. apply saturate_body_bwd. exact Hl.
  - apply lts_res_tau_n. apply saturate_body_bwd. exact Hl.
Qed.

Lemma trapped_saturate_lts_fwd : forall n l (M : gproc) al z,
  (forall c (v : ValueData) y,
     ~ lts (Ѵ n (msgs l ‖ ((g M) : proc))) (ActExt (ActOut (c,v))) y) ->
  lts (Ѵ n (msgs l ‖ ((g M) : proc))) al z ->
  lts (Ѵ n (((g (saturate l M)) : proc))) al z.
Proof.
  intros n l M al z Hmu Hz. assert (Hz0 := Hz).
  destruct (lts_res_n_shape n _ al z Hz) as (z' & Heq & Hl). subst z.
  destruct al as [mu|].
  - destruct (saturate_body_fwd l M _ _ Hl) as [ (d & w & E) | Hs ].
    + exfalso. destruct mu as [(d0,w0)|(d0,w0)]; simpl in E; [ discriminate E | ].
      eapply (Hmu d0 w0). exact Hz0.
    + apply lts_res_ext_n. exact Hs.
  - destruct (saturate_body_fwd l M _ _ Hl) as [ (d & w & E) | Hs ]; [ discriminate E | ].
    apply lts_res_tau_n. exact Hs.
Qed.

Lemma deliv1_gStatic : forall a B M, Static B -> gStatic M -> gStatic (deliv1 a B M).
Proof.
  intros (c,v) B M HB. induction M as [ | | c' P | P | M1 IH1 M2 IH2 ]; intro HM; simpl;
    try constructor.
  - destruct (Data_dec c' c); constructor. constructor; [ exact HB | ].
    apply Static_subst. inversion HM; assumption.
  - apply IH1. inversion HM; assumption.
  - apply IH2. inversion HM; assumption.
Qed.

Lemma saturate_gStatic : forall l M, gStatic M -> gStatic (saturate l M).
Proof.
  intros l M HM. unfold saturate. constructor; [ apply bagify_gStatic; exact HM | ].
  assert (Hos : forall a B, In (a,B) (msg_outs l) -> Static B).
  { intros a B Hin. eapply Static_preserved_by_lts;
      [ apply msgs_Static | apply msg_outs_bwd; exact Hin ]. }
  induction (msg_outs l) as [|x os IH]; simpl; [ constructor | constructor ].
  - apply deliv1_gStatic; [ | exact HM ]. destruct x as (a,B). apply (Hos a B). left. reflexivity.
  - apply IH. intros a B Hin. apply (Hos a B). right. exact Hin.
Qed.

Lemma domsim_trapped_saturate : forall n l (M : gproc), gStatic M ->
  (forall c (v : ValueData) y, ~ lts (NF n l M) (ActExt (ActOut (c,v))) y) ->
  domsim (NF n l M) (Ѵ n ((g (saturate l M)) : proc)).
Proof.
  intros n l M HM Hmu.
  assert (HsL : Static (NF n l M)) by (apply Static_NF; exact HM).
  assert (HsR : Static (Ѵ n ((g (saturate l M)) : proc)))
    by (apply Static_res_n; apply static_g; apply saturate_gStatic; exact HM).
  unfold NF in *. apply DomSim.
  - apply ax_same_lts; try assumption.
    + intros al z Hz. eapply trapped_saturate_lts_fwd; eassumption.
    + intros al z Hz. eapply trapped_saturate_lts_bwd; eassumption.
  - apply ax_same_lts; try assumption.
    + intros al z Hz. eapply trapped_saturate_lts_bwd; eassumption.
    + intros al z Hz. eapply trapped_saturate_lts_fwd; eassumption.
  - intros a r Hr. exists r. split; [ | apply domsim_refl ].
    eapply trapped_saturate_lts_bwd. exact Hr.
Qed.

(** A bare guarded sum with a [τ]: [ax_glb_sum], each premise a
    recursive call at a strictly smaller reduct measured by [domsim]. *)
Lemma tau_bare_gsum_of_domsim : forall (p q : proc) (M : gproc),
  Static p -> Static q -> domsim q ((g M) : proc) ->
  (exists z, lts ((g M) : proc) τ z) ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> p' ᴠᴀᴄᴄꜱ⊑ₐₓ q') ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ ((g M) : proc).
Proof.
  intros p q M Hp Hq Hsim Htau Hpre HR. apply ax_glb_tau.
  - destruct Htau as (z & Hz). exists z. apply gsum_tau_summand. exact Hz.
  - intros X HX.
    assert (Hl : lts ((g M) : proc) τ X)
      by (eapply summand_lts; [ exact HX | apply lts_tau ]).
    destruct (ds_s Hsim _ _ Hl) as (r' & Hr' & Hd).
    eapply ax_trans; [ | exact (ds_l Hd) ]. apply HR.
    + exact Hp.
    + eapply Static_preserved_by_lts; [ exact Hq | exact Hr' ].
    + eapply Static_lts_decrease; [ exact Hq | exact Hr' ].
    + intros t Ht. eapply must_i_tau_below; [ exact Hr' | ]. apply Hpre. exact Ht.
  - intros c Q HQ v.
    assert (Hl : lts ((g M) : proc) (ActExt (ActIn (c,v))) (subst_in_proc 0 v Q))
      by (eapply summand_lts; [ exact HQ | apply lts_input ]).
    destruct (ds_s Hsim _ _ Hl) as (r' & Hr' & Hd).
    eapply ax_trans; [ | exact (ds_l Hd) ]. apply HR.
    + constructor; [ constructor | exact Hp ].
    + eapply Static_preserved_by_lts; [ exact Hq | exact Hr' ].
    + eapply Static_lts_decrease; [ exact Hq | exact Hr' ].
    + eapply must_i_feed_below; [ exact Hpre | exact Hr' ].
Qed.

Theorem completeness_mute_NF_step : forall (p q : proc) n l (M : gproc),
  Static p -> Static q -> gStatic M ->
  domsim q (NF n l M) ->
  (forall c (v : ValueData) y, ~ lts (NF n l M) (ActExt (ActOut (c,v))) y) ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q ->
  (forall p' q', Static p' -> Static q' -> (size q' < size q)%nat ->
     p' ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> p' ᴠᴀᴄᴄꜱ⊑ₐₓ q') ->
  p ᴠᴀᴄᴄꜱ⊑ₐₓ (NF n l M).
Proof.
  intros p q n l M Hp Hq HM Hsim Hmu Hpre HR.
  assert (Hd2 : domsim (NF n l M) ((g (resgn n (saturate l M))) : proc))
    by (eapply domsim_trans; [ apply domsim_trapped_saturate; assumption
                             | apply domsim_resgn ]).
  assert (Hd3 : domsim q ((g (resgn n (saturate l M))) : proc))
    by (eapply domsim_trans; [ exact Hsim | exact Hd2 ]).
  eapply ax_trans; [ | exact (ds_r Hd2) ].
  destruct (lts_dec ((g (resgn n (saturate l M))) : proc) τ) as [ Hno | (z & Hz) ].
  - eapply stable_bare_gsum_of_domsim;
      [ exact Hp | exact Hq | apply resgn_gStatic; apply saturate_gStatic; exact HM
      | exact Hd3 | exact Hno | exact Hpre | exact HR ].
  - eapply tau_bare_gsum_of_domsim;
      [ exact Hp | exact Hq | exact Hd3 | exists z; exact Hz | exact Hpre | exact HR ].
Qed.

(** ** ★★★ COMPLETENESS

    | the right-hand side… | closed by |
    |---|---|
    | EMITS | [completeness_step_out_emit] — pooling, via [ax_share_msg] |
    | does not emit | [completeness_mute_NF_step] — a bare guarded sum |

    [emits_any_dec] decides between the two, and [completeness_from_step]
    supplies the recursion on the size of the right-hand side. *)
Theorem completeness_ax : forall (p q : proc), Static p -> Static q ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> p ᴠᴀᴄᴄꜱ⊑ₐₓ q.
Proof.
  apply completeness_from_step. intros p q Hp Hq Hpre HR.
  destruct (emits_any_dec q) as [ (c & v & q'' & Hout) | Hmute ].
  - eapply completeness_step_out_emit; eassumption.
  - destruct (normal_form_strong_sim q Hq) as (n & l & M & HM & Hsim).
    eapply ax_trans; [ | exact (ds_r Hsim) ].
    eapply completeness_mute_NF_step; try eassumption.
    eapply domsim_mute; [ exact Hsim | exact Hmute ].
Qed.

End VACCS_Matching.
