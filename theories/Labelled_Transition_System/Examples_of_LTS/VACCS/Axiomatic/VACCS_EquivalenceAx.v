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

(** * THE CHARACTERISATION, ON THE FRAGMENT COMPLETENESS COVERS

    Soundness of the 28-rule system is **unconditional** — no [Static]
    restriction, no side condition on any rule ([VACCS_SoundnessAx]).
    Completeness is proved on a fragment, and this file states the two
    together, in the style of [VCCS]'s [EquivalenceAx.v].

    Two restrictions remain, one per side, both stated as *classes*
    rather than as syntactic criteria:

    - the **right** must be [ResFree]: [⊢]-equal to some deeply ν-free
      process.  [ν] hides, so [ν p ⊑ₘᵤₛₜᵢ ν q] does not give
      [p ⊑ₘᵤₛₜᵢ q], and the hypothesis cannot be moved out of the block
      [normal_form] produces;
    - the **left** must be [MuteSem]: [⊢]-below a *mute* configuration
      [msgs l ‖ g M] (no continuation of any guard can emit) that is
      [⊑ₘᵤₛₜᵢ]-above it.  Pending messages are free — they go to the bag,
      never to the sum — and the class is closed under [‖]
      ([MuteSem_par]) and under the same asymmetric squeeze it is defined
      by ([MuteSem_transport]).

    [MuteSem] is strictly wider than the syntactic criterion [MuteG], and
    the gap is exactly the phenomenon that makes VACCS's must-preorder
    coarser than VCCS's: the **copycat** [ccat c = c ? (c ! x • 𝟘)] is in
    [MuteSem] ([MuteSem_ccat]) and rejected by [MuteG].

    It is not vacuous: [c ? (d ! v • 𝟘)] is in no such class, since a mute
    configuration can only emit what its bag held from the start, so it
    would have to offer [d] immediately, and [d ? ①] separates the two.
    Seven further routes to widening the left are refuted in
    [VACCS_DropProbes] and [VACCS_ChoiceProbes]. *)

From Stdlib Require Import List PeanoNat Lia.
From stdpp Require Import base gmultiset.
From TestingTheory Require Import MultisetLTSConstruction.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Shift VACCS_Precongruence VACCS_Expansion VACCS_ResNormalize
  VACCS_Copycat VACCS_Absorb VACCS_DefinitionAxiomatic VACCS_SoundnessAx VACCS_NormalForm
  VACCS_Forwarder VACCS_Cond2 VACCS_ReadySet VACCS_Canonical VACCS_Descent VACCS_Matching.
Import ListNotations.

Section VACCS_EquivalenceAx.

Context `{VP : VACCS_Parameters}.

(** ** The preorder *)

Theorem must_iff_ax_pre_gen : forall (p q : proc),
  Static p -> Static q -> ResFree q -> MuteSem p ->
  (ax_pre p q <-> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q).
Proof.
  intros p q Hp Hq Hrq Hmu. split.
  - apply soundness_ax.
  - apply completeness_resfree; assumption.
Qed.

Corollary must_iff_ax_pre_muteSem : forall (p q : proc),
  Static p -> Static q -> NoResD q -> MuteSem p ->
  (ax_pre p q <-> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q).
Proof.
  intros p q Hp Hq Hnq Hmu.
  apply must_iff_ax_pre_gen; try assumption.
  apply ResFree_of_NoResD; assumption.
Qed.

(** The syntactic instance: [MuteG] on a deeply ν-free left. *)

Corollary must_iff_ax_pre_muteG : forall (p q : proc),
  Static p -> Static q -> NoResD p -> NoResD q -> MuteG p ->
  (ax_pre p q <-> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q).
Proof.
  intros p q Hp Hq Hnp Hnq Hmu.
  apply must_iff_ax_pre_muteSem; try assumption.
  apply MuteSem_of_MuteNF. apply MuteNF_of_muteG; assumption.
Qed.

(** ** The equivalence

    [p ≂ₘᵤₛₜᵢ q] unfolds to [q ⊑ₘᵤₛₜᵢ p /\ p ⊑ₘᵤₛₜᵢ q] ([Must.v]), so the
    two directions are the preorder read twice — and the *right* side now
    has to be mute as well, since completeness is applied with the two
    processes swapped. *)

Theorem must_eq_iff_ax_eq_muteSem : forall (p q : proc),
  Static p -> Static q -> NoResD p -> NoResD q -> MuteSem p -> MuteSem q ->
  ((ax_pre p q /\ ax_pre q p) <-> p ≂ₘᵤₛₜᵢ q).
Proof.
  intros p q Hp Hq Hnp Hnq Hmp Hmq. split.
  - intros (H1 & H2). split; apply soundness_ax; assumption.
  - intros (H1 & H2). split.
    + apply completeness_muteSem; assumption.
    + apply completeness_muteSem; assumption.
Qed.

(** ** …and the two halves side by side *)

Corollary ax_pre_sound_and_complete_muteSem : forall (p q : proc),
  Static p -> Static q -> NoResD q -> MuteSem p ->
  (ax_pre p q -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q) /\ (p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q).
Proof.
  intros p q Hp Hq Hnq Hmu.
  split; apply (must_iff_ax_pre_muteSem p q); assumption.
Qed.

(** And the copycat, which [MuteG] excludes, is covered — alone, and
    **beside any mute configuration**, since [MuteSem] is closed under
    parallel composition. *)

Corollary must_iff_ax_pre_ccat : forall (c : ChannelData) (q : proc),
  Static q -> NoResD q ->
  (ax_pre (ccat c) q <-> (ccat c) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q).
Proof.
  intros c q Hq Hnq.
  apply must_iff_ax_pre_muteSem; try assumption.
  - repeat constructor.
  - apply MuteSem_ccat.
Qed.

Corollary must_iff_ax_pre_cfg_ccat :
  forall (c : ChannelData) (l : list TypeOfActions) (M : gproc) (q : proc),
  gStatic M -> ochans ((g M) : proc) = [] -> Static q -> ResFree q ->
  (ax_pre ((msgs l ‖ ((g M) : proc)) ‖ ccat c) q
     <-> ((msgs l ‖ ((g M) : proc)) ‖ ccat c) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q).
Proof.
  intros c l M q HM Hoc Hq Hrq.
  apply must_iff_ax_pre_gen; try assumption.
  - constructor; [ constructor; [ apply msgs_Static | apply static_g; exact HM ] | ].
    repeat constructor.
  - apply MuteSem_par; [ apply MuteSem_cfg; assumption | apply MuteSem_ccat ].
Qed.

(* ===================================================================== *)
(** * A SECOND CHARACTERISATION — RESTRICTED ON THE RIGHT INSTEAD

    [must_iff_ax_pre_gen] restricts the **left** ([MuteSem p]) and leaves
    the right free apart from ν-freedom.  The theorem below does the
    opposite: it restricts the **right** and leaves the left completely
    free.

    The criterion is that [q] can never emit along any run.  It is
    syntactic, decidable, and — this is what makes the recursion work —
    **closed under transitions**, so the class is never left.  And it is
    exactly what makes the residue vanish: every reduction of the
    completeness chain narrows the open case to a right-hand side that is
    stable **with a non-empty bag**, and a mute [q] has an empty bag in
    its normal form. *)

Theorem must_iff_ax_pre_mute_right : forall (p q : proc),
  Static p -> Static q -> NoResD q -> ochans q = [] ->
  (ax_pre p q <-> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q).
Proof. exact must_iff_ax_pre_no_output. Qed.

(** The equational form needs the criterion on both sides. *)
Theorem must_eq_iff_ax_eq_mute : forall (p q : proc),
  Static p -> Static q ->
  NoResD p -> ochans p = [] -> NoResD q -> ochans q = [] ->
  ((ax_pre p q /\ ax_pre q p) <-> p ≂ₘᵤₛₜᵢ q).
Proof.
  intros p q Hp Hq Hnp Hop Hnq Hoq. split.
  - intros (H1 & H2). split; apply soundness_ax; assumption.
  - intros (H1 & H2). split.
    + apply completeness_no_output_right; assumption.
    + apply completeness_no_output_right; assumption.
Qed.

(** ** Below [𝟘], the two notions coincide outright

    No side condition at all beyond [Static].  This subsumes the whole
    [Harmless] / [Bad] / [BadK] line of work: those judgements are
    *sufficient* conditions for [⊢ p ⊑ 𝟘], each provably incomplete, and
    the semantic fact now always has a derivation. *)

Theorem must_iff_ax_below_nil_final : forall (p : proc), Static p ->
  (ax_pre p ((g 𝟘) : proc) <-> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ ((g 𝟘) : proc)).
Proof. exact must_iff_ax_below_nil. Qed.


End VACCS_EquivalenceAx.
