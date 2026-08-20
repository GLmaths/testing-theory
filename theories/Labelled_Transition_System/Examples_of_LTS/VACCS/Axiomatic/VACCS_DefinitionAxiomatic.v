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

    Thirty rules.  Every one has its semantic justification proved in
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
    proves [⊢ p ⊑ q -> p ⊑ₘᵤₛₜᵢ q] outright. *)

From stdpp Require Import base gmultiset sets gmap.
From TestingTheory Require Import MultisetLTSConstruction.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Shift VACCS_Precongruence VACCS_Expansion VACCS_ResNormalize
  VACCS_Copycat VACCS_Absorb VACCS_Forwarder VACCS_Cond2 VACCS_Residues.

Section VACCS_DefinitionAxiomatic.

Context `{VP : VACCS_Parameters}.

Inductive ax_pre : proc -> proc -> Prop :=

(** *** Preorder and free equations *)

| ax_trans : forall p q r, ax_pre p q -> ax_pre q r -> ax_pre p r
| ax_cgr : forall p q, p ≡* q -> ax_pre p q

(** *** Congruence, one rule per operator

    [ax_par] and [ax_res] are sound by the two bridges — the context is
    moved into the test, and [p ⊑ₘᵤₛₜᵢ q] is applied at a *single* test.
    There is deliberately no rule for [+] beyond the two guard-preserving
    ones below. *)

| ax_par : forall p p' q q', ax_pre p p' -> ax_pre q q' -> ax_pre (p ‖ q) (p' ‖ q')
| ax_res : forall p q, ax_pre p q -> ax_pre (ν p) (ν q)
(** The omega rule, stated **with an inert context already in place**.

    The bare form [(∀v, ⊢ p^v ⊑ q^v) -> ⊢ g (c?p) ⊑ g (c?q)] is the case
    where the context is [𝟘], and is derived immediately below.  The
    context version is what the completeness recursion needs: a message
    bag sits *outside* the guard and cannot be moved inside it (a guard
    commits, a pending bag does not), so a rewrite under a guard has to
    be licensed with the bag already present.

    [Rc] is any family of **inert** processes — no [τ] and no input of
    their own, so their only moves are outputs — closed under those
    outputs.  Message bags and their sub-bags are the intended instance
    ([VACCS_Matching.bagctx]); nothing here mentions them. *)

| ax_input_ctx : forall (Rc : proc -> Prop) (c : ChannelData) (p q B : proc),
    (forall X, Rc X -> forall z, ~ lts X τ z) ->
    (forall X, Rc X -> forall a z, ~ lts X (ActExt (ActIn a)) z) ->
    (forall X, Rc X -> forall mu X', lts X (ActExt mu) X' -> Rc X') ->
    (forall X, Rc X -> forall v, ax_pre (X ‖ (p^v)) (X ‖ (q^v))) ->
    Rc B -> ax_pre (B ‖ g (c ? p)) (B ‖ g (c ? q))

(** *** Rewriting a summand's continuation, in an arbitrary context

    [ax_choice_input] is what replaces VCCS's [ax_choice_stable], which is
    unsound here ([VACCS_ChoiceProbes.v]).  The guard is preserved, so the
    sum's ready set is untouched and no new commitment becomes available;
    that is exactly the condition the counterexample violates. *)

| ax_choice_input_ctx : forall (Rc : proc -> Prop) (c : ChannelData) (P Q B : proc)
                               (G : gproc),
    (forall X, Rc X -> forall z, ~ lts X τ z) ->
    (forall X, Rc X -> forall a z, ~ lts X (ActExt (ActIn a)) z) ->
    (forall X, Rc X -> forall mu X', lts X (ActExt mu) X' -> Rc X') ->
    (forall X, Rc X -> forall v, ax_pre (X ‖ (P^v)) (X ‖ (Q^v))) ->
    Rc B -> ax_pre (B ‖ g ((c ? P) + G)) (B ‖ g ((c ? Q) + G))
| ax_choice_tau : forall (p p' : proc) (gq : gproc),
    ax_pre p p' -> ax_pre (g ((𝛕 • p) + gq)) (g ((𝛕 • p') + gq))

(** *** Internal computation, and the greatest lower bound

    [⊕] is not primitive in this syntax; it is [𝛕•X + 𝛕•Y].  What projects
    out of it is not a law about sums at all but the general **τ-step**
    rule: a server's own internal move only ever decreases it, since
    [must]'s [pt] field hands the obligation straight to every
    τ-successor.  [ax_int_l] is its guarded-sum instance and is derived
    below; [ax_int_glb] builds into an internal choice — both directions
    are needed — and [ax_int_r] follows by commutativity of [+].

    Stating it at the level of transitions rather than of guarded sums is
    what makes it usable on a **message beside a sum**, [(c!v•𝟘) ‖ g M],
    whose delivery τ is not the transition of any [gproc] — the shape the
    normal form [Ѵⁿ (msgs l ‖ g M)] actually produces.  For a [Static]
    process the premise quantifies over a finite, computable set of
    reducts, so nothing infinitary is smuggled in. *)

| ax_tau_step : forall p p', lts p τ p' -> ax_pre p p'
| ax_int_glb_ctx : forall (Rc : proc -> Prop) (p q1 q2 B : proc),
    (forall X, Rc X -> forall z, ~ lts X τ z) ->
    (forall X, Rc X -> forall a z, ~ lts X (ActExt (ActIn a)) z) ->
    (forall X, Rc X -> forall mu X', lts X (ActExt mu) X' -> Rc X') ->
    (forall X, Rc X -> ax_pre (X ‖ p) (X ‖ q1)) ->
    (forall X, Rc X -> ax_pre (X ‖ p) (X ‖ q2)) ->
    Rc B -> ax_pre (B ‖ p) (B ‖ g ((𝛕 • q1) + (𝛕 • q2)))

(** *** Managing [𝛕]-summands

    A *mixed* sum — external guards beside a [𝛕] — is its own thing,
    neither an internal choice nor reducible to one.  [ax_tau_sep]
    separates it; [ax_tau_flatten] collapses a [𝛕] whose continuation is
    itself all-[𝛕], and is what makes the normal-form recursion terminate
    ([gAllTau] deliberately excludes [𝟘], since [X + 𝛕•𝟘] has a [𝛕] into a
    deadlock and [X + 𝟘] does not). *)

| ax_tau_sep_l : forall (X Y : gproc),
    ax_pre (g (X + (𝛕 • (g Y)))) (g ((𝛕 • (g (X + Y))) + (𝛕 • (g Y))))
| ax_tau_sep_r : forall (X Y : gproc),
    ax_pre (g ((𝛕 • (g (X + Y))) + (𝛕 • (g Y)))) (g (X + (𝛕 • (g Y))))
| ax_tau_flatten_l : forall (X Y : gproc),
    gAllTau Y -> ax_pre (g (X + (𝛕 • (g Y)))) (g (X + Y))
| ax_tau_flatten_r : forall (X Y : gproc),
    gAllTau Y -> ax_pre (g (X + Y)) (g (X + (𝛕 • (g Y))))

(** *** Acceptance-family closure

    [ax_convex] is convex closure: reading the internal choice as offering
    the ready sets of [X] and of [(X+Y)+Z], every set in between is on
    offer too.  Union closure needs no rule — it is derivable from
    [ax_tau_sep_l] and [ax_int_l]. *)

| ax_convex : forall (X Y Z : gproc),
    ax_pre (g ((𝛕 • (g X)) + (𝛕 • (g ((X + Y) + Z))))) (g (X + Y))

(** *** Acceptance-tree uniformity

    The only rule that takes a ready set from one branch and a
    continuation from another — two branches pool their continuations at a
    shared action while keeping the first branch's ready set.  VCCS needed
    an output twin; VACCS does not, there being no output guard. *)

| ax_share_in : forall (c : ChannelData) (P Q : proc) (X' Y' : gproc),
    ax_pre (g ((𝛕 • (g ((c ? P) + X'))) + (𝛕 • (g ((c ? Q) + Y')))))
           (g ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + X'))

(** *** [①] is a [𝟘] on the server side

    [must]'s outcome field inspects only the *test*, and [①] has no [lts]
    rule at all.  Without these two, a normal form carrying an [①] summand
    would be stuck: structural congruence drops a [𝟘] summand but says
    nothing about [①]. *)

(** Stated with a residue, for the same reason as [ax_input_distrib_l]
    below: the two rules that rewrite inside a sum preserve the rewritten
    summand's *guard*, and [①]/[𝟘] are not guards.  Taking [R := 𝟘] and
    using [ax_cgr] recovers the bare form [⊢ g ① ≂ g 𝟘]. *)

| ax_success_l : forall R, ax_pre (g (① + R)) (g (𝟘 + R))
| ax_success_r : forall R, ax_pre (g (𝟘 + R)) (g (① + R))

(** *** Prefix distributes over choice — in an arbitrary context

    What makes a guarded-sum normal form *canonical*: one continuation per
    action.  Without it, two same-action summands leave the correspondence
    between the two sides' continuations underdetermined.

    The residue [R] is carried by the rule itself, and it has to be: the
    only rules that rewrite inside a sum are [ax_choice_input] and
    [ax_choice_tau], which preserve the rewritten summand's *guard*, and
    merging two summands into one does not.  VCCS obtains the context
    version from [ax_choice_stable], which is **unsound** here
    ([VACCS_ChoiceProbes.v]) — so this is one of the places where the
    asynchronous system has to state as a rule what the synchronous one
    derives.  Note the merge leaves the sum's guard *set* unchanged, which
    is exactly why it escapes that counterexample.  Taking [R := 𝟘] and
    using [ax_cgr] recovers the context-free form. *)

| ax_input_distrib_l : forall (c : ChannelData) (P Q : proc) (R : gproc),
    ax_pre (g (((c ? P) + (c ? Q)) + R)) (g ((c ? (g ((𝛕 • P) + (𝛕 • Q)))) + R))

(** *** Flattening the static operators

    The expansion law is pure interleaving — no synchronisation term,
    because two guarded sums can never synchronise in VACCS. *)

| ax_expansion_l : forall M N, ax_pre (g M ‖ g N) (g (ext M N + ext_r N M))
| ax_expansion_r : forall M N, ax_pre (g (ext M N + ext_r N M)) (g M ‖ g N)
| ax_res_normalize_l : forall M, ax_pre (ν (g M)) (g (resg M))
| ax_res_normalize_r : forall M, ax_pre (g (resg M)) (ν (g M))

(** *** Absorbing an input — the one genuinely asynchronous rule family

    A guard whose continuation is *bad* relative to the guard's own
    channel may be removed from a sum.  [Bad] ([VACCS_Absorb.v]) is a
    judgement, not a preorder, and it has to be: the semantic condition
    quantifies over a strict subclass of clients (τ-stuck, not good, and
    refusing the channel), which no [⊑ₘᵤₛₜᵢ] against a fixed process can
    express — three candidates were tried and all three fail.

    The premise used to be [Harmless].  [Bad] is stronger where it
    matters here: it needs only **one** bad [τ]-branch where [Harmless]
    demands all of them, and — since [bad_stuck] was corrected — only
    **one** bad residue per channel where [Harmless] demands every
    sibling.  Every [Harmless] instance the derivations actually used
    ([hm_nil], [hm_out]) has a one-line [Bad] counterpart
    ([bad_nil_any], [bad_msg]), so nothing was lost.

    Stated carefully, though, the two are **not** ordered: [Harmless] has
    a compositional clause for [‖] ([hm_par]) that [Bad] has no
    counterpart for.  [Bad] is phrased over the LTS, so it *applies* to a
    parallel term, but proving [Bad S (p ‖ q)] from [Bad S p] and
    [Bad S q] is not immediate — the synchronising case needs the
    emitting side's residue to stay bad, which [bad_stuck] says nothing
    about, whereas [Harmless] has exactly that preservation lemma
    ([hm_out_step]).  On the [Static] fragment it should go through by
    induction on termination; **not proved**.  In this development the
    question is moot: [hm_par] is used only inside [Harmless]'s own
    preservation lemmas, never in a derivation.

    This **one** rule replaces three: the copycat law, the responder law
    and the plain swallow law are all instances, derived below.  It is also
    strictly stronger than the three together — it covers
    [c ? (d ? (c ! V • 𝟘)) ⊑ 𝟘], which none of them reached, and it gives
    the responder at an *arbitrary* channel where the old [ax_resp] needed
    a constant one. *)

| ax_input_drop : forall (c : ChannelData) (P : proc) (G : gproc),
    (forall v : ValueData, Bad (fun d => d = c) (subst_in_proc 0 v P)) ->
    ax_pre (g ((c ? P) + G)) (g G)

(** The converse direction — a copycat may be *introduced* — is a separate
    rule, and [Harmless] says nothing about it.  Stated for a whole **sum**
    of copycat guards, not just one: guarded choice commits, so such a sum
    can absorb on one channel and lose the others, and it is still
    invisible because every branch is a no-op
    ([must_i_nil_below_copycats], [VACCS_Copycat.v]).

    The generality is what makes the multi-channel mirror reachable in one
    step: [ax_par] with this rule, then [ax_expansion_l], produces one
    mirror summand per channel at once. *)

| ax_ccat_r : forall M, gCopycats M -> ax_pre (g 𝟘) (g M)

(** *** Joint removal: restricting a stable sum's channel set

    The counterexample of [VACCS_DropProbes.v] shows why no rule can
    remove surplus guards *one at a time*: there, [b ? 𝟘] is removable on
    its own and [a ? PP] is not, yet it is the [b]-guard that kills every
    client, so removing the easy one first destroys the fact that
    justified removing them at all.  Guards have to go **jointly**.

    [VACCS_Absorb.must_i_restrict] is the semantically right move, but
    its premise quantifies over all clients and is the very inequation
    completeness is trying to derive — so it could not be a rule.
    [VACCS_Absorb.BadK] is that premise made **checkable**: a derivation
    of [BadK ∅ (offers M') (g M)] certifies "every τ-stuck, non-good
    client that emits on none of [M']'s channels is failed by [g M]",
    which is exactly what licenses throwing the surplus away.

    The other two premises are syntactic: [M'] is a sub-sum of [M] at the
    level of transitions, and [M] is stable. *)

(** *** The acceptance-set side: a settling SIMULATION

    [ax_restrict]'s premise is a [BadK] derivation — a *client-side*
    judgement, and the development records at length why that is the
    harder object: what the semantics hands over is an **∃ over internal
    runs** ("some run settles inside the buffer's channels"), not a ∀ over
    clients, and the two do not coincide
    ([VACCS_DropProbes.no_Bad_target]).  This rule takes the premise in
    the form the semantics produces.

    It is stated at its full generality — **any** [SettleSim] between two
    forwarder states with *possibly different* buffers — because that is
    the shape [VACCS_Cond2.settle_sim_below_bag] proves sound, and because
    the buffers are exactly what a configuration comparison must be
    allowed to differ in ([VACCS_Bad.unstable_delivery_below_nil] and
    [VACCS_DropProbes.msg_below_tau_msg] both exhibit true inequations
    between configurations whose bags do not agree).

    Nothing circular is smuggled in.  [SettleSim] is a *simulation*:
    sound for [≼ₐₛ] but not complete for it, so the premise is strictly
    stronger than the conclusion — unlike [bhv_pre_cond2], which on the
    [Static] fragment *is* [⊑ₘᵤₛₜᵢ] and would make the rule vacuous.  And
    the premise is an LTS-level object, like [Settles], [BadK] and
    [Harmless] before it.

    The earlier [ax_restrict_settle] is its instance at the **rigid**
    relation [VACCS_Cond2.restrict_rel] with both buffers empty, and is
    derived below — so the rule count is unchanged. *)

| ax_settle_sim : forall (l l' : list TypeOfActions) (p q : proc)
    (R : (proc * MO (ExtAct TypeOfActions)) ->
         (proc * MO (ExtAct TypeOfActions)) -> Prop),
    Static p -> Static q -> SettleSim R ->
    R (p ▷ bag l) (q ▷ bag l') ->
    ax_pre (msgs l ‖ p) (msgs l' ‖ q)

| ax_restrict : forall (M M' : gproc),
    (forall al q, lts (g M') al q -> lts (g M) al q) ->
    (forall p, ~ lts (g M) τ p) ->
    BadK (fun _ => False) (offers M') (g M) ->
    ax_pre (g M) (g M')

(** An **unstable right-hand side**, taken apart without separating it.

    The τ-laws ([ax_tau_sep_*], [ax_tau_flatten_*]) require a
    τ-continuation to be a guarded sum, which a VACCS normal form's
    continuations are not — they are configurations.  This rule needs no
    such shape: it reads [must]'s own structure, so its premises are
    exactly the [pt] and [com] fields at [q], and both are at **strictly
    smaller** right-hand sides ([Static_lts_decrease]), which is what
    makes it a genuine recursion rather than a restatement of the goal.

    The input premise is the asynchronous one: not "[p] offers the
    channel" — it need not, [c ? 𝟘 ⊑ₘᵤₛₜᵢ 𝟘] — but "[p] holding the
    message is above the reduct".  Sound by
    [VACCS_Precongruence.must_i_glb_tau]. *)

| ax_glb_tau : forall (p q : proc),
    (exists q0, lts q τ q0) ->
    (forall q', lts q τ q' -> ax_pre p q') ->
    (forall c v q'', lts q (ActExt (ActIn (c,v))) q'' ->
       ax_pre ((c ! v • 𝟘) ‖ p) q'') ->
    (forall c v q'', lts q (ActExt (ActOut (c,v))) q'' ->
       exists p'', lts p (ActExt (ActOut (c,v))) p'') ->
    (forall c v p'' q'', lts p (ActExt (ActOut (c,v))) p'' ->
       lts q (ActExt (ActOut (c,v))) q'' -> ax_pre p'' q'') ->
    ax_pre p q

(** *** τ makes you safe — the complement of [ax_restrict]

    Every field of [must] except [ex] is *contravariant* in the process's
    transitions ([pt] and [com] are obligations, so having fewer of them
    can only help), and [ex] is the one field that needs a transition to
    exist.  So a process with a subset of another's transitions is above
    it as soon as it can move **internally**, whatever the discarded
    branches were doing.

    This is the exact complement of [ax_restrict], which covers the case
    where the smaller sum is **stable** and pays for it with a [BadK]
    certificate.  Here the smaller side has a [τ] and the premise is
    *purely syntactic* — nothing at all is asked of the discarded
    branches, which puts the rule outside the reach of
    [Harmless]/[Bad]/[BadK], all of which constrain them.

    Sound by [VACCS_Precongruence.must_i_sub_tau]. *)

| ax_sub_tau : forall (p q : proc),
    (forall al z, lts q al z -> lts p al z) ->
    (exists z, lts q τ z) ->
    ax_pre p q

(** *** The same, with the emissions matched only WEAKLY

    [ax_glb_tau]'s output premise asks [p] to emit [(c,v)] **itself**, and
    that is *not* a consequence of [p ⊑ₘᵤₛₜᵢ q]
    ([VACCS_Matching.glb_output_premise_not_semantic]: a server [τ] only
    ever weakens, so [g (𝛕 • (c!v•𝟘))] sits below [c!v•𝟘] while offering
    no emission at all).  What *is* a consequence is the weak form,
    [VACCS_Matching.weak_out_of_below].

    The price is that weak residues cannot be compared one by one — the
    semantics constrains them only *collectively*
    ([VACCS_Matching.residues_below_d]) — so the left-hand side of the
    output premise is the **internal choice** of the residues at that
    channel and value, [VACCS_Residues.res_list_v] enumerating them.  Both
    it and the non-emptiness side condition are computable, so the rule
    carries no semantic premise.

    Both output premises are exactly what the preorder supplies:
    [VACCS_Matching.res_list_v_nonempty] for the first,
    [VACCS_Matching.ichoice_residues_below] for the second — at **every**
    value, the probe [VACCS_Matching.TCatchD] being value-selective at an
    arbitrary [ValueData].

    Sound by [VACCS_Residues.must_i_glb_res]. *)

| ax_glb_weak : forall (p q : proc) (n : nat),
    (exists q0, lts q τ q0) ->
    (forall q', lts q τ q' -> ax_pre p q') ->
    (forall c v q'', lts q (ActExt (ActIn (c,v))) q'' ->
       ax_pre ((c ! v • 𝟘) ‖ p) q'') ->
    (forall c v q'', lts q (ActExt (ActOut (c,v))) q'' ->
       res_list_v n c v p <> nil) ->
    (forall c v q'', lts q (ActExt (ActOut (c,v))) q'' ->
       ax_pre (g (ichoice (res_list_v n c v p))) q'') ->
    ax_pre p q

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
    ax_pre (g ((𝛕 • (((c ! v • 𝟘) : proc) ‖ X))
             + (𝛕 • (((c ! v • 𝟘) : proc) ‖ Y))))
           (((c ! v • 𝟘) : proc) ‖ ((g ((𝛕 • X) + (𝛕 • Y))) : proc))
.

Notation "⊢ p ≂ q" := (ax_pre p q /\ ax_pre q p) (at level 70).

(** ** Derived rules

    Each is admissible from the twenty-nine above; they are recorded here
    rather than as constructors so that the rule set stays minimal. *)

Lemma ax_refl : forall p, ax_pre p p.
Proof. intros p. apply ax_cgr. apply cgr_refl. Qed.

Lemma ax_cgr_sym : forall p q, p ≡* q -> ax_pre q p.
Proof. intros p q H. apply ax_cgr. apply cgr_symm. exact H. Qed.

(** The bare omega rules: the context of [ax_input_ctx] /
    [ax_choice_input_ctx] is [𝟘], which is inert for the trivial reason
    that it has no transitions at all — so the closure hypothesis is
    vacuous. *)

Lemma ax_nil_par : forall p, p ≡* ((g 𝟘 : proc) ‖ p).
Proof. intro p. etransitivity; [ apply cgr_par_nil_rev | apply cgr_par_com ]. Qed.

(** The restriction of a stable sum to a transition-sub-sum, certified by
    a [Settles] statement at every reachable buffer — the previous
    primitive, now an instance of [ax_settle_sim] at the rigid relation
    [VACCS_Cond2.restrict_rel] with both bags empty ([msgs [] = g 𝟘], and
    [bag [] = ∅]).  This is what Phase A of the matching argument
    discharges ([VACCS_Matching.restrict_bigsum]). *)

Lemma ax_restrict_settle : forall (M M' : gproc),
  (forall al q, lts (g M') al q -> lts (g M) al q) ->
  gStatic M -> gStatic M' ->
  (forall m, OutOnly m -> ((g M') ▷ m) ↛ ->
     Settles (emits ((g M') ▷ m)) ((g M) ▷ m)) ->
  ax_pre (g M) (g M').
Proof.
  intros M M' Hsub HM HM' Hcert.
  eapply ax_trans; [ apply ax_cgr; apply ax_nil_par | ].
  eapply ax_trans; [ | apply ax_cgr_sym; apply ax_nil_par ].
  apply (ax_settle_sim [] [] (g M) (g M') (restrict_rel M M')
           (static_g M HM) (static_g M' HM')).
  - apply restrict_settle_sim_out; assumption.
  - right. exists (∅ : MO (ExtAct TypeOfActions)).
    split; [ apply OutOnly_empty | split; reflexivity ].
Qed.

Lemma ax_input : forall (c : ChannelData) (p q : proc),
  (forall v, ax_pre (p^v) (q^v)) -> ax_pre (g (c ? p)) (g (c ? q)).
Proof.
  intros c p q H.
  eapply ax_trans; [ apply ax_cgr; apply ax_nil_par | ].
  eapply ax_trans; [ | apply ax_cgr_sym; apply ax_nil_par ].
  apply (ax_input_ctx (fun X => X = (g 𝟘 : proc)) c p q (g 𝟘));
    [ intros X HX z Hz; subst; inversion Hz
    | intros X HX a z Hz; subst; inversion Hz
    | intros X HX mu X' Hz; subst; inversion Hz
    | intros X HX v; subst; apply ax_par; [ apply ax_refl | apply H ]
    | reflexivity ].
Qed.

Lemma ax_int_glb : forall (p q1 q2 : proc),
  ax_pre p q1 -> ax_pre p q2 -> ax_pre p (g ((𝛕 • q1) + (𝛕 • q2))).
Proof.
  intros p q1 q2 H1 H2.
  eapply ax_trans; [ apply ax_cgr; apply ax_nil_par | ].
  eapply ax_trans; [ | apply ax_cgr_sym; apply ax_nil_par ].
  apply (ax_int_glb_ctx (fun X => X = (g 𝟘 : proc)) p q1 q2 (g 𝟘));
    [ intros X HX z Hz; subst; inversion Hz
    | intros X HX a z Hz; subst; inversion Hz
    | intros X HX mu X' Hz; subst; inversion Hz
    | intros X HX; subst; apply ax_par; [ apply ax_refl | exact H1 ]
    | intros X HX; subst; apply ax_par; [ apply ax_refl | exact H2 ]
    | reflexivity ].
Qed.

Lemma ax_choice_input : forall (c : ChannelData) (P Q : proc) (G : gproc),
  (forall v, ax_pre (P^v) (Q^v)) -> ax_pre (g ((c ? P) + G)) (g ((c ? Q) + G)).
Proof.
  intros c P Q G H.
  eapply ax_trans; [ apply ax_cgr; apply ax_nil_par | ].
  eapply ax_trans; [ | apply ax_cgr_sym; apply ax_nil_par ].
  apply (ax_choice_input_ctx (fun X => X = (g 𝟘 : proc)) c P Q (g 𝟘) G);
    [ intros X HX z Hz; subst; inversion Hz
    | intros X HX a z Hz; subst; inversion Hz
    | intros X HX mu X' Hz; subst; inversion Hz
    | intros X HX v; subst; apply ax_par; [ apply ax_refl | apply H ]
    | reflexivity ].
Qed.

(** The guarded-sum instance of [ax_tau_step]: an internal choice is
    below each of its branches. *)
Lemma ax_int_l : forall p q, ax_pre (g ((𝛕 • p) + (𝛕 • q))) p.
Proof. intros p q. apply ax_tau_step. apply lts_choiceL. apply lts_tau. Qed.

Lemma ax_int_r : forall p q, ax_pre (g ((𝛕 • p) + (𝛕 • q))) q.
Proof.
  intros p q. eapply ax_trans; [ | apply (ax_int_l q p) ].
  apply ax_cgr. apply cgr_choice_com.
Qed.

(** A [𝛕] prefix on its own: the context of [ax_choice_tau] is [𝟘], and
    [≡*] removes it on both sides. *)
Lemma ax_tau : forall p p', ax_pre p p' -> ax_pre (g (𝛕 • p)) (g (𝛕 • p')).
Proof.
  intros p p' H.
  eapply ax_trans; [ apply ax_cgr_sym; apply cgr_choice_nil | ].
  eapply ax_trans; [ apply (ax_choice_tau p p' 𝟘); exact H | ].
  apply ax_cgr. apply cgr_choice_nil.
Qed.

(** [Eval_Eq 0 E] is never [None] ([VACCS_Precongruence.Eval_Eq_0_not_none]),
    so a conditional is always structurally congruent to one of its
    branches and needs no rule of its own. *)
Lemma ax_if : forall E p p' q q', ax_pre p p' -> ax_pre q q' ->
  ax_pre (If E Then p Else q) (If E Then p' Else q').
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

(** ** The three laws [ax_input_drop] replaces

    The copycat, the responder and the plain swallow are now instances.
    Note [ax_resp] is obtained here at a *constant* channel only because
    its statement mentions [ccat (cst a)]; the underlying fact
    [⊢ resp a V ⊑ g 𝟘] holds at any channel. *)

Lemma ax_ccat_l : forall c, ax_pre (ccat c) (g 𝟘).
Proof.
  intro c. unfold ccat.
  eapply ax_trans; [ apply ax_cgr; apply cgr_choice_nil_rev | ].
  apply ax_input_drop. intro v. simpl. apply bad_msg. reflexivity.
Qed.

Lemma ax_resp : forall (a : Channel) (V : ValueData),
  ax_pre (resp a V) (ccat (cst a)).
Proof.
  intros a V. eapply ax_trans; [ | apply ax_ccat_r; reflexivity ].
  unfold resp.
  eapply ax_trans; [ apply ax_cgr; apply cgr_choice_nil_rev | ].
  apply ax_input_drop. intro v. simpl. apply bad_msg. reflexivity.
Qed.

Lemma ax_swallow : forall (c : ChannelData) (G : gproc),
  ax_pre (g ((c ? (g 𝟘)) + G)) (g G).
Proof.
  intros c G. apply ax_input_drop. intro v. simpl. apply bad_nil_any.
Qed.

(** …et LA forme générale, qui les subsume : une garde se laisse tomber
    dès que sa continuation n'émet que sur **sa propre voie**.

    - [ochans P = []] — le puits, à profondeur libre ([ax_swallow] en est
      le cas [P := 𝟘], et une chaîne de gardes-puits tombe d'un coup) ;
    - [ochans P ⊆ {c}] — le **copycat** et le **répondeur**.

    Le critère est purement syntaxique et [ochans_subst] le rend
    indépendant de la valeur reçue, ce qui est exactement la forme que la
    règle oméga consomme. *)

Lemma ax_drop_ochans : forall (c : ChannelData) (P : proc) (G : gproc),
  Static P -> (forall d, In d (ochans P) -> d = c) ->
  ax_pre (g ((c ? P) + G)) (g G).
Proof.
  intros c P G HSt Hsub. apply ax_input_drop. intro v.
  apply ochans_sub_Bad.
  - apply Static_subst. exact HSt.
  - intros d Hd. rewrite ochans_subst in Hd. apply Hsub. exact Hd.
Qed.

Corollary ax_drop_no_output : forall (c : ChannelData) (P : proc) (G : gproc),
  Static P -> ochans P = [] -> ax_pre (g ((c ? P) + G)) (g G).
Proof.
  intros c P G HSt Hoc. apply ax_drop_ochans; [ exact HSt | ].
  intros d Hd. rewrite Hoc in Hd. contradiction.
Qed.

Example ax_drop_nested_sink : forall (c d : ChannelData) (G : gproc),
  ax_pre (g ((c ? ((g (d ? ((g 𝟘) : proc))) : proc)) + G)) (g G).
Proof.
  intros c d G. apply ax_drop_no_output.
  - repeat constructor.
  - reflexivity.
Qed.

(** Le copycat, retrouvé comme instance du critère général : sa
    continuation [c ! bvar₀ • 𝟘] a pour empreinte d'émission [[c]]. *)

Example ax_drop_copycat : forall (c : ChannelData) (G : gproc),
  ax_pre (g ((c ? (((c ! (bvar 0) • 𝟘)) : proc)) + G)) (g G).
Proof.
  intros c G. apply ax_drop_ochans.
  - repeat constructor.
  - intros d Hd. simpl in Hd. destruct Hd as [Hd|[]]. symmetry. exact Hd.
Qed.

(** And the drop whose premise says **nothing** about the discarded
    continuation: an input guard sitting beside a [𝛕]-summand may always
    be removed, because the sum's own [τ] already discharges [ex] and
    every other field is contravariant.  [ax_input_drop] cannot do this —
    its premise constrains the continuation — so the two are genuinely
    complementary. *)

Lemma ax_drop_tau : forall (c : ChannelData) (P : proc) (G : gproc),
  (exists z, lts ((g G) : proc) τ z) ->
  ax_pre ((g ((c ? P) + G)) : proc) ((g G) : proc).
Proof.
  intros c P G Htau. apply ax_sub_tau; [ | exact Htau ].
  intros al z Hz. apply lts_choiceR. exact Hz.
Qed.

(** ** Dropping *up to* a rewrite — why the premise need not be complete

    [Bad] is an inductive judgement, so it cannot be complete for the
    semantic condition it approximates (the ∀∃ alternation is recorded in
    `VACCS_Bad.v`).  This costs nothing, because the derivation may
    **rewrite the guard's continuation first**: [ax_choice_input] installs
    any [⊢]-smaller continuation, and [ax_int_l]/[ax_int_r] project an
    internal choice onto either branch.  So a continuation only has to be
    bad *after projection*.

    [ax_input_drop_upto] is that combination.  The two projection
    instances no longer need it: [Bad]'s [bad_step] clause takes a single
    [τ]-branch, so an internal choice with one bad branch is bad outright
    — which is exactly what [Harmless]'s [hm_choice] could not say. *)

Lemma ax_input_drop_upto :
  forall (c : ChannelData) (P Q : proc) (G : gproc),
  (forall v : ValueData, ax_pre (subst_in_proc 0 v P) (subst_in_proc 0 v Q)) ->
  (forall v : ValueData, Bad (fun d => d = c) (subst_in_proc 0 v Q)) ->
  ax_pre (g ((c ? P) + G)) (g G).
Proof.
  intros c P Q G Hpq HQ.
  eapply ax_trans; [ apply ax_choice_input with (Q := Q); exact Hpq | ].
  apply ax_input_drop. exact HQ.
Qed.

Lemma ax_input_drop_int_l :
  forall (c : ChannelData) (A B : proc) (G : gproc),
  (forall v : ValueData, Bad (fun d => d = c) (subst_in_proc 0 v A)) ->
  ax_pre (g ((c ? (g ((𝛕 • A) + (𝛕 • B)))) + G)) (g G).
Proof.
  intros c A B G HA. apply ax_input_drop. intro v. simpl.
  eapply bad_step; [ apply lts_choiceL; apply lts_tau | apply HA ].
Qed.

Lemma ax_input_drop_int_r :
  forall (c : ChannelData) (A B : proc) (G : gproc),
  (forall v : ValueData, Bad (fun d => d = c) (subst_in_proc 0 v B)) ->
  ax_pre (g ((c ? (g ((𝛕 • A) + (𝛕 • B)))) + G)) (g G).
Proof.
  intros c A B G HB. apply ax_input_drop. intro v. simpl.
  eapply bad_step; [ apply lts_choiceR; apply lts_tau | apply HB ].
Qed.

End VACCS_DefinitionAxiomatic.
