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

(** * A Hennessy-Ingólfsdóttir-style inequational proof system for [⊑ₘᵤₛₜᵢ] on VCCS

    [ax_pre] is the syntactic counterpart of [⊑ₘᵤₛₜᵢ]: a preorder built
    from structural congruence, one precongruence rule per operator, and
    the internal-choice/merge inequations, in the style of Hennessy &
    Ingólfsdóttir's proof system for the must-testing preorder ("A Theory
    of Communicating Processes with Value-Passing", ICALP'90 / Information
    and Computation 107(2), 1993, §4).

    This system is intended only for the [Static] (recursion-free)
    fragment of VCCS ([VCCS_Static.v]) — there is no [Ω]/divergence axiom,
    since [Static] processes never diverge. Soundness ([SoundnessAx.v])
    is stated with explicit [Static] side conditions rather than baking
    them into the constructors themselves,
    mirroring how [Static]-ness composes structurally (if [Static (p‖q)]
    then [Static p] and [Static q] individually, etc.) and keeping this
    file's constructors syntactically identical to Hennessy's own rules. *)

From TestingTheory Require Import VCCS VCCS_Instance Must VCCS_Static VCCS_Expansion
  VCCS_ResNormalize VCCS_ReadySet.

Section DefinitionAxiomatic.

Context `{VP : VCCS_Parameters}.

Reserved Notation "⊢ p ⊑ q" (at level 70).

(** ** The proof-system relation

    - [ax_refl]/[ax_trans]: [⊢_] is a preorder by construction.
    - [ax_cgr]: every structural-congruence law ([Congruence.v]'s
      [cgr_step] — commutativity/associativity of [‖]/[+], unit laws,
      scope extrusion, [If]-reduction, [rec]-unfolding, …) is usable in
      *both* directions for free, since [≡*] is itself an equivalence.
      Carries an explicit [Static q] side condition — unlike every other
      rule here, [≡*] can otherwise relate a [Static] process to a
      *non*-[Static] one (e.g. [cgr_if_true_rev_step] lets [p ≡ (If E
      Then p Else garbage)] for a totally unconstrained, possibly
      recursive [garbage], regardless of [Eval_Eq]'s truth value) — the
      side condition is what makes [Static]-ness an invariant of every
      [⊢]-derivation ([SoundnessAx.v]'s [ax_pre_static_preserved]),
      which [ax_trans] needs to recover its middle term's [Static]-ness
      from nothing but the endpoints. [must_i_cgr] itself needs no such
      condition (structural congruence implies must-*equivalence*
      unconditionally) — the condition here is purely to keep [Static]
      invariant across the whole derivation, not because this specific
      rule would be unsound without it.
    - [ax_par]/[ax_res]/[ax_if]/[ax_input]/[ax_output]/[ax_tau]: one
      precongruence rule per operator, mirroring the lemmas proved in
      [VCCS_Precongruence.v]. Every one of these is sound.
    - [ax_int_l]/[ax_int_r]: [X⊕Y ⊑ X] (resp. [Y]), where [⊕] is
      definable as [𝛕•X + 𝛕•Y] — sound for free via [must]'s own [pt]
      field ([must_i_int_choice_l]/[_r]).
    - [ax_output_merge_l]/[_r], [ax_input_merge_l]/[_r]: Hennessy's
      merge equations (both directions), sound via
      [must_i_output_merge_l]/[_r] and [must_i_input_merge_l]/[_r].
    - [ax_expansion_l]/[_r]: Hennessy's expansion law (both directions)
      for two guarded sums [M]/[N] combined by [‖] — like the merge
      equations, this is a genuine *primitive* axiom of the system (not
      derivable from the other rules), matching how Hennessy's own
      axiomatization treats it. Sound via [VCCS_Expansion.v]'s
      [must_i_expansion_l]/[_r]. Carries explicit [gStatic M]/
      [gStatic N] side conditions — unlike [must_i_expansion_l]/[_r]
      themselves (true unconditionally), these conditions are here
      purely so [SoundnessAx.v]'s [Static]-invariant lemma can conclude
      [Static] of *either* side directly from the (already available)
      hypotheses, without needing a hard structural "reverse" fact
      recovering [gStatic M]/[gStatic N] from [gStatic] of the
      recursively-built [ext]/[ext_r]/[int] expression itself.
    - [ax_input_distrib_l]/[_r], [ax_output_distrib_l]/[_r]: prefix
      distributes over guarded choice, [a.P + a.Q ≂ a.(P ⊕ Q)] (same
      action on both summands — same channel for inputs, same channel
      *and* value for outputs). Sound via [VCCS_Precongruence.v]'s
      [must_i_input_distrib_l]/[_r] and [must_i_output_distrib_l]/[_r].
      These need no [Static] side conditions: both directions recover
      each component's [Static]-ness structurally from the other side's
      (unlike [ax_expansion_*]/[ax_res_normalize_*], whose right-hand
      sides are built by recursive *functions* over the syntax).

      This is the law that makes a guarded-sum normal form
      **canonical**, i.e. with a *unique continuation per action*, and
      it is exactly what [CompletenessAx.v]'s completeness argument
      needs to get started. Without it, two same-action summands
      ([c?P₁ + c?P₂]) leave the correspondence between the two compared
      processes' continuations underdetermined: [⊑ₘᵤₛₜᵢ] only ever
      supplies an *existential* fact ("for each configuration the
      right-hand side can settle into, *some* matching configuration of
      the left-hand side exists"), never a fixed pairing saying which
      continuation matches which — and an [ax_pre] derivation has to be
      built from a definite pairing. Collapsing same-action summands
      into a single prefix removes the choice entirely. Hennessy's
      acceptance-tree normal forms have the same shape for the same
      reason: their canonical form [⊕ᵢ Σ_{a ∈ Aᵢ} a.p(a)] takes [p(a)]
      to be a function of the *action alone*, which is precisely the
      "unique continuation per action" property.
    - [ax_res_normalize_l]/[_r]: eliminates a [ν] wrapping a guarded sum
      [M] down to a guarded sum [resg M] with no [ν] left at the top —
      needed because no existing [≡*] rule distributes [ν] over an
      arbitrary [+] (only over [‖], via [cgr_res_scope_step]). Sound via
      [VCCS_ResNormalize.v]'s [must_i_res_normalize_l]/[_r]. Carries an
      explicit [gStatic M] side condition for the same reason as
      [ax_expansion_l]/[_r] above. Together with [ax_expansion_l]/[_r],
      this is exactly what [VCCS_NormalForm.v]'s normal-form theorem
      needs to push any [Static] process down to a single guarded sum.

    - [ax_choice_stable]: guarded-choice congruence, **restricted to
      [gStable] summands on both sides**. Sound via
      [VCCS_ReadySet.v]'s [must_i_choice_stable_compat]. This is what
      makes it possible to rewrite a *sub-summand* of a larger sum at
      all — needed by [VCCS_NormalForm.v]'s canonical-form
      construction, which has to apply the distributivity laws above
      underneath a [_ + R] context (bring the two same-action summands
      adjacent and to the front with [ax_cgr], then rewrite them in
      place with this rule). Read the [ax_choice] discussion below
      first: the *unrestricted* version of this rule is genuinely
      unsound, and the [gStable] hypotheses are exactly what rules the
      counterexample out — it works by replacing a stable summand with
      an *unstable* one so that a fresh [𝛕] can pre-empt the sibling
      branch. Requiring both sides stable makes that impossible, and
      that restriction turns out to be strong enough for the whole
      acceptance-set argument to go through. Note the rule needs no
      [gStatic]/[Static] side condition: [SoundnessAx.v]'s
      [ax_pre_static_preserved] recovers [gStatic gp'] from its own
      induction hypothesis on the premise [⊢ g gp ⊑ g gp'].

    **Deliberately no general "[ax_choice]" congruence rule** of the
    shape [⊢ g gp ⊑ g gp' -> ⊢ g gq ⊑ g gq' -> ⊢ g(gp+gq) ⊑ g(gp'+gq')].
    This was in an earlier draft of this file (mirroring [ax_par]'s
    shape) but is *unsound*, not merely hard to prove — this is the
    resolution of what session 3's plan notes called "a genuine
    semantic obstacle" for guarded-choice precongruence: it wasn't a
    stuck proof, the statement itself is false. Counterexample: take
    [gp = c!5•𝟘], [gp' = 𝛕•(g(c!5•𝟘))] (must-*equivalent* standalone —
    a lone [𝛕] never changes anything when there is nothing to
    preempt), and [gq = gq' = d!7•𝟘] (literally identical, for channel
    [d ≠ c]). Then [g gp ⊑ g gp'] and [g gq ⊑ g gq'] both hold trivially,
    but [g(gp+gq) ⊑ g(gp'+gq')] does *not*: test with
    [t = d?SUCCESS] (only ever offers to receive on [d]). [g(gp+gq)] is
    stable (neither branch has a [𝛕]) and syncs with [t] via [gq]
    directly — it must-passes. [g(gp'+gq')] is *not* stable (gp''s own
    [𝛕] is unconditionally available) — [must]'s [pt] field then forces
    the reduct after that [𝛕] (which is [g(c!5•𝟘)] *alone*, [gq] having
    been discarded — guarded choice always commits to one summand only,
    permanently) to must-pass [t] too, and it can't ([c] and [d] never
    synchronise). So [g(gp+gq)] must-passes [t] while [g(gp'+gq')]
    doesn't: the inequation fails in exactly the direction the rule
    would have asserted. This is the well-known "[𝛕] is not transparent
    under choice" phenomenon (Milner's third [𝛕]-law, [P + 𝛕.P = 𝛕.P],
    is valid; ["𝛕.P + Q = P + Q"] is not, in *any* standard process
    equivalence, precisely because the [𝛕] can pre-empt [Q]) — not a
    defect specific to this development. Rewriting *inside* one summand
    of a [+] is only safe when done through a rule that cannot change
    which summand is *initially stable* — exactly what [ax_input]/
    [ax_output]/[ax_tau] already guarantee (they change a prefix's
    continuation, never its guard's own stability), and exactly what
    [ax_choice_stable] above enforces *explicitly*, by demanding
    [gStable] of both the replaced and the replacing summand. So the
    diagnosis "the general rule is false" and the rule
    [ax_choice_stable] are two halves of one statement: sum-congruence
    is available precisely when it cannot disturb initial stability. *)

Inductive ax_pre : proc -> proc -> Prop :=
| ax_refl : forall p, ⊢ p ⊑ p
| ax_trans : forall p q r, ⊢ p ⊑ q -> ⊢ q ⊑ r -> ⊢ p ⊑ r
| ax_cgr : forall p q, Static q -> p ≡* q -> ⊢ p ⊑ q

| ax_par : forall p p' q q', ⊢ p ⊑ p' -> ⊢ q ⊑ q' -> ⊢ (p ‖ q) ⊑ (p' ‖ q')
| ax_res : forall p q, ⊢ p ⊑ q -> ⊢ (ν p) ⊑ (ν q)
| ax_if : forall E p p' q q', ⊢ p ⊑ p' -> ⊢ q ⊑ q' ->
    ⊢ (If E Then p Else q) ⊑ (If E Then p' Else q')
| ax_input : forall (c : ChannelData) (p q : proc),
    (forall v, ⊢ p^v ⊑ q^v) -> ⊢ g (c ? p) ⊑ g (c ? q)
| ax_output : forall (c : ChannelData) (v : ValueData) (p q : proc),
    ⊢ p ⊑ q -> ⊢ g (c ! v • p) ⊑ g (c ! v • q)
| ax_tau : forall p q, ⊢ p ⊑ q -> ⊢ g (𝛕 • p) ⊑ g (𝛕 • q)

| ax_int_l : forall p q, ⊢ g ((𝛕 • p) + (𝛕 • q)) ⊑ p
| ax_int_r : forall p q, ⊢ g ((𝛕 • p) + (𝛕 • q)) ⊑ q

| ax_output_merge_l : forall (c : ChannelData) (v v' : ValueData) (P Q : proc),
    ⊢ g ((c ! v • P) + (c ! v' • Q)) ⊑ g ((𝛕 • (g (c ! v • P))) + (𝛕 • (g (c ! v' • Q))))
| ax_output_merge_r : forall (c : ChannelData) (v v' : ValueData) (P Q : proc),
    ⊢ g ((𝛕 • (g (c ! v • P))) + (𝛕 • (g (c ! v' • Q)))) ⊑ g ((c ! v • P) + (c ! v' • Q))
| ax_input_merge_l : forall (c : ChannelData) (P Q : proc),
    ⊢ g ((c ? P) + (c ? Q)) ⊑ g ((𝛕 • (g (c ? P))) + (𝛕 • (g (c ? Q))))
| ax_input_merge_r : forall (c : ChannelData) (P Q : proc),
    ⊢ g ((𝛕 • (g (c ? P))) + (𝛕 • (g (c ? Q)))) ⊑ g ((c ? P) + (c ? Q))

| ax_expansion_l : forall M N, gStatic M -> gStatic N -> ⊢ (g M ‖ g N) ⊑ g ((ext M N + ext_r N M) + int M N)
| ax_expansion_r : forall M N, gStatic M -> gStatic N -> ⊢ g ((ext M N + ext_r N M) + int M N) ⊑ (g M ‖ g N)

| ax_res_normalize_l : forall M, gStatic M -> ⊢ (ν (g M)) ⊑ g (resg M)
| ax_res_normalize_r : forall M, gStatic M -> ⊢ g (resg M) ⊑ (ν (g M))

| ax_input_distrib_l : forall (c : ChannelData) (P Q : proc),
    ⊢ g ((c ? P) + (c ? Q)) ⊑ g (c ? (g ((𝛕 • P) + (𝛕 • Q))))
| ax_input_distrib_r : forall (c : ChannelData) (P Q : proc),
    ⊢ g (c ? (g ((𝛕 • P) + (𝛕 • Q)))) ⊑ g ((c ? P) + (c ? Q))
| ax_output_distrib_l : forall (c : ChannelData) (v : ValueData) (P Q : proc),
    ⊢ g ((c ! v • P) + (c ! v • Q)) ⊑ g (c ! v • (g ((𝛕 • P) + (𝛕 • Q))))
| ax_output_distrib_r : forall (c : ChannelData) (v : ValueData) (P Q : proc),
    ⊢ g (c ! v • (g ((𝛕 • P) + (𝛕 • Q)))) ⊑ g ((c ! v • P) + (c ! v • Q))

| ax_choice_stable : forall (gp gp' gq : gproc),
    gStable gp -> gStable gp' ->
    ⊢ g gp ⊑ g gp' -> ⊢ g (gp + gq) ⊑ g (gp' + gq)

where "⊢ p ⊑ q" := (ax_pre p q).

Notation "⊢ p ≂ q" := (⊢ q ⊑ p /\ ⊢ p ⊑ q) (at level 70).

Hint Constructors ax_pre : mdb.

Lemma ax_cgr_sym : forall p q, Static p -> p ≡* q -> ⊢ q ⊑ p.
Proof. intros p q Hsp Hcgr. apply ax_cgr; [exact Hsp | eapply cgr_symm; exact Hcgr]. Qed.

End DefinitionAxiomatic.
