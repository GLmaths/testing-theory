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
From Stdlib.Program Require Import Equality Basics.
From stdpp Require Import finite gmap decidable gmultiset.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Subset_Act WeakTransitions Testing_Predicate
    StateTransitionSystems InteractionBetweenLts Convergence Termination FiniteImageLTS Subset_Act.

(* * Alternative preorder for Must based on acceptance-sets — PROCESS-DEPENDENT
     label abstractions.

     Parked here, not yet wired into anything, as a design record.  Not proved
     compatible with the rest of the Acceptance_Set development (Soundness.v /
     Completeness.v still use the process-INDEPENDENT [Φ : A → FinA] /
     [𝝳 : FinA → PreAct] from [DefinitionAS.v]).

     Motivation (session discussion, Applicative_process_algebra.v / PAL):
     [DefinitionAS.v]'s [AbsAction] requires a single, process-independent
     [Φ : A → FinA] collapsing the action alphabet.  For calculi like VCCS this
     works because *the calculus itself* is structurally blind to some
     dimension of the action (e.g. VCCS's bare input guard [c?p] accepts every
     value, regardless of which process you plug in — a fact true uniformly for
     every process, so a single global [Φ] can safely merge on that dimension).

     PAL has no such uniform blind spot: whether a given tuple position is
     "value-blind" (a formal field) or "value-exact" (an actual field) is a
     property of *which process* you're looking at, not of the calculus as a
     whole — some PAL process pins down an exact value at a given position,
     some doesn't.  So no process-independent [Φ] can safely merge PAL actions
     without breaking [abstraction_test_spec]/[abstraction_prog_spec] for the
     processes that *do* distinguish (concretely: for any two supposedly-merged
     tuples, PAL's own syntax can build a process with an actual field at the
     differing position, refuting the merge).

     The paper's own route to finiteness (Def 4.3 / Prop 4.4: IRT(P), OT(P),
     ID(P), D(P,α) are finite for every *fixed* process P) is syntactic and
     per-process — a process only has finitely many in/read subterms — not a
     value-collapsing abstraction of the action alphabet.  Reproducing that
     "spirit" inside the [AbsAction] framework means letting [Φ]/[𝝳] depend on
     the process being abstracted:

       Φ : P → A → FinA        (Φ p : A → FinA, for each process p)
       𝝳 : P → FinA → PreAct   (𝝳 p : FinA → PreAct, for each process p)

     kept as a *single* family (no [ΦP]/[ΦQ] split, no [𝝳P]/[𝝳Q] split — that
     was tried and reverted once already, see the [deltaP_deltaQ_must_share]
     session note: splitting a shared abstraction across two [AbsAction]
     instances breaks lemmas that need to relate one literal label through
     both sides at once).

     For PAL concretely, this lets [Φ p] be genuinely finite-valued:
       Φ p (ActIn ot)  := { it ∈ IRT(p) | match(it, ot) }   (⊆ IRT(p), finite by Prop 4.4)
       Φ p (ActOut ot) := ot                                 (OT(p) already finite, nothing to merge)

     [P] plays both the "process" and "test" role below (a single shared
     type, unlike [DefinitionAS.v]'s fully general [P]/[T]/[Q]) — process-
     dependence forces [Φ]/[𝝳] to be applied to an actual element of whatever
     type they're defined over, and every real use in this project (VCCS:
     [AbsAction proc proc ...]; PAL: self-testing, [Prop_of_Inter term term])
     already has the "test" and "process under test" be the same calculus, so
     this is not a loss of generality in practice, just dropping an unused
     degree of freedom.

     The obvious risk of process-dependence — that comparing two DIFFERENT
     processes' abstracted co-refusal sets becomes ill-typed/incomparable
     (⌈Φ p⌉(coR p) and ⌈Φ q⌉(coR q) computed by two different functions) — is
     not resolved inside [AbsActionAlt] itself, but by how [bhv_pre_cond2]
     would have to be restated: apply *one* side's abstraction ([Φ q']/
     [𝝳 q']) to *both* sides of the inclusion, rather than each process its
     own — see [bhv_pre_cond2_alt] below:

       ⌈𝝳 q' ∘ Φ q'⌉(coR p') ⊆ ⌈𝝳 q' ∘ Φ q'⌉(coR q')

     instead of the original [⌈𝝳P∘Φ⌉(coR p') ⊆ ⌈𝝳Q∘Φ⌉(coR q')].  Both sides
     then live in the same [PreAct] by construction (same function applied to
     both), with no cross-process coherence axiom needed — at the cost that
     [⌈Φ q'⌉(coR p')] has no particular reason to be finite ([Φ q'] is tailored
     to [q']'s own patterns, not [p']'s), which would need separate handling
     if a [FinitaryAbsAction]-style computable [coR_abs] is wanted for this
     version. *)

(** ** Label abstractions, process-dependent *)

Class AbsActionAlt {P FinA PreAct : Type} (A : Type) (H : ExtAction A)
  (Φ : P → A → FinA) (𝝳 : P → FinA → PreAct)
  {gLtsP : gLtsEq P H} :=
  MkAbsActionAlt {
    (** Test-side condition, process-dependent version of Definition 5 (1):
        [Φ p] plays the role the single global [Φ] used to play, but is now
        indexed by which process [p] we're looking at (whether it's acting
        as "the process under test" or "the test" — same type, same [Φ]). *)
    abstraction_test_spec_alt (p : P) (β β' : A) :
      blocking β -> blocking β' -> (Φ p β) = (Φ p β') -> β ∈ (R p) -> β' ∈ (R p);

    (** Process-side condition, process-dependent version of Definition 5 (2):
        both occurrences of [Φ]/[𝝳] below are pinned to the SAME [p] as the
        one whose [coR] is being reasoned about — no cross-process mixing
        inside the spec itself. *)
    abstraction_prog_spec_alt (p : P) (β β' : A) :
      blocking β -> blocking β' -> 𝝳 p (Φ p β) = 𝝳 p (Φ p β') ->
      (Φ p β) ∈ map_set (Φ p) (coR p) -> (Φ p β') ∈ map_set (Φ p) (coR p);
  }.

Arguments AbsActionAlt {_} {_} {_} A H Φ 𝝳 {_}.

(** ** Termination condition — unchanged from [DefinitionAS.v]; doesn't involve
      [Φ]/[𝝳] at all. *)
Definition bhv_pre_cond1_alt `{gLts P A, gLts Q A}
  (p : P) (q : Q) := forall s, p ⇓ s -> q ⇓ s.

Notation "p ₁≼ₐₛ' q" := (bhv_pre_cond1_alt p q) (at level 70).

(** ** Smyth preorder on acceptance sets, process-dependent abstraction

    Restatement of [bhv_pre_cond2] (Definition AS's Smyth-preorder clause)
    using [q']'s OWN abstraction on BOTH sides of the inclusion, instead of
    comparing [p']'s abstraction against [q']'s — see the file's header
    comment for why: this is what keeps the inclusion well-typed once [Φ]/[𝝳]
    are process-dependent, without needing any cross-process coherence
    axiom. Both [p] and [q] live in the same type [P] here (see the header
    comment on why [AbsActionAlt] itself is single-typed). *)
Definition bhv_pre_cond2_alt `{
  gLtsP : @gLtsEq P A H, AbsPT : @AbsActionAlt P FinA PreAct A H Φ 𝝳 gLtsP}
  (p q : P) :=
  forall (s : trace A) q',
    p ⇓ s -> q ⟹[s] q' -> q' ↛ ->
    ∃ p', p ⟹[s] p' /\ p' ↛ /\ (⌈ (𝝳 q' ∘ Φ q') ⌉ (coR p') ⊆ ⌈ (𝝳 q' ∘ Φ q') ⌉ (coR q')).

Notation "p ₂≼ₐₛ' q" := (bhv_pre_cond2_alt p q) (at level 70).

(** ** Definition of the alternative preorder, process-dependent abstraction *)
Definition bhv_pre_alt `{
  gLtsP : @gLtsEq P A H, AbsPT : @AbsActionAlt P FinA PreAct A H Φ 𝝳 gLtsP}
    (p q : P) :=
      p ₁≼ₐₛ' q /\ p ₂≼ₐₛ' q.

Notation "p ≼ₐₛ' q" := (bhv_pre_alt p q) (at level 70).
