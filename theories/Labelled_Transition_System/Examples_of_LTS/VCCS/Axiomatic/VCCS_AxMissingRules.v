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

(** * What the τ-encoding costs, relative to Hennessy & Ingólfsdóttir

    Transcribing Hennessy & Ingólfsdóttir's proof system ("A Theory of
    Communicating Processes with Value-Passing", Information and
    Computation 107(2), 202–236, 1993, §4) to this repository's VCCS
    gives a system that is **not** complete for [⊑ₘᵤₛₜᵢ], and one of
    whose rules is **not sound**. Eleven corrections were needed; this
    file collects them, each with a concrete witness.

    **This is not a defect in their paper.** They prove both directions
    (Theorem 4.1 soundness, Theorem 4.7 completeness w.r.t. the model
    [AT_s^v], Theorem 4.10 full abstraction transferring both to
    [⊑_M]), and for *all* terms including recursion, via two infinitary
    rules. The divergence has a single cause:

    - their VPL is "essentially full CCS, **but with τ replaced by
      internal nondeterminism ⊕**" (§2, p. 205). [⊕] is a primitive
      binary operator, [+] is unguarded, and their Rule II is a
      congruence for **every** operator in [Σ] — including both [+] and
      [⊕].
    - here [⊕] is *defined* as [𝛕•X + 𝛕•Y], [+] is guarded, and [𝛕] is
      a guard.

    Under that encoding a rewrite inside a [+] can turn a stable summand
    into a [𝛕]-guarded one, so their Rule II becomes unsound; and their
    distributivity [X + (Y ⊕ Z) = (X+Y) ⊕ (X+Z)] (Fig. 5) becomes
    invalid. Those two are exactly what their derivations Der 1, Der 2
    and Der 3′ (pp. 227–228) rest on — so what they *derive*, we must
    *postulate*:

    - [ax_convex] is their **Der 2**;
    - union closure ([ax_int_below_ext]) is their **Der 1** (derived
      here too, from [ax_tau_sep_l]);
    - [ax_share_in]/[_out] and [ax_swap_out] are their **Der 3′**;
    - [ax_int_glb] is theirs by [X ⊕ X = X] plus congruence for [⊕];
    - [ax_choice_stable] and [ax_choice_tau] are the restricted
      survivors of their Rule II;
    - [ax_output_merge] with two *different* values is their Fig. 5
      equation [c!e.X + c!e'.Y = c!e.X ⊕ c!e'.Y] — p. 204 spells out
      that the channels must agree but the expressions need not, and
      p. 235 explains why: the testing framework cannot differentiate
      the two sides. That is the same value-erasure that forces
      [ax_swap_out] here.

    Only three corrections have **no** counterpart in their system:
    [ax_tau_sep_l]/[_r] and [ax_tau_flatten_l]/[_r], which exist purely
    to manage [𝛕]-guards (VPL has none), and [ax_success_l]/[_r],
    because [①] is a process-level constructor of this repository
    whereas VPL reports success only inside a *test*, on a dedicated
    channel.

    For every added rule the witness below is a pair [p], [q] with

    - [p ⊑ₘᵤₛₜᵢ q] — machine-checked here, via [soundness_ax] applied to
      the one-rule derivation, and
    - [⊢ p ⊑ q] — likewise machine-checked, in one rule application.

    What is *documented but not machine-checked* is the third leg:
    that no other rule of the system reaches the same inequation. Those
    checks were done by hand, rule by rule, when each law was added;
    the argument is recalled with each example and in full at the
    corresponding constructor in [DefinitionAxiomatic.v]. A mechanical
    proof would need, per rule, a model or syntactic invariant preserved
    by all the others and violated by the witness — twenty-six separate
    constructions, not attempted.

    Note also that the system is stated here with **26** constructors,
    not 36: ten of the laws a Hennessy-style presentation makes
    primitive are derivable, and are proved as lemmas instead (nine in
    [DefinitionAxiomatic.v], one in [VCCS_AxRedundancy.v]). So the
    eleven corrections below are corrections to the *content* of the
    system, independently of how it is packaged. *)

From Stdlib Require Import List.
From stdpp Require Import base.
From TestingTheory Require Import VCCS VCCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VCCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VCCS_Static VCCS_Must_Characterization
  VCCS_Expansion VCCS_ResNormalize VCCS_Precongruence VCCS_ReadySet
  DefinitionAxiomatic VCCS_Canonical VCCS_NormalForm SoundnessAx CompletenessAx
  VCCS_AxRedundancy.

Section VCCS_AxMissingRules.

Context `{VP : VCCS_Parameters}.
Context {a b c : Channel} {v w : Value}.

(** A tactic for the [Static] side conditions, which are all structural. *)
Ltac st := repeat constructor.

(** ** 0. The rule that had to be REMOVED: sum congruence

    Hennessy's system has a congruence rule for [+]. In CCS with a
    [𝛕]-prefix it is **unsound**, and this is not a subtlety of the
    encoding — it is Milner's third [𝛕]-law failing:
    [𝛕.P + Q = P + Q] holds in no standard equivalence.

    The counterexample (worked out on the [must] fields directly, see
    [DefinitionAxiomatic.v]) is

      gp  := c!v•𝟘        gp' := 𝛕•(c!v•𝟘)        gq = gq' := d!w•𝟘

    with [c ≠ d]. Standalone, [gp] and [gp'] are must-*equivalent* — a
    lone [𝛕] changes nothing when there is no alternative to pre-empt.
    But [gp + gq] is stable and synchronises with the test [d?①],
    whereas [gp' + gq'] is not: its [𝛕] fires unconditionally, and
    guarded choice commits, so [must]'s [pt] field then demands that
    [c!v•𝟘] alone pass [d?①], which it cannot.

    The system keeps only the two restricted forms — [ax_choice_stable]
    and [ax_choice_tau] — which between them cover every guard shape.
    The principle they share: **sum congruence is sound exactly when
    the rewrite cannot change whether the rewritten summand is
    initially stable.** *)

(** ** 1. [ax_choice_stable] — rewriting a stable summand in context

    Without it no derivation can collapse two same-action summands
    sitting inside a larger sum, because [ax_cgr] only permutes and the
    unrestricted congruence is the unsound rule above. *)

Definition p1 : proc := g ((a ? (g 𝟘)) + (a ? (g ①)) + (b ! v • 𝟘)).
Definition q1 : proc := g ((a ? (g ((𝛕 • (g 𝟘)) + (𝛕 • (g ①))))) + (b ! v • 𝟘)).

Example ax_1 : ax_pre p1 q1.
Proof. apply ax_collapse_input_ctx_l. Qed.

Example sem_1 : p1 ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q1.
Proof. apply soundness_ax; [st | st | apply ax_1]. Qed.

(** ** 2. [ax_int_glb] — internal choice is the GREATEST lower bound

    The original system has glb *elimination* ([ax_int_l]/[ax_int_r])
    and no introduction, so nothing can ever establish [_ ⊑ q₁ ⊕ q₂].
    Completeness needs exactly that whenever the right-hand normal form
    has [𝛕]-summands. An internal choice is not [gStable], so
    [ax_choice_stable] cannot help either. *)

Definition p2 : proc := g (a ! v • 𝟘).
Definition q2 : proc := g ((𝛕 • (g (a ! v • 𝟘))) + (𝛕 • (g (a ! v • 𝟘)))).

Example ax_2 : ax_pre p2 q2.
Proof. apply ax_int_glb; apply ax_refl; st. Qed.

Example sem_2 : p2 ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q2.
Proof. apply soundness_ax; [st | st | apply ax_2]. Qed.

(** ** 3. [ax_tau_sep_l]/[_r] — a mixed sum is its own thing

    A sum with both external guards and a [𝛕]-guard is neither an
    internal choice nor its external part: [VCCS_MixedSumProbes.v]
    refutes both readings with machine-checked counterexamples. The
    separation law is what turns such a sum into the
    [⊕]-of-stable-sums shape the completeness proof matches on.

    Note [X] is carried **into the first branch** — the tempting
    [X + 𝛕•Y ≂ 𝛕•Y ⊕ X] is false, for the reason
    [VCCS_MixedSumProbes.v] exhibits: as a branch of its own, [X] would
    sit under [must]'s [pt] field and owe an interaction by itself. *)

Definition p3 : proc := g ((a ! v • 𝟘) + (𝛕 • (g (b ! w • 𝟘)))).
Definition q3 : proc :=
  g ((𝛕 • (g ((a ! v • 𝟘) + (b ! w • 𝟘)))) + (𝛕 • (g (b ! w • 𝟘)))).

Example ax_3 : ax_pre p3 q3.
Proof. apply ax_tau_sep_l. Qed.

Example sem_3 : p3 ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q3.
Proof. apply soundness_ax; [st | st | apply ax_3]. Qed.

(** ** 4. [ax_tau_flatten_l]/[_r] — what makes the normal form terminate

    [gAllTau Y] ("every summand of [Y] is [𝛕]-guarded") is essential:
    with external summands in [Y], moving it up would expose them at
    top level. And [𝟘] deliberately does not count as all-[𝛕] —
    [X + 𝛕•𝟘] has a [𝛕] into a deadlock, [X + 𝟘] does not.

    Without this law the normal-form construction does not terminate:
    separation recurses into [X + Y], and if [Y] is itself an internal
    choice its [𝛕]-summands re-enter the count. *)

Definition Y4 : gproc := (𝛕 • (g 𝟘)) + (𝛕 • (g ①)).
Definition p4 : proc := g ((a ! v • 𝟘) + (𝛕 • (g Y4))).
Definition q4 : proc := g ((a ! v • 𝟘) + Y4).

Example ax_4 : ax_pre p4 q4.
Proof. apply ax_tau_flatten_l. simpl. split; exact I. Qed.

Example sem_4 : p4 ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q4.
Proof. apply soundness_ax; [st | st | apply ax_4]. Qed.

(** ** 5. [ax_choice_tau] — rewriting a [𝛕]-summand's continuation

    The exact complement of [ax_choice_stable]. Needed because applying
    the separation law requires the [𝛕]-summand's continuation to
    already be a guarded sum, i.e. continuations must be normalised
    *in place inside a sum* — and a [𝛕]-summand is not stable. *)

Definition p5 : proc :=
  g ((𝛕 • (g ((a ! v • 𝟘) + (a ! w • 𝟘)))) + (b ! v • 𝟘)).
Definition q5 : proc := g ((𝛕 • (g (a ! v • 𝟘))) + (b ! v • 𝟘)).

Example ax_5 : ax_pre p5 q5.
Proof. apply ax_choice_tau. apply ax_output_below_l; st. Qed.

Example sem_5 : p5 ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q5.
Proof. apply soundness_ax; [st | st | apply ax_5]. Qed.

(** ** 6. [ax_convex] — convex closure of the acceptance family

    The witness that forced it. With

      p := (a!v•𝟘) ⊕ ((a!v•𝟘 + b!w•𝟘) + c!v•𝟘)     q := a!v•𝟘 + b!w•𝟘

    [q]'s ready set [{a,b}] is neither a leaf's ready set of [p] nor a
    union of them ([{a}], [{a,b,c}]) — it lies strictly *between* two of
    them. Union closure is derivable ([ax_int_below_ext]); convex
    closure is not, and every rule able to put a stable sum on the right
    ([ax_choice_stable], the merge and distributivity laws, [ax_cgr])
    can only reproduce ready sets already assembled from the left. *)

Definition A6 : gproc := a ! v • 𝟘.
Definition B6 : gproc := b ! w • 𝟘.
Definition C6 : gproc := c ! v • 𝟘.
Definition p6 : proc := g ((𝛕 • (g A6)) + (𝛕 • (g ((A6 + B6) + C6)))).
Definition q6 : proc := g (A6 + B6).

Example ax_6 : ax_pre p6 q6.
Proof. apply ax_convex. Qed.

Example sem_6 : p6 ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q6.
Proof. apply soundness_ax; [st | st | apply ax_6]. Qed.

(** ** 7. [ax_success_l]/[_r] — [①] is a [𝟘] on the server side

    [must]'s outcome field inspects only the *test*, so a server enters
    solely through its transitions — and [①] has none, exactly like
    [𝟘]. Before these two rules, **no rule of the system mentioned [①]
    at all**, and [≡*] does not relate it to [𝟘], so any normal form
    carrying an [①] summand was stuck. *)

Example ax_7l : ax_pre (g ①) (g (𝟘 : gproc)).
Proof. apply ax_success_l. Qed.

Example sem_7l : (g ① : proc) ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ (g (𝟘 : gproc)).
Proof. apply soundness_ax; [st | st | apply ax_7l]. Qed.

Example ax_7r : ax_pre (g (𝟘 : gproc)) (g ①).
Proof. apply ax_success_r. Qed.

Example sem_7r : (g (𝟘 : gproc) : proc) ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ (g ①).
Proof. apply soundness_ax; [st | st | apply ax_7r]. Qed.

(** ** 8. [ax_share_in]/[_out] — acceptance-tree uniformity

    Two branches of an internal choice pool their continuations at an
    action they share, keeping the **first** branch's ready set. This is
    the uniformity condition of acceptance-tree normal forms (one
    continuation function shared by every acceptance set), and it is the
    only rule that lets a derivation take its ready set from one leaf
    and its continuation from another.

    Nothing else does that: [ax_int_l]/[_r] reach only a whole branch;
    the merge and distributivity laws reduce the goal to itself; and
    [ax_convex] *transfers* a restricted target but cannot introduce one
    — with its [Y] empty it reduces, through [ax_int_glb], to its own
    conclusion. *)

Definition p8 : proc :=
  g ((𝛕 • (g ((a ? (g 𝟘)) + (b ! v • 𝟘)))) + (𝛕 • (g ((a ? (g ①)) + (c ! w • 𝟘))))).
Definition q8 : proc :=
  g ((a ? (g ((𝛕 • (g 𝟘)) + (𝛕 • (g ①))))) + (b ! v • 𝟘)).

Example ax_8 : ax_pre p8 q8.
Proof. apply ax_share_in. Qed.

Example sem_8 : p8 ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q8.
Proof. apply soundness_ax; [st | st | apply ax_8]. Qed.

Definition p8' : proc :=
  g ((𝛕 • (g ((a ! v • 𝟘) + (b ! v • 𝟘)))) + (𝛕 • (g ((a ! v • (g ①)) + (c ! w • 𝟘))))).
Definition q8' : proc :=
  g ((a ! v • (g ((𝛕 • 𝟘) + (𝛕 • (g ①))))) + (b ! v • 𝟘)).

Example ax_8' : ax_pre p8' q8'.
Proof. apply ax_share_out. Qed.

Example sem_8' : p8' ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q8'.
Proof. apply soundness_ax; [st | st | apply ax_8']. Qed.

(** ** 9. [ax_swap_out] — the ready-set abstraction erases the value

    The one found last, and the subtlest. VCCS's ready-set abstraction
    [⌈𝝳ᴠᴄᴄꜱ∘Φᴠᴄᴄꜱ⌉] keeps channel and polarity and **throws the value
    away** ([coR_abs_incl_iff], [VCCS_ReadySet.v]). So a leaf may offer
    [a!v] where the target offers only [a!w].

    Witness (take [v ≠ w]):

      p := (a!v•𝟘 + b!w•𝟘) ⊕ (a!w•𝟘 + b!v•𝟘)     q := a!w•𝟘 + b!w•𝟘

    [p ⊑ₘᵤₛₜᵢ q] holds — [q]'s ready set is a **transversal**, one
    summand taken from each leaf — yet no leaf of [p] has its key set
    inside [q]'s, so neither [ax_int_l]/[_r] nor [ax_convex] nor
    [ax_share_out] (which needs the *same* value) reaches it. The merge
    equations do relate same-channel different-value pairs, but only
    when the pair is the whole sum: merging turns a stable summand into
    an unstable one, so applying it in a context would reintroduce the
    unsound [ax_choice].

    Pooling at different values ([a!w•(P ⊕ Q) + X']) would be
    **unsound** — after emitting [w] the test sits in a state only [Q]
    was ever required to survive. *)

Definition p9 : proc :=
  g ((𝛕 • (g ((a ! v • 𝟘) + (b ! w • 𝟘)))) + (𝛕 • (g ((a ! w • 𝟘) + (b ! v • 𝟘))))).
Definition q9 : proc := g ((a ! w • 𝟘) + (b ! w • 𝟘)).

Example ax_9 : ax_pre p9 q9.
Proof. apply ax_swap_out. Qed.

Example sem_9 : p9 ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q9.
Proof. apply soundness_ax; [st | st | apply ax_9]. Qed.

End VCCS_AxMissingRules.
