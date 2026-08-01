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

(** * The inequational theory, exercised on [VCCS_Examples.v]'s processes

    End-to-end check of [SoundnessAx.v] and [CompletenessAx.v] against
    the two concrete examples the repository already proves by hand.

    The first one is the point of the whole development: in
    [VCCS_Examples.v], [all_out ⊑ₘᵤₛₜᵢ one_out] takes a bespoke
    acceptance-set argument with two custom tactics ([compute_coR],
    [only_two_cases]) and a case analysis on the weak transitions.
    Here it is **one rule application** — a sum of two same-channel
    outputs is below either of them — and [soundness_ax] hands back the
    semantic fact. *)

From Stdlib Require Import List.
From stdpp Require Import base.
From TestingTheory Require Import VCCS VCCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VCCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VCCS_Static VCCS_Must_Characterization
  DefinitionAxiomatic SoundnessAx CompletenessAx EquivalenceAx VCCS_AxRedundancy.

Section VCCS_AxExamples.

Context `{VP : VCCS_Parameters}.
Context {a : Channel} {I : Value}.

(** ** Offering two values on a channel is below offering one

    Same definitions as [VCCS_Examples.v]. *)

Definition all_out := g ((a ! O • 𝟘) + (a ! I • 𝟘)).
Definition one_out := g (a ! O • 𝟘).

Lemma all_out_Static : Static all_out.
Proof. repeat constructor. Qed.

Lemma one_out_Static : Static one_out.
Proof. repeat constructor. Qed.

(** The derivation, by hand: a sum of two same-channel outputs is below
    either of them. That is [ax_output_below_l] ([VCCS_AxRedundancy.v]),
    itself the [ax_swap_out] rule in disguise. *)
Example ax_all_out_below_one_out : ax_pre all_out one_out.
Proof. apply ax_output_below_l; repeat constructor. Qed.

(** …and the semantic fact, for free. Compare
    [VCCS_Examples.one_output_is_above_all_output_conv]. *)
Example all_out_below_one_out : all_out ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ one_out.
Proof.
  apply soundness_ax;
    [apply all_out_Static | apply one_out_Static | apply ax_all_out_below_one_out].
Qed.

(** Both directions at once. *)
Example all_out_characterised : ax_pre all_out one_out <-> all_out ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ one_out.
Proof. apply must_iff_ax_pre; [apply all_out_Static | apply one_out_Static]. Qed.

(** ** Scope extrusion of a private memory cell

    [VCCS_Examples.mem_outside_is_above_mem_inside], again verbatim.
    Its continuations [P]/[Q] are arbitrary there; completeness applies
    as soon as they are recursion-free, which is the fragment the
    theorem is about. *)

Context {P : proc} {Q : proc}.

Definition mem_outside :=
  ν (g (bvar 0 ! cst I • 𝟘) ‖ g (cst a ? (If (bvar 0 == cst O) Then P Else Q))).

Definition mem_inside :=
  g (cst a ? (If (bvar 0 == cst O) Then (ν ((bvar 0 ! cst I • 𝟘) ‖ P))
                                   Else (ν ((bvar 0 ! cst I • 𝟘) ‖ Q)))).

Lemma mem_outside_Static : Static P -> Static Q -> Static mem_outside.
Proof. intros HP HQ. unfold mem_outside. repeat constructor; assumption. Qed.

Lemma mem_inside_Static : Static P -> Static Q -> Static mem_inside.
Proof. intros HP HQ. unfold mem_inside. repeat constructor; assumption. Qed.

(** Every semantic fact about the [Static] fragment has a derivation —
    including the one [VCCS_Examples.v] proves by a page of
    acceptance-set reasoning. *)
Example ax_mem_outside_above_mem_inside : Static P -> Static Q ->
  mem_inside ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ mem_outside -> ax_pre mem_inside mem_outside.
Proof.
  intros HP HQ Hpre.
  apply completeness_ax;
    [apply mem_inside_Static | apply mem_outside_Static | exact Hpre]; assumption.
Qed.

End VCCS_AxExamples.
