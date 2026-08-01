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

(** * The inequational theory characterises the must-preorder

    The tie-in corollary, in the style of [VCCS_Must_Characterization.v]:
    on the recursion-free ([Static]) fragment of VCCS, the proof system
    [ax_pre] of [DefinitionAxiomatic.v] is *exactly* the must-preorder.

    - [soundness_ax] ([SoundnessAx.v]): every derivation is valid;
    - [completeness_ax] ([CompletenessAx.v]): every valid inequation is
      derivable.

    The rule set this holds of is not the one a naive reading of
    Hennessy & Ingólfsdóttir suggests. Eleven corrections were needed,
    each recorded at its own constructor in [DefinitionAxiomatic.v]:
    the sum-congruence rule [ax_choice] is **unsound** and was removed,
    and ten rules were missing — [ax_choice_stable], [ax_int_glb],
    [ax_tau_sep_l]/[_r], [ax_choice_tau], [ax_tau_flatten_l]/[_r],
    [ax_convex], [ax_success_l]/[_r], [ax_share_in]/[_out] and
    [ax_swap_out]. *)

From Stdlib Require Import List.
From stdpp Require Import base.
From TestingTheory Require Import VCCS VCCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VCCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VCCS_Static VCCS_Must_Characterization
  DefinitionAxiomatic SoundnessAx CompletenessAx.

Section EquivalenceAx.

Context `{VP : VCCS_Parameters}.

(** ** The characterisation *)

Theorem must_iff_ax_pre : forall (p q : proc), Static p -> Static q ->
  (ax_pre p q <-> p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q).
Proof.
  intros p q Hp Hq. split.
  - intro Hax. apply soundness_ax; assumption.
  - intro Hpre. apply completeness_ax; assumption.
Qed.

(** Two-sided derivability is must-equivalence. *)
Corollary must_eq_iff_ax_eq : forall (p q : proc), Static p -> Static q ->
  (ax_pre p q /\ ax_pre q p) <-> (p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q /\ q ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ p).
Proof.
  intros p q Hp Hq. split.
  - intros (H1 & H2). split; apply must_iff_ax_pre; assumption.
  - intros (H1 & H2). split; apply must_iff_ax_pre; assumption.
Qed.

(** ** Decidability-flavoured restatement

    Every semantic fact about the [Static] fragment is reachable by a
    finite derivation in the 36-constructor system, and conversely. *)

Corollary ax_pre_sound_and_complete : forall (p q : proc),
  Static p -> Static q -> (p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> ax_pre p q) /\ (ax_pre p q -> p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q).
Proof.
  intros p q Hp Hq.
  split; [apply completeness_ax | apply soundness_ax]; assumption.
Qed.

End EquivalenceAx.
