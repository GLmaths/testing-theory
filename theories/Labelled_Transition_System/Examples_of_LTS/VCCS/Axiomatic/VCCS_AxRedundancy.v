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

(** * The last derived law: the output-merge equation, left to right

    Ten of the laws a Hennessy-style presentation states as *rules* are
    admissible from the twenty-six constructors of
    [DefinitionAxiomatic.v]; nine of them are proved there, right after
    the inductive. The tenth is here, because its derivation needs
    [ax_drop_out] ([CompletenessAx.v]) and so cannot be stated that
    early.

    That dependency is the interesting part. For *inputs*, the merge
    equation's projections come from [ax_input_distrib_l]. For
    *outputs* the two values may differ, and [ax_output_distrib_l]
    wants them equal — so the projections come instead from
    [ax_drop_out], i.e. ultimately from **[ax_swap_out]**, the rule
    found last in the whole development. The rule added at the very end
    turns out to subsume one of the rules present from the start. *)

From Stdlib Require Import List.
From stdpp Require Import base.
From TestingTheory Require Import VCCS VCCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VCCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VCCS_Static VCCS_Must_Characterization
  VCCS_Expansion VCCS_ResNormalize VCCS_Precongruence VCCS_ReadySet
  DefinitionAxiomatic VCCS_Canonical VCCS_NormalForm SoundnessAx CompletenessAx.

Section VCCS_AxRedundancy.

Context `{VP : VCCS_Parameters}.

(** A sum of two same-channel outputs is below each of them. With the
    *same* value this is [ax_output_distrib_l]; with different values it
    is [ax_drop_out], and nothing weaker will do. *)

Lemma ax_output_below_r : forall c v v' P Q, Static P -> Static Q ->
  ax_pre (g ((c ! v • P) + (c ! v' • Q))) (g (c ! v' • Q)).
Proof.
  intros c v v' P Q HP HQ.
  eapply ax_trans.
  { apply ax_cgr with (q := g ((c ! v • P) + ((c ! v' • Q) + 𝟘)));
      [repeat constructor; assumption |].
    apply cgr_fullchoice; [apply cgr_refl | apply cgr_choice_nil_rev]. }
  eapply ax_trans.
  { apply (ax_drop_out c v v' P Q 𝟘); [exact HP | exact HQ | constructor | exact I]. }
  apply ax_cgr; [repeat constructor; assumption | apply cgr_choice_nil].
Qed.

Lemma ax_output_below_l : forall c v v' P Q, Static P -> Static Q ->
  ax_pre (g ((c ! v • P) + (c ! v' • Q))) (g (c ! v • P)).
Proof.
  intros c v v' P Q HP HQ.
  eapply ax_trans.
  { apply ax_cgr with (q := g ((c ! v' • Q) + (c ! v • P)));
      [repeat constructor; assumption | apply cgr_choice_com]. }
  apply ax_output_below_r; assumption.
Qed.

(** …so [ax_int_glb] assembles the internal choice. *)

Lemma ax_output_merge_l : forall c v v' P Q, Static P -> Static Q ->
  ax_pre (g ((c ! v • P) + (c ! v' • Q)))
         (g ((𝛕 • (g (c ! v • P))) + (𝛕 • (g (c ! v' • Q))))).
Proof.
  intros c v v' P Q HP HQ.
  apply ax_int_glb; [apply ax_output_below_l | apply ax_output_below_r]; assumption.
Qed.

End VCCS_AxRedundancy.
