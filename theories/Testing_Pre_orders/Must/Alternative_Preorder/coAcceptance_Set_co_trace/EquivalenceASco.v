(* begin hide *)
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
(* end hide *)

From stdpp Require Import base decidable gmap finite.
From Stdlib Require Import ssreflect.
From Stdlib.Program Require Import Equality.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB StateTransitionSystems Termination
    Must Bar Lift Subset_Act FiniteImageLTS WeakTransitions Convergence
    InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction ActTau
    Testing_Predicate DefinitionAS MustE Lts_Finite_Non_Blocking_Chain.
From TestingTheory Require Import coFiniteImage DefinitionASrel LtsFW CompletenessASco SoundnessASco
    Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic.
(* * Equivalence for the co-acceptance-set preorder *)

Section preorder.
  Context `{outcome : T -> Prop} `{outcome_dec : forall t, Decision (outcome t)} `{P : Type}
          `{H : !ExtAction A}.

  Context `{gLtsEqP : !gLtsEq P H, !coFiniteImagegLts P A}
          `{!gLtsOba T gLtsEqT, !Testing_Predicate outcome _} `{!CountablegLts T A}.

  Context `{!Prop_of_Inter P T A A dual}.

  Context `{tc_spec : !test_convergence_spec (t_conv : trace A → T)}.

  (* * Main equivalence theorems, co variant *)

  Section FWⁿ.

  Context `{!LtsFW P A}.

  Context (𝔸 : Label_abstraction P T) `{!Dichotomic P ρ[𝔸] }.

  Context `{ta_spec : !test_co_acceptance_set_spec (ta : gset (A / 𝔸) → trace A → T) ρ[𝔸] }.

  (* ** The inductive characterisation on FW is equivalent to the inductive must preorder *)
  Theorem equivalence_fw_acc_set_and_must_i_co_trace (p q : P) :
    p ⊑ₘᵤₛₜᵢ q <-> p ≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] q.
  Proof.
    split.
    - exact (completeness_fw_co 𝔸 (ta := ta) (tconv := t_conv) p q).
    - exact (soundness_fw_co 𝔸 p q).
  Qed.

  (* ---- *)

  (* ** The inductive characterisation on FW is equivalent to the extensional must preorder *)
  Theorem equivalence_fw_bhv_acc_ctx_co_trace (p q : P) :
    pre_extensional outcome p q <-> p ≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] q.
  Proof.
    rewrite pre_extensional_eq. eapply equivalence_fw_acc_set_and_must_i_co_trace.
  Qed.

  End FWⁿ.
  (* ---- *)
  Section Lⁿ.

  Context {unique_nb : UniqueDual A}.

  Context `{!FiniteImagegLts P A}.

  Context `{!gLtsOba P gLtsEqP, !gLtsObaFB P A, !FiniteNonBlockingChain_LtsOba P}
          `{!gLtsObaFB T A, !FiniteNonBlockingChain_LtsOba T}.

  Context `{!Prop_of_Inter P (MO A) A A fw_inter} `{!Prop_of_Inter (P * MO A) T A A dual}.

  Context `{!coFiniteImagegLts (P * MO A) A}.

  Context (𝔸 : Label_abstraction (P * MO A) T) `{!Dichotomic (P * MO A) ρ[𝔸] }.

  Context `{ta_spec : !test_co_acceptance_set_spec (ta : gset (A / 𝔸) → trace A → T) ρ[𝔸] }.

  (* ** The inductive characterisation on toFW is equivalent to the inductive must preorder *)
  Theorem equivalence_acc_set_and_must_i_co_trace (p q : P) :
    p ⊑ₘᵤₛₜᵢ q <-> (p, ∅) ≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] (q, ∅).
  Proof.
    split.
    - intros hpre. apply (completeness_fw_co 𝔸 (ta := ta) (tconv := t_conv)).
      now apply lift_fw_ctx_pre.
    - intros hpre%(soundness_fw_co 𝔸).
      now apply lift_fw_ctx_pre.
  Qed.

  (* ---- *)

  (* ** The inductive characterisation on toFW is equivalent to the extensional must preorder *)
  Theorem equivalence_bhv_acc_ctx_co_trace (p q : P) :
    pre_extensional outcome p q <-> (p, ∅) ≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] (q, ∅).
  Proof.
    rewrite pre_extensional_eq. apply equivalence_acc_set_and_must_i_co_trace.
  Qed.

  End Lⁿ.

End preorder.
