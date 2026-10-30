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
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB StateTransitionSystems Termination
    Must Bar Lift Subset_Act FiniteImageLTS WeakTransitions Convergence
    InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction
    Testing_Predicate DefinitionAS MustE Lts_Finite_Non_Blocking_Chain.
From TestingTheory Require Import coFiniteImage DefinitionASrel LtsFW CompletenessASco SoundnessASco EquivalenceASco
    Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic Coin_tower_co.

(* begin hide *)
Section must_co_inductive_co_trace.
  Context `{outcome : T -> Prop} `{outcome_dec : forall t, Decision (outcome t)} `{P : Type}
          `{H : !ExtAction A}.

  Context `{gLtsEqP : !gLtsEq P H, !coFiniteImagegLts P A}
          `{!gLtsOba T gLtsEqT, !Testing_Predicate outcome _} `{!CountablegLts T A}.

  Context `{!Prop_of_Inter P T A A dual}.

  Context `{tc_spec : !test_convergence_spec (t_conv : trace A → T)}.

  Section FWⁿ.

  Context `{!LtsFW P A}.

  Context (𝔸 : Label_abstraction P T) `{!Dichotomic P ρ[𝔸] }.

  Context `{ta_spec : !test_co_acceptance_set_spec (ta : gset (A / 𝔸) → trace A → T) ρ[𝔸] }.

  Corollary equivalence_fw_co_inductive_co_trace_and_must_i (p q : P) :
    p ⊑ₘᵤₛₜᵢ q <-> ({[ p ]} : gset P) ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ ρ[𝔸] ] {[ q ]}.
  Proof. rewrite copre_co_singleton. exact (equivalence_fw_acc_set_and_must_i_co_trace (ta := ta) 𝔸 p q). Qed.

  Corollary equivalence_fw_co_inductive_co_trace_and_must_e (p q : P) :
    pre_extensional outcome p q <-> ({[ p ]} : gset P) ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ ρ[𝔸] ] {[ q ]}.
  Proof. rewrite copre_co_singleton. exact (equivalence_fw_bhv_acc_ctx_co_trace (ta := ta) 𝔸 p q). Qed.

  End FWⁿ.

  Section Lⁿ.

  Context {unique_nb : UniqueDual A}.

  Context `{!FiniteImagegLts P A}.

  Context `{!gLtsOba P gLtsEqP, !gLtsObaFB P A, !FiniteNonBlockingChain_LtsOba P}
          `{!gLtsObaFB T A, !FiniteNonBlockingChain_LtsOba T}.

  Context `{!Prop_of_Inter P (MO A) A A fw_inter} `{!Prop_of_Inter (P * MO A) T A A dual}.

  Context `{!coFiniteImagegLts (P * MO A) A}.

  Context (𝔸 : Label_abstraction (P * MO A) T) `{!Dichotomic (P * MO A) ρ[𝔸] }.

  Context `{ta_spec : !test_co_acceptance_set_spec (ta : gset (A / 𝔸) → trace A → T) ρ[𝔸] }.

  Corollary equivalence_co_inductive_co_trace_and_must_i (p q : P) :
    p ⊑ₘᵤₛₜᵢ q <-> ({[ (p, ∅) ]} : gset (P * MO A)) ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ ρ[𝔸] ] {[ (q, ∅) ]}.
  Proof. rewrite copre_co_singleton. exact (equivalence_acc_set_and_must_i_co_trace (ta := ta) 𝔸 p q). Qed.

  Corollary equivalence_co_inductive_co_trace_and_must_e (p q : P) :
    pre_extensional outcome p q <-> ({[ (p, ∅) ]} : gset (P * MO A)) ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ ρ[𝔸] ] {[ (q, ∅) ]}.
  Proof. rewrite copre_co_singleton. exact (equivalence_bhv_acc_ctx_co_trace (ta := ta) 𝔸 p q). Qed.

  End Lⁿ.

End must_co_inductive_co_trace.
(* end hide *)
