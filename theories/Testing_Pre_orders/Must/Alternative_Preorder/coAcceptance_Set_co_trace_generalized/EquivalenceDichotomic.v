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

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable decidable gmap.
From TestingTheory Require Import ActTau gLts SyncActions MemAction InteractionUnion MemForwarder Bisimulation Lts_OBA
  Lts_OBA_FB Lts_FW Subset_Act coWeakSync coFiniteImage Testing_Predicate InteractionBetweenLts
  Must DefinitionASrel CompletenessASsync SoundnessASsync
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Section Equivalence_dich.

Context {P T PreAct Aproc Atest : Type}.
Context `{CC : Countable PreAct}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context (Γ : Atest → PreAct).
Context (outcome : T → Prop).

Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T _} `{!gLtsObaFB T Atest}.
Context `{TP : !Testing_Predicate outcome gLtsEqT}.

Context `{gLtsEqP : !gLtsEq P (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))} `{FWP : !gLtsFWMem P Aproc Atest}.
Context `{SYP : !Prop_of_Inter P T (Aproc + MemAct Atest) Atest sync} `{CFIP : !coFiniteImagegLts P Atest}.
Context `{AbsP : !AbsActionG (Aproc := (Aproc + MemAct Atest)) (Hp := ExtAction_sum) (SA := SyncAction_mem) P T (Γ : Atest → PreAct)}.
Context `{DichP : !Dichotomic (Hp := ExtAction_sum) (SA := SyncAction_mem) P Γ}.

Context (tconv : list Atest → T) `{!test_convergence_spec tconv}.
Context (ta : gset PreAct → list Atest → T)
        `{!test_co_acceptance_set_spec ta Γ}.

Theorem equivalence_fw_dich (p q : P) :
  p ⊆ₘᵤₛₜᵢ q ↔ p ≼꜀ₒ₋ₐₛ[ Γ ] q.
Proof.
  split.
  - intros hpre.
    by eapply (completeness_fw_co_sync_dich (tconv := tconv) (ta := ta)).
  - intros hpre.
    by eapply (soundness_fw_co_sync Γ outcome).
Qed.

End Equivalence_dich.

Section Equivalence_label_abstraction.

Context {P T Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context (outcome : T → Prop).

Context `{gLtsEqT : !gLtsEq T Ht} `{gLtsObaT : !gLtsOba T _} `{!gLtsObaFB T Atest}.
Context `{TP : !Testing_Predicate outcome gLtsEqT}.

Context `{gLtsEqP : !gLtsEq P (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))} `{FWP : !gLtsFWMem P Aproc Atest}.
Context `{SYP : !Prop_of_Inter P T (Aproc + MemAct Atest) Atest sync} `{CFIP : !coFiniteImagegLts P Atest}.

Context (𝔸 : Label_abstraction (Hp := ExtAction_sum) (SA := SyncAction_mem) P T).
Context `{DichP : !Dichotomic (Hp := ExtAction_sum) (SA := SyncAction_mem) P ρ[𝔸] }.

Context (tconv : list Atest → T) `{!test_convergence_spec tconv}.
Context (ta : gset (Atest / 𝔸) → list Atest → T)
        `{!test_co_acceptance_set_spec ta ρ[𝔸] }.

#[local] Existing Instance AbsActionG_of_LA.

Theorem equivalence_fw_label_abstraction (p q : P) :
  p ⊆ₘᵤₛₜᵢ q ↔ p ≼꜀ₒ₋ₐₛ[ ρ[𝔸] ] q.
Proof.
  exact (equivalence_fw_dich ρ[𝔸] outcome tconv ta p q).
Qed.

End Equivalence_label_abstraction.
(* end hide *)
