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
(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base tactics gmap gmultiset.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Subset_Act InputOutputActions
  InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction
  DefinitionAS Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic
  VACCS.Language.LTS VACCS.Language.gLts_Instance VACCS.Language.Label_Abstraction
  Erlang.Language.Syntax Erlang.Language.LTS Erlang.Language.gLts_Instance.

Section Erlang_Label_Abstraction.

Context `{EP : Erlang_Program}.

Lemma coR_erl (S : sys) (β : erl_act) : β ∈ coR S ↔ ∃ μ, μ ∈ dom (erl_mo S) ∧ β = co μ.
Proof.
  split.
  - intros (μ' & haccept & hduo & hb).
    destruct β as [a | a]; [| exfalso; apply hb; by exists a].
    symmetry in hduo. apply simplify_match_input in hduo as ->.
    apply lts_performs_spec1 in haccept as (T & hl).
    apply erl_out_shape in hl as (p & v & -> & ->).
    exists (out_act p v). split; [| done]. apply erl_out_dom. multiset_solver.
  - intros (μ & hμ & ->). apply erl_dom_out in hμ as (p & v & -> & hin).
    exists (out_act p v). repeat split.
    + apply lts_performs_spec2. exists (S ∖ ⟪p, v⟫).
      assert (S = ⟪p, v⟫ ⊎ (S ∖ ⟪p, v⟫)) as heq by multiset_solver.
      rewrite heq at 1. apply ErlOut.
    + by intros (a & heq).
Qed.

#[global] Instance 𝔸ᴇʀʟ : Label_abstraction (sys * MO erl_act) proc := 𝔸ᴠᴀᴄᴄꜱ_of _.

Definition coRₐ_erl (Sm : sys * MO erl_act) : gset (erl_act / 𝔸ᴇʀʟ) :=
  set_map (λ μ, ρ[𝔸ᴇʀʟ] (co μ)) (dom (erl_mo Sm.1))
  ∪ set_map (λ η, ρ[𝔸ᴇʀʟ] (co η)) (dom (MO_without_not_nb Sm.2)).

Lemma coRₐ_erl_spec (Sm : sys * MO erl_act) x : x ∈ coRₐ_erl Sm ↔ x ∈ ⌈ ρ[𝔸ᴇʀʟ] ⌉ (coR Sm).
Proof.
  destruct Sm as (S, m). unfold coRₐ_erl. simpl. rewrite elem_of_union, !elem_of_map. split.
  - intros [(μ & -> & hμ) | (η & -> & hη)].
    + exists (co μ). split; [| done]. apply coR_fw. left. apply coR_erl. by exists μ.
    + apply gmultiset_elem_of_dom in hη.
      assert (hη' : η ∈ (MO_without_not_nb (m : MO erl_act) : MO erl_act)) by exact hη.
      apply lts_MO_nb_with_nb_spec1 in hη' as (nb & hη').
      exists (co η). split; [| done]. apply coR_fw. right. by exists η.
  - intros (β & hβ & ->). apply coR_fw in hβ as [hβ | (η & nb & hη & ->)].
    + left. apply coR_erl in hβ as (μ & hμ & ->). by exists μ.
    + right. exists η. split; [done |].
      apply gmultiset_elem_of_dom.
      assert (h' : η ∈ (MO_without_not_nb (m : MO erl_act) : MO erl_act))
        by (by apply lts_MO_nb_with_nb_spec2).
      exact h'.
Qed.

#[global] Instance Finitary_𝔸ᴇʀʟ : Finitary_Label_abstraction (sys * MO erl_act) proc :=
  MkFLA _ proc _ _ _ _ _ _ _ 𝔸ᴇʀʟ coRₐ_erl coRₐ_erl_spec.

#[global] Instance Dichotomic_Erlang : Dichotomic (sys * MO erl_act) ρ[𝔸ᴇʀʟ] :=
  Decidable_dichotomic Finitary_𝔸ᴇʀʟ.

End Erlang_Label_Abstraction.
(* end hide *)
