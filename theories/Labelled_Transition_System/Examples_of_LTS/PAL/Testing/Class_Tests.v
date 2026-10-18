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
From stdpp Require Import base tactics decidable countable list gmap.
From TestingTheory Require Import ActTau gLts Bisimulation SyncActions Subset_Act RelationKernel
  Label_Abstraction.LabelAbstraction CompletenessASco TestSpecBridge
  PAL.Language.Syntax PAL.Language.LTS PAL.Language.Phi PAL.Language.Congruence PAL_Good
  PAL.Testing.Tests PAL.Testing.Test_Spec PAL.Language.Label_Abstraction.

#[local] Open Scope pal_scope.

#[local] Notation term := (term nat).
#[local] Notation PALA_Act := (PALA_Act nat).

Notation sum_list l := (foldr (λ e acc, ac_t nat e □ acc) 𝟘 l).

#[local] Hint Mode ExtAction ! : typeclass_instances.

(* The tests of De Nicola–Pugliese on the events of the classes. *)
Definition ta_𝔸 (E : gset (PALA_Act / 𝔸ᴘᴀʟ)) (s : list PALA_Act) : term :=
  ta nat (set_map (λ x, αᴛᴀᴘᴀʟ nat (`x)) E) s.

Lemma ev_in_classes (E : gset (PALA_Act / 𝔸ᴘᴀʟ)) μ :
  αᴛᴀᴘᴀʟ nat μ ∈ elements (set_map (λ x : PALA_Act / 𝔸ᴘᴀʟ, αᴛᴀᴘᴀʟ nat (`x)) E : gset (Event nat)) →
  ρ[𝔸ᴘᴀʟ] μ ∈ E.
Proof.
  intros h. apply elem_of_elements, elem_of_map in h as (x & e & hx).
  apply ρᴘᴀʟ_eq in e. rewrite e, class_of_repr_pal. exact hx.
Qed.

#[global] Instance ta_𝔸_spec : test_co_acceptance_set_spec ta_𝔸 ρ[𝔸ᴘᴀʟ].
Proof.
  split.
  - intros E. apply test_spec_of_plain. unfold ta_𝔸, ta.
    apply gen_test_spec; [apply sum_ac_closed | apply sum_ac_not_good].
  - intros E. apply no_step_refuses. apply sum_list_no_tau.
  - intros E η nb. destruct nb.
  - intros E β e _ h. apply sum_list_ext_inv in h as [hin _]. by apply ev_in_classes.
  - intros E x hx _.
    destruct (sum_list_step nat (elements (set_map (λ x : PALA_Act / 𝔸ᴘᴀʟ, αᴛᴀᴘᴀʟ nat (`x)) E
                                       : gset (Event nat))) (αᴛᴀᴘᴀʟ nat (`x)))
      as (μ & q & hq & he).
    { apply elem_of_elements. exact (elem_of_map_2 (λ x : PALA_Act / 𝔸ᴘᴀʟ, αᴛᴀᴘᴀʟ nat (`x)) E x hx). }
    exists q, μ. split; [exact hq |].
    rewrite <- (class_of_repr_pal x). by apply ρᴘᴀʟ_eq.
  - intros β e' E _ h. by apply sum_list_ext_inv in h as [_ ?].
Qed.
(* end hide *)
