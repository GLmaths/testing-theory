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
From stdpp Require Import base tactics decidable countable gmap.
From TestingTheory Require Import ActTau gLts SyncActions Subset_Act Label_Abstraction.LabelAbstraction.

Class Dichotomic (P : Type) {Ap At PreA : Type} {Hp : ExtAction Ap} {Ht : ExtAction At}
  {gLtsP : gLts P Hp} {SA : SyncAction Ap At} (Γ : At → PreA) :=
  coR_dichotomy (p q : P) : p ↛ → q ↛ →
    (⌈ Γ ⌉ (coR p) ⊆ ⌈ Γ ⌉ (coR q))
    + { x | x ∈ ⌈ Γ ⌉ (coR p) ∧ x ∉ ⌈ Γ ⌉ (coR q) }.

Section Decidable_dichotomic.
  Context {P Ap At PreA : Type} {Hp : ExtAction Ap} {Ht : ExtAction At}
    {gLtsP : gLts P Hp} {SA : SyncAction Ap At}
    `{Countable PreA} (Γ : At → PreA).

  Definition Dichotomic_of_finite
    (coRΓ : P → gset PreA) (hspec : ∀ p x, x ∈ coRΓ p ↔ x ∈ ⌈ Γ ⌉ (coR p)) :
    Dichotomic P Γ.
  Proof.
    intros p q _ _. destruct (decide (coRΓ p ⊆ coRΓ q)) as [sub | nsub].
    - left. intros x hx. apply hspec, sub, hspec, hx.
    - right. destruct (elements (coRΓ p ∖ coRΓ q)) as [| x l] eqn:e.
      + exfalso. apply nsub. intros x hx. destruct (decide (x ∈ coRΓ q)) as [| n]; [done |].
        assert (x ∈ elements (coRΓ p ∖ coRΓ q)) as m by (apply elem_of_elements; set_solver).
        rewrite e in m. inversion m.
      + exists x. assert (x ∈ coRΓ p ∖ coRΓ q) as m.
        { apply elem_of_elements. rewrite e. constructor. }
        apply elem_of_difference in m as [m1 m2].
        split; [by apply hspec | intros hq; apply m2, hspec, hq].
  Defined.
End Decidable_dichotomic.

#[global] Instance Decidable_dichotomic {P T Ap At : Type} {Hp : ExtAction Ap} {Ht : ExtAction At}
  {gLtsP : gLts P Hp} {gLtsT : gLts T Ht} {SA : SyncAction Ap At}
  (F : Finitary_Label_abstraction P T) : Dichotomic P ρ[𝔸 (Finitary_Label_abstraction := F)] :=
  Dichotomic_of_finite _ coRₐ coRₐ_spec.
(* end hide *)
