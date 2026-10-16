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

From stdpp Require Import gmap.
From TestingTheory Require Import gLts Bisimulation Testing_Predicate.
From TestingTheory Require Import Completeness.
From TestingTheory Require Import CompletenessASco.
(* ** Bridge between [Completeness.v]'s and [CompletenessASco.v]'s *)

#[global] Instance test_spec_of_plain
  {T A} `{H0 : @gLtsEq T A H} `{!Testing_Predicate outcome _}
  {gen : list A -> T}
  (Hspec : Completeness.test_spec gen)
  : CompletenessASco.test_spec gen.
Proof.
  destruct Hspec as [tu tn tt tr tf ts].
  unshelve econstructor.
  - exact tu.
  - exact tn.
  - exact tt.
  - exact tr.
  - intros; eapply tf; eassumption.
  - intros; eapply ts; eassumption.
Defined.

#[global] Instance test_co_acceptance_set_spec_of_plain
  {PreAct T A} `{CC : Countable PreAct} `{H0 : @gLtsEq T A H} `{!Testing_Predicate outcome _}
  {ta : gset PreAct -> list A -> T} {Γ : A -> PreAct}
  (Hspec : Completeness.test_co_acceptance_set_spec ta Γ)
  : CompletenessASco.test_co_acceptance_set_spec ta Γ.
Proof.
  destruct Hspec as [tts tdt tdnba taig thrt ttg].
  unshelve econstructor.
  - intro E. exact (test_spec_of_plain (tts E)).
  - exact tdt.
  - exact tdnba.
  - exact taig.
  - exact thrt.
  - exact ttg.
Defined.

#[global] Instance test_convergence_spec_of_plain
  {T A} `{H0 : @gLtsEq T A H} `{!Testing_Predicate outcome _}
  {tconv : list A -> T}
  (Hspec : Completeness.test_convergence_spec tconv)
  : CompletenessASco.test_convergence_spec tconv.
Proof.
  destruct Hspec as [ts tdea tcc tctg].
  unshelve econstructor.
  - exact (test_spec_of_plain ts).
  - exact tdea.
  - exact tcc.
  - exact tctg.
Defined.