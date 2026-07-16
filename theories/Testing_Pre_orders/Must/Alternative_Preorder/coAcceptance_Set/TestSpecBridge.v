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

From stdpp Require Import gmap.
From TestingTheory Require Import gLts Bisimulation Testing_Predicate.
From TestingTheory Require Import Completeness.
From TestingTheory Require Import CompletenessASco.

(** ** Bridge between [Completeness.v]'s and [CompletenessASco.v]'s
    identically-named, field-for-field-identical [test_spec] /
    [test_convergence_spec] / [test_co_acceptance_set_spec] classes.

    [CompletenessASco.v]'s versions were ported from [Completeness.v] (same
    "co-acceptance-set" test machinery, unrelated to the co-*preorder*
    machinery this whole port is otherwise about — the name collision is
    coincidental) and kept the exact same field names, but as genuinely
    separate nominal [Class]es. Every calculus (VCCS/VACCS/ACCS/CCS) that
    already has a concrete witness for the [Completeness.v] versions (built
    once, for the non-co characterization) can reuse it for the co
    characterization *for free* via these three instances — no
    calculus-specific work needed. Found interactively via rocq-mcp: a
    calculus's own [ta]/[tconv] witness failed to satisfy
    [EquivalenceASco.v]'s [Section preorder] Context with a "Could not
    find an instance" error naming the [CompletenessASco]-qualified
    class, even though a structurally identical witness already existed.

    Field-by-field [destruct Hspec as [...]] rather than bare
    [exact test_ungood]-style projection access: since both classes'
    fields share literal names, a bare field name inside a proof building
    the *target* ([CompletenessASco]) record resolves to the target's own
    (not-yet-built) projection, not the source [Hspec]'s — a genuine
    ambiguity, not just a display quirk (confirmed via rocq-mcp: "Hspec
    has type Completeness.test_spec gen while it is expected to have type
    test_spec ?gen"). Destructuring into fresh local names sidesteps the
    ambiguity entirely. *)

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
  (Hspec : Completeness.test_co_acceptance_set_spec PreAct ta Γ)
  : CompletenessASco.test_co_acceptance_set_spec PreAct ta Γ.
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
