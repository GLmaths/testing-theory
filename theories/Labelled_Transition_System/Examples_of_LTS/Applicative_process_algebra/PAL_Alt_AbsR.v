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
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base tactics decidable countable list gmap.
From TestingTheory Require Import ActTau gLts Subset_Act DefinitionAS
  PAL_Syntax PAL_Alt_LTS PAL_Alt_Congruence PAL_Alt_Phi PAL_Alt_Delta PAL_Alt_AbsAction.

(* * The abstraction of PAL for a characterisation on [R p]

   Written as if the [R]-based framework existed: the acceptance set of a
   process is the abstraction of its own actions, [⌈𝝳ᴿ ∘ Φᴿ⌉ (R p)], and not
   of its co-actions.
   - [Φᴿ] is [Φᴀᴘᴀʟ], the event of a label: [EvIn tp] for an input with
     template [tp], [EvOut ot] for an output of [ot] (the events [(i, p)] and
     [(o, ot)] of De Nicola–Pugliese);
   - [𝝳ᴿ] is the identity on events: for PAL the events are already the right
     granularity, and [𝝳ᴿ ∘ Φᴿ] is the canonical projection of [≈ᴛᴇꜱᴛ]
     ([Φ_kernel]).
   Results:
   - [R_abs_spec]: the acceptance set is the finite set [R_abs p];
   - [abs_prog_spec_R]: the process-side condition, for [Φᴿ];
   - [abs_test_spec_R]: the test-side condition, for [𝝳ᴿ];
   - [dual_event_in], [dual_event_out]: how a test label sees the events of
     the process it synchronises with, which is what t4 needs. *)

Section PAL_Alt_AbsR.
  Context (Val : Type) `{Countable Val} (Inh : Inhabited Val).
  #[local] Existing Instance Inh.

  Notation term := (term Val).
  Notation eot := (eot Val).
  Notation template := (template Val).
  Notation ltemplate := (ltemplate Val).
  Notation ltuple := (ltuple Val).
  Notation PALA_Act := (PALA_Act Val).
  Notation Event := (Event Val).

  (** Infer the action type of [↛[μ]] from the LTS on terms. *)
  #[local] Hint Mode ExtAction ! : typeclass_instances.

  (** ** [Φᴿ] on the actions of a process, [𝝳ᴿ] on the events *)

  Definition Φᴿ (μ : PALA_Act) : Event := Φᴀᴘᴀʟ Val μ.
  Definition 𝝳ᴿ (e : Event) : Event := e.

  (** ** The acceptance set is finite *)

  Definition R_abs (p : term) : gset Event := abs_R Val p.

  Lemma R_abs_spec p e : e ∈ R_abs p ↔ e ∈ ⌈ 𝝳ᴿ ∘ Φᴿ ⌉ (R p).
  Proof.
    unfold R_abs, 𝝳ᴿ, Φᴿ. split.
    - intros (μ & hμ & he)%(@abs_R_spec Val _ _ Inh p e). exists μ. split; [exact hμ | symmetry; exact he].
    - intros (μ & hμ & he). apply (@abs_R_spec Val _ _ Inh p e). exists μ. split; [exact hμ | symmetry; exact he].
  Qed.

  (** The two obligations of a finitary abstraction, on [R p]. *)
  Lemma R_abs_spec1 p e : e ∈ R_abs p → e ∈ ⌈ 𝝳ᴿ ∘ Φᴿ ⌉ (R p).
  Proof. apply R_abs_spec. Qed.

  Lemma R_abs_spec2 e p : e ∈ ⌈ 𝝳ᴿ ∘ Φᴿ ⌉ (R p) → e ∈ R_abs p.
  Proof. apply R_abs_spec. Qed.

  (** So the acceptance set is finite: it is the [gset] [R_abs p]. *)
  Lemma R_abs_finite p : ∃ X : gset Event, ∀ e, e ∈ ⌈ 𝝳ᴿ ∘ Φᴿ ⌉ (R p) ↔ e ∈ X.
  Proof. exists (R_abs p). intros e. symmetry. apply R_abs_spec. Qed.

  (** ** The two conditions *)

  (** Process side: two labels with the same event are accepted by the same
      processes ([Φ_kernel] even gives the converse). *)
  Lemma abs_prog_spec_R (p : term) μ μ' : Φᴿ μ = Φᴿ μ' → μ ∈ R p → μ' ∈ R p.
  Proof. intros e h. exact (Φ_test_spec Val p μ μ' e h). Qed.

  (** Test side: [𝝳ᴿ] separates the events, so the condition is trivial. *)
  Lemma abs_test_spec_R (t : term) β β' :
    𝝳ᴿ (Φᴿ β) = 𝝳ᴿ (Φᴿ β') → Φᴿ β ∈ ⌈ Φᴿ ⌉ (coR t) → Φᴿ β' ∈ ⌈ Φᴿ ⌉ (coR t).
  Proof. unfold 𝝳ᴿ. intros e h. by rewrite <- e. Qed.

  (** ** What a test label says about the events of its partner

      A test label is dual to the actions of the process it synchronises with.
      [AOut ot] is dual to every input receiving [ot], whatever its template;
      [AIn l] only to the output of [ltuple l]. *)

  Lemma dual_event_out (ot : eot) μ :
    PALA_dual Val μ (AOut Val ot) ↔ ∃ l, μ = AIn Val l ∧ ltuple l = ot.
  Proof.
    destruct μ as [l|ot']; simpl.
    - split; [intros <-; by exists l | intros (l' & e & he); by injection e as <-].
    - split; [done | intros (l & e & _); discriminate].
  Qed.

  (** The event of such a label is the template of the receiver. *)
  Lemma dual_event_out_Φ (ot : eot) μ :
    PALA_dual Val μ (AOut Val ot) → ∃ tp, Φᴿ μ = EvIn Val tp.
  Proof. intros (l & -> & _)%dual_event_out. by exists (ltemplate l). Qed.

  Lemma dual_event_in (l : label Val) μ :
    PALA_dual Val μ (AIn Val l) ↔ μ = AOut Val (ltuple l).
  Proof.
    destruct μ as [l'|ot]; simpl.
    - split; [done | discriminate].
    - split; [by intros <- | by injection 1 as <-].
  Qed.

  (** The event of such a label is the tuple received. *)
  Lemma dual_event_in_Φ (l : label Val) μ :
    PALA_dual Val μ (AIn Val l) → Φᴿ μ = EvOut Val (ltuple l).
  Proof. intros ->%dual_event_in. done. Qed.
End PAL_Alt_AbsR.
