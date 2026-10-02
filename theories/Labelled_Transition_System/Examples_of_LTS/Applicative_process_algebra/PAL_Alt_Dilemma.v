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
From stdpp Require Import base tactics countable gmap.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Testing_Predicate
  DefinitionAS CompletenessASco PAL_Syntax Applicative_process_algebra PAL_Label_Dilemma
  PAL_Label_Dilemma_Sync PAL_Alt_LTS PAL_Alt_Tau PAL_Alt_Congruence PAL_Good PAL_Alt_Tests PAL_Alt_TestSpec PAL_Alt_CoTraceHypotheses
  Subset_Act PAL_Alt_Abs.

(* * No finitary abstraction for the alternative LTS of PAL

   [PAL_Label_Dilemma_Sync.no_labelling_sync] instantiated with the
   alternative LTS ([PAL_Alt_LTS.v]) on both sides: processes and tests over
   [PALA_Act], meeting along [dual].  Whatever [Φ], [𝝳] and [gen],
   [FinitaryAbsAction] and [test_spec gen] cannot both hold.  The two
   hypotheses of the general theorem are discharged here: no action of
   [PALA_Act] is non-blocking, and the synchronisations along [dual] are
   those of PAL ([PAL_Alt_Tau.in_iff]/[out_iff]). *)

Section PAL_Alt_Dilemma.
  Context {Val : Type} `{Countable Val} (inj : nat → Val) `{!Inj eq eq inj}.

  Notation term := (PAL_Syntax.term Val).
  Notation old := (Applicative_process_algebra.lts_step Val).
  Notation new := (lts_step_a Val).

  (** The synchronisations of the alternative LTS are those of PAL. *)
  Lemma PALA_sync_iff (p t p' t' : term) :
    (∃ μ1 μ2 : PALA_Act Val, dual μ1 μ2 ∧ new p (ActExt μ1) p' ∧ new t (ActExt μ2) t')
      ↔ PAL_sync p t p' t'.
  Proof.
    split.
    - intros ([l1 | ot1] & [l2 | ot2] & hd & h1 & h2); simpl in hd; try done; subst.
      + eexists. left. split.
        * by apply (in_iff Val); exists l1.
        * by apply (out_iff Val).
      + eexists. right. split.
        * by apply (out_iff Val).
        * by apply (in_iff Val); exists l2.
    - intros (ot & [[h1 h2] | [h1 h2]]).
      + apply (in_iff Val) in h1 as (l & hl & h1). apply (out_iff Val) in h2.
        exists (AIn Val l), (AOut Val ot). by split_and!.
      + apply (out_iff Val) in h1. apply (in_iff Val) in h2 as (l & hl & h2).
        exists (AOut Val ot), (AIn Val l). by split_and!.
  Qed.

  Context {FinA PreAct : Type} `{Countable PreAct} (Φ : PALA_Act Val → FinA) (𝝳 : FinA → PreAct).
  Context (outcome : term → Prop) {TP : Testing_Predicate outcome (PALA_gLtsEq Val)}
    (gen : list (PALA_Act Val) → term).

  Theorem PALA_no_finitary_abstraction :
    @FinitaryAbsAction term term FinA PreAct (PALA_Act Val) (PALA_ExtAction Val) Φ 𝝳
      (PALA_Act Val) (PALA_ExtAction Val) (PALA_gLts Val) (PALA_gLtsEq Val) SyncAction_of_dual _ _ →
    @test_spec term (PALA_Act Val) (PALA_ExtAction Val) (PALA_gLtsEq Val) outcome TP gen →
    False.
  Proof.
    intros Fin TS.
    apply (no_labelling_sync (Val := Val) (TS := TS) (Fin := Fin) inj Φ 𝝳 outcome gen).
    - intros η [].
    - exact PALA_sync_iff.
  Qed.
End PAL_Alt_Dilemma.

(** With the tests of [PAL_Alt_Tests.v], which do satisfy [test_spec]
    ([PAL_Alt_CoTraceHypotheses.hyp_test_convergence_spec]): no [Φ], [𝝳] make
    the alternative LTS of PAL finitary — the one hypothesis that
    [PAL_Alt_CoTraceHypotheses.v] leaves open cannot be met. *)
Corollary PALA_not_finitary {Val : Type} `{Countable Val} `{!Inhabited Val}
  (inj : nat → Val) `{!Inj eq eq inj}
  {FinA PreAct : Type} `{Countable PreAct} (Φ : PALA_Act Val → FinA) (𝝳 : FinA → PreAct) :
  @FinitaryAbsAction (term Val) (term Val) FinA PreAct (PALA_Act Val) (PALA_ExtAction Val) Φ 𝝳
      (PALA_Act Val) (PALA_ExtAction Val) (PALA_gLts Val) (PALA_gLtsEq Val) SyncAction_of_dual _ _ → False.
Proof.
  intros Fin.
  exact (PALA_no_finitary_abstraction inj Φ 𝝳 (good_PAL Val) (t_conv Val) Fin
           (@tconv_test_spec _ _ _ _ _ _ _ (hyp_test_convergence_spec Val))).
Qed.

(** ** Modulo the join, [coR (in(?x).𝟘)] is still infinite

    [ρᴀʟᴛ] is the canonical projection of [LA_equiv R_prog_a R_test_a]
    ([PAL_Alt_Abs.ρᴀʟᴛ_proj]).  On outputs both [≈ᴛᴇꜱᴛ] and [≈ᴘʀᴏ] are
    equality, hence so is the join: [ρᴀʟᴛ (AOut ot) = POut ot].  The
    co-actions of [in(?x).𝟘] are all the [AOut ⟨v⟩], so no finite set
    contains [ρᴀʟᴛ (coR (in(?x).𝟘))]. *)
Lemma ρᴀʟᴛ_coR_p_formal_infinite {Val : Type} `{Countable Val} `{!Inhabited Val}
  (inj : nat → Val) `{!Inj eq eq inj} (X : gset (PreEvent Val)) :
  (∀ e, e ∈ (⌈ ρᴀʟᴛ Val ⌉ (coR (p_formal Val))) → e ∈ X) → False.
Proof.
  intros hX.
  apply (finite_pigeonhole X (λ n b, b = ρᴀʟᴛ Val (AOut Val (tuple1 Val (inj n))))).
  - intros n. eexists. split; [reflexivity |].
    apply hX. exists (AOut Val (tuple1 Val (inj n))). split; [apply coR_p_formal | done].
  - intros n m b -> e. cbn in e. injection e as e. apply (inj_iff inj). congruence.
Qed.
