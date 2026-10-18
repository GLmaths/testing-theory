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
From stdpp Require Import base tactics countable gmap.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Testing_Predicate
  DefinitionAS CompletenessASco PAL.Language.Syntax PAL.Language.Paper_LTS PAL.Dilemma.Label_Dilemma
  PAL.Dilemma.Label_Dilemma_Sync PAL.Language.LTS PAL.Language.Paper_Correspondence PAL.Language.Congruence PAL_Good PAL.Testing.Tests PAL.Testing.Test_Spec PAL.Testing.CoTrace_Hypotheses
  Subset_Act RelationKernel Label_Abstraction.LabelAbstraction PAL.Dilemma.Abs PAL.Language.Label_Abstraction.
(* * No finitary abstraction for the alternative LTS of PAL

   [PAL.Dilemma.Label_Dilemma_Sync.no_labelling_sync] instantiated with the
   alternative LTS ([PAL.Language.LTS]) on both sides: processes and tests over
   [PALA_Act], meeting along [dual].  Whatever [αᴛᴇꜱᴛ], [αᴘʀᴏ] and [gen],
   [FinitaryAbsAction] and [test_spec gen] cannot both hold.  The two
   hypotheses of the general theorem are discharged here: no action of
   [PALA_Act] is non-blocking, and the synchronisations along [dual] are
   those of PAL ([PAL.Language.Paper_Correspondence.in_iff]/[out_iff]). *)

Section PAL_Alt_Dilemma.
  Context {Val : Type} `{Countable Val} (inj : nat → Val) `{!Inj eq eq inj}.

  Notation term := (PAL.Language.Syntax.term Val).
  Notation old := (PAL.Language.Paper_LTS.pal_step Val).
  Notation new := (lts_step_a Val).

  (* The synchronisations of the alternative LTS are those of PAL. *)
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

  Context {FinA PreAct : Type} `{Countable PreAct} (αᴛᴇꜱᴛ : PALA_Act Val → FinA) (αᴘʀᴏ : FinA → PreAct).
  Context (outcome : term → Prop) {TP : Testing_Predicate outcome (PALA_gLtsEq Val)}
    (gen : list (PALA_Act Val) → term).

  Theorem PALA_no_finitary_abstraction :
    FinitaryAbsAction (Aproc := (PALA_Act Val)) (Hp := (PALA_ExtAction Val)) (gLtsP := (PALA_gLts Val)) (gLtsT := (PALA_gLtsEq Val)) (SA := SyncAction_of_dual) term term αᴛᴇꜱᴛ αᴘʀᴏ →
    test_spec (gLtsT := PALA_gLtsEq Val) gen →
    False.
  Proof.
    intros Fin TS.
    apply (no_labelling_sync (Val := Val) (TS := TS) (Fin := Fin) inj αᴛᴇꜱᴛ αᴘʀᴏ outcome gen).
    - intros η [].
    - exact PALA_sync_iff.
  Qed.
End PAL_Alt_Dilemma.

(* With the tests of [PAL.Testing.Tests], which do satisfy [test_spec]
    ([PAL.Testing.CoTrace_Hypotheses.hyp_test_convergence_spec]): no [αᴛᴇꜱᴛ], [αᴘʀᴏ] make
    the alternative LTS of PAL finitary — the one hypothesis that
    [PAL.Testing.CoTrace_Hypotheses] leaves open cannot be met. *)
Corollary PALA_not_finitary {Val : Type} `{Countable Val} `{!Inhabited Val}
  (inj : nat → Val) `{!Inj eq eq inj}
  {FinA PreAct : Type} `{Countable PreAct} (αᴛᴇꜱᴛ : PALA_Act Val → FinA) (αᴘʀᴏ : FinA → PreAct) :
  FinitaryAbsAction (Aproc := (PALA_Act Val)) (Hp := (PALA_ExtAction Val)) (gLtsP := (PALA_gLts Val)) (gLtsT := (PALA_gLtsEq Val)) (SA := SyncAction_of_dual) (term Val) (term Val) αᴛᴇꜱᴛ αᴘʀᴏ → False.
Proof.
  intros Fin.
  exact (PALA_no_finitary_abstraction inj αᴛᴇꜱᴛ αᴘʀᴏ (good_PAL Val) (t_conv Val) Fin
           (@tconv_test_spec _ _ _ _ _ _ _ (hyp_test_convergence_spec Val))).
Qed.

Lemma ρᴘᴀʟ_coR_p_formal_infinite (X : gset (PALA_Act nat / 𝔸ᴘᴀʟ)) :
  (∀ x, x ∈ ⌈ ρ[𝔸ᴘᴀʟ] ⌉ (coR (p_formal nat)) → x ∈ X) → False.
Proof.
  intros hX.
  apply (finite_pigeonhole X (λ n x, x = ρ[𝔸ᴘᴀʟ] (AOut nat (tuple1 nat n)))).
  - intros n. eexists. split; [reflexivity |].
    apply hX. exists (AOut nat (tuple1 nat n)). split; [apply coR_p_formal | done].
  - intros n m x -> e. apply ρᴘᴀʟ_eq in e. cbn in e. by injection e.
Qed.

(* end hide *)
