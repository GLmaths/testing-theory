(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>

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

Require ssreflect.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Wf Setoid.
Require Import Coq.Program.Equality.
From Coq.Logic Require Import ProofIrrelevance.
From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.
From Must Require Import ActTau InputOutputActions gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW FiniteImageLTS
            Subset_Act Must SoundnessAS CompletenessAS EquivalenceAS StateTransitionSystems
              GeneralizeLtsOutputs Termination WeakTransitions Convergence  
               InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction
               Testing_Predicate DefinitionAS DefinitionCI.

Lemma copre_if_prex
  `{@FiniteImagegLts A L HL LtsP, @FiniteImagegLts B L HL LtsQ}
  `{PreAP : @PreExtAction L HL A FinA PreA PreA_eq PreA_countable 𝝳 Φ LtsP}
  `{PreAQ : @PreExtAction L HL B FinA PreA PreA_eq PreA_countable 𝝳 Φ LtsQ}
  (ps : gset A) (q : B) : ps ≼ₓ q -> ps ⩽ q.
Proof.
  revert ps q.
  cofix H2.
  intros ps q (hsub1 & hsub2).
  constructor.
  - intros q' l. eapply H2, bhvx_preserved_by_reduction; eauto.
  - intros hterm hst.
    edestruct (hsub2 [] q) as (p' & hw & p'' & hstp' & stable & hsub0).
    eapply wt_nil. eassumption. intros p' mem. constructor.
    eapply hterm. eauto.
    exists p'. exists p''. repeat split; eauto.
  - intros μ q' ps' hcnv hw wtspec.
    eapply H2.
    eapply bhvx_preserved_by_external_action; eauto.
    intros p0 mem0.
    edestruct (hcnv p0 mem0); eauto.
  - intros. edestruct (hsub1 []); eauto.
    intros. constructor. eauto.
Qed.


