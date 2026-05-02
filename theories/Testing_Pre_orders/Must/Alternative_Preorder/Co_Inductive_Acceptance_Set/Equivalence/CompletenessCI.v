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

From Stdlib Require ssreflect.
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From Stdlib.Program Require Import Equality Wf.
From Stdlib.Wellfounded Require Import Inverse_Image.
From Stdlib Require Import Setoid.
From Stdlib .Logic Require Import ProofIrrelevance.

From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.

From TestingTheory Require Import ActTau InputOutputActions gLts Bisimulation Lts_OBA Lts_OBA_FB Lts_FW FiniteImageLTS
            Subset_Act Must Soundness Completeness Equivalence StateTransitionSystems
              Termination WeakTransitions Convergence  
               InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction ParallelLTSConstruction
               Testing_Predicate DefinitionAS DefinitionCI.


(*
Lemma copre_if_prex
  `{@FiniteImagegLts P A H gLtsP, @FiniteImagegLts Q A H gLtsQ}
  `{PreAP : @PreExtAction P A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsP}
  `{PreAQ : @PreExtAction Q A H FinA PreA PreA_eq PreA_countable 𝝳 Φ gLtsQ}
  (ps : gset P) (q : Q) : ps ≼ₓ q -> ps ⩽ q.
Proof.
  revert ps q.
  cofix H2.
  intros ps q (hsub1 & hsub2).
  constructor.
  - intros q' l. eapply H2, bhvx_preserved_by_reduction; eauto. split; eauto.
  - intros hterm hst.
    edestruct (hsub2 [] q) as (p' & hw & p'' & hstp' & stable & hsub0).
    eapply wt_nil. eassumption. intros p' mem. constructor.
    eapply hterm. eauto.
    exists p'. exists p''. repeat split; eauto.
  - intros μ q' ps' hcnv hw wtspec.
    eapply H2.
    eapply bhvx_preserved_by_external_action; eauto.
    intros p0 mem0.
    edestruct (hcnv p0 mem0); eauto. split; eauto.
  - intros. edestruct (hsub1 []); eauto.
    intros. constructor. eauto.
Qed.

*)
