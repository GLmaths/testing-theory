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
               Testing_Predicate DefinitionAS DefinitionCI SetLTSConstruction.



Lemma copre_if_prex `{
  gLtsP : @gLts P A H, !FiniteImagegLts P A, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳 gLtsP gLtsT,
  gLtsQ : @gLts Q A H, !FiniteImagegLts Q A, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳 gLtsQ gLtsT}
  (ps : gset P) (qs : gset Q) : ps ≼ₛₑₜ_ₐₛ qs -> ps ⩽ qs.
Proof.
  revert ps qs.
  cofix H2.
  intros ps qs (hsub1 & hsub2).
  constructor.
  - intros q' l. eapply H2, bhvx_preserved_by_reductions; eauto. split; eauto.
  - intros hterm q' mem' hst.
    edestruct (hsub2 q' [] q' mem') as (p' & hw & p'' & hstp' & stable & hsub0).
    + eapply wt_nil.
    + eassumption.
    + intros p' mem. constructor. eapply termination_if_termination_set_helper; eauto.
    + exists p'. split. eauto. exists p''. repeat split; eauto.
  - intros μ q' ps' hcnv hw wtspec.
    eapply H2. eapply bhvx_preserved_by_external_action; eauto.
    + eapply cnv_terminate in hcnv. eapply termination_if_termination_set_helper;eauto.
    + split; eauto.
  - intros. eapply termination_set_for_all. 
    assert ((forall p, p ∈ ps -> p ⇓ []) -> (forall q, q ∈ qs -> q ⇓ [])) as Hyp_acc_1.
    { exact (hsub1 []). }
    erewrite<- equiv_termination in H0.
    assert (∀ p : P, p ∈ ps → p ⇓ []) as conv_ps.
    { eapply convergence_forall_if_convergence_set;eauto. }
    intros. eapply Hyp_acc_1 in conv_ps;eauto. eapply equiv_termination; eauto.
Qed.
