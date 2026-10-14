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

From Stdlib.Unicode Require Import Utf8.

From stdpp Require Import base decidable sets.

From TestingTheory Require Import ActTau gLts SyncActions Subset_Act WeakTransitions
    Convergence Termination DefinitionAS DefinitionQ.
(* begin hide *)
Lemma wt_stabilise `{gLts P A} (p q : P) s :
  p ⇓ s -> p ⟹[s] q -> ∃ q', p ⟹[s] q' /\ q' ↛.
Proof.
  intros hcnv hw.
  destruct (terminate_then_wt_refuses q) as (q' & hw' & hst).
  - exact (cnv_iff_prefix_terminate_l p s hcnv s q (reflexivity s) hw).
  - exists q'. split; [eapply wt_push_nil_right; eassumption | exact hst].
Qed.

Lemma quiescent_pre_of_bhv_pre `{
  gLtsP : @gLts P A H, AbsPT : @AbsAction P T FinA PreAct A H Φ 𝝳P _ _ _ gLtsT _,
  gLtsQ : @gLts Q A H, AbsQT : @AbsAction Q T FinA PreAct A H Φ 𝝳Q _ _ _ gLtsT _}
  (p : P) (q : Q) :
  (∀ s, is_trace q s -> p ⇓ s) -> p ≼ₐₛ q -> q ⊑ǫ p.
Proof.
  intros hcnv (hpre1 & hpre2). split.
  - intros s (q' & hw).
    assert (p ⇓ s) as hp by (eapply hcnv; now exists q').
    destruct (wt_stabilise q q' s (hpre1 s hp) hw) as (q'' & hw'' & hst).
    destruct (hpre2 s q'' hp hw'' hst) as (p' & hwp & _ & _).
    now exists p'.
  - intros s (q' & hw & hst & hempty).
    assert (p ⇓ s) as hp by (eapply hcnv; now exists q').
    destruct (hpre2 s q' hp hw hst) as (p' & hwp & hstp & hsub).
    exists p'. split; [exact hwp | split; [exact hstp | ]].
    intros β. split; [| set_solver].
    intros hβ.
    assert ((𝝳P ∘ Φ) β ∈ ⌈ 𝝳Q ∘ Φ ⌉ (coR q')) as (β' & hβ' & _)
      by (eapply hsub, map_gamma_of_action, hβ).
    eapply hempty in hβ'. set_solver.
Qed.
(* end hide *)
