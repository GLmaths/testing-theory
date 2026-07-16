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

From Stdlib.Program Require Import Equality.
From stdpp Require Import base countable finite gmap list.

From TestingTheory Require Import
  ActTau InputOutputActions InListPropHelper
  gLts Bisimulation coFiniteImage.
From TestingTheory Require Export VACCS.VACCS_Instance.

(** ** [coFiniteImagegLts] for VACCS — mirrors [VCCS_CoFiniteImage.v]
    verbatim (VACCS's [dual] is the same input/output swap
    [ext_act_match], and [lts_set_input]/[lts_set_output]/[lts_set_tau]
    have the same specs), just swapping the [VCCS_]/[proc]-via-[VP
    :VCCS_Parameters] names for [VACCS_]/[proc]-via-[VP:VACCS_Parameters].
    Kept in its own file for the same compile-memory reason (see
    [[vccs_cofiniteimage_debugging]]). *)

Section VACCS_CoFiniteImage.

Context `{VP : VACCS_Parameters}.

#[local] Instance VACCS_gLts_reexport : gLts proc VACCS_ExtAction :=
  @gLtsEq_gLts proc _ _ VACCS_gLtsEq.

Lemma vaccs_dual_image_in_iff (p : proc) (a : TypeOfActions) (q : proc) :
  (exists α' : ExtAct TypeOfActions, dual α' (ActIn a) /\ p ⟶[α'] q) <-> p ⟶[ActOut a] q.
Proof.
  split.
  - intros (α' & duo & tr). destruct α' as [x|x]; simpl in duo; [done|].
    assert (x = a) as -> by exact duo. exact tr.
  - intros tr. exists (ActOut a). split; [reflexivity | exact tr].
Qed.

Lemma vaccs_dual_image_out_iff (p : proc) (a : TypeOfActions) (q : proc) :
  (exists α' : ExtAct TypeOfActions, dual α' (ActOut a) /\ p ⟶[α'] q) <-> p ⟶[ActIn a] q.
Proof.
  split.
  - intros (α' & duo & tr). destruct α' as [x|x]; simpl in duo; [|done].
    assert (x = a) as -> by exact duo. exact tr.
  - intros tr. exists (ActIn a). split; [reflexivity | exact tr].
Qed.

(* [cofolts_tau_next_states_finite]'s goal is auto-resolved by [unshelve
   refine] itself: [VACCS_gLtsFiniteImage] already provides [Finite (dsig
   (fun q => p ⟶{α} q))] for every [α] including [τ]. Verified
   interactively (rocq-mcp): only 2 goals remain after [unshelve refine],
   in this order — [cofolts_next_states_decidable], then
   [cofolts_next_states_finite]. *)
#[global] Instance VACCS_gLtsCoFiniteImage : coFiniteImagegLts proc (ExtAct TypeOfActions).
Proof.
  unshelve refine {|
    cofolts_states_countable := proc_count;
    cofolts_tau_next_states_finite := _;
    cofolts_next_states_decidable := _;
    cofolts_next_states_finite := _;
  |}.
  - intros p α q. destruct α as [a|a].
    + destruct (decide (p ⟶[ActOut a] q)) as [Hd|Hd].
      * left. eapply vaccs_dual_image_in_iff. exact Hd.
      * right. intro Hc. eapply Hd. eapply vaccs_dual_image_in_iff. exact Hc.
    + destruct (decide (p ⟶[ActIn a] q)) as [Hd|Hd].
      * left. eapply vaccs_dual_image_out_iff. exact Hd.
      * right. intro Hc. eapply Hd. eapply vaccs_dual_image_out_iff. exact Hc.
  - intros p α. unfold dsig. destruct α as [a|a].
    + unshelve eapply (in_list_finite (elements (lts_set_output p a))).
      intros q Htrans%bool_decide_unpack.
      eapply elem_of_elements, lts_set_output_spec1, vaccs_dual_image_in_iff.
      exact Htrans.
    + unshelve eapply (in_list_finite (elements (lts_set_input p a))).
      intros q Htrans%bool_decide_unpack.
      eapply elem_of_elements, lts_set_input_spec1, vaccs_dual_image_out_iff.
      exact Htrans.
Defined.

End VACCS_CoFiniteImage.
