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
From TestingTheory Require Export VCCS.VCCS_Instance.

(** ** [coFiniteImagegLts] for VCCS

    Kept in its own file (not added directly to [VCCS_Instance.v]) purely
    for compile-memory reasons: [VCCS_Instance.v] is already large enough
    that adding these three obligations in place pushed a single-process
    compile past the environment's ~11GB ceiling. Importing the already-
    compiled [VCCS_Instance] and adding the instance here instead avoids
    re-elaborating the whole file in one process.

    [dual] on VCCS's [ExtAct TypeOfActions] is the input/output swap
    ([ext_act_match], InputOutputActions.v) — for a fixed [α], the
    dual-image set collapses to a single literal successor set:
    dual-image at [ActIn a] = literal [ActOut a] successors
    ([lts_set_output p a]), dual-image at [ActOut a] = literal [ActIn a]
    successors ([lts_set_input p a]). *)

Section VCCS_CoFiniteImage.

Context `{VP : VCCS_Parameters}.

(* Typeclass search struggles to find [gLts proc VCCS_ExtAction] via the
   [gLtsEq_gLts] projection alone from outside [VCCS_Instance.v]'s own
   section (where [VCCS_gLts] is a directly-named local — [VCCS_gLts]
   itself is [Local], so inaccessible here). A directly-named re-export
   fixes it. *)
#[local] Instance VCCS_gLts_reexport : gLts proc VCCS_ExtAction :=
  @gLtsEq_gLts proc _ _ VCCS_gLtsEq.

Lemma vccs_dual_image_in_iff (p : proc) (a : TypeOfActions) (q : proc) :
  (exists α' : ExtAct TypeOfActions, dual α' (ActIn a) /\ p ⟶[α'] q) <-> p ⟶[ActOut a] q.
Proof.
  split.
  - intros (α' & duo & tr). destruct α' as [x|x]; simpl in duo; [done|].
    assert (x = a) as -> by exact duo. exact tr.
  - intros tr. exists (ActOut a). split; [reflexivity | exact tr].
Qed.

Lemma vccs_dual_image_out_iff (p : proc) (a : TypeOfActions) (q : proc) :
  (exists α' : ExtAct TypeOfActions, dual α' (ActOut a) /\ p ⟶[α'] q) <-> p ⟶[ActIn a] q.
Proof.
  split.
  - intros (α' & duo & tr). destruct α' as [x|x]; simpl in duo; [|done].
    assert (x = a) as -> by exact duo. exact tr.
  - intros tr. exists (ActIn a). split; [reflexivity | exact tr].
Qed.

(* [cofolts_tau_next_states_finite]'s goal is auto-resolved by [unshelve
   refine] itself: [VCCS_gLtsFiniteImage] (VCCS_Instance.v) already
   provides [Finite (dsig (fun q => p ⟶{α} q))] for every [α : Act
   TypeOfActions] including [τ], and [p ⟶{τ} q] is definitionally [p ⟶
   q] — so typeclass search finds it directly, no tactic needed. Verified
   interactively (rocq-mcp): only 2 goals remain after [unshelve refine],
   in this order — [cofolts_next_states_decidable], then
   [cofolts_next_states_finite] (not the textual field order). *)
#[global] Instance VCCS_gLtsCoFiniteImage : coFiniteImagegLts proc (ExtAct TypeOfActions).
Proof.
  unshelve refine {|
    cofolts_states_countable := proc_count;
    cofolts_tau_next_states_finite := _;
    cofolts_next_states_decidable := _;
    cofolts_next_states_finite := _;
  |}.
  - intros p α q. destruct α as [a|a].
    + destruct (decide (p ⟶[ActOut a] q)) as [Hd|Hd].
      * left. eapply vccs_dual_image_in_iff. exact Hd.
      * right. intro Hc. eapply Hd. eapply vccs_dual_image_in_iff. exact Hc.
    + destruct (decide (p ⟶[ActIn a] q)) as [Hd|Hd].
      * left. eapply vccs_dual_image_out_iff. exact Hd.
      * right. intro Hc. eapply Hd. eapply vccs_dual_image_out_iff. exact Hc.
  - intros p α. unfold dsig. destruct α as [a|a].
    + unshelve eapply (in_list_finite (elements (lts_set_output p a))).
      intros q Htrans%bool_decide_unpack.
      eapply elem_of_elements, lts_set_output_spec1, vccs_dual_image_in_iff.
      exact Htrans.
    + unshelve eapply (in_list_finite (elements (lts_set_input p a))).
      intros q Htrans%bool_decide_unpack.
      eapply elem_of_elements, lts_set_input_spec1, vccs_dual_image_out_iff.
      exact Htrans.
Defined.

End VCCS_CoFiniteImage.
