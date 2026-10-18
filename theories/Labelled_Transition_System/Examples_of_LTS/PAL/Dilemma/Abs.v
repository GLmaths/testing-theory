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
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base tactics decidable countable list gmap relations.
From TestingTheory Require Import ActTau gLts Subset_Act Label_Abstraction.LabelAbstraction PAL.Language.Syntax PAL.Language.LTS
  PAL.Language.Phi PAL.Language.Delta.
(* * Condition (2) of [AbsAction] on the alternative LTS of PAL

   - [prog_spec_injective]: any [κ] on events satisfying the process-side
     condition (2) of [AbsAction] is injective on the events [EvOut ⟨v⟩], all
     of which lie in [αᴛᴇꜱᴛ(coR (in(?x).𝟘))] ([coR_p_formal]); so [κ(αᴛᴇꜱᴛ(coR p))] is
     infinite as soon as [Val] is. *)

Section PAL_Alt_Abs.
  Context (Val : Type) `{Countable Val} `{!Inhabited Val}.

  Notation term := (term Val).
  Notation eot := (eot Val).
  Notation template := (template Val).
  Notation label := (label Val).
  Notation ltemplate := (ltemplate Val).
  Notation ltuple := (ltuple Val).
  Notation PALA_Act := (PALA_Act Val).
  Notation Event := (Event Val).
  Notation R_test_a := (R_test_a Val).
  Notation R_prog_a := (R_prog_a Val).

  (* Infer the action type of [↛[μ]] from the LTS on terms. *)
  #[local] Hint Mode ExtAction ! : typeclass_instances.
  Open Scope pal_scope.


  (* ** Condition (2) forces an injective abstraction of outputs *)

  Definition tuple1 (v : Val) : eot := [of_val v].

  (* [in(?x).𝟘] and [in(!v).𝟘] *)
  Definition p_formal : term := in( [? 0] ) • 𝟘.
  Definition p_val (v : Val) : term := in( [! ve_val v] ) • 𝟘.

  Lemma coR_p_formal v : AOut _ (tuple1 v) ∈ (coR p_formal : subset_of PALA_Act).
  Proof.
    exists (AIn _ [lf_formal Val v]). split_and!; [| done | intros []].
    apply PALA_performs_spec2. eexists. by apply aar1.
  Qed.

  Lemma coR_p_val v : AOut _ (tuple1 v) ∈ (coR (p_val v) : subset_of PALA_Act).
  Proof.
    exists (AIn _ [lf_val Val v]). split_and!; [| done | intros []].
    apply PALA_performs_spec2. eexists. by apply aar1.
  Qed.

  Lemma coR_p_val_only v μ : μ ∈ (coR (p_val v) : subset_of PALA_Act) → μ = AOut _ (tuple1 v).
  Proof.
    intros (μ2 & acc & hd & _). apply lts_performs_spec1 in acc as (q & hq).
    unfold p_val in hq. cbn in hq. inversion hq; subst.
    match goal with hev : eval_in_tuple _ = Some _ |- _ => cbn in hev; injection hev as <- end.
    match goal with ht : template_of _ _ = _ |- _ =>
      destruct l as [|[w|w|] [|]]; cbn in ht; try discriminate; injection ht as -> end.
    destruct μ as [l'|ot]; cbn in hd; [contradiction |]. by subst.
  Qed.

  Theorem prog_spec_injective {B : Type} (κ : Event → B) :
    (∀ (p : term) (β β' : PALA_Act), κ (αᴛᴀᴘᴀʟ Val β) = κ (αᴛᴀᴘᴀʟ Val β') →
       αᴛᴀᴘᴀʟ Val β ∈ (⌈ αᴛᴀᴘᴀʟ Val ⌉ (coR p)) → αᴛᴀᴘᴀʟ Val β' ∈ (⌈ αᴛᴀᴘᴀʟ Val ⌉ (coR p))) →
    ∀ v w, κ (EvOut _ (tuple1 v)) = κ (EvOut _ (tuple1 w)) → v = w.
  Proof.
    intros h2 v w e.
    assert (αᴛᴀᴘᴀʟ Val (AOut _ (tuple1 w)) ∈ (⌈ αᴛᴀᴘᴀʟ Val ⌉ (coR (p_val v)))) as (x & hx & ex).
    { apply (h2 (p_val v) (AOut _ (tuple1 v))); [exact e |].
      exists (AOut _ (tuple1 v)). split; [apply coR_p_val | done]. }
    apply coR_p_val_only in hx. subst x. cbn in ex. injection ex. congruence.
  Qed.

  (* All the [EvOut ⟨v⟩] lie in [αᴛᴇꜱᴛ(coR (in(?x).𝟘))]. *)
  Lemma αᴛᴇꜱᴛ_coR_p_formal v : EvOut _ (tuple1 v) ∈ (⌈ αᴛᴀᴘᴀʟ Val ⌉ (coR p_formal)).
  Proof. exists (AOut _ (tuple1 v)). split; [apply coR_p_formal | done]. Qed.

End PAL_Alt_Abs.
(* end hide *)
