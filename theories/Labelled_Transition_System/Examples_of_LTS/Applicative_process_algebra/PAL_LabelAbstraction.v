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
From stdpp Require Import base tactics countable option.
From TestingTheory Require Import ActTau gLts Subset_Act InputOutputActions
  LabelAbstraction PAL_Syntax Applicative_process_algebra.

(* * Label abstractions of PAL

   Every PAL action is singled out by a term: [in(t)•𝟘] and [out(t)•𝟘], where
   [t] has only exact values and wildcards, accept exactly one input and emit
   exactly one output. Hence equality is the only sound relation, on the test
   side as well as on the process side ([PAL_LA_test_maximal],
   [PAL_LA_prog_maximal]). *)

Section PAL_LA.
  Context (Val : Type) `{Countable Val}.

  Notation term := (term Val).
  Notation PAL_Act := (PAL_Act Val).

  #[local] Existing Instance PAL_gLts.

  (** ** The relations: equality *)

  #[global] Instance gLtsLAtest_PAL : @gLtsLAtest term PAL_Act (PAL_ExtAction Val) (PAL_gLts Val) :=
    {| LA_test := eq;
       LA_test_eq := eq_equivalence;
       LA_test_dec := λ μ μ', decide (μ = μ');
       LA_test_spec := λ μ μ' h, match h with eq_refl => λ _ h', h' end |}.

  #[global] Instance gLtsLAprog_PAL : @gLtsLAprog term PAL_Act (PAL_ExtAction Val) (PAL_gLts Val) :=
    {| LA_prog := eq;
       LA_prog_eq := eq_equivalence;
       LA_prog_dec := λ μ μ', decide (μ = μ');
       LA_prog_spec := λ μ μ' h, match h with eq_refl => λ _ h', h' end |}.

  (** ** Terms singling out an action *)

  Definition eot_to_eit (ot : eot Val) : eit Val :=
    map (λ of, match of with of_val v => if_val v | of_star => if_star end) ot.

  Lemma eval_in_eot_to_tuple (ot : eot Val) : eval_in_tuple (eot_to_tuple ot) = Some (eot_to_eit ot).
  Proof.
    induction ot as [|[|v] ot IH]; [done | |]; unfold eval_in_tuple in *; simpl; by rewrite IH.
  Qed.

  Lemma eval_out_eot_to_tuple (ot : eot Val) : eval_out_tuple (eot_to_tuple ot) = Some ot.
  Proof.
    induction ot as [|[|v] ot IH]; [done | |]; unfold eval_out_tuple in *; simpl; by rewrite IH.
  Qed.

  Lemma tuple_match_eot_to_eit (ot ot' : eot Val) : tuple_match (eot_to_eit ot) ot' ↔ ot' = ot.
  Proof.
    split.
    - revert ot'. induction ot as [|f ot IH]; intros ot' h; inversion h as [| f1 f2 it ot'' hf ht]; subst.
      + done.
      + f_equal; [| by apply IH].
        destruct f; simpl in hf; by inversion hf.
    - intros ->. induction ot as [|[|v] ot IH]; simpl; constructor; [constructor | done | constructor | done].
  Qed.

  Definition single_in (ot : eot Val) : term := t_in (eot_to_tuple ot) (t_nil).
  Definition single_out (ot : eot Val) : term := t_out (eot_to_tuple ot) (t_nil).

  Lemma single_in_accepts ot : ¬ single_in ot ↛[ActIn ot].
  Proof.
    apply lts_refuses_spec2.
    exists (subst_term (build_subst (eot_to_eit ot) ot) (t_nil)).
    apply ar1; [apply eval_in_eot_to_tuple | by apply tuple_match_eot_to_eit].
  Qed.

  Lemma single_in_only ot μ : ¬ single_in ot ↛[μ] → μ = ActIn ot.
  Proof.
    intros acc. apply lts_refuses_spec1 in acc as (q & tr).
    change (Applicative_process_algebra.lts_step Val (single_in ot) (ActExt μ) q) in tr.
    inversion tr; subst.
    match goal with
    | ev : eval_in_tuple _ = Some _, hm : tuple_match _ _ |- _ =>
        rewrite eval_in_eot_to_tuple in ev; injection ev as <-;
        apply tuple_match_eot_to_eit in hm; by subst
    end.
  Qed.

  Lemma single_out_accepts ot : ¬ single_out ot ↛[ActOut ot].
  Proof.
    apply lts_refuses_spec2. exists (t_nil).
    apply ar3, eval_out_eot_to_tuple.
  Qed.

  Lemma single_out_only ot μ : ¬ single_out ot ↛[μ] → μ = ActOut ot.
  Proof.
    intros acc. apply lts_refuses_spec1 in acc as (q & tr).
    change (Applicative_process_algebra.lts_step Val (single_out ot) (ActExt μ) q) in tr.
    inversion tr; subst.
    match goal with
    | ev : eval_out_tuple _ = Some _ |- _ =>
        rewrite eval_out_eot_to_tuple in ev; by injection ev as <-
    end.
  Qed.

  (** ** Equality is the only sound relation *)

  Lemma PAL_𝐏_incl (μ μ' : PAL_Act) : (𝐏 μ : subset_of term) ⊆ 𝐏 μ' → μ = μ'.
  Proof.
    intros incl. destruct μ as [ot|ot].
    - symmetry. apply (single_in_only ot), (incl (single_in ot)), single_in_accepts.
    - symmetry. apply (single_out_only ot), (incl (single_out ot)), single_out_accepts.
  Qed.

  Lemma PAL_LA_test_maximal (R : relation PAL_Act) :
    (∀ μ μ', R μ μ' → (𝐏 μ : subset_of term) ⊆ 𝐏 μ') → ∀ μ μ', R μ μ' → μ = μ'.
  Proof. intros sound μ μ' h. by apply PAL_𝐏_incl, sound. Qed.

  Lemma PAL_co𝐏_incl (μ μ' : PAL_Act) : (co𝐏 μ : subset_of term) ⊆ co𝐏 μ' → μ = μ'.
  Proof.
    intros incl.
    assert (∀ (ν : PAL_Act) (p : term), p ∈ co𝐏 ν ↔ p ∈ 𝐏 (comp_act Val ν)) as co_iff.
    { intros [a|a] p; split.
      - intros (μ'' & duo & acc). symmetry in duo.
        first [apply simplify_match_input in duo | apply simplify_match_output in duo].
        by subst.
      - intros acc. exists (comp_act Val (ActIn a)). split; [done | done].
      - intros (μ'' & duo & acc). symmetry in duo.
        first [apply simplify_match_input in duo | apply simplify_match_output in duo].
        by subst.
      - intros acc. exists (comp_act Val (ActOut a)). split; [done | done]. }
    assert (comp_act Val μ = comp_act Val μ') as eq.
    { apply PAL_𝐏_incl. intros p acc. apply co_iff, incl, co_iff, acc. }
    destruct μ, μ'; simpl in eq; congruence.
  Qed.

  Lemma PAL_LA_prog_maximal (R : relation PAL_Act) :
    (∀ μ μ', R μ μ' → (co𝐏 μ : subset_of term) ⊆ co𝐏 μ') → ∀ μ μ', R μ μ' → μ = μ'.
  Proof. intros sound μ μ' h. by apply PAL_co𝐏_incl, sound. Qed.
End PAL_LA.
