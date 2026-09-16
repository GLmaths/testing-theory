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

(** * Core Erlang: the label abstraction

    The observers are VACCS processes ([Erlang_Must_Characterization]), so the
    abstraction is theirs: [Φᴠᴀᴄᴄꜱ (ActIn (c,v)) = Inputs c] forgets the value
    and keeps the channel — here, the target pid.  It is the /test/ side that
    fixes [Φ]: an input prefix [c?(x).P] accepts every value on [c], so no
    observer can accept one value and refuse another.

    An Erlang [receive] could tell them apart, its patterns being able to be
    literal values; against VACCS observers that finer power is unobservable,
    and the acceptance sets record only /which pids/ a system can send to.

    [abstraction_test_spec] does not mention the processes at all, so VACCS's
    proof is reused as it stands; [abstraction_prog_spec] is trivial because
    [𝝳ᴠᴀᴄᴄꜱ] is the identity — which is also why the [Admitted] instance
    [PreActActionForFW] of [DefinitionAS.v] is not needed here. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list numbers finite sets gmap gmultiset.
From TestingTheory Require Import ActTau InputOutputActions gLts Bisimulation
  Lts_OBA Subset_Act DefinitionAS VACCS VACCS_Instance
  Erlang_Syntax Erlang_LTS Erlang_Instance.

Section Erlang_LabelAbstraction.

Context `{EP : Erlang_Program}.

(** ** The abstraction of VACCS is one for Erlang *)

#[global] Program Instance Erl_AbsAction :
  @AbsAction sys proc FinA PreAct erl_act VACCS_ExtAction Φᴠᴀᴄᴄꜱ 𝝳ᴠᴀᴄᴄꜱ _ VACCS_gLtsEq.
Next Obligation.
  (* the test side is the one of VACCS, which does not mention the processes *)
  intros t β β' hb hb' heq hmem.
  eapply (@abstraction_test_spec proc proc FinA PreAct erl_act VACCS_ExtAction
            Φᴠᴀᴄᴄꜱ 𝝳ᴠᴀᴄᴄꜱ _ VACCS_gLtsEq AbsVACCS t β β'); eassumption.
Qed.
Next Obligation.
  (* [𝝳ᴠᴀᴄᴄꜱ] is the identity, so the hypothesis /is/ the conclusion *)
  intros S β β' _ _ heq hmem. unfold 𝝳ᴠᴀᴄᴄꜱ in heq. by rewrite <- heq.
Qed.

(** ** It is finitary: the abstracted co-actions are the targets of the
    messages in transit *)

Definition coR_abs_erl (S : sys) : gset PreAct :=
  set_map (λ ξ, 𝝳ᴠᴀᴄᴄꜱ (Φᴠᴀᴄᴄꜱ ξ)) (dom (erl_mo S)).

Lemma coR_abs_erl_spec S pre_μ :
  pre_μ ∈ coR_abs_erl S ↔ ∃ p v, pre_μ = Inputs (cst p) ∧ CMsg p v ∈ S.
Proof.
  unfold coR_abs_erl. split.
  - intros (ξ & -> & hin)%elem_of_map_1.
    apply erl_dom_out in hin as (p & v & -> & hmem). by exists p, v.
  - intros (p & v & -> & hmem).
    apply (elem_of_map_2_alt _ _ (out_act p v)); [by apply erl_out_dom | done].
Qed.

#[global] Program Instance Erl_FinitaryAbsAction :
  @FinitaryAbsAction sys proc FinA PreAct erl_act VACCS_ExtAction Φᴠᴀᴄᴄꜱ 𝝳ᴠᴀᴄᴄꜱ _ VACCS_gLtsEq _ _ :=
  {| coR_abs := coR_abs_erl |}.
Next Obligation.
  intros S pre_μ hmem.
  apply coR_abs_erl_spec in hmem as (p & v & -> & hin).
  exists (in_act p v). split; [| done].
  exists (out_act p v). repeat split.
  - apply lts_refuses_spec2. exists (S ∖ ⟪p, v⟫).
    assert (S = ⟪p, v⟫ ⊎ (S ∖ ⟪p, v⟫)) as heq by multiset_solver.
    rewrite heq at 1. apply ErlOut.
  - by intros (a & heq).
Qed.
Next Obligation.
  intros pre_μ S (μ & (μ' & haccept & hduo & hb) & ->).
  apply coR_abs_erl_spec.
  destruct μ as [a | a]; [| exfalso; apply hb; by exists a].
  symmetry in hduo. apply simplify_match_input in hduo as ->.
  apply lts_refuses_spec1 in haccept as (T & hl).
  apply erl_out_shape in hl as (p & v & -> & ->).
  exists p, v. split; [done | multiset_solver].
Qed.

End Erlang_LabelAbstraction.
