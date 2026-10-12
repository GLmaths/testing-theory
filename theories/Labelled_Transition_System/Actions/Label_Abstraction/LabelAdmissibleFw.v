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

From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Relations.Relation_Definitions Classes.RelationClasses.
From stdpp Require Import base tactics decidable countable gmap gmultiset list.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Subset_Act
  InteractionBetweenLts MemAction InteractionUnion MemForwarder MultisetLTSConstruction ForwarderMem LiftMem
  LabelAbstraction LabelAdmissible.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Section Forwarder_coR.
  Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
  Context `{gLtsEqP : !gLtsEq P Hp}.
  Context `{PIP : !Prop_of_Inter P (MO (MemAct Atest)) Aproc (MemAct Atest) fw_inter_mem}.

  #[local] Existing Instance toFwEq.

  Lemma coR_fw_inv (p : P) (m : MO (MemAct Atest)) (β : Atest) :
    β ∈ coR (p, m) →
    β ∈ coR p ∨ ∃ η, msg η ∈ m ∧ non_blocking η ∧ dual η β.
  Proof.
    intros (a & acc & hs & b).
    apply lts_performs_spec1 in acc as (y & l).
    destruct a as [μ | [η | η]]; simpl in hs.
    - apply fw_inl_inv in l as (p' & -> & l). left.
      eapply coR_intro; [eapply lts_performs_spec2; by eexists | exact hs | exact b].
    - apply fw_msg_inv in l as (m' & -> & -> & nb). right.
      exists η. split_and!; [multiset_solver | exact nb | exact hs].
    - apply fw_cobar_inv in l as [_ nb]. subst. contradiction.
  Qed.

  Lemma coR_fw_intro_l (p : P) (m : MO (MemAct Atest)) (β : Atest) :
    β ∈ coR p → β ∈ coR (p, m).
  Proof.
    intros (μ & acc & hs & b). apply lts_performs_spec1 in acc as (p' & l).
    exists (inl μ). split_and!; [| exact hs | exact b].
    eapply lts_performs_spec2. exists (p', m). by apply fw_inl.
  Qed.

  Lemma coR_fw_intro_r (p : P) (m : MO (MemAct Atest)) (η β : Atest) :
    msg η ∈ m → non_blocking η → dual η β → β ∈ coR (p, m).
  Proof.
    intros hm nb d.
    rewrite (gmultiset_disj_union_difference' (msg η) m hm).
    exists (inr (msg η)). split_and!.
    - eapply lts_performs_spec2. eexists. by apply fw_give.
    - exact d.
    - apply (dual_blocks β η nb). by symmetry.
  Qed.
End Forwarder_coR.

Section Forwarder_admissible.
  Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
  Context `{gLtsEqP : !gLtsEq P Hp}.
  Context `{PIP : !Prop_of_Inter P (MO (MemAct Atest)) Aproc (MemAct Atest) fw_inter_mem}.
  Context `{gLtsT : !gLts T Ht}.
  Context (R : relation Atest).

  #[local] Existing Instance toFwEq.

  Definition LA_admissible_mem : Prop :=
    ∀ η β β'', non_blocking η → dual η β'' → blocking β → R β β'' →
      ∃ u, dual η u ∧ (𝐏 β : subset_of T) ⊆ 𝐏 u.

  Lemma LA_admissible_fw :
    LA_admissible P T R → LA_admissible_mem →
    @LA_admissible (P * MO (MemAct Atest)) T (Aproc + MemAct Atest) ExtAction_sum _
      Atest Ht _ SyncAction_mem R.
  Proof.
    intros admP admM [p m] β β'' b h mem.
    destruct (coR_fw_inv p m β'' mem) as [memp | (η & hm & nb & d)].
    - destruct (admP p β β'' b h memp) as (u & hu & hP).
      exists u. split; [by apply coR_fw_intro_l | exact hP].
    - destruct (admM η β β'' nb d b h) as (u & du & hP).
      exists u. split; [by eapply coR_fw_intro_r | exact hP].
  Qed.

  Context `{!Equivalence R} `{!RelDecision R}.
  Context (co_rep : Atest → list Atest).
  Context (co_rep_sub : ∀ η x, non_blocking η → x ∈ co_rep η → dual η x).
  Context (co_rep_cover : ∀ η β, non_blocking η → dual η β → ∃ x, x ∈ co_rep η ∧ R β x).

  Definition mem_reps (m : MO (MemAct Atest)) : list Atest :=
    elements m ≫= (λ a, match a with
                        | msg η => if decide (non_blocking η) then co_rep η else []
                        | cobar _ => []
                        end).

  Lemma mem_reps_spec (m : MO (MemAct Atest)) x :
    x ∈ mem_reps m → ∃ η, msg η ∈ m ∧ non_blocking η ∧ dual η x.
  Proof.
    unfold mem_reps. rewrite list_elem_of_bind. intros (a & hx & ha).
    apply gmultiset_elem_of_elements in ha.
    destruct a as [η | η]; [| by apply not_elem_of_nil in hx].
    destruct (decide (non_blocking η)) as [nb | nnb]; [| by apply not_elem_of_nil in hx].
    exists η. split_and!; [exact ha | exact nb | by apply co_rep_sub].
  Qed.

  Lemma mem_reps_cover (m : MO (MemAct Atest)) η β :
    msg η ∈ m → non_blocking η → dual η β → ∃ x, x ∈ mem_reps m ∧ R β x.
  Proof.
    intros hm nb d. destruct (co_rep_cover η β nb d) as (x & hx & hR).
    exists x. split; [| exact hR].
    unfold mem_reps. rewrite list_elem_of_bind. exists (msg η).
    split; [by rewrite decide_True | by apply gmultiset_elem_of_elements].
  Qed.

  Definition FinitaryLA_fw (finP : FinitaryLA P R) :
    @FinitaryLA (P * MO (MemAct Atest)) (Aproc + MemAct Atest) ExtAction_sum _
      Atest Ht SyncAction_mem R _ _.
  Proof.
    refine {| coR_absR pm := coR_absR pm.1 ∪ list_to_set (LA_class R <$> mem_reps pm.2) |}.
    intros [p m] x. simpl. rewrite elem_of_union, elem_of_list_to_set, list_elem_of_fmap.
    split.
    - intros [hx | (r & -> & hr)].
      + apply coR_absR_spec in hx as (β & hβ & <-). exists β.
        split; [by apply coR_fw_intro_l | reflexivity].
      + destruct (mem_reps_spec m r hr) as (η & hm & nb & d).
        exists r. split; [by eapply coR_fw_intro_r | reflexivity].
    - intros (β & hβ & <-). destruct (coR_fw_inv p m β hβ) as [hp | (η & hm & nb & d)].
      + left. apply coR_absR_spec. by exists β.
      + right. destruct (mem_reps_cover m η β hm nb d) as (x & hx & hR).
        exists x. split; [by apply (LA_class_proj R) | exact hx].
  Defined.
End Forwarder_admissible.
(* end hide *)
