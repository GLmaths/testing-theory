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
From stdpp Require Import base tactics decidable gmultiset.
From TestingTheory Require Import ActTau gLts Subset_Act InteractionBetweenLts
  MultisetLTSConstruction ForwarderConstruction LabelAbstraction.

(* * Process-side label abstraction of a forwarder

   In [toFW(P)], the multiset accepts every blocking action whose dual is
   non-blocking, and emits the non-blocking actions it contains. Hence the
   relation of [P] is kept only between actions with the same blocking status
   whose duals are blocking; other actions are only related to themselves. *)

Definition LA_prog_FW {A : Type} {H : ExtAction A} (R : relation A) : relation A :=
  λ μ μ', μ = μ' ∨
    (R μ μ' ∧ (non_blocking μ ↔ non_blocking μ') ∧ blocking (co μ) ∧ blocking (co μ')).

Section LA_prog_FW.
  Context {P A : Type} {H : ExtAction A} {unique_nb : UniqueDual A} {gLtsP : gLts P H} {LAp : gLtsLAprog P H}
    `{!Prop_of_Inter P (MO A) A fw_inter}.

  Lemma LA_prog_FW_equivalence : Equivalence (LA_prog_FW (LA_prog P)).
  Proof.
    split.
    - intros μ. by left.
    - intros μ μ' [<- | (hR & hnb & b & b')]; [by left | right].
      split_and!; [by symmetry | by symmetry | done | done].
    - intros μ μ' μ'' [<- | (hR & hnb & b & b')] [<- | (hR' & hnb' & c & c')].
      + by left.
      + by right.
      + by right.
      + right. split_and!; [by etransitivity | by etransitivity | done | done].
  Qed.

  Lemma LA_prog_FW_dec : RelDecision (LA_prog_FW (LA_prog P)).
  Proof. intros μ μ'. unfold LA_prog_FW. apply _. Defined.

  Lemma LA_prog_FW_spec μ μ' :
    LA_prog_FW (LA_prog P) μ μ' → (co𝐏 μ : subset_of (P * MO A)) ⊆ co𝐏 μ'.
  Proof.
    intros [<- | (hR & hnb & bco & bco')]; [done |].
    intros [p m] (μ'' & duo & acc).
    apply lts_refuses_spec1 in acc as ((p', m') & tr).
    inversion tr as [? ? ? ? l | ? ? ? ? l |]; subst.
    - (* the process moves *)
      assert (p ∈ co𝐏 μ) as mem.
      { exists μ''. split; [done |]. eapply lts_refuses_spec2. by exists p'. }
      destruct (coP_preserved_by_LA_prog p μ μ' hR mem) as (μ3 & duo3 & acc3).
      apply lts_refuses_spec1 in acc3 as (p3 & tr3).
      exists μ3. split; [done |]. eapply lts_refuses_spec2.
      exists (p3, m'). by eapply ParLeft.
    - (* the multiset moves *)
      destruct (decide (non_blocking μ'')) as [nb | b].
      + exfalso. apply bco. symmetry in duo.
        by rewrite <- (unique_nb μ'' μ duo).
      + eapply blocking_action_in_ms in l as (_ & duo'' & nb''); [| exact b].
        rewrite <- (unique_nb μ μ'' duo) in nb''.
        apply hnb in nb''.
        exists (co μ'). split; [symmetry; exact (proj2_sig (exists_dual μ')) |].
        eapply lts_refuses_spec2. exists (p', {[+ μ' +]} ⊎ m).
        eapply ParRight. eapply lts_multiset_add; [| exact nb''].
        symmetry. exact (proj2_sig (exists_dual μ')).
  Qed.

  (** Like [PreActActionForFW]: a process-side label abstraction of [P] yields one of [toFW(P)]. *)
  Definition gLtsLAprog_FW : @gLtsLAprog (P * MO A) A H (toFW gLtsP) :=
    {| LA_prog := LA_prog_FW (LA_prog P);
       LA_prog_eq := LA_prog_FW_equivalence;
       LA_prog_dec := LA_prog_FW_dec;
       LA_prog_spec := LA_prog_FW_spec |}.

  (** The relation of [P] is kept unchanged when it relates distinct actions
      only if they have the same blocking status and blocking duals. *)
  Lemma LA_prog_FW_same :
    (∀ μ μ', LA_prog P μ μ' → μ ≠ μ' →
       (non_blocking μ ↔ non_blocking μ') ∧ blocking (co μ) ∧ blocking (co μ')) →
    ∀ μ μ', LA_prog_FW (LA_prog P) μ μ' ↔ LA_prog P μ μ'.
  Proof.
    intros cond μ μ'. split.
    - intros [<- | (hR & _)]; [reflexivity | done].
    - intros hR. destruct (decide (μ = μ')) as [<- | neq]; [by left | right].
      destruct (cond μ μ' hR neq) as (hnb & b & b'). by split_and!.
  Qed.
End LA_prog_FW.

(** Used as an instance only on state types of the form [_ * MO _]: a plain
    [Instance] would also match an unknown state type and loop. *)
#[global] Hint Extern 10 (@gLtsLAprog (_ * MO _) _ _ _) =>
  simple apply @gLtsLAprog_FW : typeclass_instances.
