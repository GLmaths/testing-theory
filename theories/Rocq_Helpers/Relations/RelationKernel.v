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
From Stdlib.Logic Require Import ConstructiveEpsilon.
From stdpp Require Import base tactics countable.

Section Kernel_definitions.
  Context {A : Type}.

  Definition sym_part (R : relation A) : relation A := λ μ μ', R μ μ' ∧ R μ' μ.

  Definition rel_comp (R S : relation A) : relation A := λ μ ν, ∃ u, R μ u ∧ S u ν.

  (* Pay attention : equivalence kernel / kernel pair (categorie theory) *)
  (* Pay attention : symetrical quotient with S^{-1} / allegorie ? (categorie theory) , see Relational Mathematics from Gunther Schmidt *)

  Definition rel_ker (S : relation A) : relation A := λ μ μ', ∀ ν, S μ ν ↔ S μ' ν.

  Definition LA_S (Rt Rp : relation A) : relation A := λ μ ν, ∃ u, sym_part Rt μ u ∧ Rp u ν.

  Definition LA_S2 (Rt RpP RpQ : relation A) : relation A :=
    λ μ ν, LA_S Rt RpP μ ν ∧ LA_S Rt RpQ μ ν.

  Definition LA_K (Rt RpP RpQ : relation A) : relation A := rel_ker (LA_S2 Rt RpP RpQ).
End Kernel_definitions.

Notation "R ⨾ S" := (rel_comp R S) (at level 40, left associativity).
Notation "'Ker' S" := (rel_ker S) (at level 10).

Section Kernel.
  Context {A : Type}.

  Lemma rel_ker_equivalence (S : relation A) : Equivalence (rel_ker S).
  Proof.
    split.
    - intros μ ν. done.
    - intros μ μ' h ν. symmetry. apply h.
    - intros μ μ' μ'' h1 h2 ν. etransitivity; [apply h1 | apply h2].
  Qed.

  Lemma rel_ker_sub (S : relation A) : Reflexive S → ∀ μ μ', rel_ker S μ μ' → S μ μ'.
  Proof. intros hr μ μ' h. by apply h. Qed.

  Lemma sym_part_equivalence (R : relation A) `{!PreOrder R} : Equivalence (sym_part R).
  Proof.
    split.
    - intros μ. split; reflexivity.
    - intros μ μ' [h1 h2]. by split.
    - intros μ μ' μ'' [h1 h2] [h3 h4]. split; by etransitivity.
  Qed.
End Kernel.

Section Join.
  Context {A : Type} (Rt Rp : relation A).

  Lemma LA_S_left `{!PreOrder Rt} μ μ' ν : sym_part Rt μ μ' → LA_S Rt Rp μ' ν → LA_S Rt Rp μ ν.
  Proof.
    intros [h1 h2] (u & [h3 h4] & hp). exists u. split; [split; by etransitivity | done].
  Qed.

  Lemma LA_S_right `{!Transitive Rp} μ u ν : LA_S Rt Rp μ u → Rp u ν → LA_S Rt Rp μ ν.
  Proof. intros (w & hw & hp) h. exists w. split; [done | by etransitivity]. Qed.

  Lemma LA_S_refl `{!Reflexive Rt, !Reflexive Rp} μ : LA_S Rt Rp μ μ.
  Proof. exists μ. split; [split | ]; reflexivity. Qed.
End Join.

Section Kernel2.
  Context {A : Type} (Rt RpP RpQ : relation A).

  Lemma LA_K_equivalence : Equivalence (LA_K Rt RpP RpQ).
  Proof. apply rel_ker_equivalence. Qed.

  Context `{!PreOrder Rt, !PreOrder RpP, !PreOrder RpQ}.

  Lemma LA_K_sub μ μ' : LA_K Rt RpP RpQ μ μ' → LA_S2 Rt RpP RpQ μ μ'.
  Proof. apply rel_ker_sub. intros μ0. split; exists μ0; (split; [split | ]); reflexivity. Qed.

  Lemma LA_test_K μ μ' : sym_part Rt μ μ' → LA_K Rt RpP RpQ μ μ'.
  Proof.
    intros he ν. assert (he' : sym_part Rt μ' μ) by (destruct he; by split).
    split; intros [hP hQ]; split; eapply LA_S_left; eassumption.
  Qed.

  Lemma LA_K_largest (R : relation A) `{!Equivalence R} :
    (∀ μ μ', sym_part Rt μ μ' → R μ μ') →
    (∀ μ μ', R μ μ' → LA_S2 Rt RpP RpQ μ μ') →
    ∀ μ μ', R μ μ' → LA_K Rt RpP RpQ μ μ'.
  Proof.
    intros htest hsub.
    assert (dir : ∀ μ1 μ2 ν, R μ1 μ2 → LA_S2 Rt RpP RpQ μ2 ν → LA_S2 Rt RpP RpQ μ1 ν).
    { intros μ1 μ2 ν h [(u & hu & hp) (u' & hu' & hq)]. split.
      - apply (LA_S_right Rt RpP μ1 u ν); [| exact hp].
        apply (hsub μ1 u). etransitivity; [exact h | by apply htest].
      - apply (LA_S_right Rt RpQ μ1 u' ν); [| exact hq].
        apply (hsub μ1 u'). etransitivity; [exact h | by apply htest]. }
    intros μ μ' h ν. split; intros hs.
    - apply (dir μ' μ); [by symmetry | exact hs].
    - apply (dir μ μ'); [exact h | exact hs].
  Qed.

  Lemma LA_K_iff μ μ' :
    LA_K Rt RpP RpQ μ μ' ↔
      (∀ u, sym_part Rt μ' u → LA_S2 Rt RpP RpQ μ u) ∧ (∀ u, sym_part Rt μ u → LA_S2 Rt RpP RpQ μ' u).
  Proof.
    assert (half : ∀ μ1 μ2 ν, (∀ u, sym_part Rt μ2 u → LA_S2 Rt RpP RpQ μ1 u) →
                   LA_S2 Rt RpP RpQ μ2 ν → LA_S2 Rt RpP RpQ μ1 ν).
    { intros μ1 μ2 ν hm [(u & hu & hp) (u' & hu' & hq)]. split.
      - exact (LA_S_right Rt RpP μ1 u ν (proj1 (hm u hu)) hp).
      - exact (LA_S_right Rt RpQ μ1 u' ν (proj2 (hm u' hu')) hq). }
    split.
    - intros h. split; intros u hu.
      + apply (h u). split; exists u; (split; [exact hu | reflexivity]).
      + apply (h u). split; exists u; (split; [exact hu | reflexivity]).
    - intros [h1 h2] ν. split; intros hs.
      + exact (half μ' μ ν h2 hs).
      + exact (half μ μ' ν h1 hs).
  Qed.
End Kernel2.

(* * Canonical projections (independent of any LTS) *)

(* [f] is the canonical projection of [R]. *)
Class LA_proj {A B : Type} (R : relation A) (f : A → B) :=
  LA_proj_spec μ μ' : f μ = f μ' ↔ R μ μ'.

(* Each class of [f] has a representative. *)
Class LA_surj {A B : Type} (f : A → B) :=
  MkLA_surj {
    LA_repr : B → A;
    LA_repr_spec x : f (LA_repr x) = x;
  }.

Lemma proj_equivalence {A B : Type} (R : relation A) (f : A → B) :
  LA_proj R f → Equivalence R.
Proof.
  intros spec. split.
  - intros μ. by apply spec.
  - intros μ μ' h. apply spec. symmetry. by apply spec.
  - intros μ μ' μ'' h h'. apply spec. transitivity (f μ'); by apply spec.
Qed.

(* A relation with a canonical projection into a type with decidable equality is decidable. *)
Lemma proj_rel_dec {A B : Type} `{EqDecision B} (R : relation A) (f : A → B) :
  LA_proj R f → RelDecision R.
Proof.
  intros spec μ μ'. destruct (decide (f μ = f μ')) as [h|h].
  - left. by apply spec.
  - right. intros h'. apply h, spec, h'.
Qed.

(* * Constructive canonical surjection

    For a decidable equivalence [R] on a countable type, the representative of
    a class is its element of least index ([encode_nat]); the quotient is the
    type of representatives. No axiom is used. *)
Section Canonical.
  Context {A : Type} `{Countable A} (R : relation A) `{!Equivalence R} `{!RelDecision R}.

  Definition canon_pred (μ : A) (n : nat) : Prop := ∃ x, decode_nat n = Some x ∧ R x μ.

  Lemma canon_pred_dec μ n : {canon_pred μ n} + {¬ canon_pred μ n}.
  Proof.
    unfold canon_pred. destruct (decode_nat n) as [x|].
    - destruct (decide (R x μ)) as [h|h].
      + left. by exists x.
      + right. intros (y & [= <-] & h'). done.
    - right. by intros (y & ? & _).
  Defined.

  Lemma canon_pred_ex μ : ∃ n, canon_pred μ n.
  Proof. exists (encode_nat μ), μ. split; [apply decode_encode_nat | reflexivity]. Qed.

  (* The least index of an element of the class of [μ]. *)
  Definition canon_index (μ : A) : nat :=
    proj1_sig (epsilon_smallest (canon_pred μ) (canon_pred_dec μ) (canon_pred_ex μ)).

  Lemma canon_index_spec μ :
    canon_pred μ (canon_index μ) ∧ ∀ k, canon_pred μ k → canon_index μ ≤ k.
  Proof. unfold canon_index. destruct (epsilon_smallest _ _ _) as [n h]. exact h. Qed.

  (* The representative of the class of [μ]. *)
  Definition canon (μ : A) : A :=
    match decode_nat (canon_index μ) with Some x => x | None => μ end.

  Lemma canon_related μ : R (canon μ) μ.
  Proof.
    unfold canon. destruct (canon_index_spec μ) as ((x & eq & h) & _).
    by rewrite eq.
  Qed.

  Lemma canon_index_class μ μ' : R μ μ' → canon_index μ = canon_index μ'.
  Proof.
    intros h.
    assert (∀ n, canon_pred μ n ↔ canon_pred μ' n) as iff.
    { intros n. unfold canon_pred.
      split; intros (x & ? & hx); exists x; split;
        [done | by transitivity μ | done | transitivity μ'; [done | by symmetry]]. }
    destruct (canon_index_spec μ) as (h1 & min1), (canon_index_spec μ') as (h2 & min2).
    apply Nat.le_antisymm; [apply min1, iff, h2 | apply min2, iff, h1].
  Qed.

  Lemma canon_kernel μ μ' : canon μ = canon μ' ↔ R μ μ'.
  Proof.
    split.
    - intros eq. transitivity (canon μ); [symmetry; apply canon_related |].
      rewrite eq. apply canon_related.
    - intros h. unfold canon. rewrite (canon_index_class μ μ' h).
      destruct (canon_index_spec μ') as ((x & eq & _) & _). by rewrite eq.
  Qed.

  Lemma canon_idempotent μ : canon (canon μ) = canon μ.
  Proof. apply canon_kernel, canon_related. Qed.

  (* The quotient: the type of representatives. *)
  Definition LA_quotient : Type := dsig (λ x, canon x = x).

  (* The canonical surjection. *)
  Definition LA_class (μ : A) : LA_quotient := dexist (canon μ) (canon_idempotent μ).

  (* Not global instances, to keep instance search predictable. *)
  Lemma LA_class_proj : LA_proj R LA_class.
  Proof.
    intros μ μ'. rewrite <- canon_kernel. unfold LA_class, LA_quotient. split.
    - intros h. by apply (f_equal proj1_sig) in h.
    - intros h. by apply dsig_eq.
  Qed.

  Definition LA_class_surj : LA_surj LA_class.
  Proof.
    refine {| LA_repr q := `q |}.
    intros [x h]. apply dsig_eq. simpl. by apply bool_decide_unpack in h.
  Defined.
End Canonical.

Notation "A / R" := (LA_quotient (A := A) R) (at level 40, left associativity) : type_scope.

Notation "ρ[ R ]" := (LA_class R) (at level 0, format "ρ[ R ]").
(* end hide *)
