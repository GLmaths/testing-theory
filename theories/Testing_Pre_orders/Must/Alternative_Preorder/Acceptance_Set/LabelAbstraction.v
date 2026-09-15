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
From Stdlib Require Import Relations.Relation_Definitions Classes.RelationClasses Classes.Morphisms.
From Stdlib.Logic Require Import ConstructiveEpsilon.
From stdpp Require Import base tactics finite gmap decidable relations countable.
From TestingTheory Require Import ActTau gLts Bisimulation Subset_Act.

(* * Label abstractions as equivalences on actions *)

(** ** LTSs equipped with a test-side label abstraction *)
Class gLtsLAtest (T : Type) {A : Type} (H : ExtAction A) {gLtsT : gLts T H} :=
  MkgLtsLAtest {
    LA_test : A → A → Prop;
    LA_test_eq : Equivalence LA_test;
    LA_test_dec : RelDecision LA_test;
    (** Related actions are accepted by the same tests. *)
    LA_test_spec μ μ' : LA_test μ μ' → (𝐏 μ : subset_of T) ⊆ 𝐏 μ';
  }.

Arguments gLtsLAtest T {_} H {_}.
Arguments LA_test T {_ _ _ _} μ μ'.

Notation "μ ≈ᴛᴇꜱᴛ μ'" := (LA_test _ μ μ') (at level 70).

#[global] Instance LA_test_equivalence `{gLtsLAtest T A} : Equivalence (LA_test T).
Proof. exact LA_test_eq. Defined.

#[global] Instance LA_test_decision `{gLtsLAtest T A} : RelDecision (LA_test T).
Proof. exact LA_test_dec. Defined.

(** ** LTSs equipped with a process-side label abstraction *)
Class gLtsLAprog (P : Type) {A : Type} (H : ExtAction A) {gLtsP : gLts P H} :=
  MkgLtsLAprog {
    LA_prog : A → A → Prop;
    LA_prog_eq : Equivalence LA_prog;
    LA_prog_dec : RelDecision LA_prog;
    (** Co-actions of related actions are offered by the same processes. *)
    LA_prog_spec μ μ' : LA_prog μ μ' → (co𝐏 μ : subset_of P) ⊆ co𝐏 μ';
  }.

Arguments gLtsLAprog P {_} H {_}.
Arguments LA_prog P {_ _ _ _} μ μ'.

Notation "μ ≈ᴘʀᴏ μ'" := (LA_prog _ μ μ') (at level 70).

#[global] Instance LA_prog_equivalence `{gLtsLAprog P A} : Equivalence (LA_prog P).
Proof. exact LA_prog_eq. Defined.

#[global] Instance LA_prog_decision `{gLtsLAprog P A} : RelDecision (LA_prog P).
Proof. exact LA_prog_dec. Defined.

(** ** Properties of test-side label abstractions *)
Section LA_test_properties.
  Context {T A : Type} {H : ExtAction A} {gLtsT : gLts T H} {LAt : gLtsLAtest T H}.

  Lemma accepts_preserved_by_LA_test (t : T) μ μ' :
    μ ≈ᴛᴇꜱᴛ μ' → ¬ t ↛[μ] → ¬ t ↛[μ'].
  Proof. intros eq. exact (LA_test_spec μ μ' eq t). Qed.

  Lemma accepts_LA_test_iff (t : T) μ μ' :
    μ ≈ᴛᴇꜱᴛ μ' → ¬ t ↛[μ] ↔ ¬ t ↛[μ'].
  Proof. intros eq. split; apply accepts_preserved_by_LA_test; [done | by symmetry]. Qed.

  Lemma refuses_preserved_by_LA_test (t : T) μ μ' :
    μ ≈ᴛᴇꜱᴛ μ' → t ↛[μ] → t ↛[μ'].
  Proof.
    intros eq refuses. destruct (decide (t ↛[μ'])) as [| accepts]; [done |].
    exfalso. eapply (accepts_preserved_by_LA_test t μ' μ); [by symmetry | exact accepts | exact refuses].
  Qed.

  Lemma refuses_LA_test_iff (t : T) μ μ' :
    μ ≈ᴛᴇꜱᴛ μ' → t ↛[μ] ↔ t ↛[μ'].
  Proof. intros eq. split; apply refuses_preserved_by_LA_test; [done | by symmetry]. Qed.

  Lemma R_preserved_by_LA_test (t : T) μ μ' :
    μ ≈ᴛᴇꜱᴛ μ' → μ ∈ R t → μ' ∈ R t.
  Proof. apply accepts_preserved_by_LA_test. Qed.

  #[global] Instance Proper_accepts_LA_test (t : T) :
    Proper (LA_test T ==> iff) (λ μ, ¬ t ↛[μ]).
  Proof. intros μ μ' eq. by apply accepts_LA_test_iff. Qed.

  #[global] Instance Proper_refuses_LA_test (t : T) :
    Proper (LA_test T ==> iff) (λ μ, t ↛[μ]).
  Proof. intros μ μ' eq. by apply refuses_LA_test_iff. Qed.
End LA_test_properties.

(** ** Properties of process-side label abstractions *)
Section LA_prog_properties.
  Context {P A : Type} {H : ExtAction A} {gLtsP : gLts P H} {LAp : gLtsLAprog P H}.

  Lemma coP_preserved_by_LA_prog (p : P) μ μ' :
    μ ≈ᴘʀᴏ μ' → p ∈ co𝐏 μ → p ∈ co𝐏 μ'.
  Proof. intros eq. exact (LA_prog_spec μ μ' eq p). Qed.

  Lemma coP_LA_prog_iff (p : P) μ μ' :
    μ ≈ᴘʀᴏ μ' → p ∈ co𝐏 μ ↔ p ∈ co𝐏 μ'.
  Proof. intros eq. split; apply coP_preserved_by_LA_prog; [done | by symmetry]. Qed.

  Lemma coR_preserved_by_LA_prog (p : P) μ μ' :
    μ ≈ᴘʀᴏ μ' → blocking μ' → μ ∈ coR p → μ' ∈ coR p.
  Proof.
    intros eq b' (μ2 & accepts & duo & b).
    destruct (coP_preserved_by_LA_prog p μ μ' eq) as (μ'' & duo' & accepts');
      [by exists μ2 |].
    by exists μ''.
  Qed.

  #[global] Instance Proper_coP_LA_prog (p : P) :
    Proper (LA_prog P ==> iff) (λ μ, p ∈ co𝐏 μ).
  Proof. intros μ μ' eq. by apply coP_LA_prog_iff. Qed.
End LA_prog_properties.

(** ** Compatibility with a bisimulation *)
Section LA_eq_rel.
  Context {S A : Type} {H : ExtAction A} {gLtsEqS : gLtsEq S H}.

  Lemma 𝐏_preserved_by_eq (s s' : S) μ : s ∈ 𝐏 μ → s ⋍ s' → s' ∈ 𝐏 μ.
  Proof. apply accepts_preserved_by_eq. Qed.

  Lemma co𝐏_preserved_by_eq (s s' : S) μ : s ∈ co𝐏 μ → s ⋍ s' → s' ∈ co𝐏 μ.
  Proof.
    intros (μ'' & duo & accepts) eq. exists μ''. split; [done |].
    by eapply accepts_preserved_by_eq.
  Qed.
End LA_eq_rel.

(** * Canonical projections (independent of any LTS) *)

(** [f] is the canonical projection of [R]. *)
Class LA_proj {A B : Type} (R : relation A) (f : A → B) :=
  LA_proj_spec μ μ' : f μ = f μ' ↔ R μ μ'.

(** Each class of [f] has a representative. *)
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

(** A relation with a canonical projection into a type with decidable equality is decidable. *)
Lemma proj_rel_dec {A B : Type} `{EqDecision B} (R : relation A) (f : A → B) :
  LA_proj R f → RelDecision R.
Proof.
  intros spec μ μ'. destruct (decide (f μ = f μ')) as [h|h].
  - left. by apply spec.
  - right. intros h'. apply h, spec, h'.
Qed.

Lemma test_spec_of_proj `{gLtsLAtest T A} {B : Type} (φ : A → B) `{!LA_proj (LA_test T) φ}
  (t : T) β β' : φ β = φ β' → β ∈ R t → β' ∈ R t.
Proof. intros eq. apply R_preserved_by_LA_test. by apply LA_proj_spec. Qed.

(** ** Joining two abstractions *)

(** [μ] and [μ'] are related when some [u0 ≈ᴛᴇꜱᴛ μ] and [u1 ≈ᴛᴇꜱᴛ μ'] satisfy [u0 ≈ᴘʀᴏ u1]. *)
Definition LA_rel {A : Type} (R_prog R_test : relation A) : relation A :=
  λ μ μ', ∃ u0 u1, R_test μ u0 ∧ R_test μ' u1 ∧ R_prog u0 u1.

(** The joined equivalence is the transitive closure of [LA_rel]. *)
Definition LA_equiv {A : Type} (R_prog R_test : relation A) : relation A :=
  tc (LA_rel R_prog R_test).

Section Join.
  Context {A : Type} (R_prog R_test : relation A) `{!Equivalence R_prog} `{!Equivalence R_test}.

  Lemma LA_rel_reflexive : Reflexive (LA_rel R_prog R_test).
  Proof. intros μ. exists μ, μ. split_and!; reflexivity. Qed.

  Lemma LA_rel_symmetric : Symmetric (LA_rel R_prog R_test).
  Proof.
    intros μ μ' (u0 & u1 & h0 & h1 & hp).
    exists u1, u0. split_and!; [done | done | by symmetry].
  Qed.

  (** Not a global instance: it would loop on [Equivalence ?R]. *)
  Lemma LA_equiv_equivalence : Equivalence (LA_equiv R_prog R_test).
  Proof.
    split.
    - intros μ. apply tc_once, LA_rel_reflexive.
    - intros μ μ' h. induction h as [x y h | x y z h _ IH].
      + apply tc_once. by apply LA_rel_symmetric.
      + eapply tc_r; [exact IH |]. by apply LA_rel_symmetric.
    - apply tc_transitive.
  Qed.

  Lemma R_test_LA_equiv μ μ' : R_test μ μ' → LA_equiv R_prog R_test μ μ'.
  Proof. intros h. apply tc_once. exists μ', μ'. split_and!; [done | reflexivity | reflexivity]. Qed.

  Lemma R_prog_LA_equiv μ μ' : R_prog μ μ' → LA_equiv R_prog R_test μ μ'.
  Proof. intros h. apply tc_once. exists μ, μ'. split_and!; [reflexivity | reflexivity | done]. Qed.

  (** A map constant on both equivalences is constant on the joined one. *)
  Lemma LA_equiv_ind {B : Type} (f : A → B) :
    (∀ μ μ', R_test μ μ' → f μ = f μ') →
    (∀ μ μ', R_prog μ μ' → f μ = f μ') →
    ∀ μ μ', LA_equiv R_prog R_test μ μ' → f μ = f μ'.
  Proof.
    intros ht hp μ μ' h.
    induction h as [x y (u0 & u1 & h0 & h1 & h01) | x y z (u0 & u1 & h0 & h1 & h01) _ IH].
    - rewrite (ht _ _ h0), (hp _ _ h01). symmetry. by apply ht.
    - rewrite <- IH, (ht _ _ h0), (hp _ _ h01). symmetry. by apply ht.
  Qed.

  (** To show that [ρ] is the canonical projection of [LA_equiv]. *)
  Lemma LA_equiv_proj {B : Type} (ρ : A → B) :
    (∀ μ μ', R_test μ μ' → ρ μ = ρ μ') →
    (∀ μ μ', R_prog μ μ' → ρ μ = ρ μ') →
    (∀ μ μ', ρ μ = ρ μ' → LA_equiv R_prog R_test μ μ') →
    LA_proj (LA_equiv R_prog R_test) ρ.
  Proof. intros ht hp hρ μ μ'. split; [apply hρ | by apply LA_equiv_ind]. Qed.

End Join.

(** ** The completion of [ρ] along [φ] *)
Section Completion.
  Context {A FinA PreAct : Type} (R_prog R_test : relation A)
    `{!Equivalence R_prog} `{!Equivalence R_test}
    (φ : A → FinA) (ρ : A → PreAct)
    `{!LA_proj R_test φ} `{!LA_surj φ} `{!LA_proj (LA_equiv R_prog R_test) ρ}.

  Definition LA_complete (x : FinA) : PreAct := ρ (LA_repr x).

  Lemma LA_complete_spec μ : LA_complete (φ μ) = ρ μ.
  Proof.
    unfold LA_complete. apply (LA_proj_spec (R := LA_equiv R_prog R_test)).
    apply R_test_LA_equiv; [apply _ | apply _ |].
    apply (LA_proj_spec (f := φ)), LA_repr_spec.
  Qed.

  (** [LA_complete] is the only map [κ] such that [κ ∘ φ = ρ]. *)
  Lemma LA_complete_unique (κ : FinA → PreAct) :
    (∀ μ, κ (φ μ) = ρ μ) → ∀ x, κ x = LA_complete x.
  Proof. intros spec x. unfold LA_complete. rewrite <- spec. by rewrite LA_repr_spec. Qed.
End Completion.

(** * Constructive canonical surjection

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

  (** The least index of an element of the class of [μ]. *)
  Definition canon_index (μ : A) : nat :=
    proj1_sig (epsilon_smallest (canon_pred μ) (canon_pred_dec μ) (canon_pred_ex μ)).

  Lemma canon_index_spec μ :
    canon_pred μ (canon_index μ) ∧ ∀ k, canon_pred μ k → canon_index μ ≤ k.
  Proof. unfold canon_index. destruct (epsilon_smallest _ _ _) as [n h]. exact h. Qed.

  (** The representative of the class of [μ]. *)
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

  (** The quotient: the type of representatives. *)
  Definition LA_quotient : Type := dsig (λ x, canon x = x).

  (** The canonical surjection. *)
  Definition LA_class (μ : A) : LA_quotient := dexist (canon μ) (canon_idempotent μ).

  (** Not global instances, to keep instance search predictable. *)
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

(** ** The canonical surjections of the label abstractions *)
Section Canonical_LA.
  Context {P T A : Type} {H : ExtAction A} {gLtsP : gLts P H} {gLtsT : gLts T H}
    {LAp : gLtsLAprog P H} {LAt : gLtsLAtest T H}.

  #[local] Existing Instance LA_equiv_equivalence.

  (** [φ]: the canonical surjection of [≈ᴛᴇꜱᴛ]. *)
  Definition LA_φ : A → LA_quotient (LA_test T) := LA_class (LA_test T).

  (** [δ]: the canonical surjection of [≈ᴘʀᴏ]. *)
  Definition LA_δ : A → LA_quotient (LA_prog P) := LA_class (LA_prog P).

  (** [ρ]: the canonical surjection of the joined equivalence, when it is decidable. *)
  Definition LA_ρ `{!RelDecision (LA_equiv (LA_prog P) (LA_test T))} :
    A → LA_quotient (LA_equiv (LA_prog P) (LA_test T)) :=
    LA_class (LA_equiv (LA_prog P) (LA_test T)).
End Canonical_LA.
