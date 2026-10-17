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
From Stdlib Require Import Relations.Relation_Definitions Classes.RelationClasses Classes.Morphisms.
From stdpp Require Import base tactics gmap decidable countable.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Subset_Act.
From TestingTheory Require Export RelationKernel.

(* LTSs equipped with preorders on actions *)

(* LTSs equipped with a preorders that preserves enabledness *)
Module EPO.
Class Enable_PO (T : Type) {At : Type} (Ht : ExtAction At) {gLtsT : gLts T Ht} :=
  MkEnable_PO {
    label_preorder : At → At → Prop;
    label_preorder_is_a_preorder : PreOrder label_preorder;
    Ready_set_inclusion μ μ' : label_preorder μ μ' → (𝐄 μ : subset_of T) ⊆ 𝐄 μ';
  }.

Arguments Enable_PO T {_} Ht {_}.
Arguments label_preorder T {_ _ _ _} μ μ'.
End EPO.
Export EPO.

Notation "(≼ᴛᴇꜱᴛ)" := (EPO.label_preorder _).
Notation "μ ≼ᴛᴇꜱᴛ μ'" := (EPO.label_preorder _ μ μ') (at level 70).

#[global] Instance EPO_preorder `{Enable_PO T Ht} : PreOrder (EPO.label_preorder T).
Proof. exact EPO.label_preorder_is_a_preorder. Defined.

(* LTSs equipped with a preorders that preserves co-enabledness *)
Module CEPO.
Class CoEnable_PO (P : Type) {Ap : Type} {Hp : ExtAction Ap} {gLtsP : gLts P Hp}
  {At : Type} (Ht : ExtAction At) {SA : SyncAction Ap At} :=
  MkCoEnable_PO {
    label_preorder : At → At → Prop;
    label_preorder_is_a_preorder : PreOrder label_preorder;
    coR_reverse_inclusion μ μ' : label_preorder μ μ' → (co𝐄 μ' : subset_of P) ⊆ co𝐄 μ;
  }.

Arguments CoEnable_PO P {_ _ _ _} Ht {_}.
Arguments label_preorder P {_ _ _ _ _ _ _} μ μ'.
End CEPO.
Export CEPO.

Notation "(≼ᴘʀᴏ)" := (CEPO.label_preorder _).
Notation "μ ≼ᴘʀᴏ μ'" := (CEPO.label_preorder _ μ μ') (at level 70).

#[global] Instance CEPO_preorder `{CoEnable_PO P (At := At)} : PreOrder (CEPO.label_preorder P).
Proof. exact CEPO.label_preorder_is_a_preorder. Defined.

(* ** Properties of enabledness preorders *)
Section EPO_properties.
  Context {T At : Type} {Ht : ExtAction At} {gLtsT : gLts T Ht} {EPO : Enable_PO T Ht}.

  Lemma accepts_preserved_by_EPO (t : T) μ μ' :
    μ ≼ᴛᴇꜱᴛ μ' → t ⟶[μ] → t ⟶[μ'].
  Proof. intros le. exact (Ready_set_inclusion μ μ' le t). Qed.

  Lemma refuses_reflected_by_EPO (t : T) μ μ' :
    μ ≼ᴛᴇꜱᴛ μ' → t ↛[μ'] → t ↛[μ].
  Proof. intros le refuses accepts. apply refuses. by eapply accepts_preserved_by_EPO. Qed.

  #[global] Instance Proper_accepts_EPO (t : T) :
    Proper ((≼ᴛᴇꜱᴛ) ==> impl) (λ μ, t ⟶[μ]).
  Proof. intros μ μ' le. exact (accepts_preserved_by_EPO t μ μ' le). Qed.

  #[global] Instance Proper_refuses_EPO (t : T) :
    Proper (flip (≼ᴛᴇꜱᴛ) ==> impl) (λ μ, t ↛[μ]).
  Proof. intros μ μ' le. exact (refuses_reflected_by_EPO t μ' μ le). Qed.
End EPO_properties.

(* ** Properties of co-enabledness preorders *)
Section CEPO_properties.
  Context {P Ap At : Type} {Hp : ExtAction Ap} {Ht : ExtAction At} {SA : SyncAction Ap At}.
  Context {gLtsP : gLts P Hp} {CEPO : CoEnable_PO P Ht}.

  Lemma co𝐄_reflected_by_CEPO (p : P) μ μ' :
    μ ≼ᴘʀᴏ μ' → p ∈ co𝐄 μ' → p ∈ co𝐄 μ.
  Proof. intros le. exact (coR_reverse_inclusion μ μ' le p). Qed.

  #[global] Instance Proper_co𝐄_CEPO (p : P) :
    Proper (flip (≼ᴘʀᴏ) ==> impl) (λ μ, p ∈ co𝐄 μ).
  Proof. intros μ μ' le. exact (co𝐄_reflected_by_CEPO p μ' μ le). Qed.
End CEPO_properties.

(* ** Compatibility with a bisimulation *)
Section CEPO_EPO_and_Bissimulation_properties.
  Context {S Ap : Type} {Hp : ExtAction Ap} {gLtsEqS : gLtsEq S Hp}.

  Lemma 𝐄_preserved_by_eq (s s' : S) μ : s ∈ 𝐄 μ → s ⋍ s' → s' ∈ 𝐄 μ.
  Proof. apply accepts_preserved_by_eq. Qed.

  Context {At : Type} {Ht : ExtAction At} {SA : SyncAction Ap At}.

  Lemma co𝐄_preserved_by_eq (s s' : S) (μ : At) : s ∈ co𝐄 μ → s ⋍ s' → s' ∈ co𝐄 μ.
  Proof.
    intros (μ'' & accepts & duo & b) eq. exists μ''. split_and!; [| done | done].
    by eapply accepts_preserved_by_eq.
  Qed.
End CEPO_EPO_and_Bissimulation_properties.

Class Label_abstraction (P T : Type) {Ap At : Type} {Hp : ExtAction Ap} {Ht : ExtAction At}
  {gLtsP : gLts P Hp} {gLtsT : gLts T Ht} {SA : SyncAction Ap At} :=
  MkLA {
    EPO :: Enable_PO T Ht;
    CEPO :: CoEnable_PO P Ht;
    Label_abstraction_dec :
      RelDecision (Ker ((≼ᴛᴇꜱᴛ) ⨾ (≼ᴘʀᴏ)));
  }.

Arguments Label_abstraction P T {_ _ _ _ _ _ _}.

Notation "(≼ᴛᴇꜱᴛ[ 𝔸 ] )" := (EPO.label_preorder _ (Enable_PO := EPO (Label_abstraction := 𝔸)))
  (format "(≼ᴛᴇꜱᴛ[ 𝔸 ] )").
Notation "μ ≼ᴛᴇꜱᴛ[ 𝔸 ] μ'" := (EPO.label_preorder _ (Enable_PO := EPO (Label_abstraction := 𝔸)) μ μ')
  (at level 70, format "μ  ≼ᴛᴇꜱᴛ[ 𝔸 ]  μ'").
Notation "(≼ᴘʀᴏ[ 𝔸 ] )" := (CEPO.label_preorder _ (CoEnable_PO := CEPO (Label_abstraction := 𝔸)))
  (format "(≼ᴘʀᴏ[ 𝔸 ] )").
Notation "μ ≼ᴘʀᴏ[ 𝔸 ] μ'" := (CEPO.label_preorder _ (CoEnable_PO := CEPO (Label_abstraction := 𝔸)) μ μ')
  (at level 70, format "μ  ≼ᴘʀᴏ[ 𝔸 ]  μ'").

Definition label_ker {P T Ap At : Type} {Hp : ExtAction Ap} {Ht : ExtAction At}
  {gLtsP : gLts P Hp} {gLtsT : gLts T Ht} {SA : SyncAction Ap At}
  (𝔸 : Label_abstraction P T) : relation At :=
  Ker ((≼ᴛᴇꜱᴛ[𝔸]) ⨾ (≼ᴘʀᴏ[𝔸])).

Notation "μ ≈[ 𝔸 ] μ'" := (label_ker 𝔸 μ μ') (at level 70, format "μ  ≈[ 𝔸 ]  μ'").

#[global] Instance label_ker_dec `{𝔸 : Label_abstraction P T (At := At)} : RelDecision (label_ker 𝔸).
Proof. exact (Label_abstraction_dec (Label_abstraction := 𝔸)). Defined.

#[global] Instance label_ker_equivalence `{𝔸 : Label_abstraction P T (At := At)} :
  Equivalence (label_ker 𝔸).
Proof. apply rel_ker_equivalence. Defined.

Coercion label_ker : Label_abstraction >-> relation.

Class Finitary_Label_abstraction (P T : Type) {Ap At : Type} {Hp : ExtAction Ap} {Ht : ExtAction At}
  {gLtsP : gLts P Hp} {gLtsT : gLts T Ht} {SA : SyncAction Ap At} :=
  MkFLA {
    𝔸 :: Label_abstraction P T;
    coRₐ : P → gset (At / 𝔸);
    coRₐ_spec (p : P) x : x ∈ coRₐ p ↔ x ∈ ⌈ ρ[𝔸] ⌉ (coR p);
  }.

Arguments Finitary_Label_abstraction P T {_ _ _ _ _ _ _}.
(* end hide *)
