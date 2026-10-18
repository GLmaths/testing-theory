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
(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Relations.Relation_Definitions Classes.RelationClasses.
From stdpp Require Import base tactics gmap.
From TestingTheory Require Import ActTau gLts Bisimulation Subset_Act InputOutputActions
  DefinitionAS Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic
  VCCS.Language.gLts_Instance.

Section VCCS_Label_Abstraction.

Context `{VP : VCCS_Parameters}.

Notation A := (ExtAct TypeOfActions).
Notation gP := (@gLtsEq_gLts proc _ _ VCCS_gLtsEq).

Definition R_test_vccs (μ μ' : A) : Prop :=
  match μ, μ' with
  | ActIn (c , _), ActIn (c' , _) => c = c'
  | ActOut a, ActOut a' => a = a'
  | _, _ => False
  end.

Definition R_prog_vccs (μ μ' : A) : Prop :=
  match μ, μ' with
  | ActIn a, ActIn a' => a = a'
  | ActOut (c , _), ActOut (c' , _) => c = c'
  | _, _ => False
  end.

Definition vccs_ker (μ μ' : A) : Prop :=
  match μ, μ' with
  | ActIn (c , _), ActIn (c' , _) => c = c'
  | ActOut (c , _), ActOut (c' , _) => c = c'
  | _, _ => False
  end.

#[local] Instance R_test_vccs_preorder : PreOrder R_test_vccs.
Proof.
  split.
  - intros [[c v]|[c v]]; done.
  - intros [[c v]|[c v]] [[c' v']|[c' v']] [[c'' v'']|[c'' v'']]; simpl;
      intros; first [contradiction | congruence].
Qed.

#[local] Instance R_prog_vccs_preorder : PreOrder R_prog_vccs.
Proof.
  split.
  - intros [[c v]|[c v]]; done.
  - intros [[c v]|[c v]] [[c' v']|[c' v']] [[c'' v'']|[c'' v'']]; simpl;
      intros; first [contradiction | congruence].
Qed.

#[local] Instance vccs_ker_dec : RelDecision vccs_ker.
Proof. intros [[c v]|[c v]] [[c' v']|[c' v']]; simpl; apply _. Defined.

Lemma accepts_input_any_value (p : proc) c v w :
  p ⟶[ActIn (c , v)] → p ⟶[ActIn (c , w)].
Proof.
  intros acc.
  exact (@abstraction_test_spec _ _ _ _ _ _ _ _ _ _ _ _ _ AbsVCCS p
           (ActIn (c , v)) (ActIn (c , w)) (λ h, h) (λ h, h) eq_refl acc).
Qed.

Definition EPO_VCCS : Enable_PO proc VCCS_ExtAction (gLtsT := gP).
Proof.
  refine (MkEnable_PO proc A VCCS_ExtAction gP R_test_vccs _ _).
  intros [[c v]|[c v]] [[c' v']|[c' v']] eq t; unfold elem_of, Elements_of, 𝐄;
    simpl in eq; try contradiction.
  - subst. apply accepts_input_any_value.
  - by injection eq as -> ->.
Defined.

Definition CEPO_VCCS : CoEnable_PO proc VCCS_ExtAction (gLtsP := gP).
Proof.
  refine (MkCoEnable_PO proc A VCCS_ExtAction gP A VCCS_ExtAction _ R_prog_vccs _ _).
  intros [[c v]|[c v]] [[c' v']|[c' v']] eq p; unfold elem_of, Elements_of, co𝐄;
    simpl in eq; try contradiction.
  - by injection eq as -> ->.
  - subst. intros (μ'' & acc & duo & b).
    symmetry in duo. apply simplify_match_output in duo. subst.
    exists (ActIn (c' , v)). split_and!; [| simpl; reflexivity | exact b].
    by eapply accepts_input_any_value.
Defined.

Lemma comp_vccs μ μ2 : (R_test_vccs ⨾ R_prog_vccs) μ μ2 ↔ vccs_ker μ μ2.
Proof.
  split.
  - intros (u & h1 & h2).
    destruct μ as [[c v]|[c v]], u as [[cu vu]|[cu vu]], μ2 as [[c' v']|[c' v']];
      simpl in *; first [contradiction | congruence].
  - intros h. destruct μ as [[c v]|[c v]], μ2 as [[c' v']|[c' v']]; simpl in h;
      try contradiction; subst.
    + exists (ActIn (c' , v')). simpl. split; reflexivity.
    + exists (ActOut (c' , v)). simpl. split; reflexivity.
Qed.

Lemma ker_vccs μ μ' : Ker (R_test_vccs ⨾ R_prog_vccs) μ μ' ↔ vccs_ker μ μ'.
Proof.
  split.
  - intros h. apply comp_vccs, (proj2 (h μ')), comp_vccs.
    destruct μ' as [[c v]|[c v]]; simpl; reflexivity.
  - intros h μ2. rewrite !comp_vccs.
    destruct μ as [[c v]|[c v]], μ' as [[c' v']|[c' v']], μ2 as [[c'' v'']|[c'' v'']];
      simpl in *; split; intros; first [contradiction | congruence].
Qed.

#[global] Instance 𝔸ᴠᴄᴄꜱ : Label_abstraction proc proc.
Proof.
  refine (MkLA proc proc A A VCCS_ExtAction VCCS_ExtAction gP gP _ EPO_VCCS CEPO_VCCS _).
  intros μ μ'. destruct (decide (vccs_ker μ μ')) as [h | h].
  - left. by apply ker_vccs.
  - right. by rewrite ker_vccs.
Defined.

Definition repr_pre_vccs (x : PreAct) : A :=
  match x with
  | Inputs_on c => ActIn (c , cst O)
  | Outputs_on c => ActOut (c , cst O)
  end.

Lemma ρᴠᴄᴄꜱ_repr x : αᴘᴠᴄᴄꜱ (αᴛᴠᴄᴄꜱ (repr_pre_vccs x)) = x.
Proof. by destruct x. Qed.

Lemma ρᴠᴄᴄꜱ_ker μ μ' : αᴘᴠᴄᴄꜱ (αᴛᴠᴄᴄꜱ μ) = αᴘᴠᴄᴄꜱ (αᴛᴠᴄᴄꜱ μ') ↔ vccs_ker μ μ'.
Proof.
  destruct μ as [[c v]|[c v]], μ' as [[c' v']|[c' v']]; simpl;
    split; intros; first [contradiction | congruence].
Qed.

#[global] Instance LA_proj_VCCS : LA_proj (label_ker 𝔸ᴠᴄᴄꜱ) (λ μ, αᴘᴠᴄᴄꜱ (αᴛᴠᴄᴄꜱ μ)).
Proof. intros μ μ'. unfold label_ker. rewrite ρᴠᴄᴄꜱ_ker. symmetry. apply ker_vccs. Qed.

Lemma class_of_repr_vccs μ : ρ[𝔸ᴠᴄᴄꜱ] (repr_pre_vccs (αᴘᴠᴄᴄꜱ (αᴛᴠᴄᴄꜱ μ))) = ρ[𝔸ᴠᴄᴄꜱ] μ.
Proof.
  apply (LA_class_proj (label_ker 𝔸ᴠᴄᴄꜱ)). unfold label_ker.
  apply ker_vccs, ρᴠᴄᴄꜱ_ker. by rewrite ρᴠᴄᴄꜱ_repr.
Qed.

Definition coRₐ_vccs (p : proc) : gset (A / 𝔸ᴠᴄᴄꜱ) :=
  set_map (λ x, ρ[𝔸ᴠᴄᴄꜱ] (repr_pre_vccs x)) (PreCoAct_of p).

Lemma coRₐ_vccs_spec (p : proc) x : x ∈ coRₐ_vccs p ↔ x ∈ ⌈ ρ[𝔸ᴠᴄᴄꜱ] ⌉ (coR p).
Proof.
  unfold coRₐ_vccs. rewrite elem_of_map. split.
  - intros (pre & -> & hpre).
    apply (coR_abs_spec1 (FinitaryAbsAction := FinitaryAbsVCCS)) in hpre as (μ & hμ & ->).
    exists μ. split; [exact hμ |]. first [apply class_of_repr_vccs | symmetry; apply class_of_repr_vccs].
  - intros (μ & hμ & ->). exists (αᴘᴠᴄᴄꜱ (αᴛᴠᴄᴄꜱ μ)). split.
    + first [apply class_of_repr_vccs | symmetry; apply class_of_repr_vccs].
    + apply (coR_abs_spec2 (FinitaryAbsAction := FinitaryAbsVCCS)). by exists μ.
Qed.

#[global] Instance Finitary_𝔸ᴠᴄᴄꜱ : Finitary_Label_abstraction proc proc :=
  MkFLA proc proc A A VCCS_ExtAction VCCS_ExtAction gP gP _ 𝔸ᴠᴄᴄꜱ coRₐ_vccs coRₐ_vccs_spec.

#[global] Instance Dichotomic_VCCS : Dichotomic proc ρ[𝔸ᴠᴄᴄꜱ] :=
  Decidable_dichotomic Finitary_𝔸ᴠᴄᴄꜱ.

End VCCS_Label_Abstraction.
(* end hide *)
