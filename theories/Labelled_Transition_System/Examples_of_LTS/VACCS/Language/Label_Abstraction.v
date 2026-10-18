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
From stdpp Require Import base tactics gmap gmultiset.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Subset_Act InputOutputActions
  InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction
  DefinitionAS Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic
  VACCS.Language.gLts_Instance.

Section VACCS_Label_Abstraction.

Context `{VP : VACCS_Parameters}.

Notation A := (ExtAct TypeOfActions).
Notation gP := (@gLtsEq_gLts proc _ _ VACCS_gLtsEq).

Definition R_test_vaccs (μ μ' : A) : Prop :=
  match μ, μ' with
  | ActIn (c , _), ActIn (c' , _) => c = c'
  | ActOut a, ActOut a' => a = a'
  | _, _ => False
  end.

Definition R_prog_vaccs (μ μ' : A) : Prop :=
  match μ, μ' with
  | ActIn a, ActIn a' => a = a'
  | ActOut (c , _), ActOut (c' , _) => c = c'
  | _, _ => False
  end.

Definition vaccs_ker (μ μ' : A) : Prop :=
  match μ, μ' with
  | ActIn (c , _), ActIn (c' , _) => c = c'
  | ActOut (c , _), ActOut (c' , _) => c = c'
  | _, _ => False
  end.

#[local] Instance R_test_vaccs_preorder : PreOrder R_test_vaccs.
Proof.
  split.
  - intros [[c v]|[c v]]; done.
  - intros [[c v]|[c v]] [[c' v']|[c' v']] [[c'' v'']|[c'' v'']]; simpl;
      intros; first [contradiction | congruence].
Qed.

#[local] Instance R_prog_vaccs_preorder : PreOrder R_prog_vaccs.
Proof.
  split.
  - intros [[c v]|[c v]]; done.
  - intros [[c v]|[c v]] [[c' v']|[c' v']] [[c'' v'']|[c'' v'']]; simpl;
      intros; first [contradiction | congruence].
Qed.

#[local] Instance vaccs_ker_dec : RelDecision vaccs_ker.
Proof. intros [[c v]|[c v]] [[c' v']|[c' v']]; simpl; apply _. Defined.

Lemma accepts_input_any_value (p : proc) c v w :
  p ⟶[ActIn (c , v)] → p ⟶[ActIn (c , w)].
Proof.
  intros acc.
  assert (∀ a, ¬ @non_blocking _ VACCS_ExtAction (ActIn a)) as b by (intros a [? h]; discriminate h).
  exact (@abstraction_test_spec _ _ _ _ _ _ _ _ _ _ _ _ _ AbsVACCS p
           (ActIn (c , v)) (ActIn (c , w)) (b _) (b _) eq_refl acc).
Qed.

Lemma blocking_is_input (μ : A) : blocking μ → ∃ a, μ = ActIn a.
Proof. destruct μ as [a | a]; intros b; [by exists a | exfalso; apply b; by exists a]. Qed.

Definition EPO_VACCS : Enable_PO proc VACCS_ExtAction (gLtsT := gP).
Proof.
  refine (MkEnable_PO proc A VACCS_ExtAction gP R_test_vaccs _ _).
  intros [[c v]|[c v]] [[c' v']|[c' v']] eq t; unfold elem_of, Elements_of, 𝐄;
    simpl in eq; try contradiction.
  - subst. apply accepts_input_any_value.
  - by injection eq as -> ->.
Defined.

Definition CEPO_VACCS {P : Type} (gLtsP : gLts P VACCS_ExtAction) :
  CoEnable_PO P VACCS_ExtAction (gLtsP := gLtsP).
Proof.
  refine (MkCoEnable_PO P A VACCS_ExtAction gLtsP A VACCS_ExtAction _ R_prog_vaccs _ _).
  intros [[c v]|[c v]] [[c' v']|[c' v']] eq p; unfold elem_of, Elements_of, co𝐄;
    simpl in eq; try contradiction.
  - by injection eq as -> ->.
  - intros (μ'' & acc & duo & b). exfalso. apply b. by eexists.
Defined.

Lemma comp_vaccs μ μ2 : (R_test_vaccs ⨾ R_prog_vaccs) μ μ2 ↔ vaccs_ker μ μ2.
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

Lemma ker_vaccs μ μ' : Ker (R_test_vaccs ⨾ R_prog_vaccs) μ μ' ↔ vaccs_ker μ μ'.
Proof.
  split.
  - intros h. apply comp_vaccs, (proj2 (h μ')), comp_vaccs.
    destruct μ' as [[c v]|[c v]]; simpl; reflexivity.
  - intros h μ2. rewrite !comp_vaccs.
    destruct μ as [[c v]|[c v]], μ' as [[c' v']|[c' v']], μ2 as [[c'' v'']|[c'' v'']];
      simpl in *; split; intros; first [contradiction | congruence].
Qed.

Definition 𝔸ᴠᴀᴄᴄꜱ_of {P : Type} (gLtsP : gLts P VACCS_ExtAction) : Label_abstraction P proc.
Proof.
  refine (MkLA P proc A A VACCS_ExtAction VACCS_ExtAction gLtsP gP _ EPO_VACCS (CEPO_VACCS gLtsP) _).
  intros μ μ'. destruct (decide (vaccs_ker μ μ')) as [h | h].
  - left. by apply ker_vaccs.
  - right. by rewrite ker_vaccs.
Defined.

#[global] Instance 𝔸ᴠᴀᴄᴄꜱ : Label_abstraction (proc * MO A) proc := 𝔸ᴠᴀᴄᴄꜱ_of _.

Lemma class_eq_vaccs μ μ' : vaccs_ker μ μ' → ρ[𝔸ᴠᴀᴄᴄꜱ] μ = ρ[𝔸ᴠᴀᴄᴄꜱ] μ'.
Proof. intros h. apply (LA_class_proj (label_ker 𝔸ᴠᴀᴄᴄꜱ)). unfold label_ker. by apply ker_vaccs. Qed.

Lemma class_eq_vaccs_inv μ μ' : ρ[𝔸ᴠᴀᴄᴄꜱ] μ = ρ[𝔸ᴠᴀᴄᴄꜱ] μ' → vaccs_ker μ μ'.
Proof. intros h. apply ker_vaccs. exact (proj1 (LA_class_proj (label_ker 𝔸ᴠᴀᴄᴄꜱ) μ μ') h). Qed.

Definition repr_pre_vaccs (x : PreAct) : A :=
  match x with Inputs c => ActIn (c , cst O) end.

Lemma repr_pre_vaccs_class μ : blocking μ →
  ρ[𝔸ᴠᴀᴄᴄꜱ] (repr_pre_vaccs (αᴘᴠᴀᴄᴄꜱ (αᴛᴠᴀᴄᴄꜱ μ))) = ρ[𝔸ᴠᴀᴄᴄꜱ] μ.
Proof.
  intros b. destruct (blocking_is_input μ b) as ([c v] & ->).
  apply class_eq_vaccs. reflexivity.
Qed.

Definition coRₐ_vaccs (pm : proc * MO A) : gset (A / 𝔸ᴠᴀᴄᴄꜱ) :=
  set_map (λ x, ρ[𝔸ᴠᴀᴄᴄꜱ] (repr_pre_vaccs x)) (PreCoAct_of pm.1)
  ∪ set_map (λ η, ρ[𝔸ᴠᴀᴄᴄꜱ] (co η)) (dom (MO_without_not_nb pm.2)).

Lemma coR_blocking (pm : proc * MO A) μ : μ ∈ coR pm → blocking μ.
Proof. by intros (? & ? & ? & b). Qed.

Lemma coRₐ_vaccs_spec (pm : proc * MO A) x : x ∈ coRₐ_vaccs pm ↔ x ∈ ⌈ ρ[𝔸ᴠᴀᴄᴄꜱ] ⌉ (coR pm).
Proof.
  destruct pm as (p, m). unfold coRₐ_vaccs. simpl. rewrite elem_of_union, !elem_of_map. split.
  - intros [(pre & -> & hpre) | (η & -> & hη)].
    + apply (coR_abs_spec1 (FinitaryAbsAction := FinitaryAbsVACCS)) in hpre as (μ & hμ & ->).
      exists μ. split.
      * apply coR_fw. by left.
      * apply repr_pre_vaccs_class. by destruct hμ as (? & ? & ? & b).
    + apply gmultiset_elem_of_dom in hη.
      assert (hη' : η ∈ (MO_without_not_nb (m : MO A) : MO A)) by exact hη.
      apply lts_MO_nb_with_nb_spec1 in hη' as (nb & hη').
      exists (co η). split; [| done]. apply coR_fw. right. by exists η.
  - intros (μ & hμ & ->). pose proof (coR_blocking _ _ hμ) as b.
    apply coR_fw in hμ as [hμ | (η & nb & hη & ->)].
    + left. exists (αᴘᴠᴀᴄᴄꜱ (αᴛᴠᴀᴄᴄꜱ μ)). split.
      * symmetry. by apply repr_pre_vaccs_class.
      * apply (coR_abs_spec2 (FinitaryAbsAction := FinitaryAbsVACCS)). by exists μ.
    + right. exists η. split; [done |].
      apply gmultiset_elem_of_dom.
      assert (h' : η ∈ (MO_without_not_nb (m : MO A) : MO A)) by (by apply lts_MO_nb_with_nb_spec2).
      exact h'.
Qed.

#[global] Instance Finitary_𝔸ᴠᴀᴄᴄꜱ : Finitary_Label_abstraction (proc * MO A) proc :=
  MkFLA _ proc A A VACCS_ExtAction VACCS_ExtAction _ gP _ 𝔸ᴠᴀᴄᴄꜱ coRₐ_vaccs coRₐ_vaccs_spec.

#[global] Instance Dichotomic_VACCS : Dichotomic (proc * MO A) ρ[𝔸ᴠᴀᴄᴄꜱ] :=
  Decidable_dichotomic Finitary_𝔸ᴠᴀᴄᴄꜱ.

End VACCS_Label_Abstraction.
(* end hide *)
