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
From Stdlib Require Import Relations.Relation_Definitions.
From stdpp Require Import base tactics.
From TestingTheory Require Import ActTau gLts Bisimulation Subset_Act InputOutputActions
  DefinitionAS LabelAbstraction VCCS_Instance.

(* * Label abstractions of VCCS as canonical projections *)

Section VCCS_LA.

Context `{VP : VCCS_Parameters}.

(** Inputs are related when they share their channel, outputs when equal. *)
Definition R_test_vccs (μ μ' : ExtAct TypeOfActions) : Prop :=
  match μ, μ' with
  | ActIn (c , _), ActIn (c' , _) => c = c'
  | ActOut a, ActOut a' => a = a'
  | _, _ => False
  end.

(** Inputs are related when equal, outputs when they share their channel. *)
Definition R_prog_vccs (μ μ' : ExtAct TypeOfActions) : Prop :=
  match μ, μ' with
  | ActIn a, ActIn a' => a = a'
  | ActOut (c , _), ActOut (c' , _) => c = c'
  | _, _ => False
  end.

Inductive ProgA :=
| ProgIn (c : ChannelData) (v : ValueData)
| ProgOut (c : ChannelData).

Definition δᴠᴄᴄꜱ (μ : ExtAct TypeOfActions) : ProgA :=
  match μ with
  | ActIn (c , v) => ProgIn c v
  | ActOut (c , _) => ProgOut c
  end.

(** The joined projection. *)
Definition ρᴠᴄᴄꜱ (μ : ExtAct TypeOfActions) : PreAct := 𝝳ᴠᴄᴄꜱ (Φᴠᴄᴄꜱ μ).

Definition repr_vccs (x : FinA) : ExtAct TypeOfActions :=
  match x with
  | Inputs c => ActIn (c , cst O)
  | Output c v => ActOut (c , v)
  end.

(** Input acceptance does not depend on the value. *)
Lemma accepts_input_any_value (p : proc) c v w :
  ¬ p ↛[ActIn (c , v)] → ¬ p ↛[ActIn (c , w)].
Proof.
  intros acc.
  exact (@abstraction_test_spec _ _ _ _ _ _ _ _ _ _ AbsVCCS p
           (ActIn (c , v)) (ActIn (c , w)) (λ h, h) (λ h, h) eq_refl acc).
Qed.

Lemma R_test_vccs_proj μ μ' : Φᴠᴄᴄꜱ μ = Φᴠᴄᴄꜱ μ' ↔ R_test_vccs μ μ'.
Proof. revert μ μ'. intros [[c v]|[c v]] [[c' v']|[c' v']]; simpl; split; try done; try congruence. Qed.

Lemma R_prog_vccs_proj μ μ' : δᴠᴄᴄꜱ μ = δᴠᴄᴄꜱ μ' ↔ R_prog_vccs μ μ'.
Proof. revert μ μ'. intros [[c v]|[c v]] [[c' v']|[c' v']]; simpl; split; try done; try congruence. Qed.

#[global] Program Instance gLtsLAtest_VCCS :
  @gLtsLAtest proc _ VCCS_ExtAction (@gLtsEq_gLts proc _ _ VCCS_gLtsEq) :=
  {| LA_test := R_test_vccs |}.
Next Obligation. exact (proj_equivalence _ _ R_test_vccs_proj). Qed.
Next Obligation. intros [[c v]|[c v]] [[c' v']|[c' v']]; simpl; apply _. Defined.
Next Obligation.
  intros [[c v]|[c v]] [[c' v']|[c' v']] eq t; unfold elem_of, Elements_of, 𝐏;
    simpl in eq; try contradiction.
  - subst. apply accepts_input_any_value.
  - by injection eq as -> ->.
Qed.

#[global] Program Instance gLtsLAprog_VCCS :
  @gLtsLAprog proc _ VCCS_ExtAction (@gLtsEq_gLts proc _ _ VCCS_gLtsEq) :=
  {| LA_prog := R_prog_vccs |}.
Next Obligation. exact (proj_equivalence _ _ R_prog_vccs_proj). Qed.
Next Obligation. intros [[c v]|[c v]] [[c' v']|[c' v']]; simpl; apply _. Defined.
Next Obligation.
  intros [[c v]|[c v]] [[c' v']|[c' v']] eq p; unfold elem_of, Elements_of, co𝐏;
    simpl in eq; try contradiction.
  - by injection eq as -> ->.
  - subst. intros (μ'' & duo & acc).
    symmetry in duo. apply simplify_match_output in duo. subst.
    exists (ActIn (c' , v')). split; [simpl; reflexivity |].
    by eapply accepts_input_any_value.
Qed.

#[global] Instance LA_proj_test_VCCS : LA_proj R_test_vccs Φᴠᴄᴄꜱ := R_test_vccs_proj.
#[global] Instance LA_proj_prog_VCCS : LA_proj R_prog_vccs δᴠᴄᴄꜱ := R_prog_vccs_proj.

#[global] Program Instance LA_surj_VCCS : LA_surj Φᴠᴄᴄꜱ := {| LA_repr := repr_vccs |}.
Next Obligation. by intros [c|c v]. Qed.

#[local] Instance R_test_vccs_equivalence : Equivalence R_test_vccs :=
  proj_equivalence _ _ R_test_vccs_proj.
#[local] Instance R_prog_vccs_equivalence : Equivalence R_prog_vccs :=
  proj_equivalence _ _ R_prog_vccs_proj.

#[local] Existing Instance LA_equiv_equivalence.

#[global] Instance LA_proj_join_VCCS : LA_proj (LA_equiv R_prog_vccs R_test_vccs) ρᴠᴄᴄꜱ.
Proof.
  apply LA_equiv_proj.
  - intros [[c v]|[c v]] [[c' v']|[c' v']] h; unfold ρᴠᴄᴄꜱ in *; simpl in *; try contradiction; congruence.
  - intros [[c v]|[c v]] [[c' v']|[c' v']] h; unfold ρᴠᴄᴄꜱ in *; simpl in *; try contradiction; congruence.
  - intros [[c v]|[c v]] [[c' v']|[c' v']] h; unfold ρᴠᴄᴄꜱ in h; simpl in h; try discriminate; injection h as ->.
    + transitivity (ActIn (c' , v)).
      * by apply (R_prog_LA_equiv R_prog_vccs R_test_vccs).
      * by apply (R_test_LA_equiv R_prog_vccs R_test_vccs).
    + transitivity (ActOut (c' , v')).
      * by apply (R_prog_LA_equiv R_prog_vccs R_test_vccs).
      * by apply (R_test_LA_equiv R_prog_vccs R_test_vccs).
Qed.

(** The [𝝳ᴠᴄᴄꜱ] of [VCCS_Instance] is the completion of the joined projection. *)
Lemma delta_vccs_is_completion x :
  𝝳ᴠᴄᴄꜱ x = LA_complete Φᴠᴄᴄꜱ ρᴠᴄᴄꜱ x.
Proof. by apply (LA_complete_unique Φᴠᴄᴄꜱ). Qed.

#[global] Instance LA_equiv_dec_VCCS : RelDecision (LA_equiv R_prog_vccs R_test_vccs) :=
  proj_rel_dec _ _ LA_proj_join_VCCS.

(** The constructive canonical surjections of VCCS. *)
Definition φ_canonical_VCCS := LA_φ (T := proc).
Definition δ_canonical_VCCS := LA_δ (P := proc).
Definition ρ_canonical_VCCS := LA_ρ (P := proc) (T := proc).

End VCCS_LA.
