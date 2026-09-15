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
  DefinitionAS LabelAbstraction VACCS_Instance.

(* * Label abstractions of VACCS as canonical projections

   [Φᴠᴀᴄᴄꜱ] merges inputs and outputs on a channel, which is only sound for
   blocking actions. The canonical projections below are the semantic ones. *)

Section VACCS_LA.

Context `{VP : VACCS_Parameters}.

(** Inputs are related when they share their channel, outputs when equal. *)
Definition R_test_vaccs (μ μ' : ExtAct TypeOfActions) : Prop :=
  match μ, μ' with
  | ActIn (c , _), ActIn (c' , _) => c = c'
  | ActOut a, ActOut a' => a = a'
  | _, _ => False
  end.

(** Inputs are related when equal, outputs when they share their channel. *)
Definition R_prog_vaccs (μ μ' : ExtAct TypeOfActions) : Prop :=
  match μ, μ' with
  | ActIn a, ActIn a' => a = a'
  | ActOut (c , _), ActOut (c' , _) => c = c'
  | _, _ => False
  end.

Inductive TestA_vaccs :=
| TestIn (c : ChannelData)
| TestOut (c : ChannelData) (v : ValueData).

Inductive ProgA_vaccs :=
| ProgIn (c : ChannelData) (v : ValueData)
| ProgOut (c : ChannelData).

Inductive PreA_vaccs :=
| In_on (c : ChannelData)
| Out_on (c : ChannelData).

#[global] Instance PreA_vaccs_eqdec : EqDecision PreA_vaccs.
Proof. solve_decision. Defined.

Definition φᴠᴀᴄᴄꜱ (μ : ExtAct TypeOfActions) : TestA_vaccs :=
  match μ with
  | ActIn (c , _) => TestIn c
  | ActOut (c , v) => TestOut c v
  end.

Definition δᴠᴀᴄᴄꜱ (μ : ExtAct TypeOfActions) : ProgA_vaccs :=
  match μ with
  | ActIn (c , v) => ProgIn c v
  | ActOut (c , _) => ProgOut c
  end.

Definition ρᴠᴀᴄᴄꜱ (μ : ExtAct TypeOfActions) : PreA_vaccs :=
  match μ with
  | ActIn (c , _) => In_on c
  | ActOut (c , _) => Out_on c
  end.

Definition repr_vaccs (x : TestA_vaccs) : ExtAct TypeOfActions :=
  match x with
  | TestIn c => ActIn (c , cst O)
  | TestOut c v => ActOut (c , v)
  end.

(** Input acceptance does not depend on the value. *)
Lemma accepts_input_any_value (p : proc) c v w :
  ¬ p ↛[ActIn (c , v)] → ¬ p ↛[ActIn (c , w)].
Proof.
  intros acc.
  assert (∀ a, ¬ @non_blocking _ VACCS_ExtAction (ActIn a)) as b by (intros a [? h]; discriminate h).
  exact (@abstraction_test_spec _ _ _ _ _ _ _ _ _ _ AbsVACCS p
           (ActIn (c , v)) (ActIn (c , w)) (b _) (b _) eq_refl acc).
Qed.

Lemma R_test_vaccs_proj μ μ' : φᴠᴀᴄᴄꜱ μ = φᴠᴀᴄᴄꜱ μ' ↔ R_test_vaccs μ μ'.
Proof. revert μ μ'. intros [[c v]|[c v]] [[c' v']|[c' v']]; simpl; split; try done; try congruence. Qed.

Lemma R_prog_vaccs_proj μ μ' : δᴠᴀᴄᴄꜱ μ = δᴠᴀᴄᴄꜱ μ' ↔ R_prog_vaccs μ μ'.
Proof. revert μ μ'. intros [[c v]|[c v]] [[c' v']|[c' v']]; simpl; split; try done; try congruence. Qed.

#[global] Program Instance gLtsLAtest_VACCS :
  @gLtsLAtest proc _ VACCS_ExtAction (@gLtsEq_gLts proc _ _ VACCS_gLtsEq) :=
  {| LA_test := R_test_vaccs |}.
Next Obligation. exact (proj_equivalence _ _ R_test_vaccs_proj). Qed.
Next Obligation. intros [[c v]|[c v]] [[c' v']|[c' v']]; simpl; apply _. Defined.
Next Obligation.
  intros [[c v]|[c v]] [[c' v']|[c' v']] eq t; unfold elem_of, Elements_of, 𝐏;
    simpl in eq; try contradiction.
  - subst. apply accepts_input_any_value.
  - by injection eq as -> ->.
Qed.

#[global] Program Instance gLtsLAprog_VACCS :
  @gLtsLAprog proc _ VACCS_ExtAction (@gLtsEq_gLts proc _ _ VACCS_gLtsEq) :=
  {| LA_prog := R_prog_vaccs |}.
Next Obligation. exact (proj_equivalence _ _ R_prog_vaccs_proj). Qed.
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

#[global] Instance LA_proj_test_VACCS : LA_proj R_test_vaccs φᴠᴀᴄᴄꜱ := R_test_vaccs_proj.
#[global] Instance LA_proj_prog_VACCS : LA_proj R_prog_vaccs δᴠᴀᴄᴄꜱ := R_prog_vaccs_proj.

#[global] Program Instance LA_surj_VACCS : LA_surj φᴠᴀᴄᴄꜱ := {| LA_repr := repr_vaccs |}.
Next Obligation. by intros [c|c v]. Qed.

#[local] Instance R_test_vaccs_equivalence : Equivalence R_test_vaccs :=
  proj_equivalence _ _ R_test_vaccs_proj.
#[local] Instance R_prog_vaccs_equivalence : Equivalence R_prog_vaccs :=
  proj_equivalence _ _ R_prog_vaccs_proj.

#[local] Existing Instance LA_equiv_equivalence.

#[global] Instance LA_proj_join_VACCS : LA_proj (LA_equiv R_prog_vaccs R_test_vaccs) ρᴠᴀᴄᴄꜱ.
Proof.
  apply LA_equiv_proj.
  - intros [[c v]|[c v]] [[c' v']|[c' v']] h; simpl in *; try contradiction; congruence.
  - intros [[c v]|[c v]] [[c' v']|[c' v']] h; simpl in *; try contradiction; congruence.
  - intros [[c v]|[c v]] [[c' v']|[c' v']] h; simpl in h; try discriminate; injection h as ->.
    + transitivity (ActIn (c' , v)).
      * by apply (R_prog_LA_equiv R_prog_vaccs R_test_vaccs).
      * by apply (R_test_LA_equiv R_prog_vaccs R_test_vaccs).
    + transitivity (ActOut (c' , v')).
      * by apply (R_prog_LA_equiv R_prog_vaccs R_test_vaccs).
      * by apply (R_test_LA_equiv R_prog_vaccs R_test_vaccs).
Qed.

(** The completion of [ρᴠᴀᴄᴄꜱ] along [φᴠᴀᴄᴄꜱ]. *)
Definition completeᴠᴀᴄᴄꜱ (x : TestA_vaccs) : PreA_vaccs :=
  match x with
  | TestIn c => In_on c
  | TestOut c _ => Out_on c
  end.

Lemma completeᴠᴀᴄᴄꜱ_is_completion x : completeᴠᴀᴄᴄꜱ x = LA_complete φᴠᴀᴄᴄꜱ ρᴠᴀᴄᴄꜱ x.
Proof. apply (LA_complete_unique φᴠᴀᴄᴄꜱ). by intros [[c v]|[c v]]. Qed.

#[global] Instance LA_equiv_dec_VACCS : RelDecision (LA_equiv R_prog_vaccs R_test_vaccs) :=
  proj_rel_dec _ _ LA_proj_join_VACCS.

(** The constructive canonical surjections of VACCS. *)
Definition φ_canonical_VACCS := LA_φ (T := proc).
Definition δ_canonical_VACCS := LA_δ (P := proc).
Definition ρ_canonical_VACCS := LA_ρ (P := proc) (T := proc).

End VACCS_LA.
