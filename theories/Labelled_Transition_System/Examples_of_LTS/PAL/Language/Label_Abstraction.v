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
(* end hide *)

(* begin hide *)
From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base tactics decidable countable list gmap.
From TestingTheory Require Import ActTau gLts Bisimulation SyncActions Subset_Act RelationKernel
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic 
  PAL.Language.Syntax PAL.Language.LTS PAL.Language.Phi PAL.Language.Delta PAL.Language.AbsAction PAL.Language.Congruence
  PAL.Language.Dichotomy.

#[local] Open Scope pal_scope.

#[local] Notation term := (term nat).
#[local] Notation PALA_Act := (PALA_Act nat).
#[local] Notation gP := (@gLtsEq_gLts term _ _ (PALA_gLtsEq nat)).

#[local] Hint Mode ExtAction ! : typeclass_instances.

Lemma tf_match_ext f f' : (∀ o, tf_match f o ↔ tf_match f' o) → f = f'.
Proof.
  intros h. destruct f as [| v |], f' as [| w |]; try reflexivity.
  - pose proof (proj1 (h (of_val (S w))) I) as e. simpl in e. lia.
  - exact (False_rect _ (proj1 (h (of_val 0)) I)).
  - pose proof (proj2 (h (of_val (S v))) I) as e. simpl in e. lia.
  - f_equal. symmetry. exact (proj1 (h (of_val v)) eq_refl).
  - exact (False_rect _ (proj1 (h (of_val v)) eq_refl)).
  - exact (False_rect _ (proj2 (h (of_val 0)) I)).
  - exact (False_rect _ (proj2 (h (of_val w)) eq_refl)).
Qed.

Lemma tf_match_inhabited f : ∃ o, tf_match f o.
Proof. destruct f as [| v |]; [exists (of_val 0) | exists (of_val v) | exists of_star]; done. Qed.

Lemma t_match_ext tp tp' : (∀ ot, t_match tp ot ↔ t_match tp' ot) → tp = tp'.
Proof.
  unfold t_match. revert tp'.
  induction tp as [| f tp IH]; intros tp' h.
  - destruct tp' as [| f' tp']; [done |].
    assert (hm : Forall2 tf_match (f' :: tp') []) by (apply h; constructor). inversion hm.
  - destruct (tf_match_inhabited f) as (o0 & ho0).
    pose proof (t_match_gen_pt 0 tp) as hot0. unfold t_match in hot0.
    destruct tp' as [| f' tp'].
    { assert (hm : Forall2 tf_match [] (o0 :: gen_pt 0 tp)) by (apply h; by constructor). inversion hm. }
    assert (hm : Forall2 tf_match (f' :: tp') (o0 :: gen_pt 0 tp)) by (apply h; by constructor).
    apply Forall2_cons in hm as [ho0' hot0'].
    f_equal.
    + apply tf_match_ext. intros o. split; intros ho.
      * assert (hh : Forall2 tf_match (f' :: tp') (o :: gen_pt 0 tp)) by (apply h; by constructor).
        by apply Forall2_cons in hh as [? _].
      * assert (hh : Forall2 tf_match (f :: tp) (o :: gen_pt 0 tp)) by (apply h; by constructor).
        by apply Forall2_cons in hh as [? _].
    + apply IH. intros ot. split; intros hot.
      * assert (hh : Forall2 tf_match (f' :: tp') (o0 :: ot)) by (apply h; by constructor).
        by apply Forall2_cons in hh as [_ ?].
      * assert (hh : Forall2 tf_match (f :: tp) (o0 :: ot)) by (apply h; by constructor).
        by apply Forall2_cons in hh as [_ ?].
Qed.

Lemma comp_refl μ : (R_test_a nat ⨾ R_prog_a nat) μ μ.
Proof. exists μ. split; reflexivity. Qed.

Lemma comp_out μ' ot : (R_test_a nat ⨾ R_prog_a nat) μ' (AOut nat ot) → αᴛᴀᴘᴀʟ nat μ' = EvOut nat ot.
Proof.
  intros (u & h1 & h2). unfold R_test_a, R_prog_a in *.
  destruct u as [l | ot']; simpl in h2; [discriminate |]. injection h2 as ->. exact h1.
Qed.

Lemma comp_in l l' :
  (∀ ν, (R_test_a nat ⨾ R_prog_a nat) (AIn nat l) ν → (R_test_a nat ⨾ R_prog_a nat) (AIn nat l') ν) →
  ∀ ot, t_match (ltemplate nat l) ot → t_match (ltemplate nat l') ot.
Proof.
  intros h ot hm. apply t_match_label in hm as (m & em & <-).
  destruct (h (AIn nat m)) as (u & h1 & h2).
  { exists (AIn nat m). unfold R_test_a, R_prog_a. simpl. by rewrite em. }
  unfold R_test_a, R_prog_a in *.
  destruct u as [k | ot']; simpl in h1, h2; [| discriminate].
  injection h1 as e1. injection h2 as e2.
  apply t_match_label. exists k. by rewrite e1, e2.
Qed.

Lemma ker_pal μ μ' : Ker (R_test_a nat ⨾ R_prog_a nat) μ μ' ↔ αᴛᴀᴘᴀʟ nat μ = αᴛᴀᴘᴀʟ nat μ'.
Proof.
  split.
  - intros h. destruct μ as [l | ot].
    + destruct μ' as [l' | ot'].
      * simpl. f_equal. apply t_match_ext. intros ot.
        split; apply comp_in; intros ν; apply h.
      * exact (comp_out _ ot' (proj2 (h _) (comp_refl _))).
    + symmetry. exact (comp_out _ ot (proj1 (h _) (comp_refl _))).
  - intros e ν. unfold R_test_a.
    split; intros (u & h1 & h2); exists u; split; [congruence | exact h2 | congruence | exact h2].
Qed.

#[global] Instance 𝔸ᴘᴀʟ :
  @Label_abstraction term term PALA_Act PALA_Act (PALA_ExtAction nat) (PALA_ExtAction nat) gP gP _.
Proof.
  refine (MkLA term term PALA_Act PALA_Act (PALA_ExtAction nat) (PALA_ExtAction nat) gP gP _
            (EPO_PALA nat) (CEPO_PALA nat) _).
  intros μ μ'. destruct (decide (αᴛᴀᴘᴀʟ nat μ = αᴛᴀᴘᴀʟ nat μ')) as [h | h].
  - left. by apply ker_pal.
  - right. by rewrite ker_pal.
Defined.

Lemma ρᴘᴀʟ_eq μ μ' : ρ[𝔸ᴘᴀʟ] μ = ρ[𝔸ᴘᴀʟ] μ' ↔ αᴛᴀᴘᴀʟ nat μ = αᴛᴀᴘᴀʟ nat μ'.
Proof.
  split; intros h.
  - apply ker_pal. exact (proj1 (LA_class_proj (label_ker 𝔸ᴘᴀʟ) μ μ') h).
  - apply (LA_class_proj (label_ker 𝔸ᴘᴀʟ)). exact (proj2 (ker_pal μ μ') h).
Qed.

Definition repr_ev (e : Event nat) : PALA_Act := LA_repr (LA_surj := αᴛᴀᴘᴀʟ_surj nat) e.

Lemma repr_ev_spec e : αᴛᴀᴘᴀʟ nat (repr_ev e) = e.
Proof. apply (LA_repr_spec (LA_surj := αᴛᴀᴘᴀʟ_surj nat)). Qed.

#[global] Instance Dichotomic_PAL : Dichotomic term ρ[𝔸ᴘᴀʟ].
Proof.
  intros p q _ _.
  destruct (PALA_coR_dichotomy p q) as [sub | (x & hp & hq)].
  - left. intros c (μ & hμ & ->).
    destruct (sub (αᴛᴀᴘᴀʟ nat μ)) as (μ' & hμ' & e); [by exists μ |].
    exists μ'. split; [exact hμ' |]. by apply ρᴘᴀʟ_eq.
  - right. exists (ρ[𝔸ᴘᴀʟ] (repr_ev x)). split.
    + destruct hp as (μ & hμ & ->). exists μ. split; [exact hμ |].
      apply ρᴘᴀʟ_eq. apply repr_ev_spec.
    + intros (μ & hμ & e). apply hq. exists μ. split; [exact hμ |].
      apply ρᴘᴀʟ_eq in e. rewrite repr_ev_spec in e. exact e.
Defined.

Lemma class_of_repr_pal (x : PALA_Act / 𝔸ᴘᴀʟ) : ρ[𝔸ᴘᴀʟ] (`x) = x.
Proof. exact (@LA_repr_spec _ _ _ (LA_class_surj _) x). Qed.

Definition class_to_ev (x : PALA_Act / 𝔸ᴘᴀʟ) : Event nat := αᴛᴀᴘᴀʟ nat (`x).

Definition ev_to_class (e : Event nat) : PALA_Act / 𝔸ᴘᴀʟ := ρ[𝔸ᴘᴀʟ] (repr_ev e).

Lemma ev_to_class_to_ev x : ev_to_class (class_to_ev x) = x.
Proof.
  unfold ev_to_class, class_to_ev. transitivity (ρ[𝔸ᴘᴀʟ] (`x)).
  - apply ρᴘᴀʟ_eq, repr_ev_spec.
  - apply class_of_repr_pal.
Qed.

Lemma class_to_ev_to_class e : class_to_ev (ev_to_class e) = e.
Proof.
  unfold ev_to_class, class_to_ev. transitivity (αᴛᴀᴘᴀʟ nat (repr_ev e)).
  - apply ρᴘᴀʟ_eq, class_of_repr_pal.
  - apply repr_ev_spec.
Qed.
(* end hide *)
