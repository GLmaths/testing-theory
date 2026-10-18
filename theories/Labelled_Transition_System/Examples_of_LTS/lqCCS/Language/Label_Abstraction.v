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
From stdpp Require Import base tactics countable decidable gmap gmultiset.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths
  lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum lqCCS.Language.Syntax lqCCS.Language.Program
  lqCCS.Language.FwLTS lqCCS.Testing.Observer.LTS lqCCS.Testing.Observer.Tests
  lqCCS.Testing.Observer.Interaction.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Subset_Act
  InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction DefinitionAS
  Label_Abstraction.LabelAbstraction Label_Abstraction.Decidable_dichotomic.

Definition R_test_lq (μ μ' : lact) : Prop :=
  match μ, μ' with
  | LIn c _, LIn c' _ => c = c'
  | LOut c v, LOut c' v' => c = c' ∧ v = v'
  | LOp E qs, LOp E' qs' => E = E' ∧ qs = qs'
  | LMeas M qs _, LMeas M' qs' _ => M = M' ∧ qs = qs'
  | _, _ => False
  end.

Definition R_prog_lq (μ μ' : lact) : Prop :=
  match μ, μ' with
  | LIn c v, LIn c' v' => c = c' ∧ v = v'
  | LOut c _, LOut c' _ => c = c'
  | LOp _ _, LOp _ _ => True
  | LMeas M qs n, LMeas M' qs' n' => M = M' ∧ qs = qs' ∧ n = n'
  | _, _ => False
  end.

Definition lq_ker (μ μ' : lact) : Prop :=
  match μ, μ' with
  | LIn c _, LIn c' _ => c = c'
  | LOut c _, LOut c' _ => c = c'
  | LOp _ _, LOp _ _ => True
  | LMeas M qs _, LMeas M' qs' _ => M = M' ∧ qs = qs'
  | _, _ => False
  end.

#[local] Instance R_test_lq_preorder : PreOrder R_test_lq.
Proof.
  split.
  - intros []; simpl; auto.
  - intros [] [] []; simpl; intros; naive_solver.
Qed.

#[local] Instance R_prog_lq_preorder : PreOrder R_prog_lq.
Proof.
  split.
  - intros []; simpl; auto.
  - intros [] [] []; simpl; intros; naive_solver.
Qed.

#[local] Instance lq_ker_dec : RelDecision lq_ker.
Proof. intros [] []; simpl; apply _. Defined.

Lemma lq_ker_refl μ : lq_ker μ μ.
Proof. destruct μ; simpl; auto. Qed.

Lemma comp_lq μ μ2 : (R_test_lq ⨾ R_prog_lq) μ μ2 ↔ lq_ker μ μ2.
Proof.
  split.
  - intros (u & h1 & h2). destruct μ, u, μ2; simpl in *; naive_solver.
  - intros h. destruct μ, μ2; simpl in h; try contradiction.
    + exists (LOut c v). simpl. naive_solver.
    + exists (LIn c0 v0). simpl. naive_solver.
    + exists (LOp E qs). simpl. naive_solver.
    + exists (LMeas M0 qs0 k0). simpl. naive_solver.
Qed.

Lemma ker_lq μ μ' : Ker (R_test_lq ⨾ R_prog_lq) μ μ' ↔ lq_ker μ μ'.
Proof.
  split.
  - intros h. apply comp_lq, (proj2 (h μ')), comp_lq, lq_ker_refl.
  - intros h μ2. rewrite !comp_lq. destruct μ, μ', μ2; simpl in *; naive_solver.
Qed.

Section lqCCS_Label_Abstraction.

Context `{QM : QuantumModel} `{SC : !Countable St}.

Notation pconf := (proc * St)%type.

Definition EPO_lq : Enable_PO proc lact_ExtAction (gLtsT := @gLtsEq_gLts _ _ _ obs_gLtsEq).
Proof.
  refine (MkEnable_PO proc lact lact_ExtAction _ R_test_lq _ _).
  intros μ μ' h t ht. unfold elem_of, Elements_of, 𝐄 in *.
  destruct μ, μ'; simpl in h; try contradiction.
  - destruct h as [-> ->]. exact ht.
  - subst. refine (obs_abs_test t _ _ _ _ _ ht); [exact (λ h, h) | exact (λ h, h) | reflexivity].
  - destruct h as [-> ->]. exact ht.
  - destruct h as [-> ->]. refine (obs_abs_test t _ _ _ _ _ ht); [exact (λ h, h) | exact (λ h, h) | reflexivity].
Defined.

Definition CEPO_lq : CoEnable_PO (pconf * MO lact) lact_ExtAction.
Proof.
  refine (MkCoEnable_PO (pconf * MO lact) lact lact_ExtAction _ lact lact_ExtAction _ R_prog_lq _ _).
  intros μ μ' h x hx. unfold elem_of, Elements_of, co𝐄 in *.
  destruct μ, μ'; simpl in h; try contradiction.
  - exfalso. destruct hx as (? & _ & _ & b). by apply b.
  - destruct h as [-> ->]. exact hx.
  - exists (LOp E qs). split_and!; [apply fw_accepts_op | done | by intros ?].
  - destruct h as (-> & -> & ->). exact hx.
Defined.

#[global] Instance 𝔸ʟǫ : Label_abstraction (pconf * MO lact) proc.
Proof.
  refine (MkLA _ proc lact lact lact_ExtAction lact_ExtAction _ _ _ EPO_lq CEPO_lq _).
  intros μ μ'. destruct (decide (lq_ker μ μ')) as [h | h].
  - left. by apply ker_lq.
  - right. by rewrite ker_lq.
Defined.

Lemma class_eq_lq μ μ' : lq_ker μ μ' → ρ[𝔸ʟǫ] μ = ρ[𝔸ʟǫ] μ'.
Proof. intros h. apply (LA_class_proj (label_ker 𝔸ʟǫ)). unfold label_ker. by apply ker_lq. Qed.

Lemma class_eq_lq_inv μ μ' : ρ[𝔸ʟǫ] μ = ρ[𝔸ʟǫ] μ' → lq_ker μ μ'.
Proof. intros h. apply ker_lq. exact (proj1 (LA_class_proj (label_ker 𝔸ʟǫ) μ μ') h). Qed.

Lemma coR_lq (x : pconf) β :
  β ∈ coR x ↔
    (∃ ξ, ξ ∈ dom (fmo x) ∧ β = lco ξ) ∨ (∃ E qs, β = LOp E qs)
    ∨ (∃ M qs n, β = LMeas M qs n ∧ x ⟶[LMeas M qs n]).
Proof.
  split.
  - intros (μ2 & acc & hsync & hb). simpl in hsync. subst β.
    destruct μ2 as [c v|c v|E qs|M qs n].
    + left. exists (LOut c v). split; [| done].
      apply lts_performs_spec1 in acc as (y & hl). by eapply pmo_of_step.
    + exfalso. by apply hb.
    + right; left. by exists E, qs.
    + right; right. by exists M, qs, n.
  - intros [(ξ & hξ & ->) | [(E & qs & ->) | (M & qs & n & -> & acc)]].
    + destruct (pmo_out x ξ hξ) as (c & v & ->).
      exists (LOut c v). split_and!; [| done | by intros ?].
      destruct (pmo_step x _ hξ) as (y & hl).
      apply (lts_performs_spec2 x (ActExt (LOut c v))). by exists y.
    + exists (LOp E qs). split_and!; [apply p_accepts_op | done | by intros ?].
    + exists (LMeas M qs n). split_and!; [exact acc | done | by intros ?].
Qed.

Definition coR_fin_lq (xm : pconf * MO lact) : gset (lact / 𝔸ʟǫ) :=
  set_map (λ ξ, ρ[𝔸ʟǫ] (lco ξ)) (dom (fmo xm.1))
  ∪ dom (gmultiset_map (λ η, ρ[𝔸ʟǫ] (lco η)) (MO_without_not_nb xm.2))
  ∪ {[ ρ[𝔸ʟǫ] (LOp 0 []) ]}.

Lemma meas_not_fin xm M qs n : ρ[𝔸ʟǫ] (LMeas M qs n) ∉ coR_fin_lq xm.
Proof.
  destruct xm as (x, m). unfold coR_fin_lq. cbn [fst snd].
  intros h. apply elem_of_union in h as [h | e].
  - apply elem_of_union in h as [h | h].
    + apply elem_of_map in h as (ξ & e & hξ).
      apply class_eq_lq_inv in e. destruct (pmo_out x ξ hξ) as (c & v & ->). simpl in e. done.
    + apply gmultiset_elem_of_dom, elem_of_gmultiset_map in h as (η & e & mem).
      apply (lts_MO_nb_with_nb_spec1 η m) in mem as (nb & _).
      apply class_eq_lq_inv in e. destruct η; simpl in nb, e; done.
  - apply elem_of_singleton in e. apply class_eq_lq_inv in e. simpl in e. done.
Qed.

Lemma mb_in_lq (m : MO lact) η : non_blocking η → η ∈ m →
  ρ[𝔸ʟǫ] (lco η) ∈ dom (gmultiset_map (λ η, ρ[𝔸ʟǫ] (lco η)) (MO_without_not_nb m)).
Proof.
  intros nb hη. apply gmultiset_elem_of_dom, elem_of_gmultiset_map. exists η. split; [done |].
  exact (lts_MO_nb_with_nb_spec2 η m nb hη).
Qed.

Lemma mb_out_lq (m : MO lact) y :
  y ∈ dom (gmultiset_map (λ η, ρ[𝔸ʟǫ] (lco η)) (MO_without_not_nb m)) →
  ∃ η, non_blocking η ∧ η ∈ m ∧ y = ρ[𝔸ʟǫ] (lco η).
Proof.
  intros h. apply gmultiset_elem_of_dom, elem_of_gmultiset_map in h as (η & -> & mem).
  apply (lts_MO_nb_with_nb_spec1 η m) in mem as (nb & mem). by exists η.
Qed.

Lemma coR_fw_mb_lq (x : pconf) (m : MO lact) η : non_blocking η → η ∈ m → lco η ∈ coR (x ▷ m).
Proof. intros nb hη. apply coR_fw. right. by exists η. Qed.

Lemma img_coR_lq (xm : pconf * MO lact) y :
  y ∈ ⌈ ρ[𝔸ʟǫ] ⌉ (coR xm) ↔
    y ∈ coR_fin_lq xm ∨ (xm.1.2 ≠ szero ∧ ∃ M qs, y = ρ[𝔸ʟǫ] (LMeas M qs 0)).
Proof.
  destruct xm as (x, m). unfold coR_fin_lq. cbn [fst snd]. split.
  - intros (β & hβ & ->). apply coR_fw in hβ as [hβ | (η & nb & hη & ->)].
    + apply coR_lq in hβ as [(ξ & hξ & ->) | [(E & qs & ->) | (M & qs & n & -> & acc)]].
      * left. apply elem_of_union_l, elem_of_union_l.
        exact (elem_of_map_2 (λ ξ0, ρ[𝔸ʟǫ] (lco ξ0)) _ ξ hξ).
      * left. apply elem_of_union_r, elem_of_singleton. by apply class_eq_lq.
      * right. apply lts_performs_spec1 in acc as (y & hl).
        apply p_meas_code in hl as [hz _]. split; [exact hz |].
        exists M, qs. by apply class_eq_lq.
    + left. apply elem_of_union_l, elem_of_union_r.
      change (co η) with (lco η). exact (mb_in_lq m η nb hη).
  - intros [h | (hz & M & qs & ->)].
    + apply elem_of_union in h as [h | h]; [apply elem_of_union in h as [h | h] |].
      * apply elem_of_map in h as (ξ & -> & hξ).
        exists (lco ξ). split; [| done]. apply coR_fw. left. apply coR_lq. left. by exists ξ.
      * apply mb_out_lq in h as (η & nb & hη & ->).
        exists (lco η). split; [| done]. by apply coR_fw_mb_lq.
      * apply elem_of_singleton in h as ->.
        exists (LOp 0 []). split; [| done]. apply coR_fw. left. apply coR_lq. right. left. by exists 0, [].
    + destruct (p_accepts_meas x M qs hz) as (n & acc).
      exists (LMeas M qs n). split.
      * apply coR_fw. left. apply coR_lq. right. right. by exists M, qs, n.
      * by apply class_eq_lq.
Qed.

#[global] Instance Dichotomic_lqCCS : Dichotomic (pconf * MO lact) ρ[𝔸ʟǫ].
Proof.
  intros xm ym _ _.
  destruct (decide (coR_fin_lq xm ⊆ coR_fin_lq ym)) as [sub | nsub].
  - destruct (decide (xm.1.2 ≠ szero ∧ ym.1.2 = szero)) as [(hx & hy) | hok].
    + right. exists (ρ[𝔸ʟǫ] (LMeas 0 [] 0)). split.
      * apply img_coR_lq. right. split; [exact hx | by exists 0, []].
      * intros [h | (hz & _)]%img_coR_lq; [by apply meas_not_fin in h | done].
    + left. intros y [h | (hz & M & qs & ->)]%img_coR_lq; apply img_coR_lq.
      * left. by apply sub.
      * right. split; [| by exists M, qs].
        intros hy. apply hok. split; done.
  - right. destruct (elements (coR_fin_lq xm ∖ coR_fin_lq ym)) as [| y l] eqn:e.
    + exfalso. apply nsub. intros y hy. destruct (decide (y ∈ coR_fin_lq ym)) as [| n]; [done |].
      assert (y ∈ elements (coR_fin_lq xm ∖ coR_fin_lq ym)) as hm
        by (apply elem_of_elements, elem_of_difference; by split).
      rewrite e in hm. inversion hm.
    + assert (y ∈ coR_fin_lq xm ∖ coR_fin_lq ym) as hm.
      { apply elem_of_elements. rewrite e. constructor. }
      apply elem_of_difference in hm as [h1 h2].
      exists y. split.
      * apply img_coR_lq. by left.
      * intros [h | (hz & M & qs & ->)]%img_coR_lq; [done |].
        by apply meas_not_fin in h1.
Defined.

End lqCCS_Label_Abstraction.
(* end hide *)
