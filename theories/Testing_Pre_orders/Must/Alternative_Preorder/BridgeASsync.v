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

From Stdlib.Unicode Require Import Utf8.
From Stdlib Require Import Relations.Relation_Definitions Classes.RelationClasses.
From stdpp Require Import base tactics decidable countable finite gmap list.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation StateTransitionSystems
  Testing_Predicate Must Subset_Act LabelAbstraction LabelAdmissible DefinitionAS.
From TestingTheory Require Completeness CompletenessASsync.
(* begin hide *)
Section Test_bridges.
  Context `{gLtsT : @gLtsEq T A H} {outcome : T → Prop} `{TP : !Testing_Predicate outcome gLtsT}.

  Definition test_spec_bridge (gen : list A → T) :
    Completeness.test_spec gen → CompletenessASsync.test_spec gen.
  Proof. intros []. constructor; assumption. Defined.

  Definition test_convergence_spec_bridge (tconv : list A → T) :
    Completeness.test_convergence_spec tconv → CompletenessASsync.test_convergence_spec tconv.
  Proof.
    intros [ts c1 c2 c3]. constructor; [exact (test_spec_bridge tconv ts) | exact c1 | exact c2 | exact c3].
  Defined.

  Context {PreAct : Type} `{Countable PreAct} (Γ : A → PreAct).

  Definition ker_rel : relation A := λ μ μ', Γ μ = Γ μ'.

  #[global] Instance ker_rel_equivalence : Equivalence ker_rel.
  Proof. split; [intros μ; done | intros μ μ' h; done | intros μ μ' μ'' h1 h2; by etransitivity]. Qed.

  #[global] Instance ker_rel_dec : RelDecision ker_rel.
  Proof. intros μ μ'. unfold ker_rel. apply _. Defined.

  Definition ta_ker (ta : gset PreAct → list A → T) (E : gset (LA_quotient ker_rel)) :
    list A → T := ta (set_map (λ x, Γ (`x)) E).

  Lemma class_of_repr (x : LA_quotient ker_rel) : LA_class ker_rel (`x) = x.
  Proof. exact (@LA_repr_spec _ _ _ (LA_class_surj ker_rel) x). Qed.

  Lemma class_of_ker μ (x : LA_quotient ker_rel) : Γ μ = Γ (`x) → LA_class ker_rel μ = x.
  Proof. intros e. rewrite <- (class_of_repr x). by apply (LA_class_proj ker_rel). Qed.

  Definition ta_ker_bridge (ta : gset PreAct → list A → T) :
    Completeness.test_co_acceptance_set_spec PreAct ta Γ →
    CompletenessASsync.test_co_acceptance_set_spec (LA_quotient ker_rel) (ta_ker ta) (LA_class ker_rel).
  Proof.
    intros h. constructor.
    - intros E. exact (test_spec_bridge _ (Completeness.ta_test_spec (set_map (λ x, Γ (`x)) E))).
    - intros E. exact (Completeness.ta_does_no_tau (set_map (λ x, Γ (`x)) E)).
    - intros E η nb. exact (Completeness.ta_does_no_non_blocking_actions (set_map (λ x, Γ (`x)) E) η nb).
    - intros E β e b l. apply (Completeness.ta_actions_are_in_its_gamma_set (set_map (λ x, Γ (`x)) E) β e b) in l.
      apply elem_of_map in l as (x & hx & hxE). by rewrite (class_of_ker β x hx).
    - intros E x hx.
      destruct (Completeness.ta_has_a_representative_transition_for_its_gamma_set
                  (set_map (λ x, Γ (`x)) E) (Γ (`x)) (elem_of_map_2 _ _ _ hx)) as (r & β & l & e).
      exists r, β. split; [exact l | exact (class_of_ker β x e)].
    - intros β e' E b l. exact (Completeness.ta_transition_to_good β e' (set_map (λ x, Γ (`x)) E) b l).
  Defined.
End Test_bridges.

Section Must_transfer.
  Context `{gLtsP : @gLts P Aproc Hp} `{gLtsT : !@gLtsEq T Atest Ht}
    {outcome : T → Prop} `{TP : !Testing_Predicate outcome gLtsT} {SA : SyncAction Aproc Atest}.
  Context (STS1 STS2 : ParSts P T gLtsP gLtsT)
    (S1 : ParStsSpec P T gLtsP gLtsT SA STS1) (S2 : ParStsSpec P T gLtsP gLtsT SA STS2).

  Lemma must_transfer (p : P) (t : T) : must (STS := STS1) p t → must (STS := STS2) p t.
  Proof.
    induction 1 as [p t ho | p t nh ex pt IHpt et IHet com IHcom].
    - by apply m_now.
    - apply m_step; [exact nh | | exact IHpt | exact IHet | exact IHcom].
      destruct ex as (y & hy).
      apply (@par_step_inv _ _ _ _ _ _ _ _ _ _ S1) in hy
        as [(p' & -> & l) | [(t' & -> & l) | (p' & t' & μ1 & μ2 & -> & hs & l1 & l2)]].
      + exists (p', t). exact (@par_step_left _ _ _ _ _ _ _ _ _ _ S2 p p' t l).
      + exists (p, t'). exact (@par_step_right _ _ _ _ _ _ _ _ _ _ S2 p t t' l).
      + exists (p', t'). exact (@par_step_sync _ _ _ _ _ _ _ _ _ _ S2 p p' t t' μ1 μ2 hs l1 l2).
  Qed.
End Must_transfer.
Section Abs_bridges.
  Context {P T FinA PreAct A : Type} {H : ExtAction A} {gLtsP : gLts P H} {gLtsT : gLtsEq T H}
    {Φ : A → FinA} {𝝳 : FinA → PreAct} `{Countable PreAct}.

  Lemma LA_admissible_of_AbsAction
    `{AbsPT : !@AbsAction P T FinA PreAct A H Φ 𝝳 A H gLtsP gLtsT SyncAction_of_dual} :
    @LA_admissible P T A H gLtsP A H (@gLtsEq_gLts T A H gLtsT) SyncAction_of_dual (ker_rel (λ x, 𝝳 (Φ x))).
  Proof.
    intros p β β'' b h mem.
    pose proof mem as (μ2 & _ & _ & b'').
    destruct (abstraction_prog_spec p β'' β b'' b (eq_sym h) (map_gamma_of_action Φ _ β'' mem))
      as (u & hu & e).
    exists u. split; [exact hu |]. intros t acc.
    pose proof hu as (? & ? & ? & bu).
    exact (abstraction_test_spec t β u b bu e acc).
  Qed.

  Definition FinitaryLA_of_Finitary (r : PreAct → A) (hr : ∀ x, 𝝳 (Φ (r x)) = x)
    `{FA : !@FinitaryAbsAction P T FinA PreAct A H Φ 𝝳 A H gLtsP gLtsT SyncAction_of_dual _ _} :
    FinitaryLA P (ker_rel (λ x, 𝝳 (Φ x))).
  Proof.
    refine {| coR_absR p := set_map (λ x, LA_class (ker_rel (λ x, 𝝳 (Φ x))) (r x)) (coR_abs p) |}.
    intros p x. rewrite elem_of_map. split.
    - intros (pre & -> & hpre). apply coR_abs_spec1 in hpre as (β & hβ & ->).
      exists β. split; [exact hβ |]. apply (LA_class_proj (ker_rel _)). unfold ker_rel. cbn. by rewrite hr.
    - intros (β & hβ & <-). exists (𝝳 (Φ β)). split.
      + apply (LA_class_proj (ker_rel _)). unfold ker_rel. cbn. by rewrite hr.
      + apply coR_abs_spec2. by exists β.
  Defined.
End Abs_bridges.
(* end hide *)
