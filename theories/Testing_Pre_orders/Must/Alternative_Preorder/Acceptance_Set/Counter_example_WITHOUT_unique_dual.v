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
From Stdlib.Program Require Import Equality.
From stdpp Require Import base decidable countable finite list sets gmap.
From TestingTheory Require Import ActTau gLts Bisimulation Lts_OBA Lts_FW
  InteractionBetweenLts ParallelLTSConstruction Termination WeakTransitions
  Convergence Testing_Predicate Must Subset_Act DefinitionAS.

Import ListNotations.

(** * [completeness1] and [completeness2] are false without [UniqueDual]

    [Completeness.v] proves [p ⊑ₘᵤₛₜᵢ q -> p ₁≼ₐₛ q] ([completeness1]) and
    [p ⊑ₘᵤₛₜᵢ q -> p ₂≼ₐₛ q] ([completeness2]) under the hypothesis
    [UniqueDual A]. This file shows that both statements are false without it.

    Actions are [la], [lb], [lc], [ld], [le], all blocking, and the dual
    relation is [la — lc — lb] and [ld — le]: [lc] is dual to both [la] and
    [lb]. This is an [ExtAction] ([EA_NU]) which is not [UniqueDual].

    The swap [la ↔ lb] preserves the dual relation, and a test can only
    interact with [la] or [lb] through [lc], so no test separates a process
    from its swap: [p ⊑ₘᵤₛₜᵢ swap p], for tests of any LTS. Hence:
    - convergence ([completeness1]): [p0 = la.0 + lb.Ω], [q0 = la.Ω + lb.0].
      [p0 ⇓ [la]] while [q0 ⟹{la} Ω] diverges, so [¬ p0 ₁≼ₐₛ q0].
    - acceptance sets ([completeness2]): [p1 = la.(ld.0) + lb.0],
      [q1 = la.0 + lb.(ld.0)], with [Φ = 𝝳 = id]. After [la], [q1] reaches the
      stable [0], whose [coR] is empty, while the only state [p1] reaches is
      [ld.0], whose [coR] is [{le}], so [¬ p1 ₂≼ₐₛ q1]. Both processes
      converge, so the failure really is on the acceptance sets.

    The process LTS satisfies the process-side hypotheses of [completeness1]
    ([gLtsOba], [gLtsObaFW]): with every action blocking, their axioms are
    vacuous. *)

(** ** Actions *)

Inductive ABC := la | lb | lc | ld | le.

#[global] Instance ABC_eqdec : EqDecision ABC.
Proof. solve_decision. Defined.

#[global] Program Instance ABC_finite : Finite ABC := {| enum := [la; lb; lc; ld; le] |}.
Next Obligation. repeat constructor; set_solver. Qed.
Next Obligation. intros []; set_solver. Qed.

#[global] Instance ABC_countable : Countable ABC := finite_countable.

(** ** The non-unique dual: [la — lc — lb] *)

Definition dualNU (x y : ABC) : Prop :=
  match x, y with
  | la, lc | lc, la | lb, lc | lc, lb | ld, le | le, ld => True
  | _, _ => False
  end.

#[global] Instance dualNU_dec x y : Decision (dualNU x y).
Proof. destruct x, y; simpl; apply _. Defined.

Lemma dualNU_sym : Symmetric dualNU.
Proof. intros [] []; simpl; tauto. Qed.

Definition coNU (x : ABC) : ABC :=
  match x with la => lc | lb => lc | lc => la | ld => le | le => ld end.

Lemma coNU_spec x : dualNU x (coNU x).
Proof. by destruct x. Qed.

#[global] Instance EA_NU : ExtAction ABC := {|
    eqdec := _;
    countable := _;
    non_blocking _ := False;
    non_blocking_dec _ := _;
    dual := dualNU;
    dual_dec := dualNU_dec;
    dual_blocks _ _ _ _ nb := nb;
    duo_sym := dualNU_sym;
    exists_dual μ := exist _ (coNU μ) (coNU_spec μ);
  |}.

Lemma EA_NU_not_unique : ¬ UniqueDual ABC.
Proof. intros Hu. by specialize (Hu lb lc I). Qed.

(** ** The processes

    - [p0 = la.0 + lb.Ω] and [q0 = la.Ω + lb.0], for [completeness1];
    - [p1 = la.dz + lb.0] and [q1 = la.0 + lb.dz] with [dz = ld.0], for
      [completeness2]. *)

Inductive st := p0 | q0 | p1 | q1 | dz | nil | om.

#[global] Instance st_eqdec : EqDecision st.
Proof. solve_decision. Defined.

Definition next (s : st) (α : Act ABC) : list st :=
  match s, α with
  | p0, ActExt la => [nil]
  | p0, ActExt lb => [om]
  | q0, ActExt la => [om]
  | q0, ActExt lb => [nil]
  | p1, ActExt la => [dz]
  | p1, ActExt lb => [nil]
  | q1, ActExt la => [nil]
  | q1, ActExt lb => [dz]
  | dz, ActExt ld => [nil]
  | om, τ => [om]
  | _, _ => []
  end.

Definition st_step (s : st) (α : Act ABC) (s' : st) : Prop := s' ∈ next s α.

Lemma st_refuses_spec1 s α : ¬ next s α = [] → { s' | st_step s α s' }.
Proof.
  unfold st_step. destruct (next s α) as [|x l]; intro h.
  - exfalso. by apply h.
  - exists x. set_solver.
Qed.

Lemma st_refuses_spec2 s α : { s' | st_step s α s' } → ¬ next s α = [].
Proof. intros [s' h] e. unfold st_step in h. rewrite e in h. set_solver. Qed.

#[global] Instance st_gLts : gLts st EA_NU := {|
    lts_step := st_step;
    lts_state_eqdec := _;
    lts_step_decidable s α s' := decide (s' ∈ next s α);
    lts_refuses s α := next s α = [];
    lts_refuses_decidable s α := decide (next s α = []);
    lts_refuses_spec1 := st_refuses_spec1;
    lts_refuses_spec2 := st_refuses_spec2;
  |}.

#[global] Program Instance st_gLtsEq : gLtsEq st EA_NU := {|
    eq_rel := eq;
  |}.
Next Obligation. intros p q α (r & -> & l). eauto. Qed.

#[global] Instance st_gLtsOba : gLtsOba st.
Proof. constructor; intros; simpl in *; contradiction. Qed.

#[global] Instance st_gLtsObaFW : gLtsObaFW st ABC.
Proof.
  constructor.
  - intros p1 η β. exists p1. intros nb. contradiction.
  - intros ? ? ? ? ? nb. contradiction.
Qed.

(** ** The swap [la ↔ lb] *)

Definition swap_act (x : ABC) : ABC :=
  match x with la => lb | lb => la | x => x end.

Definition swap_st (s : st) : st :=
  match s with p0 => q0 | q0 => p0 | p1 => q1 | q1 => p1 | x => x end.

Lemma swap_st_invol s : swap_st (swap_st s) = s.
Proof. by destruct s. Qed.

(** The swap preserves [dualNU] (one side is enough). *)
Lemma dualNU_swap x y : dualNU (swap_act x) y ↔ dualNU x y.
Proof. destruct x, y; simpl; tauto. Qed.

Lemma step_swap s α s' :
  s ⟶{α} s' →
  swap_st s ⟶{match α with ActExt μ => ActExt (swap_act μ) | τ => τ end} swap_st s'.
Proof.
  simpl. unfold st_step.
  destruct s, α as [[]|]; simpl; intro h; set_solver.
Qed.

Lemma step_swap_tau s s' : swap_st s ⟶ s' → s ⟶ swap_st s'.
Proof.
  intro h. apply step_swap in h. by rewrite swap_st_invol in h.
Qed.

Lemma step_swap_ext s μ s' : swap_st s ⟶[μ] s' → s ⟶[swap_act μ] swap_st s'.
Proof.
  intro h. apply step_swap in h. by rewrite swap_st_invol in h.
Qed.

Lemma step_swap_ext' s μ s' : s ⟶[μ] s' → swap_st s ⟶[swap_act μ] swap_st s'.
Proof. apply step_swap. Qed.

(** ** No test separates [s] from [swap_st s] *)

Section Tests.

Context `{gLtsT : !gLtsEq T EA_NU} `{!Testing_Predicate outcome _}.
Context `{!Prop_of_Inter st T ABC dual}.

Lemma must_swap (s : st) (t : T) :
  s must_pass t → swap_st s must_pass t.
Proof.
  intro hm. induction hm as [s t hh | s t nh ex pt IHpt et IHet com IHcom].
  - by apply m_now.
  - apply m_step; auto.
    + destruct ex as (u & hu). inversion hu; subst.
      * eexists. apply ParLeft. exact (step_swap _ _ _ l).
      * eexists. apply ParRight. exact l.
      * eexists. eapply ParSync.
        -- apply dualNU_swap. exact eq.
        -- exact (step_swap_ext' _ _ _ l1).
        -- exact l2.
    + intros s' l. rewrite <- (swap_st_invol s').
      apply IHpt, step_swap_tau, l.
    + intros s' t' μ1 μ2 duo l1 l2. rewrite <- (swap_st_invol s').
      eapply (IHcom _ _ (swap_act μ1) μ2).
      * apply dualNU_swap, duo.
      * apply step_swap_ext, l1.
      * exact l2.
Qed.

Lemma p0_ctx_pre_q0 : p0 ⊑ₘᵤₛₜᵢ q0.
Proof. intros t hm. exact (must_swap p0 t hm). Qed.

Lemma p1_ctx_pre_q1 : p1 ⊑ₘᵤₛₜᵢ q1.
Proof. intros t hm. exact (must_swap p1 t hm). Qed.

End Tests.

(** ** [p0 ⇓ [la]] but not [q0 ⇓ [la]] *)

Lemma om_diverges : ¬ om ⤓.
Proof.
  intro h. dependent induction h. apply (H0 om); simpl; unfold st_step; set_solver.
Qed.

Lemma no_tau_terminates s : next s τ = [] → s ⤓.
Proof.
  intro e. constructor. intros q l. simpl in l. unfold st_step in l.
  rewrite e in l. set_solver.
Qed.

Lemma p0_cnv_la : p0 ⇓ [la].
Proof.
  apply cnv_act.
  - by apply no_tau_terminates.
  - intros q w. apply cnv_nil.
    inversion w as [| ? ? ? ? ? l | ? ? ? ? ? l w']; subst.
    + simpl in l. unfold st_step in l. set_solver.
    + simpl in l. unfold st_step in l. simpl in l.
      apply list_elem_of_singleton in l as ->.
      inversion w'; subst.
      * by apply no_tau_terminates.
      * simpl in l. unfold st_step in l. set_solver.
Qed.

Lemma q0_not_cnv_la : ¬ q0 ⇓ [la].
Proof.
  intro h. inversion h as [| ? ? ? _ hw]; subst.
  assert (om ⇓ ε) as hom.
  { apply hw. apply (wt_act la [] q0 om om).
    - simpl. unfold st_step. simpl. set_solver.
    - apply wt_nil. }
  inversion hom as [? hterm |]; subst.
  exact (om_diverges hterm).
Qed.

(** ** The counterexample *)

Theorem completeness1_fails_without_unique_dual :
  ¬ UniqueDual ABC
  (* [p0 ⊑ₘᵤₛₜᵢ q0], for tests of any LTS *)
  ∧ (∀ `{gLtsT : !gLtsEq T EA_NU} `{!Testing_Predicate outcome _}
       `{!Prop_of_Inter st T ABC dual},
       p0 ⊑ₘᵤₛₜᵢ q0)
  (* but not [p0 ₁≼ₐₛ q0] *)
  ∧ ¬ (p0 ₁≼ₐₛ q0).
Proof.
  split; [|split].
  - exact EA_NU_not_unique.
  - intros. apply p0_ctx_pre_q0.
  - intro h. apply q0_not_cnv_la, h, p0_cnv_la.
Qed.

(** ** The acceptance sets of [p1] and [q1] after [la] *)

Definition idA (x : ABC) : ABC := x.

#[global] Program Instance AbsAction_id `{gLtsT : !gLtsEq T EA_NU} :
  @AbsAction st T ABC ABC ABC EA_NU idA idA st_gLts gLtsT.
Next Obligation. intros T gLtsT t β β' b b' e mem. unfold idA in e. subst. exact mem. Qed.
Next Obligation. intros T gLtsT p β β' b b' e mem. unfold idA in *. subst. exact mem. Qed.

(** [₂≼ₐₛ] with [Φ = 𝝳 = idA] *)
Definition cond2_id `{gLtsT : !gLtsEq T EA_NU} (p q : st) : Prop :=
  @bhv_pre_cond2 st ABC EA_NU st_gLts T ABC ABC idA idA gLtsT AbsAction_id
    st st_gLts idA AbsAction_id p q.

Lemma dz_terminates : dz ⤓.
Proof. by apply no_tau_terminates. Qed.

Lemma p1_cnv_la : p1 ⇓ [la].
Proof.
  apply cnv_act.
  - by apply no_tau_terminates.
  - intros q w. apply cnv_nil.
    inversion w as [| ? ? ? ? ? l | ? ? ? ? ? l w']; subst.
    + simpl in l. unfold st_step in l. set_solver.
    + simpl in l. unfold st_step in l. simpl in l.
      apply list_elem_of_singleton in l as ->.
      inversion w'; subst.
      * exact dz_terminates.
      * simpl in l. unfold st_step in l. set_solver.
Qed.

Lemma q1_wt_la_nil : q1 ⟹[[la]] nil.
Proof.
  apply (wt_act la [] q1 nil nil).
  - simpl. unfold st_step. simpl. set_solver.
  - apply wt_nil.
Qed.

Lemma nil_stable : nil ↛.
Proof. reflexivity. Qed.

Lemma p1_wt_la_inv p' : p1 ⟹[[la]] p' → p' = dz.
Proof.
  intro w.
  inversion w as [| ? ? ? ? ? l | ? ? ? ? ? l w']; subst.
  - simpl in l. unfold st_step in l. set_solver.
  - simpl in l. unfold st_step in l. simpl in l.
    apply list_elem_of_singleton in l as ->.
    inversion w'; subst.
    + reflexivity.
    + simpl in l. unfold st_step in l. set_solver.
Qed.

Lemma le_in_coR_dz : le ∈ ⌈ (idA ∘ idA) ⌉ (coR dz).
Proof.
  exists le. split; [| reflexivity].
  exists ld. repeat split.
  - simpl. discriminate.
  - intros [].
Qed.

Lemma coR_nil_empty μ : ¬ μ ∈ ⌈ (idA ∘ idA) ⌉ (coR nil).
Proof.
  intros (μ' & (μ'' & acc & _ & _) & _).
  apply acc. reflexivity.
Qed.

Lemma p1_not_cond2 `{gLtsT : !gLtsEq T EA_NU} : ¬ cond2_id p1 q1.
Proof.
  intro h.
  destruct (h [la] nil p1_cnv_la q1_wt_la_nil nil_stable) as (p' & w & _ & sub).
  apply p1_wt_la_inv in w as ->.
  exact (coR_nil_empty le (sub le le_in_coR_dz)).
Qed.

(** Every state reachable from [p1] or [q1] converges on every trace. *)

Definition fin_st (x : st) : Prop :=
  match x with p1 | q1 | dz | nil => True | _ => False end.

Lemma fin_st_step x α y : fin_st x → x ⟶{α} y → fin_st y ∧ α ≠ τ.
Proof.
  simpl. unfold st_step.
  destruct x, α as [[]|]; simpl; intros hx hy; try contradiction;
    repeat match goal with
    | H : _ ∈ [] |- _ => apply not_elem_of_nil in H; contradiction
    | H : _ ∈ [_] |- _ => apply list_elem_of_singleton in H; subst
    end; split; (exact I || discriminate).
Qed.

Lemma fin_st_wt x s y : fin_st x → x ⟹[s] y → fin_st y.
Proof.
  intros hx w. induction w as [| s p q r l w IH | μ s p q r l w IH].
  - exact hx.
  - apply IH. exact (proj1 (fin_st_step _ _ _ hx l)).
  - apply IH. exact (proj1 (fin_st_step _ _ _ hx l)).
Qed.

Lemma fin_st_terminates x : fin_st x → x ⤓.
Proof.
  intro hx. constructor. intros q l.
  destruct (fin_st_step _ _ _ hx l) as [_ hτ]. by destruct hτ.
Qed.

Lemma fin_st_cnv s x : fin_st x → x ⇓ s.
Proof.
  revert x. induction s as [| μ s IH]; intros x hx.
  - apply cnv_nil, fin_st_terminates, hx.
  - apply cnv_act; [apply fin_st_terminates, hx |].
    intros q w. apply IH. exact (fin_st_wt _ _ _ hx w).
Qed.

Lemma p1_cond1_q1 : p1 ₁≼ₐₛ q1.
Proof. intros s _. apply fin_st_cnv. exact I. Qed.

Theorem completeness2_fails_without_unique_dual :
  ¬ UniqueDual ABC
  (* [p1 ⊑ₘᵤₛₜᵢ q1], for tests of any LTS *)
  ∧ (∀ `{gLtsT : !gLtsEq T EA_NU} `{!Testing_Predicate outcome _}
       `{!Prop_of_Inter st T ABC dual},
       p1 ⊑ₘᵤₛₜᵢ q1)
  (* both converge on every trace [p1] converges on *)
  ∧ (p1 ₁≼ₐₛ q1)
  (* but not [p1 ₂≼ₐₛ q1], with [Φ = 𝝳 = id] *)
  ∧ (∀ `{gLtsT : !gLtsEq T EA_NU}, ¬ cond2_id p1 q1).
Proof.
  split; [|split; [|split]].
  - exact EA_NU_not_unique.
  - intros. apply p1_ctx_pre_q1.
  - exact p1_cond1_q1.
  - intros. apply p1_not_cond2.
Qed.
