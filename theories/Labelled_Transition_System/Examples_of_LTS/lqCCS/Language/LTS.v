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
(* * lqCCS: the process LTS and the observer LTS

    Two LTSs on two alphabets, linked by [sync], as in the classical
    development ([SyncActions.v], [InteractionBetweenLts.v]):

    - observers are programs alone, over [tact]: outputs [c!v], receptions
      [c?v], requests [E(q̃)] to the memory, and the reception of the outcome
      [k] of a measurement [M(q̃)] (only for codes [k] of outcomes of [M]);
    - processes are a program with its memory [(P, ρ)], over [aact]: the
      outputs and receptions of [P], and the *services* of the memory,
      [Apply E q̃] and [Meas M q̃ k] — the memory accepts every request, and
      answers [k] only if [M_k(ρ) ≠ 0].  The silent steps of [(P, ρ)] are the
      silent steps of [P], and its own requests to its memory.

    [sync] is a bijection between labels: each action has exactly one
    partner.  No action is declared non-blocking: [must] does not depend on
    it, and the axioms on non-blocking actions are then empty.

    Both LTSs are given by their lists of successors, so that they are
    decidable by construction. *)

From Stdlib.Unicode Require Import Utf8.
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base countable decidable list sets gmap.
From TestingTheory Require Import lqCCS.Harmony_Lemma.Lifted lqCCS.Harmony_Lemma.Paths lqCCS.Harmony_Lemma.States lqCCS.Language.Quantum.
From TestingTheory Require Import lqCCS.Language.Syntax lqCCS.Language.Program lqCCS.Language.Composition lqCCS.Language.Succ
  lqCCS.Language.Congruence.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Testing_Predicate
  InteractionBetweenLts.
(* ** LTSs given by their successors *)

Definition list_witness {A} (l : list A) (Hl : l ≠ []) : { x | x ∈ l }.
Proof. destruct l as [|x l]; [done|]. exists x. set_solver. Defined.

Definition gLts_of_succs {S A} `{EA : ExtAction A} `{EqDecision S}
  (f : S → Labels A → list S) : gLts S EA :=
  {| lts_step p 𝜆 q := q ∈ f p 𝜆;
     lts_step_decidable p 𝜆 q := (_ : Decision (q ∈ f p 𝜆));
     lts_performs p 𝜆 := f p 𝜆 ≠ [];
     lts_performs_decidable p 𝜆 := _;
     lts_performs_spec1 p 𝜆 Hl := list_witness (f p 𝜆) Hl;
     lts_performs_spec2 p 𝜆 '(exist _ q Hq) := ltac:(intros E; rewrite E in Hq; set_solver) |}.

(* ** Alphabets *)

Inductive tact : Type :=
| TOut (c : chan) (v : val)
| TIn (c : chan) (v : val)
| TOp (E : sop) (qs : list qubit)
| TMeas (M : meas) (qs : list qubit) (k : nat).

Inductive aact : Type :=
| POut (c : chan) (v : val)
| PIn (c : chan) (v : val)
| SApply (E : sop) (qs : list qubit)
| SMeas (M : meas) (qs : list qubit) (k : nat).

#[global] Instance tact_eq_dec : EqDecision tact.
Proof. solve_decision. Defined.
#[global] Instance aact_eq_dec : EqDecision aact.
Proof. solve_decision. Defined.

Notation actsum := ((chan * val) + (chan * val) + (sop * list qubit) + (meas * list qubit * nat))%type.

#[global] Instance tact_countable : Countable tact.
Proof.
  refine (inj_countable'
    (λ a : tact, match a with
       | TOut c v => inl (inl (inl (c, v))) | TIn c v => inl (inl (inr (c, v)))
       | TOp E qs => inl (inr (E, qs)) | TMeas M qs k => inr (M, qs, k) end : actsum)
    (λ s : actsum, match s with
       | inl (inl (inl (c, v))) => TOut c v | inl (inl (inr (c, v))) => TIn c v
       | inl (inr (E, qs)) => TOp E qs | inr (M, qs, k) => TMeas M qs k end) _).
  by intros [].
Defined.

#[global] Instance aact_countable : Countable aact.
Proof.
  refine (inj_countable'
    (λ a : aact, match a with
       | POut c v => inl (inl (inl (c, v))) | PIn c v => inl (inl (inr (c, v)))
       | SApply E qs => inl (inr (E, qs)) | SMeas M qs k => inr (M, qs, k) end : actsum)
    (λ s : actsum, match s with
       | inl (inl (inl (c, v))) => POut c v | inl (inl (inr (c, v))) => PIn c v
       | inl (inr (E, qs)) => SApply E qs | inr (M, qs, k) => SMeas M qs k end) _).
  by intros [].
Defined.

(* Duals inside each alphabet: an output and the matching reception;
    requests and measurements are their own duals. *)
Definition tco (a : tact) : tact :=
  match a with TOut c v => TIn c v | TIn c v => TOut c v | _ => a end.
Definition aco (a : aact) : aact :=
  match a with POut c v => PIn c v | PIn c v => POut c v | _ => a end.

Lemma tco_sym : Symmetric (λ a b : tact, b = tco a).
Proof. intros a b ->. by destruct a. Qed.
Lemma aco_sym : Symmetric (λ a b : aact, b = aco a).
Proof. intros a b ->. by destruct a. Qed.

#[global] Instance tact_ExtAction : ExtAction tact := {|
  non_blocking _ := False;
  non_blocking_dec _ := _;
  dual a b := b = tco a;
  dual_dec a b := _ : Decision (b = tco a);
  dual_blocks β η Hnb _ := False_ind _ Hnb;
  duo_sym := tco_sym;
  exists_dual a := exist _ (tco a) eq_refl;
|}.

#[global] Instance aact_ExtAction : ExtAction aact := {|
  non_blocking _ := False;
  non_blocking_dec _ := _;
  dual a b := b = aco a;
  dual_dec a b := _ : Decision (b = aco a);
  dual_blocks β η Hnb _ := False_ind _ Hnb;
  duo_sym := aco_sym;
  exists_dual a := exist _ (aco a) eq_refl;
|}.

(* The synchronisation: the partner of a process action. *)
Definition partner (a : aact) : tact :=
  match a with
  | POut c v => TIn c v
  | PIn c v => TOut c v
  | SApply E qs => TOp E qs
  | SMeas M qs k => TMeas M qs k
  end.

Definition copartner (b : tact) : aact :=
  match b with
  | TOut c v => PIn c v
  | TIn c v => POut c v
  | TOp E qs => SApply E qs
  | TMeas M qs k => SMeas M qs k
  end.

Lemma partner_copartner a b : b = partner a ↔ a = copartner b.
Proof. split; intros ->; [by destruct a|by destruct b]. Qed.

#[global] Instance lqCCS_SyncAction : SyncAction aact tact :=
  {| sync a b := b = partner a; sync_dec a b := _ : Decision (b = partner a) |}.

Section LTSs.
  Context `{QM : QuantumModel}.


  (* Codes of the outcomes of [M]. *)
  Definition codes (M : meas) (qs : list qubit) : list nat :=
    code (meas_of M qs) <$> outs (meas_of M qs).

  (* *** Observers *)

  Definition tsuccs (Q : proc) (𝜆 : Labels tact) : list proc :=
    match 𝜆 with
    | τ => succ Q UTau
    | ActExt (TOut c v) => succ Q (UAct (AOut c v))
    | ActExt (TIn c v) => succ Q (UAct (AIn c v))
    | ActExt (TOp E qs) => succ Q (UAct (AOp E qs))
    | ActExt (TMeas M qs k) =>
        if decide (k ∈ codes M qs) then
          acts Q ≫= λ '(a, Q0),
            match a with
            | AMeas M' qs' x =>
                if decide (M' = M ∧ qs' = qs) then [subst Q0 x (VNat k)] else []
            | _ => []
            end
        else []
    end.

  #[global] Instance test_gLts : gLts proc tact_ExtAction := gLts_of_succs tsuccs.

  (* *** Processes: a program and its memory *)

  Definition nonzero (ρ : St) : Prop := ρ ≠ szero.

  Definition psuccs (x : proc * St) (𝜆 : Labels aact) : list (proc * St) :=
    let '(P, ρ) := x in
    match 𝜆 with
    | τ =>
        ((λ P', (P', ρ)) <$> succ P UTau)
        ++ (acts P ≫= λ '(a, P0),
              match a with
              | AOp E qs => [(P0, sop_apply E qs ρ)]
              | AMeas M qs x =>
                  (λ k, (subst P0 x (VNat (code _ k)), meas_branch M qs k ρ))
                    <$> filter (λ k, nonzero (meas_branch M qs k ρ)) (outs (meas_of M qs))
              | _ => []
              end)
    | ActExt (POut c v) => (λ P', (P', ρ)) <$> succ P (UAct (AOut c v))
    | ActExt (PIn c v) => (λ P', (P', ρ)) <$> succ P (UAct (AIn c v))
    | ActExt (SApply E qs) => [(P, sop_apply E qs ρ)]
    | ActExt (SMeas M qs j) =>
        (λ k, (P, meas_branch M qs k ρ))
          <$> filter (λ k, code _ k = j ∧ nonzero (meas_branch M qs k ρ))
                     (outs (meas_of M qs))
    end.

  #[global] Instance proc_gLts : gLts (proc * St) aact_ExtAction := gLts_of_succs psuccs.

  (* *** What the steps are *)

  Lemma test_step_def Q 𝜆 Q' : Q ⟶{𝜆} Q' ↔ Q' ∈ tsuccs Q 𝜆.
  Proof. done. Qed.

  Lemma proc_step_def x 𝜆 y : x ⟶{𝜆} y ↔ y ∈ psuccs x 𝜆.
  Proof. done. Qed.

  Lemma tstep_ext Q a Q' :
    (∀ M qs k, a ≠ TMeas M qs k) →
    Q ⟶[a] Q' ↔ ustep Q (match a with
                         | TOut c v => UAct (AOut c v) | TIn c v => UAct (AIn c v)
                         | TOp E qs => UAct (AOp E qs) | TMeas M qs _ => UTau end) Q'.
  Proof.
    intros Ha. rewrite test_step_def.
    destruct a; simpl; try apply succ_spec. by edestruct Ha.
  Qed.

  Lemma tstep_tau Q Q' : Q ⟶ Q' ↔ ustep Q UTau Q'.
  Proof. apply succ_spec. Qed.

  Lemma tstep_meas Q M qs k Q' :
    Q ⟶[TMeas M qs k] Q' ↔
    k ∈ codes M qs ∧ ∃ t x Q0, pstep Q (LAct t (AMeas M qs x)) Q0 ∧ Q' = subst Q0 x (VNat k).
  Proof.
    rewrite test_step_def. simpl.
    case_decide as Hk; [|set_solver]. rewrite list_elem_of_bind. split.
    - intros ([a Q0] & Hin & Hacts). apply acts_spec in Hacts as (_ & t & Hs).
      destruct a; try set_solver. case_decide as Hd; [|set_solver].
      destruct Hd as [-> ->]. apply list_elem_of_singleton in Hin as ->. eauto 10.
    - intros (_ & t & x & Q0 & Hs & ->). exists (AMeas M qs x, Q0). split.
      + rewrite decide_True by done. set_solver.
      + apply acts_spec. split; [done|]. eauto.
  Qed.

  Lemma pstep_out P ρ c v x :
    (P, ρ) ⟶[POut c v] x ↔ ∃ P', x = (P', ρ) ∧ ustep P (UAct (AOut c v)) P'.
  Proof.
    rewrite proc_step_def. simpl.
    rewrite list_elem_of_fmap. split; intros (P' & -> & Hs); exists P';
      split; try done; by apply succ_spec.
  Qed.

  Lemma pstep_in P ρ c v x :
    (P, ρ) ⟶[PIn c v] x ↔ ∃ P', x = (P', ρ) ∧ ustep P (UAct (AIn c v)) P'.
  Proof.
    rewrite proc_step_def. simpl.
    rewrite list_elem_of_fmap. split; intros (P' & -> & Hs); exists P';
      split; try done; by apply succ_spec.
  Qed.

  Lemma pstep_apply P ρ E qs x : (P, ρ) ⟶[SApply E qs] x ↔ x = (P, sop_apply E qs ρ).
  Proof. rewrite proc_step_def. simpl. set_solver. Qed.

  Lemma pstep_smeas P ρ M qs j x :
    (P, ρ) ⟶[SMeas M qs j] x ↔
    ∃ k, code _ k = j ∧ nonzero (meas_branch M qs k ρ) ∧ x = (P, meas_branch M qs k ρ).
  Proof.
    rewrite proc_step_def. simpl.
    rewrite list_elem_of_fmap. split.
    - intros (k & -> & Hk). apply list_elem_of_filter in Hk as [[Hc Hn] _]. eauto.
    - intros (k & Hc & Hn & ->). exists k. split; [done|].
      apply list_elem_of_filter. split; [done|]. apply list_elem_of_In, outs_all.
  Qed.

  Lemma pstep_tau P ρ x :
    (P, ρ) ⟶ x ↔
      (∃ P', x = (P', ρ) ∧ ustep P UTau P')
    ∨ (∃ t E qs P', pstep P (LAct t (AOp E qs)) P' ∧ x = (P', sop_apply E qs ρ))
    ∨ (∃ t M qs y P0 k, pstep P (LAct t (AMeas M qs y)) P0
                        ∧ nonzero (meas_branch M qs k ρ)
                        ∧ x = (subst P0 y (VNat (code _ k)), meas_branch M qs k ρ)).
  Proof.
    rewrite proc_step_def. simpl.
    rewrite elem_of_app, list_elem_of_fmap, list_elem_of_bind. split.
    - intros [(P' & -> & Hs)|([a P0] & Hin & Hacts)].
      + left. exists P'. split; [done|]. by apply succ_spec.
      + right. apply acts_spec in Hacts as (_ & t & Hs).
        destruct a as [c v|c v|E qs|M qs y]; simpl in Hin.
        * set_solver.
        * set_solver.
        * left. apply list_elem_of_singleton in Hin as ->. eauto 10.
        * right. apply list_elem_of_fmap in Hin as (k & -> & Hk).
          apply list_elem_of_filter in Hk as [Hn _]. eauto 20.
    - intros [(P' & -> & Hs)|[(t & E & qs & P' & Hs & ->)|(t & M & qs & y & P0 & k & Hs & Hn & ->)]].
      + left. exists P'. split; [done|]. by apply succ_spec.
      + right. exists (AOp E qs, P'). split; [set_solver|]. apply acts_spec. split; [done|eauto].
      + right. exists (AMeas M qs y, P0). split.
        * apply list_elem_of_fmap. exists k. split; [done|].
          apply list_elem_of_filter. split; [done|]. apply list_elem_of_In, outs_all.
        * apply acts_spec. split; [done|eauto].
  Qed.

  (* *** Observers up to structural congruence *)

  Lemma cgr_goodb P Q : P ≡* Q → goodb P = goodb Q.
  Proof.
    induction 1 as [P|P Q R [Hc|Hc] _ IH]; [done| |]; rewrite <- IH.
    - apply (proj1 cs_gcs_goodb P Q Hc).
    - symmetry. apply (proj1 cs_gcs_goodb Q P Hc).
  Qed.

  #[global] Instance test_gLtsEq : gLtsEq proc tact_ExtAction.
  Proof.
    refine {| gLtsEq_gLts := test_gLts; eq_rel := cgr; eq_rel_eq := _ |}.
    intros p q 𝜆 (r & Hpr & Hr).
    assert (Hrp : fwd r p) by (apply cgr_bisim; by symmetry).
    destruct 𝜆 as [a|].
    - destruct a as [c v|c v|E qs|M qs k].
      + apply tstep_ext in Hr as (l & El & Hs); [|done].
        destruct (Hrp _ _ Hs) as (l' & p' & El' & Hs' & Hq).
        exists p'. split; [|by symmetry]. apply tstep_ext; [done|]. exists l'. split; [congruence|done].
      + apply tstep_ext in Hr as (l & El & Hs); [|done].
        destruct (Hrp _ _ Hs) as (l' & p' & El' & Hs' & Hq).
        exists p'. split; [|by symmetry]. apply tstep_ext; [done|]. exists l'. split; [congruence|done].
      + apply tstep_ext in Hr as (l & El & Hs); [|done].
        destruct (Hrp _ _ Hs) as (l' & p' & El' & Hs' & Hq).
        exists p'. split; [|by symmetry]. apply tstep_ext; [done|]. exists l'. split; [congruence|done].
      + apply tstep_meas in Hr as (Hk & t & x & Q0 & Hs & ->).
        destruct (Hrp _ _ Hs) as ([s'|t' a'] & P0 & El & Hs' & HQ); simpl in El; simplify_eq.
        exists (subst P0 x (VNat k)). split.
        * apply tstep_meas. split; [done|]. eauto.
        * symmetry. by apply cgr_subst.
    - apply tstep_tau in Hr as (l & El & Hs).
      destruct (Hrp _ _ Hs) as (l' & p' & El' & Hs' & Hq).
      exists p'. split; [|by symmetry]. apply tstep_tau. exists l'. split; [congruence|done].
  Defined.

  #[global] Instance test_predicate : Testing_Predicate good test_gLtsEq.
  Proof.
    split.
    - apply _.
    - intros p q Hp Heq. unfold good in *. by rewrite <- (cgr_goodb p q Heq).
    - intros ??? [].
    - intros ??? [].
  Qed.

  (* *** Essential actions *)

  Definition ess_left (x : proc * St) : gset aact :=
    list_to_set ((λ '(c, v, _), POut c v) <$> prog_outs x.1).

  Definition test_ess (a : pact) : list tact :=
    match a with
    | AOut c v => [TOut c v]
    | AOp E qs => [TOp E qs]
    | AMeas M qs _ => (λ k, TMeas M qs k) <$> codes M qs
    | AIn _ _ => []
    end.

  Definition ess_right (Q : proc) : gset tact :=
    list_to_set (acts Q ≫= λ '(a, _), test_ess a).

  Lemma ess_left_step x μ : μ ∈ ess_left x → ∃ y, x ⟶[μ] y.
  Proof.
    destruct x as [P ρ]. unfold ess_left. rewrite elem_of_list_to_set, list_elem_of_fmap.
    intros ([[c v] P'] & -> & Hin). apply prog_outs_spec in Hin as (t & Hs).
    exists (P', ρ). apply pstep_out. exists P'. split; [done|]. by exists (LAct t (AOut c v)).
  Qed.

  Lemma ess_right_step Q μ : μ ∈ ess_right Q → ∃ Q', Q ⟶[μ] Q'.
  Proof.
    unfold ess_right. rewrite elem_of_list_to_set, list_elem_of_bind.
    intros ([a Q0] & Hξ & Hacts). apply acts_spec in Hacts as (Hni & t & Hs).
    destruct a; simpl in Hξ; try set_solver.
    - apply list_elem_of_singleton in Hξ as ->. exists Q0. apply tstep_ext; [done|].
      by exists (LAct t (AOut c v)).
    - apply list_elem_of_singleton in Hξ as ->. exists Q0. apply tstep_ext; [done|].
      by exists (LAct t (AOp E qs)).
    - apply list_elem_of_fmap in Hξ as (k & -> & Hk).
      exists (subst Q0 x (VNat k)). apply tstep_meas. split; [done|]. eauto.
  Qed.

  Lemma step_witness {S A} `{EA : ExtAction A} `{gL : !gLts S EA} p (μ : A) :
    (∃ q, p ⟶[μ] q) → {q | p ⟶[μ] q}.
  Proof.
    intros Hex. apply lts_performs_spec1.
    destruct Hex as (q & Hq). apply lts_performs_spec2. by exists q.
  Qed.

  #[global] Instance lqCCS_Prop_of_Inter :
    @Prop_of_Inter (proc * St) proc aact tact sync aact_ExtAction proc_gLts
      tact_ExtAction test_gLts.
  Proof.
    refine {|
      lts_essential_actions_left :=
        (ess_left : proc * St → @gset aact (@eqdec aact aact_ExtAction) (@countable aact aact_ExtAction));
      lts_essential_action_spec_left p ξ Hξ := step_witness p ξ (ess_left_step p ξ Hξ);
      lts_essential_actions_right :=
        (ess_right : proc → @gset tact (@eqdec tact tact_ExtAction) (@countable tact tact_ExtAction));
      lts_essential_action_spec_right p ξ Hξ := step_witness p ξ (ess_right_step p ξ Hξ);
      lts_co_inter_action_left ξ _ := {[ copartner ξ ]};
      lts_co_inter_action_right ξ _ := {[ partner ξ ]};
    |}.
    - (* every synchronisation goes through an essential action *)
      intros [P ρ] μ1 x Q μ2 Q' Hp Ht Hs. change (μ2 = partner μ1) in Hs. subst.
      destruct μ1 as [c v|c v|E qs|M qs j]; cbn [partner] in Ht.
      + left. apply pstep_out in Hp as (P' & -> & (l & El & Hs)).
        destruct l as [|t a]; simpl in El; simplify_eq. unfold ess_left.
        rewrite elem_of_list_to_set, list_elem_of_fmap. exists (c, v, P'). split; [done|].
        apply prog_outs_spec. eauto.
      + right. apply tstep_ext in Ht as (l & El & Hs); [|done].
        destruct l as [|t a]; simpl in El; simplify_eq. unfold ess_right.
        rewrite elem_of_list_to_set, list_elem_of_bind. exists (AOut c v, Q').
        split; [set_solver|]. apply acts_spec. split; [done|eauto].
      + right. apply tstep_ext in Ht as (l & El & Hs); [|done].
        destruct l as [|t a]; simpl in El; simplify_eq. unfold ess_right.
        rewrite elem_of_list_to_set, list_elem_of_bind. exists (AOp E qs, Q').
        split; [set_solver|]. apply acts_spec. split; [done|eauto].
      + right. apply tstep_meas in Ht as (Hk & t & y & Q0 & Hs & ->). unfold ess_right.
        rewrite elem_of_list_to_set, list_elem_of_bind. exists (AMeas M qs y, Q0).
        split.
        * simpl. apply list_elem_of_fmap. by exists j.
        * apply acts_spec. split; [done|eauto].
    - intros p p' ξ μ q _ _ Hs. change (ξ = partner μ) in Hs.
      apply partner_copartner in Hs as ->. set_solver.
    - intros q q' ξ μ p _ _ Hs. change (μ = partner ξ) in Hs. subst. set_solver.
  Defined.
End LTSs.
(* end hide *)
