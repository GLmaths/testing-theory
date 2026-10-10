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

(* * The almost-sure must of lqCCS, characterised by co-acceptance sets

    Three steps:
    - [lqCCS_AlmostSure.v] and [lqCCS_MustSupp.v]: the almost-sure must of
      lqCCS is the must of the two LTSs of [lqCCS_LTS.v] (processes over
      [aact], observers over [tact], linked by [sync]);
    - here: that must is the must of the one-alphabet LTSs of
      [lqCCS_FwLTS.v] and [lqCCS_Observers.v] — same states, same silent
      steps, same synchronisations up to the names of the actions
      ([must_transfer]);
    - [lqCCS_Observers.v]: the latter is characterised by co-acceptance
      sets.

    Scope: the observers are untyped — they may act on every qubit of the
    memory, including those the process owns.  With the linear typing of
    the paper ([lqCCS_Typing.v]) an observer only acts on the qubits it owns,
    and the preorder is strictly coarser: [0_q] with [|0⟩⟨0|] and [0_q] with
    [|1⟩⟨1|] own [q] and never give it away; the untyped observer
    [M(q ▷ x).(if x = 0 then ① else 0)] tells them apart, no typed observer
    does.  The typed preorder needs its own characterisation: co-traces
    restricted to what a typed observer can perform. *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base countable decidable list gmap gmultiset.
From TestingTheory Require Import Lifted Paths States lqCCS_Quantum.
From TestingTheory Require Import lqCCS_Syntax lqCCS_Program lqCCS_Succ lqCCS_Congruence
  lqCCS_Composition lqCCS_LTS lqCCS_MustSupp lqCCS_AlmostSure lqCCS_FwLTS lqCCS_Observers.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Testing_Predicate
  StateTransitionSystems InteractionBetweenLts MultisetLTSConstruction ForwarderConstruction
  Must DefinitionASco pMust_almost_sure pMust_smyth.

(* ** Must is invariant under a renaming of the actions *)

Section MustTransfer.
  Context {P T A1 B1 A2 B2 : Type}.
  Context {HA1 : ExtAction A1} {HB1 : ExtAction B1} {HA2 : ExtAction A2} {HB2 : ExtAction B2}.
  Context {gP1 : gLts P HA1} {gT1 : gLtsEq T HB1} {SA1 : SyncAction A1 B1}
    {ST1 : ParSts P T gP1 gT1}.
  Context {gP2 : gLts P HA2} {gT2 : gLtsEq T HB2} {SA2 : SyncAction A2 B2}
    {ST2 : ParSts P T gP2 gT2}.
  Context (PS1 : ParStsSpec P T gP1 gT1 SA1 ST1) (PS2 : ParStsSpec P T gP2 gT2 SA2 ST2).
  Context {outcome : T → Prop} {TP1 : Testing_Predicate outcome gT1}
    {TP2 : Testing_Predicate outcome gT2}.

  Notation step1 := (@lts_step P A1 HA1 gP1).
  Notation tstep1 := (@lts_step T B1 HB1 (@gLtsEq_gLts T B1 HB1 gT1)).
  Notation step2 := (@lts_step P A2 HA2 gP2).
  Notation tstep2 := (@lts_step T B2 HB2 (@gLtsEq_gLts T B2 HB2 gT2)).
  Notation sync1 := (@sync A1 B1 HA1 HB1 SA1).
  Notation sync2 := (@sync A2 B2 HA2 HB2 SA2).

  Context (Hp21 : ∀ p p', step2 p τ p' → step1 p τ p')
          (Ht21 : ∀ t t', tstep2 t τ t' → tstep1 t τ t')
          (Hs21 : ∀ p p' t t' a b, sync2 a b → step2 p (ActExt a) p' → tstep2 t (ActExt b) t' →
                  ∃ μ1 μ2, sync1 μ1 μ2 ∧ step1 p (ActExt μ1) p' ∧ tstep1 t (ActExt μ2) t')
          (Hp12 : ∀ p p', step1 p τ p' → step2 p τ p')
          (Ht12 : ∀ t t', tstep1 t τ t' → tstep2 t τ t')
          (Hs12 : ∀ p p' t t' μ1 μ2, sync1 μ1 μ2 → step1 p (ActExt μ1) p' →
                  tstep1 t (ActExt μ2) t' →
                  ∃ a b, sync2 a b ∧ step2 p (ActExt a) p' ∧ tstep2 t (ActExt b) t').

  Lemma must_transfer p t :
    @must P A1 HA1 gP1 T B1 HB1 gT1 outcome TP1 SA1 ST1 p t →
    @must P A2 HA2 gP2 T B2 HB2 gT2 outcome TP2 SA2 ST2 p t.
  Proof.
    induction 1 as [p t Ho|p t nh ex pt IHpt et IHet com IHcom].
    - by apply m_now.
    - apply m_step; [done| | | |].
      + destruct ex as (y & Hy).
        destruct (par_step_inv (ParStsSpec := PS1) p t y Hy)
          as [(p' & -> & H)|[(t' & -> & H)|(p' & t' & μ1 & μ2 & -> & Hsy & H1 & H2)]].
        * exists (p', t). apply (par_step_left (ParStsSpec := PS2)). by apply Hp12.
        * exists (p, t'). apply (par_step_right (ParStsSpec := PS2)). by apply Ht12.
        * destruct (Hs12 _ _ _ _ _ _ Hsy H1 H2) as (a & b & Hab & Ha & Hb).
          exists (p', t'). by apply (par_step_sync (ParStsSpec := PS2) _ _ _ _ a b).
      + intros p' H. apply IHpt. by apply Hp21.
      + intros t' H. apply IHet. by apply Ht21.
      + intros p' t' a b Hab H1 H2.
        destruct (Hs21 _ _ _ _ _ _ Hab H1 H2) as (μ1 & μ2 & Hsy & H1' & H2').
        by eapply IHcom.
  Qed.
End MustTransfer.

(* ** The two settings of lqCCS have the same steps *)

Section Settings.
  Context `{QM : QuantumModel}.

  Notation pconf := (proc * St)%type.

  Lemma test_tau_one_two (Q Q' : proc) :
    @lts_step _ _ _ obs_gLts Q τ Q' ↔ @lts_step _ _ _ test_gLts Q τ Q'.
  Proof. reflexivity. Qed.

  Lemma tau_one_two (x y : pconf) :
    @lts_step _ _ _ pconf_gLts x τ y ↔ @lts_step _ _ _ proc_gLts x τ y.
  Proof.
    destruct x as [P ρ]. rewrite pconf_step_def, pstep_tau. split.
    - intros Hs. inversion Hs; subst.
      + left. eauto.
      + right; left. eauto 10.
      + right; right. eauto 10.
    - intros [(P' & -> & Hu)|[(t & E & qs & P' & Hp & ->)|(t & M & qs & y' & P0 & k & Hp & Hn & ->)]].
      + by constructor.
      + by econstructor.
      + by econstructor.
  Qed.

  Lemma sync_one_two (x x' : pconf) Q Q' μ1 μ2 :
    μ2 = lco μ1 → @lts_step _ _ _ pconf_gLts x (ActExt μ1) x' →
    @lts_step _ _ _ obs_gLts Q (ActExt μ2) Q' →
    ∃ a b, b = partner a ∧ @lts_step _ _ _ proc_gLts x (ActExt a) x'
           ∧ @lts_step _ _ _ test_gLts Q (ActExt b) Q'.
  Proof.
    intros -> Hx1 Hx2. destruct x as [P ρ].
    apply pconf_step_def in Hx1. apply obs_step_def in Hx2.
    inversion Hx1 as [| | |P0 P' ρ0 c v Hu|P0 P' ρ0 c v Hu|P0 ρ0 E qs|P0 ρ0 M qs k Hn];
      subst; simpl in Hx2.
    - exists (POut c v), (TIn c v). split_and!; [done|apply pstep_out; eauto|].
      apply (tstep_ext _ (TIn c v)); [by intros ???|exact Hx2].
    - exists (PIn c v), (TOut c v). split_and!; [done|apply pstep_in; eauto|].
      apply (tstep_ext _ (TOut c v)); [by intros ???|exact Hx2].
    - exists (SApply E qs), (TOp E qs). split_and!; [done|by apply pstep_apply|].
      apply (tstep_ext _ (TOp E qs)); [by intros ???|exact Hx2].
    - exists (SMeas M qs (code _ k)), (TMeas M qs (code _ k)).
      split_and!; [done|apply pstep_smeas; eauto|].
      destruct Hx2 as (y & Q0 & ([s|t a] & El & Hs) & ->); simpl in El; simplify_eq.
      apply tstep_meas. split.
      + unfold codes. apply list_elem_of_fmap. exists k. split; [done|].
        apply list_elem_of_In, outs_all.
      + eauto.
  Qed.

  Lemma sync_two_one (x x' : pconf) Q Q' a b :
    b = partner a → @lts_step _ _ _ proc_gLts x (ActExt a) x' →
    @lts_step _ _ _ test_gLts Q (ActExt b) Q' →
    ∃ μ1 μ2, μ2 = lco μ1 ∧ @lts_step _ _ _ pconf_gLts x (ActExt μ1) x'
             ∧ @lts_step _ _ _ obs_gLts Q (ActExt μ2) Q'.
  Proof.
    intros -> Hx1 Hx2. destruct x as [P ρ].
    destruct a as [c v|c v|E qs|M qs n]; simpl in Hx2.
    - apply pstep_out in Hx1 as (P' & -> & Hu).
      apply (tstep_ext _ (TIn c v)) in Hx2; [|by intros ???].
      exists (LOut c v), (LIn c v). split_and!; [done| |].
      + apply pconf_step_def. by constructor.
      + by apply obs_step_def.
    - apply pstep_in in Hx1 as (P' & -> & Hu).
      apply (tstep_ext _ (TOut c v)) in Hx2; [|by intros ???].
      exists (LIn c v), (LOut c v). split_and!; [done| |].
      + apply pconf_step_def. by constructor.
      + by apply obs_step_def.
    - apply pstep_apply in Hx1 as ->.
      apply (tstep_ext _ (TOp E qs)) in Hx2; [|by intros ???].
      exists (LOp E qs), (LOp E qs). split_and!; [done| |].
      + apply pconf_step_def. constructor.
      + by apply obs_step_def.
    - apply pstep_smeas in Hx1 as (k & <- & Hn & ->).
      apply tstep_meas in Hx2 as (_ & t & y & Q0 & Hs & ->).
      exists (LMeas M qs (code _ k)), (LMeas M qs (code _ k)). split_and!; [done| |].
      + apply pconf_step_def. by constructor.
      + apply obs_step_def. exists y, Q0. split; [|done].
        by exists (LAct t (AMeas M qs y)).
  Qed.

  Lemma must_one_two (x : pconf) (Q : proc) :
    must (gLtsP := pconf_gLts) (gLtsT := obs_gLtsEq) (outcome := good)
      (SA := SyncAction_of_dual) x Q →
    must (gLtsP := proc_gLts) (gLtsT := test_gLtsEq) (outcome := good) x Q.
  Proof.
    intros Hm. unshelve eapply (must_transfer _ _ _ _ _ _ _ _ x Q Hm).
    all: lazymatch goal with
         | |- ParStsSpec _ _ _ _ _ _ => exact _
         | |- ∀ _ _, @lts_step _ _ _ _ _ τ _ → _ =>
             intros ?? Hτ; first [by apply tau_one_two | by apply test_tau_one_two]
         | |- _ =>
             intros p p' t t' a b Hab Hx1 Hx2;
             first [by apply (sync_two_one p p' t t' a b) | by apply (sync_one_two p p' t t' a b)]
         end.
  Qed.

  Lemma must_two_one (x : pconf) (Q : proc) :
    must (gLtsP := proc_gLts) (gLtsT := test_gLtsEq) (outcome := good) x Q →
    must (gLtsP := pconf_gLts) (gLtsT := obs_gLtsEq) (outcome := good)
      (SA := SyncAction_of_dual) x Q.
  Proof.
    intros Hm. unshelve eapply (must_transfer _ _ _ _ _ _ _ _ x Q Hm).
    all: lazymatch goal with
         | |- ParStsSpec _ _ _ _ _ _ => exact _
         | |- ∀ _ _, @lts_step _ _ _ _ _ τ _ → _ =>
             intros ?? Hτ; first [by apply tau_one_two | by apply test_tau_one_two]
         | |- _ =>
             intros p p' t t' a b Hab Hx1 Hx2;
             first [by apply (sync_two_one p p' t t' a b) | by apply (sync_one_two p p' t t' a b)]
         end.
  Qed.
End Settings.

(* ** The characterisation of the almost-sure must *)

Section Characterisation.
  Context `{QM : QuantumModel} `{SC : !Countable St}.
  Context (XM : ∀ P : Prop, P ∨ ¬ P).
  Context (W_strict : ∀ a b, W_le (W_add a b) a → b = W_zero).
  Context (W_dense : ∀ a b : W, a <ₚ b → ∃ c, a <ₚ c ∧ c <ₚ b).

  (* For non-zero memories: [(P, ρ)] is below [(Q, σ)] for the almost-sure
      must of lqCCS iff, up to the abstraction, the co-acceptance sets of
      [(Q, σ)] are matched by those of [(P, ρ)] ([≼꜀ₒ₋ₐₛ]). *)
  Theorem lq_pre_as_iff_co_acceptance_set P ρ Q σ :
    nonzero ρ → nonzero σ →
    (P, ρ) ⊑ₐₛ (Q, σ) ↔ ((P, ρ) ▷ (∅ : MO lact)) ≼꜀ₒ₋ₐₛ ((Q, σ) ▷ (∅ : MO lact)).
  Proof.
    intros Hρ Hσ. rewrite <- must_iff_co_acceptance_set_lqCCS. split.
    - intros Hpre T Hm.
      apply must_two_one. apply (lq_must_as_iff_must XM W_strict W_dense _ _ _ Hσ).
      apply Hpre. apply (lq_must_as_iff_must XM W_strict W_dense _ _ _ Hρ).
      by apply must_one_two.
    - intros Hpre T Hm.
      apply (lq_must_as_iff_must XM W_strict W_dense _ _ _ Hσ). apply must_one_two.
      apply Hpre. apply must_two_one.
      by apply (lq_must_as_iff_must XM W_strict W_dense _ _ _ Hρ).
  Qed.

  (* ** The Smyth must

      It is quantitative, so it is not determined by the supports and has no
      characterisation by co-acceptance sets: the inclusion of co-acceptance
      sets is only a necessary condition. *)

  #[local] Instance lq_DenseWeights : DenseWeights := {| prob_dense := W_dense |}.

  Lemma lq_pre_sm_as P ρ Q σ :
    W_le (tr σ) (tr ρ) → (P, ρ) ⊑ₛₘ (Q, σ) → (P, ρ) ⊑ₐₛ (Q, σ).
  Proof.
    intros Htr. apply ctx_pre_sm_as. intros t w Hw. simpl in *.
    rewrite W_add_zero_r in *. by eapply prob_lt_le_trans.
  Qed.

  Corollary lq_pre_sm_co_acceptance_set P ρ Q σ :
    nonzero ρ → nonzero σ → W_le (tr σ) (tr ρ) →
    (P, ρ) ⊑ₛₘ (Q, σ) → ((P, ρ) ▷ (∅ : MO lact)) ≼꜀ₒ₋ₐₛ ((Q, σ) ▷ (∅ : MO lact)).
  Proof.
    intros Hρ Hσ Htr Hsm.
    apply (lq_pre_as_iff_co_acceptance_set _ _ _ _ Hρ Hσ).
    by apply lq_pre_sm_as.
  Qed.
End Characterisation.
(* end hide *)
