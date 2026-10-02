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
From Stdlib.Lists Require Import List.
Import ListNotations.
From stdpp Require Import base tactics decidable countable list gmap.
From TestingTheory Require Import ActTau gLts SyncActions Bisimulation Subset_Act
  Testing_Predicate DefinitionAS CompletenessASco PAL_Syntax Applicative_process_algebra
  PAL_Label_Dilemma.

(* * The PAL dilemma survives the separation of the alphabets

   [PAL_Label_Dilemma.v] with two alphabets: the processes are labelled over
   [Aproc], the tests over [Atest], and they meet along [sync].  The two LTSs
   on the terms of PAL are now independent — a process and a test may label
   the same term differently — and nothing is asked of the process labels.
   Only the test labels are blocking.

   The proof is the one-alphabet one: it never compares a process label with
   a test label except through the synchronisation, so [dual] becomes [sync]
   and nothing else moves.  The obstruction is on the observer's side: the
   co-actions [coR in(?x)] are test emissions, one per value, which (1) and
   (2) make pairwise distinct, while the process labels play no role in the
   count.  Separating [Aproc] from [Atest] therefore cannot make PAL
   finitary; only making the test emissions non-blocking (they then leave
   [coR]) or changing (1)/(2) can. *)

Section PAL_Label_Dilemma_Sync.
  Context {Val : Type} `{Countable Val} (inj : nat → Val) `{!Inj eq eq inj}.

  Notation term := (PAL_Syntax.term Val).
  Open Scope pal_scope.

  (** ** Any pair of labellings *)

  Context {Aproc Atest : Type} {Hp : ExtAction Aproc} {Ht : ExtAction Atest}.
  Context {SA : SyncAction Aproc Atest}.
  Context {gLtsP : gLts term Hp} {gLtsT : gLtsEq term Ht}.
  Context {FinA PreAct : Type} `{Countable PreAct} (Φ : Atest → FinA) (𝝳 : FinA → PreAct).
  Context {Fin : @FinitaryAbsAction term term FinA PreAct Atest Ht Φ 𝝳 Aproc Hp gLtsP gLtsT SA _ _}.
  Context (outcome : term → Prop) {TP : Testing_Predicate outcome gLtsT} (gen : list Atest → term)
    {TS : @test_spec term Atest Ht gLtsT outcome TP gen}.

  #[local] Hint Mode ExtAction ! : typeclass_instances.

  (** Every test action is blocking. *)
  Context (hblock : ∀ η : Atest, ¬ non_blocking η).

  (** A process and a test communicate along [sync] exactly when they
      synchronise in PAL. *)
  Context (hsync : ∀ p t p' t' : term,
    (∃ (μ1 : Aproc) (μ2 : Atest), sync μ1 μ2 ∧ p ⟶[μ1] p' ∧ t ⟶[μ2] t') ↔ PAL_sync p t p' t').

  Definition Abs_sync : @AbsAction term term FinA PreAct Atest Ht Φ 𝝳 Aproc Hp gLtsP gLtsT SA :=
    Fin.(FinitaryAbsAction_Abs).

  Lemma accepts_of_step_p (p q : term) (μ : Aproc) : p ⟶[μ] q → μ ∈ R p.
  Proof. intros h. exact (lts_refuses_spec2 p (ActExt μ) (exist _ q h)). Qed.

  Lemma accepts_of_step_t (p q : term) (μ : Atest) : p ⟶[μ] q → μ ∈ R p.
  Proof. intros h. exact (lts_refuses_spec2 p (ActExt μ) (exist _ q h)). Qed.

  (** [c] is a label by which the test [out(!v).𝟘] synchronises with the
      process [in(?x).out(!x).𝟘]. *)
  Definition spec_sync (v : Val) (c : Atest) : Prop :=
    ∃ a : Aproc, sync a c ∧ p_any ⟶[a] out_val v ∧ out_val v ⟶[c] t_nil.

  Lemma spec_sync_exists v : ∃ c, spec_sync v c.
  Proof.
    destruct (proj2 (hsync p_any (out_val v) (out_val v) t_nil)) as (a & c & hd & ha & hc).
    - exists [of_val v]. left. split; [apply p_any_in | apply out_val_out].
    - exists c, a. done.
  Qed.

  Lemma spec_sync_coR v c : spec_sync v c → c ∈ coR p_any.
  Proof.
    intros (a & hd & ha & hc).
    exists a. split_and!; [by eapply accepts_of_step_p | done | apply hblock].
  Qed.

  (** By (1): different values give different [Φ c]. *)
  Lemma Φ_spec_sync_inj v w c c' : spec_sync v c → spec_sync w c' → Φ c = Φ c' → v = w.
  Proof.
    intros (a & hd & ha & hc) (a' & hd' & ha' & hc') e.
    assert (c' ∈ R (out_val v)) as hacc.
    { apply (Abs_sync.(abstraction_test_spec) (out_val v) c c' (hblock c) (hblock c') e).
      by eapply accepts_of_step_t. }
    apply lts_refuses_spec1 in hacc as (t' & ht').
    destruct (proj1 (hsync p_any (out_val v) (out_val w) t')) as (ot & [[h1 h2] | [h1 h2]]).
    - exists a', c'. done.
    - apply p_any_in_inv in h1 as (u & -> & hq). apply out_val_inj in hq.
      apply out_val_out_inv in h2. injection h2. congruence.
    - by apply p_any_out_inv in h1.
  Qed.

  (** By (2) and (1). *)
  Lemma not_in_coR_val_sync v w c c' :
    v ≠ w → spec_sync v c → spec_sync w c' → 𝝳 (Φ c) = 𝝳 (Φ c') →
    Φ c ∉ ⌈ Φ ⌉ (coR (in_val v)).
  Proof.
    intros hne hc hc' e hin.
    apply (Abs_sync.(abstraction_prog_spec) (in_val v) c c' (hblock c) (hblock c') e)
      in hin as (x & hx & ex).
    destruct hx as (μ2 & acc & hd & _). apply lts_refuses_spec1 in acc as (q & hq).
    destruct hc' as (a' & hd' & ha' & hstep').
    assert (x ∈ R (out_val w)) as hacc.
    { apply (Abs_sync.(abstraction_test_spec) (out_val w) c' x (hblock c') (hblock x) ex).
      by eapply accepts_of_step_t. }
    apply lts_refuses_spec1 in hacc as (t' & ht').
    destruct (proj1 (hsync (in_val v) (out_val w) q t')) as (ot & [[h1 h2] | [h1 h2]]).
    - exists μ2, x. done.
    - apply in_val_in_inv in h1 as ->. apply out_val_out_inv in h2. injection h2. congruence.
    - by apply in_val_out_inv in h1.
  Qed.

  (** By (2), (5), (6): [𝝳 ∘ Φ] is injective on these labels. *)
  Lemma 𝝳Φ_spec_sync_inj v w c c' :
    spec_sync v c → spec_sync w c' → 𝝳 (Φ c) = 𝝳 (Φ c') → v = w.
  Proof.
    intros hc hc' e. destruct (decide (v = w)) as [| hne]; [done | exfalso].
    destruct (TS.(test_next_step) c []) as (t & ht & heq).
    destruct hc as (a & hd & ha & hstep).
    (* [gen [c]] emits [⟨v⟩] towards [t] *)
    destruct (proj1 (hsync p_any (gen [c]) (out_val v) t)) as (ot & [[h1 h2] | [h1 h2]]).
    { exists a, c. done. }
    2: { by apply p_any_out_inv in h1. }
    apply p_any_in_inv in h1 as (u & -> & hq). apply out_val_inj in hq. subst u.
    (* so it synchronises with [in(!v).𝟘] towards [t] *)
    destruct (proj2 (hsync (in_val v) (gen [c]) t_nil t)) as (μ1 & d & hd1 & h1' & hdstep).
    { exists [of_val v]. left. split; [apply in_val_in | exact h2]. }
    destruct (decide (d = c)) as [-> | hdc].
    - apply (not_in_coR_val_sync v w c c' hne); [by exists a | done | done |].
      exists c. split; [| done].
      exists μ1. split_and!; [by eapply accepts_of_step_p | done | apply hblock].
    - apply (TS.(test_ungood) []).
      apply (TP.(outcome_preserved_by_eq) t (gen [])); [| exact heq].
      exact (TS.(test_side_effect_by_construction) (hblock c) hdstep hdc).
  Qed.

  Theorem no_labelling_sync : False.
  Proof.
    apply (finite_pigeonhole (Fin.(coR_abs) p_any) (λ n b, ∃ c, spec_sync (inj n) c ∧ b = 𝝳 (Φ c))).
    - intros n. destruct (spec_sync_exists (inj n)) as (c & hc).
      exists (𝝳 (Φ c)). split; [by exists c |].
      apply (Fin.(coR_abs_spec2) (𝝳 (Φ c)) p_any). exists c. split; [by eapply spec_sync_coR | done].
    - intros n m b (c & hc & ->) (c' & hc' & e). apply (inj_iff inj).
      by apply (𝝳Φ_spec_sync_inj (inj n) (inj m) c c').
  Qed.
End PAL_Label_Dilemma_Sync.
