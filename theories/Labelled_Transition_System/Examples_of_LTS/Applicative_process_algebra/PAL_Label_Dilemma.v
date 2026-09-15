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
From TestingTheory Require Import ActTau gLts InputOutputActions Bisimulation Subset_Act
  Testing_Predicate DefinitionAS Completeness PAL_Syntax Applicative_process_algebra.

(* * No labelling of PAL fits [FinitaryAbsAction] and [test_spec]

   Take any type of labels [A] with any [dual], and any LTS on the terms of
   PAL whose synchronisations along [dual] are exactly those of PAL
   ([hsync]; this is what [must] uses to make a process and a test
   communicate), with every action blocking. If [Val] is infinite, there are
   no [Φ], [𝝳] with [FinitaryAbsAction] and no [gen] with [test_spec].

   With [p? = in(?x).out(!x).𝟘], [p_v = in(!v).𝟘] and [T_v = out(!v).𝟘], let
   [c] be a label by which [T_v] synchronises with [p?] ([spec v c]):
   - [Φ_spec_inj]: by (1), different [v] give different [Φ c];
   - [not_in_coR_val]: by (2) and (1), if [𝝳 (Φ c) = 𝝳 (Φ c')] for a
     different [w], then [Φ c ∉ Φ(coR p_v)];
   - [𝝳Φ_spec_inj]: then [gen [c]] performs [c] and a second label towards
     the same state (the one synchronising with [p_v]), contradicting (6);
   - [no_labelling]: so [𝝳 ∘ Φ] is injective on these labels, which all lie
     in [coR p?], and [coR_abs p?] cannot be finite. *)

(** A finite set cannot contain infinitely many distinct elements. *)
Lemma finite_pigeonhole `{Countable B} (X : gset B) (P : nat → B → Prop) :
  (∀ n, ∃ b, P n b ∧ b ∈ X) → (∀ n m b, P n b → P m b → n = m) → False.
Proof.
  intros hex hinj.
  assert (∀ N, ∃ l, length l = N ∧ NoDup l ∧ ∀ b, b ∈ l → b ∈ X ∧ ∃ n, n < N ∧ P n b) as hlist.
  { induction N as [|N IH].
    - exists []. split_and!; [done | constructor | intros b hb; by apply elem_of_nil in hb].
    - destruct IH as (l & hlen & hnd & hl). destruct (hex N) as (b & hb & hbS).
      exists (b :: l). split_and!.
      + simpl. by rewrite hlen.
      + constructor; [| done]. intros hbl. destruct (hl b hbl) as (_ & n & hn & hPn).
        pose proof (hinj n N b hPn hb). lia.
      + intros b' [-> | hb']%elem_of_cons.
        * split; [done |]. exists N. split; [lia | done].
        * destruct (hl b' hb') as (hS & n & hn & hPn). split; [done |]. exists n. split; [lia | done]. }
  destruct (hlist (Datatypes.S (length (elements X)))) as (l & hlen & hnd & hl).
  assert (length l ≤ length (elements X)) as hle.
  { apply NoDup_incl_length; [by apply NoDup_ListNoDup |].
    intros b hb%list_elem_of_In. apply list_elem_of_In, elem_of_elements. by apply hl. }
  lia.
Qed.

Section PAL_Label_Dilemma.
  Context {Val : Type} `{Countable Val} (inj : nat → Val) `{!Inj eq eq inj}.

  Notation term := (PAL_Syntax.term Val).
  Notation eot := (eot Val).
  Notation old := (Applicative_process_algebra.lts_step Val).
  Open Scope pal_scope.


  (** ** PAL synchronisations *)

  Definition PAL_sync (p t p' t' : term) : Prop :=
    ∃ ot : eot, (old p (ActExt (ActIn ot)) p' ∧ old t (ActExt (ActOut ot)) t')
              ∨ (old p (ActExt (ActOut ot)) p' ∧ old t (ActExt (ActIn ot)) t').

  (** [in(?x).out(!x).𝟘], [in(!v).𝟘] and [out(!v).𝟘] *)
  Definition p_any : term := in( [? 0] ) • (out( [! ve_var 0] ) • 𝟘).
  Definition in_val (v : Val) : term := in( [! ve_val v] ) • 𝟘.
  Definition out_val (v : Val) : term := out( [! ve_val v] ) • 𝟘.

  Lemma p_any_in u : old p_any (ActExt (ActIn [of_val u])) (out_val u).
  Proof. exact (ar1 Val [f_formal 0] (t_out [f_actual (ve_var 0)] t_nil) [if_formal 0] [of_val u] eq_refl ltac:(repeat constructor)). Qed.

  Lemma p_any_in_inv ot q : old p_any (ActExt (ActIn ot)) q → ∃ u, ot = [of_val u] ∧ q = out_val u.
  Proof.
    inversion 1; subst.
    match goal with hev : eval_in_tuple _ = Some _ |- _ => cbn in hev; injection hev as <- end.
    match goal with hm : tuple_match _ _ |- _ =>
      inversion hm as [| ? ? ? ? hf ht]; subst; inversion hf; subst; inversion ht; subst end.
    eexists. split; [done |]. reflexivity.
  Qed.

  Lemma p_any_out_inv ot q : ¬ old p_any (ActExt (ActOut ot)) q.
  Proof. inversion 1. Qed.

  Lemma in_val_in v : old (in_val v) (ActExt (ActIn [of_val v])) t_nil.
  Proof. exact (ar1 Val [f_actual (ve_val v)] t_nil [if_val v] [of_val v] eq_refl ltac:(repeat constructor)). Qed.

  Lemma in_val_in_inv v ot q : old (in_val v) (ActExt (ActIn ot)) q → ot = [of_val v].
  Proof.
    inversion 1; subst.
    match goal with hev : eval_in_tuple _ = Some _ |- _ => cbn in hev; injection hev as <- end.
    match goal with hm : tuple_match _ _ |- _ =>
      inversion hm as [| ? ? ? ? hf ht]; subst; inversion hf; subst; inversion ht; subst end.
    done.
  Qed.

  Lemma in_val_out_inv v ot q : ¬ old (in_val v) (ActExt (ActOut ot)) q.
  Proof. inversion 1. Qed.

  Lemma out_val_out v : old (out_val v) (ActExt (ActOut [of_val v])) t_nil.
  Proof. by apply ar3. Qed.

  Lemma out_val_out_inv v ot q : old (out_val v) (ActExt (ActOut ot)) q → ot = [of_val v].
  Proof.
    inversion 1; subst.
    match goal with hev : eval_out_tuple _ = Some _ |- _ => cbn in hev; by injection hev end.
  Qed.

  Lemma out_val_in_inv v ot q : ¬ old (out_val v) (ActExt (ActIn ot)) q.
  Proof. inversion 1. Qed.

  Lemma out_val_inj u v : out_val u = out_val v → u = v.
  Proof. by injection 1. Qed.

  (** ** Any labelling *)

  Context {A : Type} {EA : ExtAction A} {gLtsT : gLtsEq term EA}.
  Context {FinA PreAct : Type} `{Countable PreAct} (Φ : A → FinA) (𝝳 : FinA → PreAct).
  Context {Fin : @FinitaryAbsAction term term FinA PreAct A EA Φ 𝝳 gLtsEq_gLts gLtsT _ _}.
  Context (outcome : term → Prop) {TP : Testing_Predicate outcome gLtsT} (gen : list A → term)
    {TS : @test_spec term A EA gLtsT outcome TP gen}.

  #[local] Hint Mode ExtAction ! : typeclass_instances.

  (** Every action is blocking. *)
  Context (hblock : ∀ μ : A, ¬ non_blocking μ).

  (** A process and a test communicate along [dual] exactly when they synchronise in PAL. *)
  Context (hsync : ∀ p t p' t' : term,
    (∃ μ1 μ2 : A, dual μ1 μ2 ∧ p ⟶[μ1] p' ∧ t ⟶[μ2] t') ↔ PAL_sync p t p' t').

  (** The fields used, with their instances given explicitly. *)
  Definition Abs : @AbsAction term term FinA PreAct A EA Φ 𝝳 gLtsEq_gLts gLtsT := Fin.(FinitaryAbsAction_Abs).

  Lemma accepts_of_step (p q : term) (μ : A) : p ⟶[μ] q → μ ∈ R p.
  Proof. intros h. exact (lts_refuses_spec2 p (ActExt μ) (exist _ q h)). Qed.

  (** [c] is a label by which [out(!v).𝟘] synchronises with [in(?x).out(!x).𝟘]. *)
  Definition spec (v : Val) (c : A) : Prop :=
    ∃ a : A, dual a c ∧ p_any ⟶[a] out_val v ∧ out_val v ⟶[c] t_nil.

  Lemma spec_exists v : ∃ c, spec v c.
  Proof.
    destruct (proj2 (hsync p_any (out_val v) (out_val v) t_nil)) as (a & c & hd & ha & hc).
    - exists [of_val v]. left. split; [apply p_any_in | apply out_val_out].
    - exists c, a. done.
  Qed.

  Lemma spec_coR v c : spec v c → c ∈ coR p_any.
  Proof. intros (a & hd & ha & hc). exists a. split_and!; [by eapply accepts_of_step | done | apply hblock]. Qed.

  (** By (1): different values give different [Φ c]. *)
  Lemma Φ_spec_inj v w c c' : spec v c → spec w c' → Φ c = Φ c' → v = w.
  Proof.
    intros (a & hd & ha & hc) (a' & hd' & ha' & hc') e.
    assert (c' ∈ R (out_val v)) as hacc.
    { apply (Abs.(abstraction_test_spec) (out_val v) c c' (hblock c) (hblock c') e).
      by eapply accepts_of_step. }
    apply lts_refuses_spec1 in hacc as (t' & ht').
    destruct (proj1 (hsync p_any (out_val v) (out_val w) t')) as (ot & [[h1 h2] | [h1 h2]]).
    - exists a', c'. done.
    - apply p_any_in_inv in h1 as (u & -> & hq). apply out_val_inj in hq.
      apply out_val_out_inv in h2. injection h2. congruence.
    - by apply p_any_out_inv in h1.
  Qed.

  (** By (2) and (1). *)
  Lemma not_in_coR_val v w c c' :
    v ≠ w → spec v c → spec w c' → 𝝳 (Φ c) = 𝝳 (Φ c') → Φ c ∉ ⌈ Φ ⌉ (coR (in_val v)).
  Proof.
    intros hne hc hc' e hin.
    apply (Abs.(abstraction_prog_spec) (in_val v) c c' (hblock c) (hblock c') e) in hin as (x & hx & ex).
    destruct hx as (μ2 & acc & hd & _). apply lts_refuses_spec1 in acc as (q & hq).
    destruct hc' as (a' & hd' & ha' & hstep').
    assert (x ∈ R (out_val w)) as hacc.
    { apply (Abs.(abstraction_test_spec) (out_val w) c' x (hblock c') (hblock x) ex).
      by eapply accepts_of_step. }
    apply lts_refuses_spec1 in hacc as (t' & ht').
    destruct (proj1 (hsync (in_val v) (out_val w) q t')) as (ot & [[h1 h2] | [h1 h2]]).
    - exists μ2, x. done.
    - apply in_val_in_inv in h1 as ->. apply out_val_out_inv in h2. injection h2. congruence.
    - by apply in_val_out_inv in h1.
  Qed.

  (** By (2), (5), (6): [𝝳 ∘ Φ] is injective on these labels. *)
  Lemma 𝝳Φ_spec_inj v w c c' : spec v c → spec w c' → 𝝳 (Φ c) = 𝝳 (Φ c') → v = w.
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
    - apply (not_in_coR_val v w c c' hne); [by exists a | done | done |].
      exists c. split; [| done].
      exists μ1. split_and!; [by eapply accepts_of_step | done | apply hblock].
    - apply (TS.(test_ungood) []).
      apply (TP.(outcome_preserved_by_eq) t (gen [])); [| exact heq].
      exact (TS.(test_side_effect_by_construction) (hblock c) hdstep hdc).
  Qed.

  Theorem no_labelling : False.
  Proof.
    apply (finite_pigeonhole (Fin.(coR_abs) p_any) (λ n b, ∃ c, spec (inj n) c ∧ b = 𝝳 (Φ c))).
    - intros n. destruct (spec_exists (inj n)) as (c & hc).
      exists (𝝳 (Φ c)). split; [by exists c |].
      apply (Fin.(coR_abs_spec2) (𝝳 (Φ c)) p_any). exists c. split; [by eapply spec_coR | done].
    - intros n m b (c & hc & ->) (c' & hc' & e). apply (inj_iff inj).
      by apply (𝝳Φ_spec_inj (inj n) (inj m) c c').
  Qed.
End PAL_Label_Dilemma.
