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
From stdpp Require Import base countable decidable.
From TestingTheory Require Import ActTau gLts SyncActions MemAction InteractionUnion Bisimulation WeakTransitions Termination.

Section SyncMem.

Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.

Definition sync_mem (a : Aproc + MemAct Atest) (ζ : Atest) : Prop :=
  match a with
  | inl μ => sync μ ζ
  | inr (msg η) => dual η ζ
  | inr (cobar η) => ζ = η
  end.

#[local] Instance sync_mem_dec : RelDecision sync_mem.
Proof. intros [μ | [η | η]] ζ; simpl; apply _. Defined.

Definition SyncAction_mem : @SyncAction (Aproc + MemAct Atest) Atest ExtAction_sum Ht :=
  {| sync := sync_mem; sync_dec := sync_mem_dec |}.

End SyncMem.

#[global] Hint Extern 10 (ExtAction (?A + MemAct ?B)) =>
  assert_fails (is_evar A); assert_fails (is_evar B);
  exact (@ExtAction_sum A (MemAct B) _ _) : typeclass_instances.

#[global] Hint Extern 10 (@SyncAction (?A + MemAct ?B) _ _ _) =>
  assert_fails (is_evar A); assert_fails (is_evar B);
  exact (@SyncAction_mem A _ B _ _) : typeclass_instances.

Section FWMem.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Context {P Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context `{gLtsEqP : !gLtsEq P (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))}.

Class gLtsFWMem :=
  MkgLtsFWMem {
      fwm_boomerang (p : P) (η : Atest) :
        non_blocking η → ∃ p', p ⟶[inr (cobar η)] p' ∧ p' ⟶[inr (msg η)] p;
      fwm_feedback (p1 p2 p3 : P) (η : Atest) μ :
        non_blocking η → sync_mem μ η →
        p1 ⟶[inr (msg η)] p2 → p2 ⟶[μ] p3 → p1 ⟶⋍ p3 ∨ p1 ⋍ p3;
      fwm_delay (p q r : P) (η : Atest) 𝜆 :
        non_blocking η → p ⟶[inr (msg η)] q → q ⟶{𝜆} r →
        ∃ t, p ⟶{𝜆} t ∧ t ⟶⋍[inr (msg η)] r;
    }.

End FWMem.

Arguments gLtsFWMem P Aproc Atest {Hp Ht SA gLtsEqP}.

Section FWMemFacts.

#[local] Hint Mode ExtAction ! : typeclass_instances.

Context {P Aproc Atest : Type}.
Context `{Hp : ExtAction Aproc} `{Ht : ExtAction Atest} `{SA : !SyncAction Aproc Atest}.
Context `{gLtsEqP : !gLtsEq P (@ExtAction_sum Aproc (MemAct Atest) Hp (@ExtAction_mem Atest Ht))}.
Context `{FW : !gLtsFWMem P Aproc Atest}.

Lemma msg_spec (η : Atest) : non_blocking η →
    non_blocking (inr (msg η) : Aproc + MemAct Atest)
  ∧ (∀ μ, dual μ η → sync (inr (msg η) : Aproc + MemAct Atest) μ).
Proof. intros nb. split; [exact nb |]. intros μ hd. simpl. by symmetry. Qed.

Lemma fw_boomerang_total (p1 : P) (η : Atest) : non_blocking η →
  ∃ (β : Aproc + MemAct Atest) p2, sync β η ∧ p1 ⟶[β] p2 ∧ p2 ⟶[inr (msg η)] p1.
Proof.
  intros nb. destruct (fwm_boomerang p1 η nb) as (p2 & l1 & l2).
  by exists (inr (cobar η)), p2.
Qed.

Lemma sync_fwd_feedback {p1 p2 p3 : P} (η : Atest) (β : Aproc + MemAct Atest) :
  non_blocking η → sync β η →
  p1 ⟶[inr (msg η)] p2 → p2 ⟶[β] p3 → p1 ⟶⋍ p3 ∨ p1 ⋍ p3.
Proof. intros nb hs l1 l2. exact (fwm_feedback p1 p2 p3 η β nb hs l1 l2). Qed.

Lemma fw_delay {p q r : P} (η : Atest) {𝜆} :
  non_blocking η → p ⟶[inr (msg η)] q → q ⟶{𝜆} r →
  ∃ t, p ⟶{𝜆} t ∧ t ⟶⋍[inr (msg η)] r.
Proof. intros nb l1 l2. exact (fwm_delay p q r η 𝜆 nb l1 l2). Qed.

Lemma fw_delay_wt_nil {p q r : P} (η : Atest) :
  non_blocking η → p ⟶⋍[inr (msg η)] q → q ⟹ r →
  ∃ t, p ⟹ t ∧ t ⟶⋍[inr (msg η)] r.
Proof.
  intros nb l w.
  remember ([] : trace (Aproc + MemAct Atest)) as s0 eqn:Hs.
  revert p nb l Hs.
  induction w as [ x | s1 x y z lt w IH | μ s1 x y z lt w IH ];
    intros p0 nb (p' & hl & heq) Hs.
  - exists p0. split; [eapply wt_nil |].
    exists p'. split; [exact hl | exact heq].
  - assert (p' ⟶⋍ y) as (r0 & hlr & heqr).
    { eapply eq_spec. exists x. split; [exact heq | exact lt]. }
    destruct (fw_delay η nb hl hlr) as (r' & l1 & (t' & l2 & heqt')).
    destruct (IH r' nb
                (ex_intro _ t' (conj l2 (transitivity heqt' heqr))) Hs)
      as (r1 & w1 & sc).
    exists r1. split; [eapply wt_tau; [exact l1 | exact w1] | exact sc].
  - discriminate.
Qed.

Lemma fw_terminate_preserved {p q : P} (η : Atest) :
  non_blocking η → p ⟶[inr (msg η)] q → p ⤓ → q ⤓.
Proof.
  intros nb l ht. revert q l.
  induction ht as [p Hyp1 Hyp2].
  intros q l1.
  eapply tstep. intros q' l2.
  destruct (fw_delay η nb l1 l2) as (t & l3 & (q0 & l0 & eq0)).
  eapply terminate_preserved_by_eq; [| exact eq0].
  by eapply Hyp2.
Qed.

End FWMemFacts.
(* end hide *)
