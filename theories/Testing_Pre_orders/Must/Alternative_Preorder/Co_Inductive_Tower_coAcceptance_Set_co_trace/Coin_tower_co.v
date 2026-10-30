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
From stdpp Require Import base countable finite gmap list sets.
From Coinduction Require Import all.
From TestingTheory Require Import ActTau gLts SyncActions Subset_Act Termination
  coWeakTransition coConvergence coFiniteImage DefinitionASrel.
Import ListNotations.

(* begin hide *)
Record copre_co_ `{gLtsP : @gLts P Ap Hp} `{Ht : ExtAction At} `{SA : !SyncAction Ap At}
  `{CFI : !coFiniteImagegLts P At} {PreAct : Type} (Γ : At → PreAct)
  (FIX : gset P → gset P → Prop) (X Y : gset P) : Prop := {
    cc_tau_ Y' : (∀ q', q' ∈ Y' → ∃ q, q ∈ Y ∧ q ⟹ᶜᵒ q') → FIX X Y'
  ; cc_now_ : (∀ p, p ∈ X → p ⤓) → ∀ q, q ∈ Y → q ↛ →
      ∃ p, p ∈ X ∧ ∃ p', p ⟹ᶜᵒ p' ∧ p' ↛ ∧ ⌈ Γ ⌉ (coR p') ⊆ ⌈ Γ ⌉ (coR q)
  ; cc_step_ μ X' Y' : (∀ p, p ∈ X → p ⇓ᶜᵒ [μ]) →
      (∀ q', q' ∈ Y' → ∃ q, q ∈ Y ∧ q ⟹ᶜᵒ{μ} q') →
      (∀ p', p' ∈ X' ↔ ∃ p, p ∈ X ∧ p ⟹ᶜᵒ{μ} p') → FIX X' Y'
  ; cc_cnv_ : (∀ p, p ∈ X → p ⤓) → ∀ q, q ∈ Y → q ⤓
  }.

#[global] Arguments cc_tau_ {_ _ _ _ _ _ _ _ _ Γ FIX X Y}.
#[global] Arguments cc_now_ {_ _ _ _ _ _ _ _ _ Γ FIX X Y}.
#[global] Arguments cc_step_ {_ _ _ _ _ _ _ _ _ Γ FIX X Y}.
#[global] Arguments cc_cnv_ {_ _ _ _ _ _ _ _ _ Γ FIX X Y}.
(* end hide *)

Program Definition copre_co_m `{gLtsP : @gLts P Ap Hp} `{Ht : ExtAction At} `{SA : !SyncAction Ap At}
  `{CFI : !coFiniteImagegLts P At} {PreAct : Type} (Γ : At → PreAct) : mon (gset P → gset P → Prop) :=
  {| body := copre_co_ Γ |}.
Next Obligation.
  intros F1 F2 HF X Y h. constructor.
  - intros Y' hY'. apply HF, (cc_tau_ h Y' hY').
  - exact (cc_now_ h).
  - intros μ X' Y' hX hY' hX'. apply HF, (cc_step_ h μ X' Y' hX hY' hX').
  - exact (cc_cnv_ h).
Qed.

Definition copre_co `{gLtsP : @gLts P Ap Hp} `{Ht : ExtAction At} `{SA : !SyncAction Ap At}
  `{CFI : !coFiniteImagegLts P At} {PreAct : Type} (Γ : At → PreAct) : gset P → gset P → Prop :=
  gfp (copre_co_m Γ).

Notation "X ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ Γ ] Y" := (copre_co Γ X Y) (at level 70).

(* begin hide *)
Section copre_co.

Context `{gLtsP : @gLts P Ap Hp} `{Ht : ExtAction At} `{SA : !SyncAction Ap At}.
Context `{CFI : !coFiniteImagegLts P At}.
Context {PreAct : Type} (Γ : At → PreAct).

Definition set_cnv_co (X Y : gset P) : Prop :=
  ∀ s, (∀ p, p ∈ X → p ⇓ᶜᵒ s) → ∀ q, q ∈ Y → q ⇓ᶜᵒ s.

Definition set_acc_co (X Y : gset P) : Prop :=
  ∀ s q q', q ∈ Y → (∀ p, p ∈ X → p ⇓ᶜᵒ s) → q ⟹ᶜᵒ[s] q' → q' ↛ →
    ∃ p, p ∈ X ∧ ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γ ⌉ (coR p') ⊆ ⌈ Γ ⌉ (coR q').

Definition set_pre_co (X Y : gset P) : Prop := set_cnv_co X Y ∧ set_acc_co X Y.

Lemma cc_tau (X Y Y' : gset P) :
  X ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ Γ ] Y → (∀ q', q' ∈ Y' → ∃ q, q ∈ Y ∧ q ⟹ᶜᵒ q') → X ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ Γ ] Y'.
Proof. intros h%(gfp_pfp (copre_co_m Γ)) hY'. exact (cc_tau_ h Y' hY'). Qed.

Lemma cc_now (X Y : gset P) :
  X ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ Γ ] Y → (∀ p, p ∈ X → p ⤓) → ∀ q, q ∈ Y → q ↛ →
  ∃ p, p ∈ X ∧ ∃ p', p ⟹ᶜᵒ p' ∧ p' ↛ ∧ ⌈ Γ ⌉ (coR p') ⊆ ⌈ Γ ⌉ (coR q).
Proof. intros h%(gfp_pfp (copre_co_m Γ)). exact (cc_now_ h). Qed.

Lemma cc_step (X Y X' Y' : gset P) μ :
  X ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ Γ ] Y → (∀ p, p ∈ X → p ⇓ᶜᵒ [μ]) →
  (∀ q', q' ∈ Y' → ∃ q, q ∈ Y ∧ q ⟹ᶜᵒ{μ} q') →
  (∀ p', p' ∈ X' ↔ ∃ p, p ∈ X ∧ p ⟹ᶜᵒ{μ} p') → X' ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ Γ ] Y'.
Proof. intros h%(gfp_pfp (copre_co_m Γ)). exact (cc_step_ h μ X' Y'). Qed.

Lemma cc_cnv (X Y : gset P) : X ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ Γ ] Y → (∀ p, p ∈ X → p ⤓) → ∀ q, q ∈ Y → q ⤓.
Proof. intros h%(gfp_pfp (copre_co_m Γ)). exact (cc_cnv_ h). Qed.

Lemma cocnv_head {p : P} {μ : At} {s : trace At} : p ⇓ᶜᵒ μ :: s → p ⇓ᶜᵒ [μ].
Proof.
  intros h. inversion h as [| p0 μ0 s0 ht hall]; subst. apply cocnv_act; [exact ht |].
  intros q w. apply cocnv_nil. exact (cocnv_terminate q s (hall q w)).
Qed.

Lemma cnv_cons_of_step (X X' : gset P) μ s :
  (∀ p, p ∈ X → p ⇓ᶜᵒ [μ]) → (∀ p', p' ∈ X' ↔ ∃ p, p ∈ X ∧ p ⟹ᶜᵒ{μ} p') →
  (∀ p', p' ∈ X' → p' ⇓ᶜᵒ s) → ∀ p, p ∈ X → p ⇓ᶜᵒ μ :: s.
Proof.
  intros hX hX' hs p mp. apply cocnv_act; [exact (cocnv_terminate p [μ] (hX p mp)) |].
  intros p' w. apply hs, hX'. exists p. split; [exact mp | exact w].
Qed.

Lemma copre_co_if_set (X Y : gset P) : set_pre_co X Y → X ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ Γ ] Y.
Proof.
  revert X Y. unfold copre_co. coinduction RR CIH. intros X Y [hc ha]. constructor.
  - intros Y' hY'. apply CIH. split.
    + intros s hX q' mq'. destruct (hY' q' mq') as (q & mq & w).
      exact (cocnv_preserved_by_cowt_nil s q (hc s hX q mq) q' w).
    + intros s q' q'' mq' hX w st. destruct (hY' q' mq') as (q & mq & w0).
      exact (ha s q q'' mq hX (cowt_push_nil_left w0 w) st).
  - intros hX q mq st.
    destruct (ha [] q q mq (λ p mp, cocnv_nil p (hX p mp)) (cowt_nil q) st) as (p & mp & p' & w & st' & sub).
    exists p. split; [exact mp |]. exists p'. split_and!; assumption.
  - intros μ X' Y' hX hY' hX'. apply CIH. split.
    + intros s hX's q' mq'. destruct (hY' q' mq') as (q & mq & w).
      exact (cocnv_preserved_by_cowt_act s q μ (hc (μ :: s) (cnv_cons_of_step X X' μ s hX hX' hX's) q mq) q' w).
    + intros s q' q'' mq' hX's w st. destruct (hY' q' mq') as (q & mq & w0).
      destruct (ha (μ :: s) q q'' mq (cnv_cons_of_step X X' μ s hX hX' hX's) (cowt_concat q q' q'' [μ] s w0 w) st)
        as (p & mp & p'' & w1 & st'' & sub).
      change (μ :: s) with ([μ] ++ s) in w1. apply cowt_split in w1 as (p1 & w1 & w2).
      exists p1. split; [apply hX'; exists p; split; assumption |]. exists p''. split_and!; assumption.
  - intros hX q mq. exact (cocnv_terminate q [] (hc [] (λ p mp, cocnv_nil p (hX p mp)) q mq)).
Qed.

Lemma set_cnv_if_copre_co (s : trace At) : ∀ (X Y : gset P), X ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ Γ ] Y →
  (∀ p, p ∈ X → p ⇓ᶜᵒ s) → ∀ q, q ∈ Y → q ⇓ᶜᵒ s.
Proof.
  induction s as [| μ s IH]; intros X Y h hX q mq.
  - apply cocnv_nil. exact (cc_cnv X Y h (λ p mp, cocnv_terminate p [] (hX p mp)) q mq).
  - apply cocnv_act; [exact (cc_cnv X Y h (λ p mp, cocnv_terminate p _ (hX p mp)) q mq) |]. intros q' w.
    set (X' := coreachable_from [μ] X (λ p mp, cocnv_head (hX p mp))).
    apply (IH X' {[ q' ]}); [| | set_solver].
    + apply (cc_step X Y X' {[ q' ]} μ h (λ p mp, cocnv_head (hX p mp))).
      * intros q'' ->%elem_of_singleton. exists q. split; [exact mq | exact w].
      * intros p'. apply coreachable_from_spec.
    + intros p' mp'. apply coreachable_from_spec in mp' as (p & mp & w').
      exact (cocnv_preserved_by_cowt_act s p μ (hX p mp) p' w').
Qed.

Lemma set_acc_if_copre_co (s : trace At) : ∀ (X Y : gset P) q q', X ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ Γ ] Y → q ∈ Y →
  (∀ p, p ∈ X → p ⇓ᶜᵒ s) → q ⟹ᶜᵒ[s] q' → q' ↛ →
  ∃ p, p ∈ X ∧ ∃ p', p ⟹ᶜᵒ[s] p' ∧ p' ↛ ∧ ⌈ Γ ⌉ (coR p') ⊆ ⌈ Γ ⌉ (coR q').
Proof.
  induction s as [| μ s IH]; intros X Y q q' h mq hX w st.
  - remember ([] : trace At) as s0 eqn:hs0 in w. revert Y h mq hs0.
    induction w as [q | s0 q q1 q' l w IHw | ]; intros Y h mq hs0; [| | discriminate].
    + exact (cc_now X Y h (λ p mp, cocnv_terminate p [] (hX p mp)) q mq st).
    + subst. apply (IHw st {[ q1 ]}); [| set_solver | reflexivity].
      apply (cc_tau X Y {[ q1 ]} h). intros q'' ->%elem_of_singleton.
      exists q. split; [exact mq | exact (lts_to_cowt_tau l)].
  - change (μ :: s) with ([μ] ++ s) in w. apply cowt_split in w as (q1 & w1 & w2).
    set (X' := coreachable_from [μ] X (λ p mp, cocnv_head (hX p mp))).
    assert (h' : X' ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ Γ ] {[ q1 ]}).
    { apply (cc_step X Y X' {[ q1 ]} μ h (λ p mp, cocnv_head (hX p mp))).
      - intros q'' ->%elem_of_singleton. exists q. split; [exact mq | exact w1].
      - intros p'. apply coreachable_from_spec. }
    destruct (IH X' {[ q1 ]} q1 q' h' ltac:(set_solver)) as (p1 & mp1 & p' & w' & st' & sub); [| exact w2 | exact st |].
    + intros p1 mp1. apply coreachable_from_spec in mp1 as (p & mp & w0).
      exact (cocnv_preserved_by_cowt_act s p μ (hX p mp) p1 w0).
    + apply coreachable_from_spec in mp1 as (p & mp & w0).
      exists p. split; [exact mp |]. exists p'. split_and!; [exact (cowt_concat p p1 p' [μ] s w0 w') | exact st' | exact sub].
Qed.

Theorem eqx_co (X Y : gset P) : set_pre_co X Y ↔ X ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ Γ ] Y.
Proof.
  split; [apply copre_co_if_set |]. intros h. split.
  - intros s hX q mq. exact (set_cnv_if_copre_co s X Y h hX q mq).
  - intros s q q' mq hX w st. exact (set_acc_if_copre_co s X Y q q' h mq hX w st).
Qed.

Lemma set_pre_co_singleton (p q : P) : set_pre_co {[ p ]} {[ q ]} ↔ p ≼꜀ₒ₋ₐₛ[ Γ ] q.
Proof.
  split.
  - intros [hc ha]. split.
    + intros s hp. apply (hc s); [intros p0 ->%elem_of_singleton; exact hp | set_solver].
    + intros s q' hp w st.
      destruct (ha s q q' ltac:(set_solver) (λ p0 m, eq_ind_r (λ x, x ⇓ᶜᵒ s) hp (proj1 (elem_of_singleton _ _) m)) w st)
        as (p0 & ->%elem_of_singleton & p' & w' & st' & sub).
      exists p'. split_and!; assumption.
  - intros [hc ha]. split.
    + intros s hp q0 ->%elem_of_singleton. apply hc, hp. set_solver.
    + intros s q0 q' ->%elem_of_singleton hp w st.
      destruct (ha s q' (hp p ltac:(set_solver)) w st) as (p' & w' & st' & sub).
      exists p. split; [set_solver |]. exists p'. split_and!; assumption.
Qed.

Corollary copre_co_singleton (p q : P) : ({[ p ]} : gset P) ᶜᵒ≼ₜₒᵥᵥₑᵣ꜀ₒ[ Γ ] {[ q ]} ↔ p ≼꜀ₒ₋ₐₛ[ Γ ] q.
Proof. rewrite <- eqx_co. apply set_pre_co_singleton. Qed.

End copre_co.
(* end hide *)
