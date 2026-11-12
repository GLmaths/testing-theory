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
(* * Scheduled probabilistic systems: distributions, liftings, runs

    The setting is the scheduled semantics of lqCCS (Ceragioli, Gadducci,
    Lomurno, Tedeschi, arXiv:2604.23756, Section 6), made abstract.

    - A *distribution* is a formal sum [Σ ρᵢ • cᵢ] of weighted states, kept
      as a list.  Weights have a *mass* into probabilities: weight =
      probability for a pLTS, weight = partial density operator and mass =
      trace for lqCCS.  Components with the same state are not merged (the
      paper merges them, Example 6.3): mass and success are additive, so
      must does not see the difference, and lists keep the proofs about
      runs elementary.
    - A weighted state [ρ • c] steps, under a *scheduler* [σ] (a tag, or a
      pair of tags), to a distribution; that this is deterministic in [σ]
      (Assumption 1) is the hypothesis [SchedDeterministic], not a field.
    - A distribution moves *as a whole* under one scheduler: this is the
      physically admissible restriction.  Successful components are frozen.
      What happens to a component that cannot follow [σ] is the *lifting*:
      with [Stay] it stays where it is, with [Drop] it disappears, as in
      the probabilistic runs of Ceragioli et al. (JLAMP 2027, Definition
      5), where a path that cannot follow the scheduler has no run.

    Staying is what testing needs when the scheduler may come back to a
    component later: whether a component enables [σ] is classical
    information (tags depend on the process and on the qubit *names*
    only).  Dropping counts the component as failed, whatever it could
    have done.  A run is an infinite sequence that stutters once stable,
    so that a divergent system has runs of value zero under both liftings.
    The musts are in [pMust_almost_sure.v] and [pMust_smyth.v]. *)

From Stdlib.Unicode Require Import Utf8.
From stdpp Require Import base decidable list.
(* begin hide *)
(* ** Probabilities and weights *)

Class Weights := MkWeights {
    prob : Type;
    prob_zero : prob;
    prob_add : prob → prob → prob;
    prob_le : prob → prob → Prop;
    prob_le_preorder :: PreOrder prob_le;

    weight : Type;
    weight_zero : weight;
    weight_add : weight → weight → weight;
    weight_add_comm a b : weight_add a b = weight_add b a;
    weight_add_assoc a b c :
      weight_add a (weight_add b c) = weight_add (weight_add a b) c;
    weight_add_zero a : weight_add weight_zero a = a;

    mass : weight → prob;
  }.

Arguments prob {_}.
Arguments weight {_}.

Notation "a ≤ₚ b" := (prob_le a b) (at level 70).
Definition prob_lt `{Weights} (a b : prob) : Prop := a ≤ₚ b ∧ ¬ b ≤ₚ a.
Notation "a <ₚ b" := (prob_lt a b) (at level 70).

(* ** Distributions *)

Notation dist C := (list (C * weight)) (only parsing).

Section Distributions.
  Context `{Weights} {C : Type}.

  Definition dpoint (c : C) (ρ : weight) : dist C := [(c, ρ)].

  Definition dplus (Δ Θ : dist C) : dist C := Δ ++ Θ.

  Definition dsum (l : list (dist C)) : dist C := concat l.

  (* Image of a distribution by a renaming of its states. *)
  Definition dmap {D} (f : C → D) (Δ : dist C) : dist D :=
    map (λ cρ, (f cρ.1, cρ.2)) Δ.

  (* [|Δ|], the mass of a distribution. *)
  Definition dmass (Δ : dist C) : prob :=
    foldr (λ cρ acc, prob_add (mass cρ.2) acc) prob_zero Δ.

  (* The mass of the components satisfying [good]. *)
  Definition dmass_of (good : C → Prop) `{∀ c, Decision (good c)}
    (Δ : dist C) : prob :=
    foldr (λ cρ acc, if decide (good cρ.1) then prob_add (mass cρ.2) acc else acc)
      prob_zero Δ.
End Distributions.

(* ** Scheduled systems

    [C] are the states of the composed system [p ∥ t] (configurations), [Sch]
    the schedulers.  Only the silent steps of the composition are needed to
    define must, as in [Must.v]. *)

Class SchedSts (C Sch : Type) `{Weights} := MkSchedSts {
    (* [ρ • c —σ→ Δ] *)
    sstep : weight → C → Sch → dist C → Prop;
    (* Success of the observer in [c]. *)
    psuccess : C → Prop;
    psuccess_dec :: ∀ c, Decision (psuccess c);
  }.

(* Assumption 1 of the paper: the scheduler determines the step.  It is
    not a field of [SchedSts], which is about any scheduled system;
    the results that need it take it as a hypothesis.  Without it a
    scheduler could resolve differently in different components, which is
    what admissibility forbids. *)
Definition SchedDeterministic (C Sch : Type) `{Weights} `{!SchedSts C Sch} : Prop :=
  ∀ ρ c σ Δ Δ', sstep ρ c σ Δ → sstep ρ c σ Δ' → Δ = Δ'.

(* ** Liftings

    How a component that cannot follow the scheduler is lifted: it stays
    ([Stay]) or it disappears ([Drop]); successful components stay in both
    cases. *)
Inductive lifting : Type := Stay | Drop.

Section Runs.
  Context `{Weights} {C Sch : Type} `{!SchedSts C Sch}.

  Definition rest (L : lifting) (c : C) (ρ : weight) : dist C :=
    match L with
    | Stay => dpoint c ρ
    | Drop => if decide (psuccess c) then dpoint c ρ else []
    end.

  Lemma elem_of_rest L c ρ x : x ∈ rest L c ρ → x = (c, ρ).
  Proof.
    destruct L; simpl; [by intros ->%list_elem_of_singleton|].
    case_decide; [by intros ->%list_elem_of_singleton|by intros ?%elem_of_nil].
  Qed.

  (* What happens to one component when [σ] is scheduled: it moves if it is
      not successful and enables [σ]; otherwise it is lifted. *)
  Definition comp_step (L : lifting) (ρ : weight) (c : C) (σ : Sch) (Δ : dist C) : Prop :=
    (¬ psuccess c ∧ sstep ρ c σ Δ)
    ∨ ((psuccess c ∨ ∀ Δ', ¬ sstep ρ c σ Δ') ∧ Δ = rest L c ρ).

  (* [σ] moves at least one component of [𝔇]. *)
  Definition dmoves (𝔇 : dist C) (σ : Sch) : Prop :=
    ∃ c ρ Δ, (c, ρ) ∈ 𝔇 ∧ ¬ psuccess c ∧ sstep ρ c σ Δ.

  (* [𝔇 ⟿{σ} 𝔇'], the admissible lifted step: one scheduler for the whole
      distribution. *)
  Definition dstep (L : lifting) (𝔇 : dist C) (σ : Sch) (𝔇' : dist C) : Prop :=
    dmoves 𝔇 σ ∧
    ∃ Δs, Forall2 (λ cρ Δ, comp_step L cρ.2 cρ.1 σ Δ) 𝔇 Δs ∧ 𝔇' = dsum Δs.

  Definition dstable (𝔇 : dist C) : Prop := ∀ σ, ¬ dmoves 𝔇 σ.

  (* A maximal run from [𝔇], as a sequence that stutters once stable. *)
  Definition is_run (L : lifting) (𝔇 : dist C) (r : nat → dist C) : Prop :=
    r 0 = 𝔇 ∧
    ∀ n, (∃ σ, dstep L (r n) σ (r (S n))) ∨ (dstable (r n) ∧ r (S n) = r n).

  (* Successful mass after [n] steps. *)
  Definition succ_mass (r : nat → dist C) (n : nat) : prob :=
    dmass_of psuccess (r n).

  Lemma dstep_not_stable L Δ σ Δ' : dstep L Δ σ Δ' → ¬ dstable Δ.
  Proof. intros [Hm _] Hst. by apply (Hst σ). Qed.
End Runs.

Notation "𝔇 ⟿{ σ } 𝔇'" := (dstep Stay 𝔇 σ 𝔇') (at level 30, format "𝔇  ⟿{ σ }  𝔇'").

(* ** Testing

    [p ∥ t] is a distribution of configurations: for lqCCS the initial
    quantum state is part of [p] (a quantum distribution) and the qubits the
    observer owns are part of [t]. *)

Class pTesting (P T C Sch : Type) `{Weights} `{!SchedSts C Sch} :=
  MkpTesting { compose : P → T → dist C }.

(* end hide *)
