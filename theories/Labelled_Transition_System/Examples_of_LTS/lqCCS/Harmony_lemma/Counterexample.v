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
(* * Counterexample to [Kierner 2025, Lemma 3.2]

    S = (if M01[q] then skip else skip) ; (skip □ q *= X),   ρ = |+⟩⟨+|.

    Lifted semantics [FX]:  ⟦S⟧(ρ) = {I/2}.
    MDP semantics [K] (normalised configurations): a memoryless scheduler
    picking skip on |0⟩ and X on |1⟩ reaches |0⟩⟨0|.

    All states involved are real, so 2×2 matrices over Q suffice. *)
(* end hide *)

From Stdlib Require Import QArith List.
Import ListNotations.
(* begin hide *)
Open Scope Q_scope.

Record mat := Mat { m00 : Q; m01 : Q; m10 : Q; m11 : Q }.

Definition madd A B := Mat (m00 A + m00 B) (m01 A + m01 B) (m10 A + m10 B) (m11 A + m11 B).
Definition mscale q A := Mat (q * m00 A) (q * m01 A) (q * m10 A) (q * m11 A).
Definition tr A := m00 A + m11 A.
Definition P0 A := Mat (m00 A) 0 0 0.           (* P⁰ A P⁰ *)
Definition P1 A := Mat 0 0 0 (m11 A).           (* P¹ A P¹ *)
Definition Xc A := Mat (m11 A) (m10 A) (m01 A) (m00 A). (* X A X *)
Definition Hc A :=                                     (* H A H *)
  let '(Mat a b c d) := A in
  mscale (1#2) (Mat (a + b + c + d) (a - b + c - d) (a + b - c - d) (a - b - c + d)).
Definition Init A := Mat (tr A) 0 0 0.                (* q := 0 *)
Definition meqb A B :=
  Qeq_bool (m00 A) (m00 B) && Qeq_bool (m01 A) (m01 B) &&
  Qeq_bool (m10 A) (m10 B) && Qeq_bool (m11 A) (m11 B).

(* Loop-free fragment.  [If p0 p1] measures in the computational basis;
    outcome 0 runs [p0], outcome 1 runs [p1]. *)
Inductive prog := Done | Skip | Xg | Hg | Ini | Seq (p q : prog) | Nd (p q : prog) | If (p0 p1 : prog).

(* ** Lifted semantics [FX, Fig. 2], applied to an input state.
    ⟦p;q⟧ρ = ⋃_{ρ' ∈ ⟦p⟧ρ} ⟦q⟧ρ' and ⟦if⟧ρ = {a + b : a ∈ ⟦p0⟧(P⁰ρ), b ∈ ⟦p1⟧(P¹ρ)}
    are the pointwise images of ⟦q⟧∘⟦p⟧ and ⟦p0⟧∘𝒫⁰ + ⟦p1⟧∘𝒫¹. *)
Fixpoint den p ρ : list mat :=
  match p with
  | Done | Skip => [ρ]
  | Xg => [Xc ρ]
  | Hg => [Hc ρ]
  | Ini => [Init ρ]
  | Seq p q => flat_map (den q) (den p ρ)
  | Nd p q => den p ρ ++ den q ρ
  | If p0 p1 => flat_map (fun a => map (madd a) (den p1 (P1 ρ))) (den p0 (P0 ρ))
  end.

(* ** MDP semantics [K]: configurations ⟨p, ρ⟩ with ρ normalised. *)
Inductive mtrans :=
| MLeaf (x : prog) (ρ : mat)
| MProb (q0 : Q) (x0 : prog) (ρ0 : mat) (q1 : Q) (x1 : prog) (ρ1 : mat)
| MCh (x0 x1 : prog).

Definition mmap f τ :=
  match τ with
  | MLeaf x ρ => MLeaf (f x) ρ
  | MProb q0 x0 ρ0 q1 x1 ρ1 => MProb q0 (f x0) ρ0 q1 (f x1) ρ1
  | MCh x0 x1 => MCh (f x0) (f x1)
  end.

Fixpoint mstep p ρ :=
  match p with
  | Done | Skip => MLeaf Done ρ
  | Xg => MLeaf Done (Xc ρ)
  | Hg => MLeaf Done (Hc ρ)
  | Ini => MLeaf Done (Init ρ)
  | Seq Done q => MLeaf q ρ
  | Seq p q => mmap (fun x => Seq x q) (mstep p ρ)
  | Nd p q => MCh p q
  | If p0 p1 =>
      MProb (tr (P0 ρ)) p0 (mscale (/ tr (P0 ρ)) (P0 ρ))
            (tr (P1 ρ)) p1 (mscale (/ tr (P1 ρ)) (P1 ρ))
  end.

(* Σ_{ρ'} Pr^𝔖(◇⟨↓,ρ'⟩)·ρ' for a memoryless scheduler [sch] (the MDP of
    a loop-free program is acyclic, so finite fuel suffices). *)
Fixpoint run (sch : prog -> mat -> bool) n p ρ :=
  match p, n with
  | Done, _ => ρ
  | _, O => Mat 0 0 0 0
  | _, S n =>
      match mstep p ρ with
      | MLeaf x ρ' => run sch n x ρ'
      | MProb q0 x0 ρ0 q1 x1 ρ1 => madd (mscale q0 (run sch n x0 ρ0)) (mscale q1 (run sch n x1 ρ1))
      | MCh x0 x1 => run sch n (if sch p ρ then x1 else x0) ρ
      end
  end.

Definition ex := Seq (If Skip Skip) (Nd Skip Xg).
Definition plus := Mat (1#2) (1#2) (1#2) (1#2).
Definition half := Mat (1#2) 0 0 (1#2).
Definition ket0 := Mat 1 0 0 0.

(* Memoryless: apply X exactly when the current state is |1⟩⟨1|. *)
Definition sch (_ : prog) ρ := Qeq_bool (m00 ρ) 0.

Lemma fx_side : den ex plus = [Mat (1#2) 0 0 (1#2); Mat (1#2) 0 0 (1#2)].
Proof. reflexivity. Qed.

Lemma mdp_side : meqb (run sch 10 ex plus) ket0 = true.
Proof. reflexivity. Qed.

(* Kierner's Lemma 3.2 claims ⟦S⟧(ρ) = { Σ Pr^𝔖 · ρ' : 𝔖 }; the right-hand
    side contains |0⟩⟨0|, which is not in ⟦S⟧(ρ) = {I/2}. *)
Theorem counterexample :
  meqb (run sch 10 ex plus) ket0 = true /\
  forall σ, In σ (den ex plus) -> meqb σ half = true /\ meqb σ ket0 = false.
Proof.
  split; [reflexivity |]. rewrite fx_side. simpl.
  intros σ [<- | [<- | []]]; split; reflexivity.
Qed.

(* ** The MDP semantics is not compositional

    T1 = q := 0; H; if M01 then skip else skip
    T2 = q := 0; H; if M01 then H else H
    have the same lifted semantics (ρ ↦ tr ρ · I/2), but after T1 the MDP is
    in |0⟩ or |1⟩ (where X acts), after T2 in |+⟩ or |−⟩ (where X does not). *)
Definition T1 := Seq Ini (Seq Hg (If Skip Skip)).
Definition T2 := Seq Ini (Seq Hg (If Hg Hg)).
Definition C := Nd Skip Xg.

Definition meq A B :=
  m00 A == m00 B /\ m01 A == m01 B /\ m10 A == m10 B /\ m11 A == m11 B.

Lemma same_denotation ρ :
  exists x y, den T1 ρ = [x] /\ den T2 ρ = [y] /\ meq x (mscale (tr ρ) half) /\ meq x y.
Proof.
  destruct ρ as [a b c d]. do 2 eexists. split; [reflexivity |]. split; [reflexivity |].
  unfold meq; simpl; repeat split; ring.
Qed.

(* From |0⟩⟨0|, the scheduler [sch] reaches |0⟩⟨0| after T1; C ... *)
Lemma T1_C : meqb (run sch 20 (Seq T1 C) ket0) ket0 = true.
Proof. reflexivity. Qed.

(* ... whereas after T2; C the only two reachable decision configurations
    are ⟨C, |+⟩⟨+|⟩ and ⟨C, |−⟩⟨−|⟩ (told apart by m01 = ±1/2), and all four
    ways of resolving them — hence every scheduler, history-dependent or not —
    yield I/2. *)
Definition sch2 (b1 b2 : bool) (_ : prog) ρ := if Qeq_bool (m01 ρ) (1#2) then b1 else b2.

Lemma T2_C b1 b2 : meqb (run (sch2 b1 b2) 20 (Seq T2 C) ket0) half = true.
Proof. destruct b1, b2; reflexivity. Qed.
(* end hide *)
