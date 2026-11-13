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
(* * The abstract algebra of super-operators and states

    The semantics of lqCCS is parametric in an abstract domain of
    super-operators ([Alg]), with finitely many outcomes for each measurement
    ([FinAlg]), acting linearly on states ([StAlg]). *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
(* ** Abstract domain of super-operators *)

Class Ord := { T : Type; le : T -> T -> Prop }.
Infix "⊑" := le (at level 70).
Definition chain `{Ord} (f : nat -> T) := forall n, f n ⊑ f (S n).

(* A measurement [m] has (at most countably many) outcomes [Out m], coded
    injectively into [nat].  [comp a b] is [a ∘ b]; [br m f] is
    [Σ_k f k ∘ ℳ_k]. *)
Class Alg `{Ord} := {
  Act : Type; Meas : Type; Out : Meas -> Type;
  code m : Out m -> nat;
  decode m : nat -> option (Out m);
  decode_code m k : decode m (code m k) = Some k;
  zero : T; one : T; comp : T -> T -> T; act : Act -> T;
  br m : (Out m -> T) -> T; sup : (nat -> T) -> T;
  le_refl a : a ⊑ a;
  le_trans a b c : a ⊑ b -> b ⊑ c -> a ⊑ c;
  le_antisym a b : a ⊑ b -> b ⊑ a -> a = b;
  zero_le a : zero ⊑ a;
  comp_assoc a b c : comp a (comp b c) = comp (comp a b) c;
  comp_1l a : comp one a = a;
  comp_1r a : comp a one = a;
  comp_0r a : comp a zero = zero;
  comp_mono a a' b b' : a ⊑ a' -> b ⊑ b' -> comp a b ⊑ comp a' b';
  br_mono m f g : (forall k, f k ⊑ g k) -> br m f ⊑ br m g;
  comp_br m f c : comp c (br m f) = br m (fun k => comp c (f k));
  sup_ub f n : chain f -> f n ⊑ sup f;
  sup_lub f x : chain f -> (forall n, f n ⊑ x) -> sup f ⊑ x;
  comp_sup_l f a : chain f -> comp (sup f) a = sup (fun n => comp (f n) a);
  comp_sup_r f a : chain f -> comp a (sup f) = sup (fun n => comp a (f n));
  br_sup m (f : nat -> Out m -> T) : (forall k, chain (fun n => f n k)) ->
    br m (fun k => sup (fun n => f n k)) = sup (fun n => br m (f n)) }.
Infix "⋅" := comp (at level 40, left associativity).

Section Alg.
Context `{Alg}.

Lemma code_inj m k k' : code m k = code m k' -> k = k'.
Proof. intro E. pose proof (decode_code m k) as D. rewrite E, decode_code in D. congruence. Qed.

End Alg.

(* Finite branching: outcomes are enumerated, [+] exists, and [br] is the
    sum of its branches precomposed with the Kraus maps [ℳ_k]. *)
Class FinAlg `{Alg} := {
  add : T -> T -> T;
  kraus m : Out m -> T;
  outs m : list (Out m);
  outs_nodup m : NoDup (outs m);
  outs_all m k : In k (outs m);
  add_0l a : add zero a = a;
  add_0r a : add a zero = a;
  add_assoc a b c : add a (add b c) = add (add a b) c;
  comp_addl a b c : add a b ⋅ c = add (a ⋅ c) (b ⋅ c);
  comp_0l c : zero ⋅ c = zero;
  br_sum m f : br m f = fold_right add zero (map (fun k => f k ⋅ kraus m k) (outs m)) }.

Section FinAlg.
Context `{FinAlg}.

Definition sum := fold_right add zero.

Lemma sum_app l1 l2 : sum (l1 ++ l2) = add (sum l1) (sum l2).
Proof. induction l1; simpl; [now rewrite add_0l | now rewrite IHl1, add_assoc]. Qed.

Lemma sum_comp l c : sum l ⋅ c = sum (map (fun a => a ⋅ c) l).
Proof. induction l; simpl; [apply comp_0l | now rewrite comp_addl, IHl]. Qed.

End FinAlg.

Class StAlg `{FinAlg} := {
  St : Type;
  szero : St;
  sadd : St -> St -> St;
  ssup : (nat -> St) -> St;
  app : T -> St -> St;
  app_one ρ : app one ρ = ρ;
  app_zero ρ : app zero ρ = szero;
  app_comp a b ρ : app (a ⋅ b) ρ = app a (app b ρ);
  app_add a b ρ : app (add a b) ρ = sadd (app a ρ) (app b ρ);
  app_szero a : app a szero = szero;
  sadd_szero : sadd szero szero = szero;
  (* Evaluation at a state commutes with suprema (pointwise limits). *)
  app_sup f g ρ : chain f -> (forall n, g n = app (f n) ρ) -> app (sup f) ρ = ssup g;
  (* A super-operator is determined by its action on states. *)
  app_ext a b : (forall ρ, app a ρ = app b ρ) -> a = b }.

Section StAlg.
Context `{StAlg}.

Definition ssum := fold_right sadd szero.

Lemma app_ssum (l : list T) ρ : app (sum l) ρ = ssum (map (fun a => app a ρ) l).
Proof. induction l; simpl; [apply app_zero | now rewrite app_add, IHl]. Qed.

End StAlg.
(* end hide *)
