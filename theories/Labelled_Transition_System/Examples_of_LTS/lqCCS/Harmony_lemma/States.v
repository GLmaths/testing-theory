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
(* * Quantum states, acted upon linearly by super-operators

    Shared by the state-level results: [Harmony], [Corollaries], [Kierner]. *)
(* end hide *)

From Stdlib Require Import List.
From TestingTheory Require Import Lifted Paths.
Import ListNotations.
(* begin hide *)
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

Section States.
Context `{StAlg}.

Definition ssum := fold_right sadd szero.

Lemma app_ssum (l : list T) ρ : app (sum l) ρ = ssum (map (fun a => app a ρ) l).
Proof. induction l; simpl; [apply app_zero | now rewrite app_add, IHl]. Qed.

End States.
(* end hide *)
