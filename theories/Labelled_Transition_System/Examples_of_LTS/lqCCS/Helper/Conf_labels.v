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

(* * lqCCS: the labels of the configurations, actions of the memory or of the program, with the coercions of both alphabets into their sum *)

From Stdlib.Unicode Require Import Utf8.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.lqCCS_prog.Syntax.
From TestingTheory Require Import lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS.

(* The type of a label is read from the context, so that the coercions
    below apply under [ActExt]. *)
Arguments ActExt {A} & μ.

(* ** The injections into a sum *)

Definition inj_l {A B : Type} (a : A) : A + B := inl a.
Definition inj_r {A B : Type} (b : B) : A + B := inr b.

Section Sum_ActExt_Coercion.
  Context `{lqP : lqCCS_Parameters} `{QM : QuantumModel}.

  (* ** The labels: actions of the memory or of the program *)

  Definition mlbl : mem_action → mem_action + prog_action := inj_l.
  Definition plbl : prog_action → mem_action + prog_action := inj_r.

  Coercion mlbl : mem_action >-> Datatypes.sum.
  Coercion plbl : prog_action >-> Datatypes.sum.
End Sum_ActExt_Coercion.