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
From stdpp Require Import base gmultiset countable decidable list.
From TestingTheory Require Import ActTau.
From TestingTheory Require Import lqCCS.General_definition.Algebra lqCCS.quantum_mem.Syntax lqCCS.lqCCS_prog.Syntax.
From TestingTheory Require Import lqCCS.quantum_mem.LTS lqCCS.lqCCS_prog.LTS lqCCS.lqCCS_par_Qmem.LTS.

#[local] Open Scope lqccs_scope.

Section Sync_Testing.
  Context `{lqP : lqCCS_Parameters} `{QM : QuantumModel}.

  (* [c!v sync c?v] and [c?v sync c!v] *)
  Inductive sync_chan : prog_action → prog_action → Prop :=
  | sync_out_in c v : sync_chan (PrOut c v) (PrIn c v)
  | sync_in_out c v : sync_chan (PrIn c v) (PrOut c v).

  (* Synchronisation of [ρ ∣ P] with a test in parallel: a memory action
      ([sync]) or a channel action of the program ([sync_chan]) against an
      action of the test. *)
  Inductive sync_sys : mem_action + prog_action → prog_action → Prop :=
  | sync_sys_mem μ1 μ2 : 𝔻ₘₑₘ μ1 μ2 → sync_sys (inl μ1) μ2
  | sync_sys_chan μ1 μ2 : sync_chan μ1 μ2 → sync_sys (inr μ1) μ2.

End Sync_Testing.
