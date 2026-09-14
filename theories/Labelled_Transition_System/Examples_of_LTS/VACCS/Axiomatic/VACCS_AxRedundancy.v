(*
   Copyright (c) 2026 Gaëtan Lopez <gaetanlopez.maths@gmail.com>

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

(** * Redundant rules of the VACCS system

    The system of [VACCS_DefinitionAxiomatic.v] has **nine** rules:

    - [ax_trans], [ax_cgr] — preorder and structural congruence;
    - [ax_par], [ax_res] — congruence for [‖] and [ν];
    - [ax_tau_step] — a server's own internal move only decreases it;
    - [ax_same_lts] — two processes with the same transitions;
    - [ax_glb_tau], [ax_glb_settle] — below a guarded sum, read off its
      [must] fields (with a [𝛕]-branch; or settling against any bag);
    - [ax_share_msg] — two branches carrying the same pending message
      pool their residues, the message factoring out of the choice.

    Every other law of earlier versions of the system is now a lemma, with
    the same statement, proved from these nine:

    - from [ax_same_lts]: [ax_success_l]/[_r], [ax_expansion_l]/[_r],
      [ax_res_normalize_l]/[_r];
    - from [ax_glb_tau] and [ax_glb_settle] (joined as the lemma
      [ax_glb_sum], and through [ax_below_gsum], whose [Settles] premise
      is discharged by one internal run of the left-hand side to a stable,
      silent state receiving only on channels the sum offers):
      [ax_int_glb], [ax_choice_tau], [ax_tau_sep_l]/[_r],
      [ax_tau_flatten_l]/[_r], [ax_convex], [ax_share_in],
      [ax_input_distrib_l], [ax_ccat_r], [ax_choice_input], [ax_input],
      [ax_sub_tau], [ax_drop_tau];
    - from [ax_tau_step]: [ax_int_l], [ax_int_r], [ax_tau_run];
    - from [ax_cgr] and the rest: [ax_refl], [ax_tau], [ax_if];
    - as corollaries of completeness ([VACCS_DerivedRules.v]), under
      [gStatic] side conditions: [ax_input_drop], [ax_restrict].

    Independence of the nine is not proved.  [ax_share_msg] is the one
    rule whose conclusion is a parallel composition built from a guarded
    sum, which none of the others can produce; [ax_same_lts] and
    [ax_glb_settle] are the only rules with semantic (LTS-level) premises. *)
