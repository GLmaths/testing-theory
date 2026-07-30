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

(** * Soundness of the [ax_pre] proof system w.r.t. [⊑ₘᵤₛₜᵢ]

    [soundness_ax] below is the payoff of [VCCS_Precongruence.v]: every
    constructor of [ax_pre] ([DefinitionAxiomatic.v]) has a matching
    semantic lemma there, so this file is mostly assembly. *)

From TestingTheory Require Import VCCS VCCS_Instance Must ActTau
  gLts Bisimulation InputOutputActions WeakTransitions Convergence
  VCCS_Static VCCS_Precongruence VCCS_Expansion VCCS_ResNormalize VCCS_ReadySet
  DefinitionAxiomatic.

Section SoundnessAx.

Context `{VP : VCCS_Parameters}.

(** ** [Static] is an invariant of every [⊢]-derivation

    Needed so [ax_trans]'s middle term can be shown [Static] from
    nothing but the endpoints' [Static]-ness — this is exactly why
    [ax_cgr] carries its explicit [Static q] side condition (see
    [DefinitionAxiomatic.v]): without it, [≡*] could relate a [Static]
    process to a non-[Static] one, and this invariant would be false.
    [ax_input]'s case needs [Static_subst]/[Static_subst_rev]
    (]VCCS_Static.v]) to move between [Static (p^v)] (what the [∀v]
    premise talks about) and [Static p]/[Static q] themselves — [O]
    ([VCCS_Parameters]'s distinguished value) supplies a witness value
    to instantiate the universal at. *)

Lemma ax_pre_static_preserved : forall p q, ax_pre p q -> Static p -> Static q.
Proof.
  intros p q Hax.
  induction Hax; intro Hsp.
  - exact Hsp.
  - apply IHHax2, IHHax1, Hsp.
  - exact H.
  - inversion Hsp; subst.
    constructor; [apply IHHax1 | apply IHHax2]; assumption.
  - inversion Hsp; subst.
    constructor.
    apply IHHax.
    assumption.
  - inversion Hsp; subst.
    constructor; [apply IHHax1 | apply IHHax2]; assumption.
  - inversion Hsp; subst.
    inversion H2; subst.
    constructor.
    constructor.
    eapply Static_subst_rev.
    apply (H0 (cst_value O)).
    apply Static_subst.
    exact H3.
  - inversion Hsp; subst.
    inversion H0; subst.
    constructor.
    constructor.
    apply IHHax.
    exact H1.
  - inversion Hsp; subst.
    inversion H0; subst.
    constructor.
    constructor.
    apply IHHax.
    exact H1.
  - inversion Hsp; subst.
    inversion H0; subst.
    inversion H3; subst.
    inversion H2; subst.
    exact H4.
  - inversion Hsp; subst.
    inversion H0; subst.
    inversion H3; subst.
    exact H1.
  - inversion Hsp; subst.
    inversion H0; subst.
    inversion H2; subst.
    inversion H3; subst.
    repeat constructor; assumption.
  - inversion Hsp; subst.
    inversion H0; subst.
    inversion H2; subst.
    inversion H3; subst.
    constructor.
    constructor; [inversion H1 | inversion H4]; assumption.
  - inversion Hsp; subst.
    inversion H0; subst.
    inversion H2; subst.
    inversion H3; subst.
    repeat constructor; assumption.
  - inversion Hsp; subst.
    inversion H0; subst.
    inversion H2; subst.
    inversion H3; subst.
    constructor.
    constructor; [inversion H1 | inversion H4]; assumption.
  - constructor.
    constructor.
    + constructor.
      * apply ext_gStatic; assumption.
      * apply ext_r_gStatic; assumption.
    + apply int_gStatic; assumption.
  - constructor; constructor; assumption.
  - constructor. apply resg_gStatic. assumption.
  - constructor. constructor. assumption.
  - inversion Hsp; subst; inversion H0; subst; inversion H2; subst; inversion H3; subst; repeat constructor; assumption.
  - inversion Hsp; subst; inversion H0; subst; inversion H1; subst; inversion H2; subst; inversion H4; subst; inversion H5; subst; repeat constructor; assumption.
  - inversion Hsp; subst; inversion H0; subst; inversion H2; subst; inversion H3; subst; repeat constructor; assumption.
  - inversion Hsp; subst; inversion H0; subst; inversion H1; subst; inversion H2; subst; inversion H4; subst; inversion H5; subst; repeat constructor; assumption.
  - (* ax_choice_stable: [gStatic gp'] comes from the IH on the premise,
       so the rule needs no [gStatic] side condition of its own. *)
    inversion Hsp; subst. inversion H2; subst.
    assert (Hgp' : Static (g gp')) by (apply IHHax; constructor; assumption).
    inversion Hgp'; subst.
    constructor. constructor; assumption.
Qed.

(** ** Soundness

    By induction on the [ax_pre] derivation; each case is one
    application of a [VCCS_Precongruence.v] lemma (none of which need
    [ax_choice] — there is no such constructor, see
    [DefinitionAxiomatic.v]). *)

Theorem soundness_ax : forall p q, Static p -> Static q -> ax_pre p q -> p ⊑ₘᵤₛₜᵢ q.
Proof.
  intros p q Hsp Hsq Hax.
  revert Hsp Hsq.
  induction Hax; intros Hsp Hsq.
  - reflexivity.
  - assert (Hq : Static q) by (eapply ax_pre_static_preserved; [exact Hax1 | exact Hsp]).
    transitivity q.
    + apply IHHax1; assumption.
    + apply IHHax2; assumption.
  - destruct (must_i_cgr p q H0) as (_ & Hd).
    exact Hd.
  - inversion Hsp; subst.
    inversion Hsq; subst.
    apply must_i_par_compat2; try assumption.
    + apply IHHax1; assumption.
    + apply IHHax2; assumption.
  - inversion Hsp; subst.
    inversion Hsq; subst.
    apply must_i_res_compat; try assumption.
    apply IHHax; assumption.
  - inversion Hsp; subst.
    inversion Hsq; subst.
    apply must_i_if_compat.
    + apply IHHax1; assumption.
    + apply IHHax2; assumption.
  - inversion Hsp; subst.
    inversion H2; subst.
    inversion Hsq; subst.
    inversion H4; subst.
    apply must_i_input_compat.
    intro v.
    apply H0; apply Static_subst; assumption.
  - inversion Hsp; subst.
    inversion H0; subst.
    inversion Hsq; subst.
    inversion H2; subst.
    apply must_i_output_compat.
    apply IHHax; assumption.
  - inversion Hsp; subst.
    inversion H0; subst.
    inversion Hsq; subst.
    inversion H2; subst.
    apply must_i_tau_compat.
    apply IHHax; assumption.
  - apply must_i_int_choice_l.
  - apply must_i_int_choice_r.
  - apply must_i_output_merge_l.
  - apply must_i_output_merge_r.
  - apply must_i_input_merge_l.
  - apply must_i_input_merge_r.
  - apply must_i_expansion_l.
  - apply must_i_expansion_r.
  - apply must_i_res_normalize_l.
  - apply must_i_res_normalize_r.
  - apply must_i_input_distrib_l.
  - apply must_i_input_distrib_r.
  - apply must_i_output_distrib_l.
  - apply must_i_output_distrib_r.
  - inversion Hsp; subst. inversion H2; subst.
    inversion Hsq; subst. inversion H4; subst.
    apply must_i_choice_stable_compat; try assumption; try (constructor; assumption).
    apply IHHax; constructor; assumption.
Qed.

End SoundnessAx.
