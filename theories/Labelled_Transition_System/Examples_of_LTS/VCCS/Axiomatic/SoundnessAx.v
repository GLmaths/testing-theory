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
  - (* ax_int_glb: both branches' [Static]-ness comes from the two IHs *)
    constructor. constructor.
    + constructor. apply IHHax1. exact Hsp.
    + constructor. apply IHHax2. exact Hsp.
  - (* ax_choice_tau. Again: invert only [gStatic (𝛕 • p)], never
       [gStatic gq] — [gq] is a bare variable. *)
    inversion Hsp; subst. inversion H0; subst. inversion H2; subst.
    constructor. constructor.
    + constructor. apply IHHax. assumption.
    + assumption.
  - (* ax_tau_flatten_l *)
    inversion Hsp; subst. inversion H1; subst. inversion H4; subst. inversion H2; subst.
    constructor. constructor; assumption.
  - (* ax_tau_flatten_r *)
    inversion Hsp; subst. inversion H1; subst.
    constructor. constructor; [assumption | constructor; constructor; assumption].
  - (* ax_tau_sep_l *)
    inversion Hsp; subst. inversion H0; subst. inversion H3; subst. inversion H1; subst.
    repeat constructor; assumption.
  - (* ax_tau_sep_r *)
    inversion Hsp; subst. inversion H0; subst. inversion H2; subst. inversion H3; subst.
    inversion H1; subst. inversion H4; subst. inversion H5; subst.
    constructor. constructor.
    + assumption.
    + constructor. constructor. assumption.
  - (* ax_convex: [gStatic (X + Y)] is read off the *second* summand's
       continuation [(X + Y) + Z]; the first one is not needed at all. *)
    inversion Hsp; subst. inversion H0; subst. inversion H3; subst.
    inversion H1; subst. inversion H4; subst.
    constructor. assumption.
  - (* ax_success_l *) repeat constructor.
  - (* ax_success_r *) repeat constructor.
  - (* ax_share_in: [Static P] and [gStatic X'] come from the first
       branch, [Static Q] from the second. The [match goal] selections
       keep this robust to [inversion]'s hypothesis numbering, which is
       eight levels deep here. *)
    inversion Hsp; subst. inversion H0; subst.
    inversion H2; subst. inversion H3; subst.
    inversion H1; subst. inversion H4; subst.
    match goal with H : gStatic (c ? P + X') |- _ => inversion H; subst end.
    match goal with H : gStatic (c ? Q + Y') |- _ => inversion H; subst end.
    match goal with H : gStatic (c ? P) |- _ => inversion H; subst end.
    match goal with H : gStatic (c ? Q) |- _ => inversion H; subst end.
    apply static_g. constructor;
      [constructor; apply static_g; constructor; constructor; assumption | assumption].
  - (* ax_share_out *)
    inversion Hsp; subst. inversion H0; subst.
    inversion H2; subst. inversion H3; subst.
    inversion H1; subst. inversion H4; subst.
    match goal with H : gStatic (c ! v • P + X') |- _ => inversion H; subst end.
    match goal with H : gStatic (c ! v • Q + Y') |- _ => inversion H; subst end.
    match goal with H : gStatic (c ! v • P) |- _ => inversion H; subst end.
    match goal with H : gStatic (c ! v • Q) |- _ => inversion H; subst end.
    apply static_g. constructor;
      [constructor; apply static_g; constructor; constructor; assumption | assumption].
  - (* ax_swap_out: [Static Q] from the second branch, [gStatic X'] from
       the first -- the asymmetry the rule is about, read off the
       [Static] derivation. *)
    inversion Hsp; subst. inversion H0; subst.
    inversion H2; subst. inversion H3; subst.
    inversion H1; subst. inversion H4; subst.
    match goal with H : gStatic (c ! v • P + X') |- _ => inversion H; subst end.
    match goal with H : gStatic (c ! v' • Q + Y') |- _ => inversion H; subst end.
    match goal with H : gStatic (c ! v' • Q) |- _ => inversion H; subst end.
    apply static_g. constructor; [constructor; assumption | assumption].
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
  - (* ax_choice_stable. NB: invert [H3 : gStatic (gp' + gq)], never
       [H4 : gStatic gp] — the latter's head is a bare variable, so
       [inversion] would case-split on [gp]'s shape instead. *)
    inversion Hsp; subst. inversion H2; subst.
    inversion Hsq; subst. inversion H3; subst.
    apply must_i_choice_stable_compat.
    + exact H.
    + exact H0.
    + constructor. exact H4.
    + constructor. assumption.
    + constructor. exact H5.
    + apply IHHax; constructor; assumption.
  - (* ax_int_glb *)
    inversion Hsq; subst. inversion H0; subst.
    inversion H2; subst. inversion H3; subst.
    apply must_i_int_glb_pre.
    + apply IHHax1; assumption.
    + apply IHHax2; assumption.
  - (* ax_choice_tau *)
    inversion Hsp; subst. inversion H0; subst. inversion H2; subst.
    inversion Hsq; subst. inversion H4; subst. inversion H6; subst.
    apply must_i_choice_tau_compat.
    apply IHHax; assumption.
  - apply must_i_tau_flatten_pre_l. exact H.
  - apply must_i_tau_flatten_pre_r. exact H.
  - apply must_i_tau_sep_pre_l.
  - apply must_i_tau_sep_pre_r.
  - apply must_i_convex_pre.
  - apply must_i_success_nil_l.
  - apply must_i_success_nil_r.
  - apply must_i_share_in_pre.
  - apply must_i_share_out_pre.
  - apply must_i_swap_out_pre.
Qed.

End SoundnessAx.
