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


(** * Residue enumeration, and the weak-emission glb law

    Everything a rule with **weakly matched emissions** needs, placed
    upstream of the axiom system so that a constructor can name it.

    Three layers:

    - [ichoice], the n-ary internal choice, and the fact that it passes a
      test as soon as all its members do ([ichoice_must]).  This is what
      turns a *conjunction* of residue obligations into a **process**.
    - [tau_list]/[reach_list]/[res_list_v], the computations that
      enumerate a [Static] process's weak τ-closure and, from it, the
      residues of its emissions on a given channel at a given value.
      Both recursions run **by fuel on [size]** rather than on
      [terminate], which lives in [Prop] and forbids large elimination.
    - [must_i_glb_res], [VACCS_Precongruence.must_i_glb_weak] with its
      collecting premise discharged once and for all.

    Why weakly matched emissions are wanted at all:
    [VACCS_Precongruence.must_i_glb_gen]'s output premise asks the
    left-hand side to emit **itself**, which is not a consequence of the
    preorder ([VACCS_Matching.glb_output_premise_not_semantic]); the weak
    form is ([VACCS_Matching.weak_out_of_below]). *)

From Stdlib Require Import List Lia.
From stdpp Require Import base sets gmap.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure VACCS_Shift VACCS_Precongruence.

Section VACCS_Residues.

Context `{VP : VACCS_Parameters}.

(** ** n-ary internal choice

    Ported from VCCS's [CompletenessAx.v].  The singleton case is
    [𝛕•p + 𝛕•p], not [𝛕•p]: the obvious version would need Milner's first
    [𝛕]-law, [⊢ g (𝛕 • p) ≂ p], which this system does not have (no rule
    has a lone [𝛕]-guard on either side).  Duplicating sidesteps the
    question, and it is what makes [VACCS_Matching.ax_ichoice_below] hold
    at a singleton. *)

Fixpoint ichoice (l : list proc) : gproc :=
match l with
| nil       => 𝟘
| p :: nil  => (𝛕 • p) + (𝛕 • p)
| p :: l'   => (𝛕 • p) + ichoice l'
end.

Lemma ichoice_gAllTau : forall l, l <> nil -> gAllTau (ichoice l).
Proof.
  induction l as [|p l IH]; intro Hne; [ contradiction | ].
  destruct l as [|p2 l2]; simpl.
  - split; exact I.
  - split; [ exact I | apply IH; discriminate ].
Qed.

Lemma lts_ichoice : forall (l : list proc) (p : proc), In p l ->
  lts (g (ichoice l)) τ p.
Proof.
  induction l as [|p0 l IH]; intros p Hin; [ contradiction | ].
  destruct l as [|p2 l2].
  - destruct Hin as [E|F]; [ subst p0 | contradiction ].
    apply lts_choiceL. apply lts_tau.
  - destruct Hin as [E|Hin].
    + subst p0. apply lts_choiceL. apply lts_tau.
    + apply lts_choiceR. apply IH. exact Hin.
Qed.

(** ** The n-ary join

    [ichoice] turns a conjunction of obligations into a process only if
    "all members pass [t]" gives "[ichoice L] passes [t]".  The binary
    case is [must_i_int_glb]; the n-ary one needs the asymmetric shape
    [𝛕•x + M] with [M] all-τ, since [ichoice (x :: l)] is *not* of the
    form [𝛕•_ + 𝛕•_].  [gAllTau_no_ext] is what makes its [com] field
    vacuous. *)

Lemma must_i_tau_join_gen : forall (x : proc) (M : gproc) t,
  gAllTau M -> x must_pass t -> ((g M) : proc) must_pass t ->
  (g (((𝛕 • x) + M) : gproc)) must_pass t.
Proof.
  intros x M t HM Hm1. revert HM. revert M.
  induction Hm1 as [t Hout | p t nh ex pt IHpt et IHet com IHcom];
    intros M HM Hm2.
  - now apply m_now.
  - assert (Hp : p must_pass t) by (apply m_step; assumption).
    apply m_step.
    + exact nh.
    + exists (p, t). eapply ParLeft. apply lts_choiceL. apply lts_tau.
    + intros p' Hp'. inversion Hp'; subst.
      * inversion H3; subst. exact Hp.
      * inversion Hm2; subst.
        { exfalso. apply nh. assumption. }
        eapply pt0. exact H3.
    + intros t' Ht'. apply IHet; [ exact Ht' | exact HM | ].
      inversion Hm2; subst.
      * exfalso. apply nh. assumption.
      * eapply et0. exact Ht'.
    + intros p' t' mu1 mu2 Hdual Hp' Ht'. inversion Hp'; subst.
      * inversion H3.
      * exfalso. eapply gAllTau_no_ext; [ exact HM | exact H3 ].
Qed.

Lemma ichoice_must : forall (L : list proc) t, L <> nil ->
  (forall x, In x L -> x must_pass t) -> (g (ichoice L)) must_pass t.
Proof.
  induction L as [|x L IH]; intros t Hne Hall; [ contradiction | ].
  destruct L as [|y L'].
  - simpl. apply must_i_int_glb; apply Hall; left; reflexivity.
  - assert (Hrec : (g (ichoice (y :: L'))) must_pass t).
    { apply IH; [ discriminate | ]. intros z Hz. apply Hall. right. exact Hz. }
    simpl. apply must_i_tau_join_gen.
    + apply (ichoice_gAllTau (y :: L')). discriminate.
    + apply Hall. left. reflexivity.
    + exact Hrec.
Qed.

(** ** Enumerating the reducts

    The τ-reducts of a state form a [gset] through [lts_set], which the
    VACCS instance exposes concretely — so no choice principle is needed
    to turn them into a list. *)

Definition tau_list (q : proc) : list proc := elements (lts_set q τ).

Lemma tau_list_spec : forall q x, In x (tau_list q) <-> lts q τ x.
Proof.
  intros q x. unfold tau_list. split.
  - intro Hin. apply lts_set_spec0. apply elem_of_elements.
    apply list_elem_of_In. exact Hin.
  - intro Hl. apply list_elem_of_In. apply elem_of_elements.
    apply lts_set_spec1. exact Hl.
Qed.

(** [reach_list] closes [tau_list] under iteration.  Each τ strictly
    shrinks a [Static] process ([Static_lts_decrease]), so [S (size p)]
    steps of fuel suffice. *)

Fixpoint reach_list (n : nat) (p : proc) : list proc :=
match n with
| 0 => [p]
| S n' => p :: flat_map (reach_list n') (tau_list p)
end.

Lemma reach_list_sound : forall n p x, In x (reach_list n p) -> p ⟹[[]] x.
Proof.
  induction n as [|n IH]; intros p x Hin; simpl in Hin.
  - destruct Hin as [He|[]]. subst. apply wt_nil.
  - destruct Hin as [He|Hin]; [ subst; apply wt_nil | ].
    apply in_flat_map in Hin as (y & Hy & Hx).
    eapply wt_tau; [ apply tau_list_spec; exact Hy | apply IH; exact Hx ].
Qed.

Lemma reach_list_complete : forall n p x, Static p -> (size p < n)%nat ->
  p ⟹[[]] x -> In x (reach_list n p).
Proof.
  induction n as [|n IH]; intros p x Hst Hsz Hw; [ lia | ].
  inversion Hw; subst.
  - left. reflexivity.
  - right. apply in_flat_map. exists q. split.
    + apply tau_list_spec. exact l.
    + apply IH.
      * eapply Static_preserved_by_lts; [ exact Hst | exact l ].
      * assert (Hlt : (size q < size p)%nat)
          by (eapply Static_lts_decrease; eassumption). lia.
      * exact w.
Qed.

(** ** The residues at ONE value

    The value being given, the residues are read straight off [lts_set];
    no enumeration of the emittable values is needed. *)

Definition res_v (c : ChannelData) (v : ValueData) (u : proc) : list proc :=
  elements (lts_set u (ActExt (ActOut (c,v)))).

Definition res_list_v (n : nat) (c : ChannelData) (v : ValueData) (p : proc)
  : list proc := flat_map (res_v c v) (reach_list n p).

Lemma res_list_v_sound : forall n p c v r, In r (res_list_v n c v p) ->
  exists p1, p ⟹[[]] p1 /\ lts p1 (ActExt (ActOut (c,v))) r.
Proof.
  intros n p c v r Hin. unfold res_list_v in Hin.
  apply in_flat_map in Hin. destruct Hin as (p1 & Hp1 & Hr).
  exists p1. split.
  - eapply reach_list_sound. exact Hp1.
  - unfold res_v in Hr.
    apply lts_set_spec0. apply elem_of_elements. apply list_elem_of_In. exact Hr.
Qed.

Lemma res_list_v_complete : forall n p c v, Static p -> (size p < n)%nat ->
  forall p1 r, p ⟹[[]] p1 -> lts p1 (ActExt (ActOut (c,v))) r ->
  In r (res_list_v n c v p).
Proof.
  intros n p c v Hst Hn p1 r Hp1 Hr.
  unfold res_list_v. apply in_flat_map. exists p1. split.
  - eapply reach_list_complete; eassumption.
  - unfold res_v. apply list_elem_of_In. apply elem_of_elements.
    apply lts_set_spec1. exact Hr.
Qed.

(** ** The weak-emission glb law, with its collecting premise discharged

    [must_i_glb_weak] is stated over an abstract [W]; the intended [W] is
    the internal choice of the residues, and with it the collecting
    premise holds once and for all. *)

Lemma ichoice_res_collect : forall n c v (p : proc) t,
  res_list_v n c v p <> nil ->
  (forall p1 p'', p ⟹[[]] p1 ->
     lts p1 (ActExt (ActOut (c,v))) p'' -> p'' must_pass t) ->
  (g (ichoice (res_list_v n c v p))) must_pass t.
Proof.
  intros n c v p t Hne Hall. apply ichoice_must; [ exact Hne | ].
  intros x Hx. apply res_list_v_sound in Hx as (p1 & Hp1 & Ho).
  eapply Hall; [ exact Hp1 | exact Ho ].
Qed.

(** Compare [must_i_glb_gen], whose output premise asks [p] to emit
    itself.  The two output premises here are, at a constant value,
    exactly what the preorder supplies:
    [VACCS_Matching.res_list_v_nonempty] for the first,
    [VACCS_Matching.ichoice_residues_below] for the second.

    Note the law needs neither [Static] nor a bound on [n]: those enter
    only when the premises are *discharged*, not when they are used. *)

Theorem must_i_glb_res : forall (p q : proc) n,
  (exists q0, lts q τ q0) ->
  (forall q', lts q τ q' -> p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q') ->
  (forall c v q'', lts q (ActExt (ActIn (c,v))) q'' ->
     ((c ! v • 𝟘) ‖ p) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q'') ->
  (forall c v q'', lts q (ActExt (ActOut (c,v))) q'' ->
     res_list_v n c v p <> nil) ->
  (forall c v q'', lts q (ActExt (ActOut (c,v))) q'' ->
     (g (ichoice (res_list_v n c v p))) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q'') ->
  p ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ q.
Proof.
  intros p q n Htau0 Htau Hin Hne Hout.
  apply (must_i_glb_weak p q (fun c v => g (ichoice (res_list_v n c v p))));
    try assumption.
  intros c v q'' t Hq'' Hall.
  apply ichoice_res_collect; [ eapply Hne; exact Hq'' | exact Hall ].
Qed.

End VACCS_Residues.
