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

(** ** The summands of a guarded sum, and how they carry its transitions *)

Fixpoint summands (M : gproc) : list gproc :=
match M with
| M1 + M2 => summands M1 ++ summands M2
| b => [b]
end.

Lemma summand_lts : forall (M a : gproc), In a (summands M) ->
  forall al q, lts (g a) al q -> lts (g M) al q.
Proof.
  induction M as [ | | c p | p | M1 IH1 M2 IH2 ]; intros a Hin al q Hl; simpl in Hin.
  - destruct Hin as [He|[]]; subst; exact Hl.
  - destruct Hin as [He|[]]; subst; exact Hl.
  - destruct Hin as [He|[]]; subst; exact Hl.
  - destruct Hin as [He|[]]; subst; exact Hl.
  - apply in_app_or in Hin. destruct Hin as [H1|H2].
    + apply lts_choiceL. eapply IH1; eassumption.
    + apply lts_choiceR. eapply IH2; eassumption.
Qed.

Lemma gsum_in_summand : forall (M : gproc) c w p',
  lts (g M) (ActExt (ActIn (c,w))) p' ->
  exists P, In (c ? P) (summands M) /\ p' = P ^ w.
Proof.
  induction M as [ | | d P | P | M1 IH1 M2 IH2 ]; intros c w p' Hl;
    inversion Hl; subst.
  - exists P. split; [ left; reflexivity | reflexivity ].
  - destruct (IH1 c w p' H3) as (P & Hin & He).
    exists P. split; [ apply in_or_app; left; exact Hin | exact He ].
  - destruct (IH2 c w p' H3) as (P & Hin & He).
    exists P. split; [ apply in_or_app; right; exact Hin | exact He ].
Qed.

Lemma gsum_tau_summand : forall (M : gproc) X,
  lts (g M) τ X -> In (𝛕 • X) (summands M).
Proof.
  induction M as [ | | d P | P | M1 IH1 M2 IH2 ]; intros X Hl; inversion Hl; subst.
  - left. reflexivity.
  - apply in_or_app. left. apply IH1. exact H3.
  - apply in_or_app. right. apply IH2. exact H3.
Qed.

(** ** n-ary internal choice

    Ported from VCCS's [CompletenessAx.v].  The singleton case is
    [𝛕•p + 𝛕•p], not [𝛕•p]: the obvious version would need Milner's first
    [𝛕]-law, [(g (𝛕 • p)) ᴠᴀᴄᴄꜱ≂ₐₓ p], which this system does not have (no rule
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

End VACCS_Residues.
