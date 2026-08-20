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

(** * A negative result: stable-choice congruence is UNSOUND for VACCS

    In VCCS, sum-congruence is unsound in general but becomes sound once
    both sides are required to be *initially stable*
    ([VCCS_ReadySet.must_i_choice_stable_compat]) — the design principle
    being that a rewrite may not change whether the rewritten summand is
    initially stable.  That rule, [ax_choice_stable], is what licenses
    every rewrite inside a sum in VCCS's completeness proof.

    **It does not survive the move to VACCS**, and this file exhibits the
    counterexample.  The reason is asynchrony, and specifically the
    copycat: [VACCS_Examples.v] machine-checks

        ccat := a ? (a ! x • 𝟘)   ≂ₘᵤₛₜᵢ   𝟘

    A copycat is invisible *standalone* — whatever a test sends it, it
    sends straight back, so the test cannot tell it apart from a process
    that never listened at all.  But guarded choice **commits**: putting a
    copycat beside another summand lets the sum consume a message, discard
    the alternative, and then be stuck holding a message nobody wants.

    Concretely, with three distinct channels [a], [b], [c] and

        S₁ := 𝟘    + (b ? (c!w•𝟘))          S₂ := ccat + (b ? (c!w•𝟘))
        T  := (a!I•𝟘) ‖ ((b!u•𝟘) ‖ (c ? ①))

    both summands are [gStable] and [g 𝟘 ⊑ₘᵤₛₜᵢ g ccat] holds, yet
    [S₁ must_pass T] and [¬ (S₂ must_pass T)].

    The mechanism, and why it does not contradict [ccat ≂ 𝟘]: standalone,
    [g 𝟘] *also* fails [T] (nothing can move at all), so [T] does not
    separate [𝟘] from [ccat].  It is only under the choice that they part
    company — the [b]-summand supplies the interaction that [S₁] needs,
    while [S₂] may instead commit to the copycat branch, swallow [a!I],
    lose the [b]-summand, and deadlock holding [a!I•𝟘] against a test that
    never listens on [a].

    **Consequence for the axiom system.** No [ax_choice_stable] for VACCS.
    What survives is *guard-preserving* congruence — rewriting a summand's
    continuation while keeping its guard, so the sum's ready set is
    untouched: [VACCS_Precongruence.must_i_choice_input_compat] for an
    input summand and [must_i_choice_tau_compat] for a [𝛕] summand.  Those
    are proved, by direct [must] induction, and between them they cover
    every guard shape VACCS has. *)

From Stdlib Require Import Lia.
From Stdlib.Program Require Import Equality.
From stdpp Require Import base.
From TestingTheory Require Import InputOutputActions ActTau Must VACCS_Must_Characterization
  gLts Bisimulation Lts_OBA Lts_FW Lts_OBA_FB ParallelLTSConstruction
  InteractionBetweenLts Testing_Predicate DefinitionAS VACCS VACCS_Good VACCS_Instance
  Convergence WeakTransitions Subset_Act MultisetLTSConstruction Termination
  VACCS_Static VACCS_Erasure VACCS_Examples.

Section VACCS_ChoiceProbes.

Context `{VP : VACCS_Parameters}.
Context {a b c : Channel} {I u w O : Value}.
Context {nab : a <> b} {nac : a <> c} {nbc : b <> c} {nOI : O <> I}.

(** ** The processes *)

Definition Kc : proc := (cst c) ! (cst w) • 𝟘.
Definition GQ : gproc := (cst b) ? Kc.
Definition CCAT : gproc := (cst a) ? ((cst a) ! (bvar 0) • 𝟘).

Definition S1 : proc := g (𝟘 + GQ).
Definition S2 : proc := g (CCAT + GQ).

Definition TT : proc :=
  ((cst a) ! (cst I) • 𝟘) ‖ (((cst b) ! (cst u) • 𝟘) ‖ (g ((cst c) ? (g ①)))).

(** [TT] after the [b]-synchronisation. *)
Definition T2 : proc := ((cst a) ! (cst I) • 𝟘) ‖ ((g 𝟘) ‖ (g ((cst c) ? (g ①)))).

(** ** Enumerating the transitions

    [blast2] inverts every [lts] hypothesis whose subject has a concrete
    head, then closes the residue with the channel disequalities.  The
    leading [unfold lts_step in *] is needed because [must]'s own fields
    are stated with the [gLts] notation [⟶], not with [lts] directly. *)

Ltac blast2 :=
  unfold lts_step in *; simpl in *;
  repeat match goal with
  | H : lts (_ ‖ _) _ _ |- _ => inversion H; subst; clear H
  | H : lts (_ ! _ • 𝟘) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g (_ + _)) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g (_ ? _)) _ _ |- _ => inversion H; subst; clear H
  | H : lts (g 𝟘) _ _ |- _ => inversion H
  | H : lts (g ①) _ _ |- _ => inversion H
  end; simpl in *; try congruence; try contradiction.

Lemma dual_io : forall (x : TypeOfActions), dual (ActIn x) (ActOut x).
Proof. intros x. simpl. reflexivity. Qed.

Lemma TT_not_good : ~ good_VACCS TT.
Proof.
  unfold TT. intro H. inversion H; subst. destruct H1 as [H1|H1].
  - inversion H1.
  - inversion H1; subst. destruct H2 as [H2|H2]; inversion H2.
Qed.

Lemma T2_not_good : ~ good_VACCS T2.
Proof.
  unfold T2. intro H. inversion H; subst. destruct H1 as [H1|H1]; [ inversion H1 | ].
  inversion H1; subst. destruct H2 as [H2|H2]; inversion H2.
Qed.

(** The test has no internal [τ] of its own: its only outputs are on [a]
    and [b], its only input is on [c], and the three channels differ. *)
Lemma TT_no_tau : forall t', ~ lts TT τ t'.
Proof. unfold TT. intros t' Hl. blast2. Qed.

(** ** [S₁] passes the test *)

Lemma level2 : Kc must_pass T2.
Proof.
  apply m_step.
  - apply T2_not_good.
  - exists ((g 𝟘) ▷ (((cst a) ! (cst I) • 𝟘) ‖ ((g 𝟘) ‖ (g ①)))).
    eapply ParSync; [ apply dual_out_in | unfold Kc; apply lts_output | ].
    unfold T2. apply lts_parR. apply lts_parR.
    assert (E : ((g ①) : proc) ^ (cst w) = g ①) by reflexivity.
    rewrite <- E. apply lts_input.
  - intros p' Hp'. unfold Kc in Hp'. blast2.
  - intros t' Ht'. unfold T2 in Ht'. blast2.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold Kc in Hp'. unfold T2 in Ht'. blast2.
    apply m_now. apply good_par. right. apply good_par. right. apply good_success.
Qed.

Lemma S1_passes : S1 must_pass TT.
Proof.
  apply m_step.
  - apply TT_not_good.
  - exists (Kc ▷ T2).
    eapply ParSync; [ apply dual_io | | ].
    + unfold S1, GQ. apply lts_choiceR.
      assert (E : Kc ^ (cst u) = Kc) by reflexivity. rewrite <- E at 2. apply lts_input.
    + unfold TT, T2. apply lts_parR. apply lts_parL. apply lts_output.
  - intros p' Hp'. unfold S1, GQ in Hp'. blast2.
  - intros t' Ht'. exfalso. eapply TT_no_tau. exact Ht'.
  - intros p' t' mu1 mu2 Hd Hp' Ht'.
    unfold S1, GQ in Hp'. unfold TT in Ht'. blast2.
    exact level2.
Qed.

(** ** [S₂] fails it

    [S₂] may commit to the copycat branch, swallowing [a!I] and discarding
    the [b]-summand.  What is left is a message on [a] facing a test that
    only ever listens on [c] — nothing can move, and the test is not good. *)

Lemma stuck_after_theft :
  ~ ((cst a ! cst I • 𝟘) must_pass ((g 𝟘) ‖ (((cst b) ! (cst u) • 𝟘) ‖ (g ((cst c) ? (g ①)))))).
Proof.
  intro Hm. inversion Hm as [Ho | Ho Hex Hpt Het Hcom]; subst.
  - inversion Ho; subst. destruct H0 as [H0|H0]; [ inversion H0 | ].
    inversion H0; subst. destruct H1 as [H1|H1]; inversion H1.
  - destruct Hex as ((y1,y2) & Hs). inversion Hs; subst; blast2.
Qed.

Lemma S2_fails : ~ (S2 must_pass TT).
Proof.
  intro Hm. inversion Hm as [Ho | Ho Hex Hpt Het Hcom]; subst.
  - apply TT_not_good. exact Ho.
  - apply stuck_after_theft.
    eapply (Hcom _ _ (ActIn (cst a, cst I)) (ActOut (cst a, cst I))).
    + apply dual_io.
    + unfold S2, CCAT. apply lts_choiceL.
      assert (E : ((cst a ! (bvar 0) • 𝟘) : proc) ^ (cst I) = cst a ! cst I • 𝟘) by reflexivity.
      rewrite <- E. apply lts_input.
    + unfold TT. apply lts_parL. apply lts_output.
Qed.

(** ** The negative result

    Note how weak the refuted rule is: both summands being rewritten are
    [gStable] (one is [𝟘], the other an input guard), the context [GQ] is
    a plain input guard, and every process in sight is [Static].  Adding
    those side conditions back would not save it. *)

Theorem choice_stable_congruence_is_unsound :
  ~ (forall (gp gp' gq : gproc),
       (g gp) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g gp') -> (g (gp + gq)) ᴠᴀᴄᴄꜱ⊑ₘᵤₛₜᵢ (g (gp' + gq))).
Proof.
  intro Hrule.
  apply S2_fails.
  apply (Hrule 𝟘 CCAT GQ).
  - exact (@copycat_is_above_NIL VP a O I nOI).
  - exact S1_passes.
Qed.

End VACCS_ChoiceProbes.
