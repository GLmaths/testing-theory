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

(** * The recursion-free fragment of VACCS

    Checkpoint 0 of the inequational theory for the *asynchronous*
    value-passing calculus, mirroring [VCCS_Static.v]. [Static] excludes
    exactly [pr_var] and [pr_rec]; everything else is preserved.

    **Two syntactic differences from VCCS drive the whole development.**

    - An output is an *atomic message*: [pr_output : ChannelData ->
      ValueData -> proc], written [c ! v • 𝟘] but with no continuation to
      speak of. Hence [static_out] takes no premise, and there is no
      output congruence rule to be had later — there is nothing under an
      output to rewrite.
    - [gproc] has **no output constructor**: a guarded sum is built from
      [①], [𝟘], inputs, [𝛕] and [+] only. So a process can never choose
      *by sending*, which is exactly asynchrony, and it is why the
      must-preorder collapses distinctions VCCS keeps (e.g.
      [a ? (a ! x • 𝟘) ≂ₘᵤₛₜᵢ 𝟘], [VACCS_Examples.v]'s
      [NIL_is_equivalent_to_ccat]).

    Everything below is the [VCCS_Static.v] development with those two
    cases adjusted; the proofs are unchanged in shape (well-founded
    induction on [size], with the [+] case going through a [Hgen]
    helper because the two sub-sums are not immediate [proc] subterms). *)

From Stdlib.Wellfounded Require Import Inverse_Image.
From Stdlib.Program Require Import Equality.
From Stdlib Require Import PeanoNat Lia.
From stdpp Require Import base.
From TestingTheory Require Import VACCS VACCS_Instance Termination ActTau
  gLts Bisimulation InputOutputActions WeakTransitions Convergence.

Section VACCS_Static.

Context `{VP : VACCS_Parameters}.

(** ** Definition *)

Inductive Static : proc -> Prop :=
| static_par : forall p q, Static p -> Static q -> Static (p ‖ q)
| static_if  : forall C p q, Static p -> Static q -> Static (If C Then p Else q)
| static_out : forall c v, Static (c ! v • 𝟘)
| static_res : forall p, Static p -> Static (ν p)
| static_g   : forall p, gStatic p -> Static (g p)

with gStatic : gproc -> Prop :=
| gstatic_success : gStatic ①
| gstatic_nil     : gStatic 𝟘
| gstatic_input   : forall c p, Static p -> gStatic (c ? p)
| gstatic_tau     : forall p, Static p -> gStatic (𝛕 • p)
| gstatic_choice  : forall p q, gStatic p -> gStatic q -> gStatic (p + q).

Scheme Static_ind0 := Induction for Static Sort Prop
with gStatic_ind0 := Induction for gStatic Sort Prop.

Combined Scheme Static_ind' from Static_ind0, gStatic_ind0.

Hint Constructors Static : ccs.
Hint Constructors gStatic : ccs.

(** ** [Static] is preserved by value substitution

    Note the output case is now trivial: [subst_in_proc] rewrites the
    *value* carried by the message ([c ! (subst_Data k X v) • 𝟘]), and
    [static_out] holds for every value. *)

Lemma Static_subst : forall p, Static p -> forall k X, Static (subst_in_proc k X p).
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs k X.
  destruct p; simpl in *; inversion Hs; subst.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor.
  - constructor; eapply (IH p); try (simpl; lia); eassumption.
  - destruct g as [ | | c p | p | ga gb ]; simpl in *; inversion H0; subst.
    + repeat constructor.
    + repeat constructor.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + assert (Hgen: forall g1, gStatic g1 -> gsize g1 < S (gsize ga + gsize gb) ->
                    gStatic (subst_in_gproc k X g1)).
      { intros g1 Hg1 Hsz.
        assert (Hh: Static (g (subst_in_gproc k X g1))).
        { eapply (IH (g g1)); simpl; try lia. constructor; eassumption. }
        inversion Hh; eassumption. }
      constructor. constructor; apply Hgen; simpl; eauto; lia.
Qed.

(** The reverse direction, needed by the input rule's soundness case:
    its premise only ever gives [Static] of a *substituted* term. *)

Lemma Static_subst_rev : forall p, forall k X, Static (subst_in_proc k X p) -> Static p.
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros k X Hs.
  destruct p; simpl in *; inversion Hs; subst.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor.
  - constructor; eapply (IH p); try (simpl; lia); eassumption.
  - destruct g as [ | | c p | p | ga gb ]; simpl in *; inversion H0; subst.
    + repeat constructor.
    + repeat constructor.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + assert (Hgen: forall g1, gStatic (subst_in_gproc k X g1) ->
                    gsize g1 < S (gsize ga + gsize gb) -> gStatic g1).
      { intros g1 Hg1 Hsz.
        assert (Hh: Static (g g1)).
        { eapply (IH (g g1)); simpl; try lia. constructor; eassumption. }
        inversion Hh; eassumption. }
      constructor. constructor; apply Hgen; simpl; eauto; lia.
Qed.

(** ** [Static] rules out every source of non-termination

    The output case is where asynchrony shows: [c ! v • 𝟘] steps to
    [𝟘] and is consumed, so emitting strictly decreases [size] just like
    any other action. *)

Lemma Static_preserved_by_lts : forall p, Static p -> forall α q, lts p α q -> Static q.
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs α q Ht.
  destruct p; simpl in *.
  - inversion Hs; subst.
    dependent destruction Ht.
    + constructor.
      * eapply (IH p1); [simpl; lia | eassumption | eassumption].
      * eapply (IH p2); [simpl; lia | eassumption | eassumption].
    + constructor.
      * eapply (IH p1); [simpl; lia | eassumption | eassumption].
      * eapply (IH p2); [simpl; lia | eassumption | eassumption].
    + constructor.
      * eapply (IH p1); [simpl; lia | eassumption | eassumption].
      * eassumption.
    + constructor.
      * eassumption.
      * eapply (IH p2); [simpl; lia | eassumption | eassumption].
  - inversion Hs.
  - inversion Hs.
  - dependent destruction Ht.
    + inversion Hs; subst.
      eapply (IH p1); [simpl; lia | eassumption | eassumption].
    + inversion Hs; subst.
      eapply (IH p2); [simpl; lia | eassumption | eassumption].
  - dependent destruction Ht. repeat constructor.
  - dependent destruction Ht.
    + inversion Hs; subst.
      constructor.
      eapply (IH p); [simpl; lia | eassumption | eassumption].
    + inversion Hs; subst.
      constructor.
      eapply (IH p); [simpl; lia | eassumption | eassumption].
  - inversion Hs; subst.
    destruct g as [ | | c p | p | ga gb ]; simpl in *; inversion H0; subst.
    + dependent destruction Ht.
    + dependent destruction Ht.
    + dependent destruction Ht. apply Static_subst. eassumption.
    + dependent destruction Ht. eassumption.
    + dependent destruction Ht.
      * eapply (IH (g ga)); simpl; try lia; [constructor|]; eassumption.
      * eapply (IH (g gb)); simpl; try lia; [constructor|]; eassumption.
Qed.

Lemma size_subst : forall p k X, size (subst_in_proc k X p) = size p.
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros k X.
  destruct p; simpl in *.
  - rewrite (IH p1); [rewrite (IH p2) | ]; simpl; lia.
  - reflexivity.
  - rewrite (IH p); simpl; lia.
  - rewrite (IH p1); [rewrite (IH p2) | ]; simpl; lia.
  - reflexivity.
  - rewrite (IH p); simpl; lia.
  - destruct g as [ | | c p | p | ga gb ]; simpl in *; try reflexivity.
    + rewrite (IH p); simpl; lia.
    + rewrite (IH p); simpl; lia.
    + assert (Heq1: gsize (subst_in_gproc k X ga) = gsize ga) by (apply (IH (g ga)); simpl; lia).
      assert (Heq2: gsize (subst_in_gproc k X gb) = gsize gb) by (apply (IH (g gb)); simpl; lia).
      rewrite Heq1, Heq2. reflexivity.
Qed.

Lemma Static_lts_decrease : forall p, Static p -> forall α q, lts p α q -> size q < size p.
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs α q Ht.
  destruct p; simpl in *.
  - inversion Hs; subst.
    dependent destruction Ht.
    + assert (size p3 < size p1) by (eapply (IH p1); [simpl; lia | eassumption | eassumption]).
      assert (size q2 < size p2) by (eapply (IH p2); [simpl; lia | eassumption | eassumption]).
      simpl; lia.
    + assert (size p3 < size p2) by (eapply (IH p2); [simpl; lia | eassumption | eassumption]).
      assert (size q2 < size p1) by (eapply (IH p1); [simpl; lia | eassumption | eassumption]).
      simpl; lia.
    + assert (size p3 < size p1) by (eapply (IH p1); [simpl; lia | eassumption | eassumption]).
      simpl; lia.
    + assert (size q2 < size p2) by (eapply (IH p2); [simpl; lia | eassumption | eassumption]).
      simpl; lia.
  - inversion Hs.
  - inversion Hs.
  - dependent destruction Ht.
    + inversion Hs; subst.
      assert (size p' < size p1) by (eapply (IH p1); [simpl; lia | eassumption | eassumption]).
      simpl; lia.
    + inversion Hs; subst.
      assert (size q' < size p2) by (eapply (IH p2); [simpl; lia | eassumption | eassumption]).
      simpl; lia.
  - dependent destruction Ht. simpl; lia.
  - dependent destruction Ht.
    + inversion Hs; subst.
      assert (size p' < size p) by (eapply (IH p); [simpl; lia | eassumption | eassumption]).
      simpl; lia.
    + inversion Hs; subst.
      assert (size p' < size p) by (eapply (IH p); [simpl; lia | eassumption | eassumption]).
      simpl; lia.
  - inversion Hs; subst.
    destruct g as [ | | c p | p | ga gb ]; simpl in *; inversion H0; subst.
    + dependent destruction Ht.
    + dependent destruction Ht.
    + dependent destruction Ht. rewrite size_subst. simpl; lia.
    + dependent destruction Ht. simpl; lia.
    + dependent destruction Ht.
      * assert (size q < gsize ga)
          by (eapply (IH (g ga)); simpl; try lia; [constructor|]; eassumption).
        simpl; lia.
      * assert (size q < gsize gb)
          by (eapply (IH (g gb)); simpl; try lia; [constructor|]; eassumption).
        simpl; lia.
Qed.

Lemma Static_terminate : forall p, Static p -> p ⤓.
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs. constructor. intros q Htr.
  assert (Static q) by (eapply Static_preserved_by_lts; eassumption).
  assert (size q < size p) by (eapply Static_lts_decrease; eassumption).
  eapply IH; eassumption.
Qed.

(** Since a [Static] process never diverges it converges along *every*
    trace, which collapses the convergence half of the acceptance-set
    preorder to a triviality — exactly as in VCCS. *)

Lemma Static_preserved_by_wt : forall p s q, Static p -> p ⟹[s] q -> Static q.
Proof.
  intros p s q Hs Hw. induction Hw.
  - exact Hs.
  - apply IHHw. eapply Static_preserved_by_lts; eassumption.
  - apply IHHw. eapply Static_preserved_by_lts; eassumption.
Qed.

Lemma Static_converge : forall s p, Static p -> p ⇓ s.
Proof.
  induction s as [ | μ s IHs]; intros p Hs.
  - constructor. eapply Static_terminate; eassumption.
  - constructor.
    + eapply Static_terminate; eassumption.
    + intros q Hw. apply IHs. eapply Static_preserved_by_wt; eassumption.
Qed.

(** ** [Static] is preserved by the index-shifting operations

    [NewVarC]/[VarSwap_in_proc] shift *channel* indices (structural
    congruence's [ν]-swap and scope-extrusion steps); [NewVar]/[gNewVar]
    shift *value* indices. Same skeleton throughout: none of these
    fixpoints ever introduces or removes a [pr_var]/[pr_rec] node. *)

Lemma Static_NewVarC : forall p, Static p -> forall k, Static (NewVarC k p).
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs k.
  destruct p; simpl in *; inversion Hs; subst.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor.
  - constructor; eapply (IH p); try (simpl; lia); eassumption.
  - destruct g as [ | | c p | p | ga gb ]; simpl in *; inversion H0; subst.
    + repeat constructor.
    + repeat constructor.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + assert (Hgen: forall g1, gStatic g1 -> gsize g1 < S (gsize ga + gsize gb) ->
                    gStatic (gNewVarC k g1)).
      { intros g1 Hg1 Hsz.
        assert (Hh: Static (g (gNewVarC k g1))).
        { eapply (IH (g g1)); simpl; try lia. constructor; eassumption. }
        inversion Hh; eassumption. }
      constructor. constructor; apply Hgen; simpl; eauto; lia.
Qed.

Lemma Static_NewVar : forall p, Static p -> forall k, Static (NewVar k p).
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs k.
  destruct p; simpl in *; inversion Hs; subst.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor.
  - constructor; eapply (IH p); try (simpl; lia); eassumption.
  - destruct g as [ | | c p | p | ga gb ]; simpl in *; inversion H0; subst.
    + repeat constructor.
    + repeat constructor.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + assert (Hgen: forall g1, gStatic g1 -> gsize g1 < S (gsize ga + gsize gb) ->
                    gStatic (gNewVar k g1)).
      { intros g1 Hg1 Hsz.
        assert (Hh: Static (g (gNewVar k g1))).
        { eapply (IH (g g1)); simpl; try lia. constructor; eassumption. }
        inversion Hh; eassumption. }
      constructor. constructor; apply Hgen; simpl; eauto; lia.
Qed.

Lemma gStatic_gNewVar : forall M, gStatic M -> forall k, gStatic (gNewVar k M).
Proof.
  intros M Hm k.
  assert (Static (NewVar k (g M))) by (apply Static_NewVar; constructor; eassumption).
  simpl in H. inversion H; assumption.
Qed.

Lemma Static_VarSwap : forall p, Static p -> forall k, Static (VarSwap_in_proc k p).
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs k.
  destruct p; simpl in *; inversion Hs; subst.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor.
  - constructor; eapply (IH p); try (simpl; lia); eassumption.
  - destruct g as [ | | c p | p | ga gb ]; simpl in *; inversion H0; subst.
    + repeat constructor.
    + repeat constructor.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + assert (Hgen: forall g1, gStatic g1 -> gsize g1 < S (gsize ga + gsize gb) ->
                    gStatic (gVarSwap_in_proc k g1)).
      { intros g1 Hg1 Hsz.
        assert (Hh: Static (g (gVarSwap_in_proc k g1))).
        { eapply (IH (g g1)); simpl; try lia. constructor; eassumption. }
        inversion Hh; eassumption. }
      constructor. constructor; apply Hgen; simpl; eauto; lia.
Qed.

End VACCS_Static.
