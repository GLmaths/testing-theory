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

(** * The recursion-free ("Static") fragment of VCCS

    This is the first building block of a Hennessy-Ingólfsdóttir-style
    inequational proof system for the must-preorder on VCCS. The proof
    system's completeness result is stated only for [Static] processes,
    i.e. processes that never use [pr_var]/[pr_rec] (no recursion, hence
    no divergence, hence no need for a [Ω]-like bottom element). *)

From Stdlib.Wellfounded Require Import Inverse_Image.
From Stdlib.Program Require Import Equality.
From Stdlib Require Import PeanoNat Lia.
From stdpp Require Import base.
From TestingTheory Require Import VCCS VCCS_Instance Termination ActTau
  gLts Bisimulation InputOutputActions WeakTransitions Convergence.

Section VCCS_Static.

Context `{VP : VCCS_Parameters}.

(** ** Definition *)

Inductive Static : proc -> Prop :=
| static_par : forall p q, Static p -> Static q -> Static (p ‖ q)
| static_if  : forall C p q, Static p -> Static q -> Static (If C Then p Else q)
| static_res : forall p, Static p -> Static (ν p)
| static_g   : forall p, gStatic p -> Static (g p)

with gStatic : gproc -> Prop :=
| gstatic_success : gStatic ①
| gstatic_nil     : gStatic 𝟘
| gstatic_input   : forall c p, Static p -> gStatic (c ? p)
| gstatic_output  : forall c v p, Static p -> gStatic (c ! v • p)
| gstatic_tau     : forall p, Static p -> gStatic (𝛕 • p)
| gstatic_choice  : forall p q, gStatic p -> gStatic q -> gStatic (p + q).

Scheme Static_ind0 := Induction for Static Sort Prop
with gStatic_ind0 := Induction for gStatic Sort Prop.

Combined Scheme Static_ind' from Static_ind0, gStatic_ind0.

Hint Constructors Static : ccs.
Hint Constructors gStatic : ccs.

(** ** [Static] is preserved by substitution *)

Lemma Static_subst : forall p, Static p -> forall k X, Static (subst_in_proc k X p).
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs k X.
  destruct p; simpl in *; inversion Hs; subst.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor; eapply (IH p); try (simpl; lia); eassumption.
  - inversion Hs; subst.
    destruct g; simpl in *; inversion H0; subst.
    + repeat constructor.
    + repeat constructor.
    + constructor.
      constructor.
      eapply (IH p); try (simpl; lia); eassumption.
    + constructor.
      constructor.
      eapply (IH p); try (simpl; lia); eassumption.
    + constructor.
      constructor.
      eapply (IH p); try (simpl; lia); eassumption.
    + assert (Hgen: forall g0, gStatic g0 -> gsize g0 < S (gsize g1 + gsize g2) -> gStatic (subst_in_gproc k X g0)).
      { intros g0 Hg0 Hsz.
        assert (Hh: Static (g (subst_in_gproc k X g0))).
        { eapply (IH (g g0)); simpl; try lia.
          constructor; eassumption. }
        inversion Hh; eassumption. }
      constructor.
      constructor; apply Hgen; simpl; eauto; lia.
Qed.

(** ** The reverse of [Static_subst]: [Static] reflects substitution too

    Needed for [ax_input]'s case of [SoundnessAx.v]'s
    [ax_pre_static_preserved]: the premise there is
    [forall v, Static (p^v) -> Static (q^v)], which only ever gives
    [Static] of a *substituted* [q] — recovering [Static q] itself
    needs this reverse direction ([subst_in_proc]/[subst_in_gproc] never
    introduce or remove [pr_var]/[pr_rec] nodes, so — like
    [NewVarC]/[VarSwap_in_proc] above — the same well-founded-induction
    skeleton as [Static_subst] works, just reading the case split the
    other way). *)

Lemma Static_subst_rev : forall p, forall k X, Static (subst_in_proc k X p) -> Static p.
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros k X Hs.
  destruct p; simpl in *; inversion Hs; subst.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor; eapply (IH p); try (simpl; lia); eassumption.
  - destruct g; simpl in *; inversion H0; subst.
    + repeat constructor.
    + repeat constructor.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + assert (Hgen: forall g0, gStatic (subst_in_gproc k X g0) -> gsize g0 < S (gsize g1 + gsize g2) -> gStatic g0).
      { intros g0 Hg0 Hsz.
        assert (Hh: Static (g g0)).
        { eapply (IH (g g0)); simpl; try lia. constructor; eassumption. }
        inversion Hh; eassumption. }
      constructor. constructor; apply Hgen; simpl; eauto; lia.
Qed.

(** ** [Static] rules out every source of non-termination *)

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
  - dependent destruction Ht.
    + inversion Hs; subst.
      constructor.
      eapply (IH p); [simpl; lia | eassumption | eassumption].
    + inversion Hs; subst.
      constructor.
      eapply (IH p); [simpl; lia | eassumption | eassumption].
  - inversion Hs; subst.
    destruct g; simpl in *; inversion H0; subst.
    + dependent destruction Ht.
    + dependent destruction Ht.
    + dependent destruction Ht.
      apply Static_subst.
      eassumption.
    + dependent destruction Ht.
      eassumption.
    + dependent destruction Ht.
      eassumption.
    + dependent destruction Ht.
      * eapply (IH (g g1)); simpl; try lia; [constructor|]; eassumption.
      * eapply (IH (g g2)); simpl; try lia; [constructor|]; eassumption.
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
  - rewrite (IH p); simpl; lia.
  - destruct g; simpl in *; try reflexivity.
    + rewrite (IH p); simpl; lia.
    + rewrite (IH p); simpl; lia.
    + rewrite (IH p); simpl; lia.
    + assert (Heq1: gsize (subst_in_gproc k X g1) = gsize g1) by (apply (IH (g g1)); simpl; lia).
      assert (Heq2: gsize (subst_in_gproc k X g2) = gsize g2) by (apply (IH (g g2)); simpl; lia).
      rewrite Heq1, Heq2.
      reflexivity.
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
  - dependent destruction Ht.
    + inversion Hs; subst.
      assert (size p' < size p) by (eapply (IH p); [simpl; lia | eassumption | eassumption]).
      simpl; lia.
    + inversion Hs; subst.
      assert (size p' < size p) by (eapply (IH p); [simpl; lia | eassumption | eassumption]).
      simpl; lia.
  - inversion Hs; subst.
    destruct g; simpl in *; inversion H0; subst.
    + dependent destruction Ht.
    + dependent destruction Ht.
    + dependent destruction Ht.
      rewrite size_subst.
      simpl; lia.
    + dependent destruction Ht.
      simpl; lia.
    + dependent destruction Ht.
      simpl; lia.
    + dependent destruction Ht.
      * assert (size q < gsize g1) by (eapply (IH (g g1)); simpl; try lia; [constructor|]; eassumption).
        simpl; lia.
      * assert (size q < gsize g2) by (eapply (IH (g g2)); simpl; try lia; [constructor|]; eassumption).
        simpl; lia.
Qed.

Lemma Static_terminate : forall p, Static p -> p ⤓.
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs.
  constructor.
  intros q Htr.
  assert (Static q) by (eapply Static_preserved_by_lts; eassumption).
  assert (size q < size p) by (eapply Static_lts_decrease; eassumption).
  eapply IH; eassumption.
Qed.

(** ** [Static] is preserved by weak transitions, and converges along every trace

    Since a [Static] process never diverges, it converges ([⇓ s]) along
    *every* trace [s], not just some — this collapses the convergence-
    inclusion half of the acceptance-set preorder to a triviality for the
    processes this development cares about. *)

Lemma Static_preserved_by_wt : forall p s q, Static p -> p ⟹[s] q -> Static q.
Proof.
  intros p s q Hs Hw.
  induction Hw.
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

(** ** [Static] is preserved by the channel-index-shifting operations
    [NewVarC]/[VarSwap_in_proc] used by structural congruence's [ν]-swap
    and scope-extrusion steps ([Congruence.v]) — same well-founded-
    induction-on-size skeleton as [Static_subst], since both fixpoints
    have the same recursive shape and never introduce [pr_var]/[pr_rec]. *)

Lemma Static_NewVarC : forall p, Static p -> forall k, Static (NewVarC k p).
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs k.
  destruct p; simpl in *; inversion Hs; subst.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor; eapply (IH p); try (simpl; lia); eassumption.
  - destruct g; simpl in *; inversion H0; subst.
    + repeat constructor.
    + repeat constructor.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + assert (Hgen: forall g0, gStatic g0 -> gsize g0 < S (gsize g1 + gsize g2) -> gStatic (gNewVarC k g0)).
      { intros g0 Hg0 Hsz.
        assert (Hh: Static (g (gNewVarC k g0))).
        { eapply (IH (g g0)); simpl; try lia. constructor; eassumption. }
        inversion Hh; eassumption. }
      constructor. constructor; apply Hgen; simpl; eauto; lia.
Qed.

(** ** [Static] is preserved by the value-index-shifting operation [NewVar]/[gNewVar]

    Same recursive shape as [NewVarC]/[gNewVarC] above (compare
    [VCCS.v]'s [NewVar]/[gNewVar] to [NewVarC]/[gNewVarC] — identical
    case split, just shifting the value-index space instead of the
    channel-index space), hence the same well-founded-induction-on-size
    proof. Needed by [VCCS_Expansion.v]'s [ext]/[ext_r] (the input case
    shifts the *other* side's guarded sum out of the fresh value
    binder's way via [gNewVar 0 _]) to show [gStatic] is preserved. *)

Lemma Static_NewVar : forall p, Static p -> forall k, Static (NewVar k p).
Proof.
  induction p as (p & IH) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros Hs k.
  destruct p; simpl in *; inversion Hs; subst.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor; [eapply (IH p1) | eapply (IH p2)]; try (simpl; lia); eassumption.
  - constructor; eapply (IH p); try (simpl; lia); eassumption.
  - destruct g; simpl in *; inversion H0; subst.
    + repeat constructor.
    + repeat constructor.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + assert (Hgen: forall g0, gStatic g0 -> gsize g0 < S (gsize g1 + gsize g2) -> gStatic (gNewVar k g0)).
      { intros g0 Hg0 Hsz.
        assert (Hh: Static (g (gNewVar k g0))).
        { eapply (IH (g g0)); simpl; try lia. constructor; eassumption. }
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
  - constructor; eapply (IH p); try (simpl; lia); eassumption.
  - destruct g; simpl in *; inversion H0; subst.
    + repeat constructor.
    + repeat constructor.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + constructor. constructor. eapply (IH p); try (simpl; lia); eassumption.
    + assert (Hgen: forall g0, gStatic g0 -> gsize g0 < S (gsize g1 + gsize g2) -> gStatic (gVarSwap_in_proc k g0)).
      { intros g0 Hg0 Hsz.
        assert (Hh: Static (g (gVarSwap_in_proc k g0))).
        { eapply (IH (g g0)); simpl; try lia. constructor; eassumption. }
        inversion Hh; eassumption. }
      constructor. constructor; apply Hgen; simpl; eauto; lia.
Qed.

End VCCS_Static.
