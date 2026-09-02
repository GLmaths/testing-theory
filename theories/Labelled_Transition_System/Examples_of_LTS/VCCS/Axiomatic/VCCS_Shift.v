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

(** * The channel-index shift [NewVarC] transports transitions, both ways

    [NewVarC k] inserts a fresh channel binder at de Bruijn level [k].
    This file shows it is a *strong bisimulation* between [p] and
    [NewVarC k p], with labels shifted accordingly — the exact analogue of
    [VCCS_Erasure.v]'s [lts_noone] / [lts_noone_inv], and proved the same
    way (forward by induction on the derivation; backward with an explicit
    equation on the subject, so that [induction] applies).

    It is the missing ingredient of the *restriction bridge*

        must (ν p) t  <->  must p (NewVarC 0 t)

    which is to [ax_res] what [VCCS_Precongruence.v]'s parallel bridge is
    to [ax_par]: [(ν p) | t] and [p | t↑] are the same system, because
    [lts_res_ext] / [lts_res_tau] already characterise [ν]'s transitions in
    both directions, and a shifted test can only ever act on shifted
    channels — so it can never synchronise on the restricted one, which is
    exactly what [ν] hides.  The bridge itself lives in
    [VCCS_Precongruence.v], where it replaces the acceptance-set route
    that [must_i_res_compat] used to take — and with it the [Static] side
    conditions that route needed.

    This is a **port** of [VACCS_Shift.v]: the two calculi differ here
    only in the output, which is a *guard* with a continuation in VCCS
    and an atomic message in VACCS.  Every proof carries over unchanged
    apart from that one case.

    Note the two shifts the development uses are different functions —
    [NewVar_in_ChannelData k] ("insert a binder at level [k]") and
    [VarC_add k] ("add [k] to every index") — and they agree exactly at
    [k = 0] ([NewVarC_at_zero]), which is what makes the bridge's [k = 0]
    instance line up with [lts_res_ext]'s [VarC_action_add 1]. *)

From Stdlib Require Import Lia.
From Stdlib.Program Require Import Equality.
From stdpp Require Import base.
From TestingTheory Require Import VCCS VCCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VCCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VCCS_Static VCCS_Must_Characterization VCCS_Erasure.

Section VCCS_Shift.

Context `{VP : VCCS_Parameters}.

(** ** Shifting a label *)

Definition NewVarC_TOA (k : nat) (a : TypeOfActions) : TypeOfActions :=
  match a with (c,v) => (NewVar_in_ChannelData k c, v) end.

Definition NewVar_in_action (k : nat) (mu : ExtAct TypeOfActions) : ExtAct TypeOfActions :=
  match mu with
  | ActIn x  => ActIn (NewVarC_TOA k x)
  | ActOut x => ActOut (NewVarC_TOA k x)
  end.

Definition NewVarC_act (k : nat) (a : ActIO TypeOfActions) : ActIO TypeOfActions :=
  match a with
  | ActExt (ActIn x)  => ActExt (ActIn (NewVarC_TOA k x))
  | ActExt (ActOut x) => ActExt (ActOut (NewVarC_TOA k x))
  | τ => τ
  end.

Lemma NewVarC_act_ext : forall k mu,
  NewVarC_act k (ActExt mu) = ActExt (NewVar_in_action k mu).
Proof. intros k [x|x]; reflexivity. Qed.

(** The two shifts of the development coincide at level [0]. *)
Lemma NewVarC_at_zero : forall c, NewVar_in_ChannelData 0 c = VarC_add 1 c.
Proof.
  intros [a|i]; simpl; [ reflexivity | ].
  destruct (decide (0 < S i)) as [H|H]; [ reflexivity | exfalso; lia ].
Qed.

(** ** How the two shifts commute, and how they invert *)

Lemma NewVarC_shift_comm : forall k c,
  NewVar_in_ChannelData (S k) (VarC_add 1 c) = VarC_add 1 (NewVar_in_ChannelData k c).
Proof.
  intros k [a|i]; simpl; [ reflexivity | ].
  destruct (decide (S k < S (S i))) as [H1|H1]; destruct (decide (k < S i)) as [H2|H2];
    simpl; try reflexivity; exfalso; lia.
Qed.

(** The converse of [NewVarC_shift_comm]: a channel that is *both* a
    [VarC_add 1]-shift and a [NewVar_in_ChannelData (S k)]-shift is the
    shift of a single common channel.  This is what lets the [ν] case of
    [lts_NewVarC_inv_aux] pull a label back out through the binder. *)

Lemma NewVarC_shift_inv : forall k c c0, VarC_add 1 c = NewVar_in_ChannelData (S k) c0 ->
  exists c1, c = NewVar_in_ChannelData k c1 /\ c0 = VarC_add 1 c1.
Proof.
  intros k c [a|j] Heq.
  - destruct c as [b|m]; simpl in Heq; try discriminate Heq.
    inversion Heq; subst. exists (cst a). split; reflexivity.
  - destruct c as [b|m]; simpl in Heq;
      [ destruct (decide (S k < S j)); discriminate Heq | ].
    destruct (decide (S k < S j)) as [Hlt|Hge].
    + destruct j as [|j']; [ exfalso; lia | ].
      exists (bvar j'). inversion Heq; subst. simpl.
      split; [ destruct (decide (k < S j')) as [H1|H1];
               [ reflexivity | exfalso; lia ] | reflexivity ].
    + exists (bvar m). inversion Heq; subst. simpl.
      split; [ destruct (decide (k < S m)) as [H1|H1];
               [ exfalso; lia | reflexivity ] | reflexivity ].
Qed.

Lemma NewVar_in_ChannelData_inj : forall k c1 c2,
  NewVar_in_ChannelData k c1 = NewVar_in_ChannelData k c2 -> c1 = c2.
Proof.
  intros k [a|i] [b|j] Heq; simpl in Heq.
  - inversion Heq; reflexivity.
  - destruct (decide (k < S j)); discriminate Heq.
  - destruct (decide (k < S i)); discriminate Heq.
  - destruct (decide (k < S i)) as [H1|H1]; destruct (decide (k < S j)) as [H2|H2];
      inversion Heq; f_equal; lia.
Qed.

Lemma NewVar_in_action_inv : forall k mu mu0,
  VarC_action_add 1 mu = NewVar_in_action (S k) mu0 ->
  exists mu1, mu = NewVar_in_action k mu1 /\ mu0 = VarC_action_add 1 mu1.
Proof.
  intros k [[c v]|[c v]] [[c0 v0]|[c0 v0]] Heq; simpl in Heq; inversion Heq; subst;
    match goal with H : VarC_add 1 c = _ |- _ =>
      destruct (NewVarC_shift_inv k c c0 H) as (c1 & Hc1 & Hc2) end; subst;
    [ exists (ActIn (c1, v0)) | exists (ActOut (c1, v0)) ]; split; reflexivity.
Qed.

(** ** The shift transports transitions forwards *)

Lemma lts_NewVarC : forall p a q, lts p a q ->
  forall k, lts (NewVarC k p) (NewVarC_act k a) (NewVarC k q).
Proof.
  intros p a q Hl. induction Hl; intros k; simpl in *.
  - assert (NewVarC k (P ^ v) = (NewVarC k P) ^ v) as E by (symmetry; apply subst_and_NewVarC).
    rewrite E. apply lts_input.
  - apply lts_output.
  - apply lts_tau.
  - assert (NewVarC k (pr_subst x P (rec x • P))
            = pr_subst x (NewVarC k P) (rec x • (NewVarC k P))) as E
      by (symmetry; apply (pr_subst_and_NewVarC P (rec x • P) x k)).
    rewrite E. apply lts_recursion.
  - eapply lts_ifOne; [ eassumption | apply IHHl ].
  - eapply lts_ifZero; [ eassumption | apply IHHl ].
  - specialize (IHHl (S k)).
    destruct μ as [[c v]|[c v]]; simpl in *; apply lts_res_ext;
      rewrite NewVarC_shift_comm in IHHl; exact IHHl.
  - apply lts_res_tau. apply (IHHl (S k)).
  - eapply lts_comL; [ apply (IHHl1 k) | apply (IHHl2 k) ].
  - eapply lts_comR; [ apply (IHHl1 k) | apply (IHHl2 k) ].
  - apply lts_parL. apply IHHl.
  - apply lts_parR. apply IHHl.
  - apply lts_choiceL. apply IHHl.
  - apply lts_choiceR. apply IHHl.
Qed.

(** ** …and backwards

    Every transition of [NewVarC k p] is the shift of a transition of [p],
    at a label that is itself a shift.  Same shape as
    [VCCS_Erasure.lts_noone_inv_aux]: an explicit equation on the subject,
    and a local tactic recovering [p]'s constructor from it. *)

Local Ltac dnvc p Heq :=
  destruct p as [zp1 zp2|zn|zn zq0|zE zp1 zp2|zq0|zM];
  [ | | | | | destruct zM as [| |zc0 zq0|zc0 zv0 zq0|zq0|zM1 zM2] ];
  simpl in Heq; try discriminate Heq; inversion Heq; subst; try clear Heq.

Lemma lts_NewVarC_inv_aux : forall P a q', lts P a q' ->
  forall p k, P = NewVarC k p ->
  exists a0 q, a = NewVarC_act k a0 /\ q' = NewVarC k q /\ lts p a0 q.
Proof.
  intros P a q' Hl. induction Hl; intros p0 k Heq.
  - dnvc p0 Heq. exists (ActExt (ActIn (zc0, v))), (zq0 ^ v).
    split; [ reflexivity | split; [ apply subst_and_NewVarC | apply lts_input ] ].
  - dnvc p0 Heq. exists (ActExt (ActOut (zc0, zv0))), zq0.
    split; [ reflexivity | split; [ reflexivity | apply lts_output ] ].
  - dnvc p0 Heq. exists τ, zq0. split; [ reflexivity | split; [ reflexivity | apply lts_tau ] ].
  - dnvc p0 Heq. exists τ, (pr_subst zn zq0 (rec zn • zq0)).
    split; [ reflexivity | split; [ apply (pr_subst_and_NewVarC zq0 (rec zn • zq0) zn k)
                                  | apply lts_recursion ] ].
  - dnvc p0 Heq. destruct (IHHl _ _ eq_refl) as (a0 & q & Ha & Hq & Hlq).
    exists a0, q. split; [ exact Ha | split; [ exact Hq | eapply lts_ifOne; eassumption ] ].
  - dnvc p0 Heq. destruct (IHHl _ _ eq_refl) as (a0 & q & Ha & Hq & Hlq).
    exists a0, q. split; [ exact Ha | split; [ exact Hq | eapply lts_ifZero; eassumption ] ].
  - dnvc p0 Heq. destruct (IHHl zq0 (S k) eq_refl) as (a0 & q & Ha & Hq & Hlq).
    destruct a0 as [mu0|]; [ | simpl in Ha; discriminate Ha ].
    simpl in Ha. inversion Ha as [Ha']. clear Ha.
    assert (Ha2 : VarC_action_add 1 μ = NewVar_in_action (S k) mu0)
      by (destruct mu0; simpl in Ha' |- *; congruence).
    destruct (NewVar_in_action_inv k μ mu0 Ha2) as (mu1 & Hmu1 & Hmu2). subst.
    exists (ActExt mu1), (ν q).
    split; [ destruct mu1; reflexivity
           | split; [ simpl; f_equal; exact Hq | apply lts_res_ext; exact Hlq ] ].
  - dnvc p0 Heq. destruct (IHHl zq0 (S k) eq_refl) as (a0 & q & Ha & Hq & Hlq).
    destruct a0 as [mu0|]; [ simpl in Ha; destruct mu0; discriminate Ha | ].
    exists τ, (ν q).
    split; [ reflexivity | split; [ simpl; f_equal; exact Hq | apply lts_res_tau; exact Hlq ] ].
  - dnvc p0 Heq. destruct (IHHl1 _ _ eq_refl) as (b1 & r1 & Hb1 & Hr1 & Hlr1).
    destruct (IHHl2 _ _ eq_refl) as (b2 & r2 & Hb2 & Hr2 & Hlr2).
    destruct b1 as [[x1|x1]|]; simpl in Hb1; try discriminate Hb1.
    destruct b2 as [[x2|x2]|]; simpl in Hb2; try discriminate Hb2.
    destruct x1 as (d1,w1); destruct x2 as (d2,w2).
    inversion Hb1; inversion Hb2; subst.
    assert (d2 = d1) by (eapply NewVar_in_ChannelData_inj; eauto). subst.
    exists τ, (r1 ‖ r2).
    split; [ reflexivity | split; [ simpl; f_equal; assumption | eapply lts_comL; eassumption ] ].
  - dnvc p0 Heq. destruct (IHHl1 _ _ eq_refl) as (b1 & r1 & Hb1 & Hr1 & Hlr1).
    destruct (IHHl2 _ _ eq_refl) as (b2 & r2 & Hb2 & Hr2 & Hlr2).
    destruct b1 as [[x1|x1]|]; simpl in Hb1; try discriminate Hb1.
    destruct b2 as [[x2|x2]|]; simpl in Hb2; try discriminate Hb2.
    destruct x1 as (d1,w1); destruct x2 as (d2,w2).
    inversion Hb1; inversion Hb2; subst.
    assert (d2 = d1) by (eapply NewVar_in_ChannelData_inj; eauto). subst.
    exists τ, (r2 ‖ r1).
    split; [ reflexivity | split; [ simpl; f_equal; assumption | eapply lts_comR; eassumption ] ].
  - dnvc p0 Heq. destruct (IHHl _ _ eq_refl) as (b0 & r0 & Hb & Hr & Hlr).
    exists b0, (r0 ‖ zp2).
    split; [ exact Hb | split; [ simpl; rewrite Hr; reflexivity | apply lts_parL; exact Hlr ] ].
  - dnvc p0 Heq. destruct (IHHl _ _ eq_refl) as (b0 & r0 & Hb & Hr & Hlr).
    exists b0, (zp1 ‖ r0).
    split; [ exact Hb | split; [ simpl; rewrite Hr; reflexivity | apply lts_parR; exact Hlr ] ].
  - dnvc p0 Heq. destruct (IHHl (g zM1) k eq_refl) as (b0 & r0 & Hb & Hr & Hlr).
    exists b0, r0. split; [ exact Hb | split; [ exact Hr | apply lts_choiceL; exact Hlr ] ].
  - dnvc p0 Heq. destruct (IHHl (g zM2) k eq_refl) as (b0 & r0 & Hb & Hr & Hlr).
    exists b0, r0. split; [ exact Hb | split; [ exact Hr | apply lts_choiceR; exact Hlr ] ].
Qed.

Lemma lts_NewVarC_inv : forall p k a q', lts (NewVarC k p) a q' ->
  exists a0 q, a = NewVarC_act k a0 /\ q' = NewVarC k q /\ lts p a0 q.
Proof. intros p k a q' Hl. eapply lts_NewVarC_inv_aux; [ exact Hl | reflexivity ]. Qed.

End VCCS_Shift.
