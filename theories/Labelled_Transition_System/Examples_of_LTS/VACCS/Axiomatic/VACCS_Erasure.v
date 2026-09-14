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

(** * Erasing [①] from a server

    [good] (VACCS_Good.v) is the *client*'s outcome predicate; a server's
    own [①] is never observed, because [must]'s [m_now] inspects only the
    test.  And indeed [①] has no [lts] rule at all — exactly like [𝟘].

    This file makes that precise with a syntactic erasure [noone], which
    rewrites every [①] to [𝟘], and shows it is invisible to [must] on the
    server side.  Two things need it:

    - the soundness of the rule [① ⊑ 𝟘] (and back) in the axiom system;
    - the *parallel bridge* of [VACCS_Precongruence.v], whose statement
      [must (p ‖ r) t <-> must p (r ‖ t)] moves [r] from the server to the
      client and therefore needs [r] to be unable to become [good].  An
      erased process never is, and erasedness is preserved by [lts],
      because [noone]'s image is closed under transitions.

    Everything here is about *any* VACCS process — [Static] is not
    assumed, so [pr_rec] is covered too. *)

From Stdlib.Program Require Import Equality.
From stdpp Require Import base.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization.

Section VACCS_Erasure.

Context `{VP : VACCS_Parameters}.

(** ** The erasure *)

Fixpoint noone (p : proc) : proc :=
match p with
| P ‖ Q => (noone P) ‖ (noone Q)
| pr_var i => pr_var i
| rec x • P => rec x • (noone P)
| If C Then P Else Q => If C Then (noone P) Else (noone Q)
| c ! v • 𝟘 => c ! v • 𝟘
| ν P => ν (noone P)
| g M => g (gnoone M)
end
with gnoone (M : gproc) : gproc :=
match M with
| ① => 𝟘
| 𝟘 => 𝟘
| c ? p => c ? (noone p)
| 𝛕 • p => 𝛕 • (noone p)
| p1 + p2 => (gnoone p1) + (gnoone p2)
end.

(** ** [noone] commutes with every substitution and shift the LTS uses *)

Lemma noone_subst : forall p k X, noone (subst_in_proc k X p) = subst_in_proc k X (noone p)
with gnoone_subst : forall M k X, gnoone (subst_in_gproc k X M) = subst_in_gproc k X (gnoone M).
Proof.
  - destruct p; intros k X; simpl; try reflexivity.
    + f_equal; apply noone_subst.
    + f_equal; apply noone_subst.
    + f_equal; apply noone_subst.
    + f_equal; apply noone_subst.
    + f_equal; apply gnoone_subst.
  - destruct M; intros k X; simpl; try reflexivity.
    + f_equal; apply noone_subst.
    + f_equal; apply noone_subst.
    + f_equal; apply gnoone_subst.
Qed.

Lemma noone_NewVarC : forall p k, noone (NewVarC k p) = NewVarC k (noone p)
with gnoone_gNewVarC : forall M k, gnoone (gNewVarC k M) = gNewVarC k (gnoone M).
Proof.
  - destruct p; intros k; simpl; try reflexivity.
    + f_equal; apply noone_NewVarC.
    + f_equal; apply noone_NewVarC.
    + f_equal; apply noone_NewVarC.
    + f_equal; apply noone_NewVarC.
    + f_equal; apply gnoone_gNewVarC.
  - destruct M; intros k; simpl; try reflexivity.
    + f_equal; apply noone_NewVarC.
    + f_equal; apply noone_NewVarC.
    + f_equal; apply gnoone_gNewVarC.
Qed.

Lemma noone_NewVar : forall p k, noone (NewVar k p) = NewVar k (noone p)
with gnoone_gNewVar : forall M k, gnoone (gNewVar k M) = gNewVar k (gnoone M).
Proof.
  - destruct p; intros k; simpl; try reflexivity.
    + f_equal; apply noone_NewVar.
    + f_equal; apply noone_NewVar.
    + f_equal; apply noone_NewVar.
    + f_equal; apply noone_NewVar.
    + f_equal; apply gnoone_gNewVar.
  - destruct M; intros k; simpl; try reflexivity.
    + f_equal; apply noone_NewVar.
    + f_equal; apply noone_NewVar.
    + f_equal; apply gnoone_gNewVar.
Qed.

Lemma noone_pr_subst : forall p x q, noone (pr_subst x p q) = pr_subst x (noone p) (noone q)
with gnoone_gpr_subst : forall M x q, gnoone (gpr_subst x M q) = gpr_subst x (gnoone M) (noone q).
Proof.
  - destruct p; intros x q; simpl; try reflexivity.
    + f_equal; apply noone_pr_subst.
    + destruct (decide (x = n)); reflexivity.
    + destruct (decide (x = n)); simpl; try reflexivity. f_equal. apply noone_pr_subst.
    + f_equal; apply noone_pr_subst.
    + f_equal. rewrite noone_pr_subst. f_equal. apply noone_NewVarC.
    + f_equal. apply gnoone_gpr_subst.
  - destruct M; intros x q; simpl; try reflexivity.
    + f_equal. rewrite noone_pr_subst. f_equal. apply noone_NewVar.
    + f_equal; apply noone_pr_subst.
    + f_equal; apply gnoone_gpr_subst.
Qed.

(** ** [noone] is a strong bisimulation, in both directions

    Erasing does not change a single transition: [①] has no [lts] rule,
    so replacing it by [𝟘] cannot remove one, and cannot add one either. *)

Lemma lts_noone : forall p a q, lts p a q -> lts (noone p) a (noone q).
Proof.
  intros p a q Hl. induction Hl; simpl in *.
  - assert (noone (P ^ v) = (noone P) ^ v) as E by apply noone_subst.
    rewrite E. apply lts_input.
  - apply lts_output.
  - apply lts_tau.
  - assert (noone (pr_subst x P (rec x • P)) = pr_subst x (noone P) (rec x • (noone P))) as E
      by apply noone_pr_subst.
    rewrite E. apply lts_recursion.
  - eapply lts_ifOne; eauto.
  - eapply lts_ifZero; eauto.
  - apply lts_res_ext; assumption.
  - apply lts_res_tau; assumption.
  - eapply lts_comL; eauto.
  - eapply lts_comR; eauto.
  - apply lts_parL; assumption.
  - apply lts_parR; assumption.
  - apply lts_choiceL; assumption.
  - apply lts_choiceR; assumption.
Qed.

(** The converse.  Stated with an explicit equation on the subject so that
    [induction] applies (the subject [noone p] is a compound term); the
    local tactic recovers [p]'s shape from it, one [proc] constructor at a
    time, with the [gproc] case nested. *)

Local Ltac dnoone p Heq :=
  destruct p as [zp1 zp2|zn|zn zq0|zE zp1 zp2|zc0 zv0|zq0|zM];
  [ | | | | | | destruct zM as [| |zc0 zq0|zq0|zM1 zM2] ];
  simpl in Heq; try discriminate Heq; inversion Heq; subst; try clear Heq.

Lemma lts_noone_inv_aux : forall P a q', lts P a q' ->
  forall p, P = noone p -> exists q, q' = noone q /\ lts p a q.
Proof.
  intros P a q' Hl. induction Hl; intros p0 Heq.
  - dnoone p0 Heq. eexists. split; [ symmetry; apply noone_subst | apply lts_input ].
  - dnoone p0 Heq. exists (g 𝟘). split; [ reflexivity | apply lts_output ].
  - dnoone p0 Heq. eexists. split; [ reflexivity | apply lts_tau ].
  - dnoone p0 Heq. eexists.
    split; [ symmetry; apply (noone_pr_subst zq0 zn (rec zn • zq0)) | apply lts_recursion ].
  - dnoone p0 Heq. destruct (IHHl _ eq_refl) as (x & Hx & Hlx).
    exists x. split; [ assumption | eapply lts_ifOne; eauto ].
  - dnoone p0 Heq. destruct (IHHl _ eq_refl) as (x & Hx & Hlx).
    exists x. split; [ assumption | eapply lts_ifZero; eauto ].
  - dnoone p0 Heq. destruct (IHHl _ eq_refl) as (x & Hx & Hlx).
    exists (ν x). split; [ simpl; f_equal; assumption | apply lts_res_ext; assumption ].
  - dnoone p0 Heq. destruct (IHHl _ eq_refl) as (x & Hx & Hlx).
    exists (ν x). split; [ simpl; f_equal; assumption | apply lts_res_tau; assumption ].
  - dnoone p0 Heq. destruct (IHHl1 _ eq_refl) as (x & Hx & Hlx).
    destruct (IHHl2 _ eq_refl) as (y & Hy & Hly).
    exists (x ‖ y). split; [ simpl; f_equal; assumption | eapply lts_comL; eauto ].
  - dnoone p0 Heq. destruct (IHHl1 _ eq_refl) as (x & Hx & Hlx).
    destruct (IHHl2 _ eq_refl) as (y & Hy & Hly).
    exists (y ‖ x). split; [ simpl; f_equal; assumption | eapply lts_comR; eauto ].
  - dnoone p0 Heq. destruct (IHHl _ eq_refl) as (x & Hx & Hlx).
    exists (x ‖ zp2). split; [ simpl; f_equal; assumption | apply lts_parL; assumption ].
  - dnoone p0 Heq. destruct (IHHl _ eq_refl) as (x & Hx & Hlx).
    exists (zp1 ‖ x). split; [ simpl; f_equal; assumption | apply lts_parR; assumption ].
  - dnoone p0 Heq. destruct (IHHl (g zM1) eq_refl) as (x & Hx & Hlx).
    exists x. split; [ assumption | apply lts_choiceL; assumption ].
  - dnoone p0 Heq. destruct (IHHl (g zM2) eq_refl) as (x & Hx & Hlx).
    exists x. split; [ assumption | apply lts_choiceR; assumption ].
Qed.

Lemma lts_noone_inv : forall p a q', lts (noone p) a q' ->
  exists q, q' = noone q /\ lts p a q.
Proof. intros p a q' Hl. eapply lts_noone_inv_aux; [ exact Hl | reflexivity ]. Qed.

(** ** An erased process is never [good] *)

Lemma noone_not_good : forall p, ~ good_VACCS (noone p)
with gnoone_not_good : forall M, ~ good_VACCS (g (gnoone M)).
Proof.
  - destruct p; simpl; intro Hg.
    + inversion Hg; subst. destruct H0 as [H|H]; eapply noone_not_good; eassumption.
    + inversion Hg.
    + inversion Hg.
    + inversion Hg; subst; eapply noone_not_good; eassumption.
    + inversion Hg.
    + inversion Hg; subst; eapply noone_not_good; eassumption.
    + eapply gnoone_not_good; exact Hg.
  - destruct M; simpl; intro Hg.
    + inversion Hg.
    + inversion Hg.
    + inversion Hg.
    + inversion Hg.
    + inversion Hg; subst. destruct H0 as [H|H]; eapply gnoone_not_good; eassumption.
Qed.

(** ** Erasing a server is invisible to [must]

    Both directions, by induction on the derivation: every field of
    [m_step] transports along [lts_noone] / [lts_noone_inv], and the
    outcome field mentions only the test. *)

Lemma must_noone : forall (p t : proc), p must_pass t -> (noone p) must_pass t.
Proof.
  intros p t Hm. induction Hm as [ p t Ho | p t Ho Hex Hpt IHpt Het IHet Hcom IHcom ].
  - now apply m_now.
  - apply m_step.
    + exact Ho.
    + destruct Hex as ((x1,x2) & Hs). inversion Hs; subst.
      * eexists. eapply ParLeft. apply lts_noone. eassumption.
      * eexists. eapply ParRight. eassumption.
      * eexists. eapply ParSync; [ eassumption | apply lts_noone; eassumption | eassumption ].
    + intros y Hy. destruct (lts_noone_inv _ _ _ Hy) as (x & Hx & Hlx).
      subst y. apply IHpt. exact Hlx.
    + intros t' Ht'. apply IHet. exact Ht'.
    + intros y t' mu1 mu2 Hd Hy Ht'.
      destruct (lts_noone_inv _ _ _ Hy) as (x & Hx & Hlx).
      subst y. eapply IHcom; eassumption.
Qed.

Lemma must_noone_rev_aux : forall (P t : proc), P must_pass t ->
  forall p, P = noone p -> p must_pass t.
Proof.
  intros P t Hm. induction Hm as [ P t Ho | P t Ho Hex Hpt IHpt Het IHet Hcom IHcom ];
    intros p Heq; subst.
  - now apply m_now.
  - apply m_step.
    + exact Ho.
    + destruct Hex as ((x1,x2) & Hs). inversion Hs; subst.
      * destruct (lts_noone_inv _ _ _ l) as (y & _ & Hly).
        eexists. eapply ParLeft. eassumption.
      * eexists. eapply ParRight. eassumption.
      * destruct (lts_noone_inv _ _ _ l1) as (y & _ & Hly).
        eexists. eapply ParSync; eassumption.
    + intros p' Hp'. eapply IHpt; [ apply lts_noone; exact Hp' | reflexivity ].
    + intros t' Ht'. eapply IHet; [ exact Ht' | reflexivity ].
    + intros p' t' mu1 mu2 Hd Hp' Ht'.
      eapply IHcom; [ exact Hd | apply lts_noone; exact Hp' | exact Ht' | reflexivity ].
Qed.

Lemma must_noone_rev : forall (p t : proc), (noone p) must_pass t -> p must_pass t.
Proof. intros p t Hm. eapply must_noone_rev_aux; [ exact Hm | reflexivity ]. Qed.

Lemma must_i_noone_l (p : proc) : p ⊑ₘᵤₛₜᵢ (noone p).
Proof. intros t Hm. apply must_noone. exact Hm. Qed.

Lemma must_i_noone_r (p : proc) : (noone p) ⊑ₘᵤₛₜᵢ p.
Proof. intros t Hm. apply must_noone_rev. exact Hm. Qed.

(** ** Reading off the polarity of a [dual] pair

    [dual] is [ext_act_match], which pairs [ActIn a] with [ActOut a].
    These three tiny lemmas save unfolding it by hand at every use. *)

Lemma dual_shape : forall (mu1 mu2 : ExtAct TypeOfActions), dual mu1 mu2 ->
  (exists a, mu1 = ActOut a /\ mu2 = ActIn a) \/ (exists a, mu1 = ActIn a /\ mu2 = ActOut a).
Proof.
  intros [a|a] [b|b] Hd; simpl in Hd; try (exact (match Hd with end)); subst;
    [ right | left ]; eexists; split; reflexivity.
Qed.

Lemma dual_out_in : forall (a : TypeOfActions), dual (ActOut a) (ActIn a).
Proof. intros a. simpl. reflexivity. Qed.

Lemma dual_in_out : forall (a : TypeOfActions), dual (ActIn a) (ActOut a).
Proof. intros a. simpl. reflexivity. Qed.

End VACCS_Erasure.
