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

From Stdlib.Program Require Import Equality.
From stdpp Require Import base.
From TestingTheory Require Import VCCS VCCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VCCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VCCS_Static VCCS_Must_Characterization.

(** * Erasing [①] from a server — the bridge that moves a context into the test

    This is the VCCS counterpart of [VACCS_Erasure.v], and it exists for
    the reason recorded there: a **contextual** preorder is best attacked
    by moving the context into the *test*, not by re-deriving the
    context's effect on a behavioural characterisation.  The only
    obstruction is the outcome predicate — [good (r ‖ t)] holds as soon
    as [good r] does — and erasing [①] from [r] removes it.

    [noone] rewrites every [①] to [𝟘].  Since [①] has no [lts] rule at
    all, erasing removes no transition and adds none, so [noone] is a
    strong bisimulation in both directions and is invisible to [must].

    Consequence, in [VCCS_Precongruence.v]: [‖]-precongruence becomes a
    six-line proof — erase, cross the bridge, apply the hypothesis at the
    single test [noone r ‖ t], cross back, un-erase — with **no [Static]
    side conditions at all**, where the original route
    ([par_wt_transfer], [par_nosync_transfer], the abstraction bridge)
    needs three and spans two sessions' worth of lemmas. *)

Section VCCS_Erasure.

Context `{VP : VCCS_Parameters}.

Fixpoint noone (p : proc) : proc :=
match p with
| P ‖ Q => (noone P) ‖ (noone Q)
| pr_var i => pr_var i
| rec x • P => rec x • (noone P)
| If C Then P Else Q => If C Then (noone P) Else (noone Q)
| ν P => ν (noone P)
| g M => g (gnoone M)
end
with gnoone (M : gproc) : gproc :=
match M with
| ① => 𝟘
| 𝟘 => 𝟘
| c ? p => c ? (noone p)
| c ! v • p => c ! v • (noone p)
| 𝛕 • p => 𝛕 • (noone p)
| p1 + p2 => (gnoone p1) + (gnoone p2)
end.

(** ** [noone] commutes with every substitution and shift the LTS uses *)

Lemma noone_subst : forall p k X, noone (subst_in_proc k X p) = subst_in_proc k X (noone p)
with gnoone_subst : forall M k X, gnoone (subst_in_gproc k X M) = subst_in_gproc k X (gnoone M).
Proof.
  - destruct p; intros k X; simpl; try reflexivity;
    try (f_equal; apply noone_subst).
    + f_equal; apply gnoone_subst.
  - destruct M; intros k X; simpl; try reflexivity;
    try (f_equal; apply noone_subst).
    + f_equal; apply gnoone_subst.
Qed.

Lemma noone_NewVarC : forall p k, noone (NewVarC k p) = NewVarC k (noone p)
with gnoone_gNewVarC : forall M k, gnoone (gNewVarC k M) = gNewVarC k (gnoone M).
Proof.
  - destruct p; intros k; simpl; try reflexivity;
    try (f_equal; apply noone_NewVarC).
    + f_equal; apply gnoone_gNewVarC.
  - destruct M; intros k; simpl; try reflexivity;
    try (f_equal; apply noone_NewVarC).
    + f_equal; apply gnoone_gNewVarC.
Qed.

Lemma noone_NewVar : forall p k, noone (NewVar k p) = NewVar k (noone p)
with gnoone_gNewVar : forall M k, gnoone (gNewVar k M) = gNewVar k (gnoone M).
Proof.
  - destruct p; intros k; simpl; try reflexivity;
    try (f_equal; apply noone_NewVar).
    + f_equal; apply gnoone_gNewVar.
  - destruct M; intros k; simpl; try reflexivity;
    try (f_equal; apply noone_NewVar).
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
    + f_equal. apply noone_pr_subst.
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
  destruct p as [zp1 zp2|zn|zn zq0|zE zp1 zp2|zq0|zM];
  [ | | | | | destruct zM as [| |zc0 zq0|zc0 zv0 zq0|zq0|zM1 zM2] ];
  simpl in Heq; try discriminate Heq; inversion Heq; subst; try clear Heq.

Lemma lts_noone_inv_aux : forall P a q', lts P a q' ->
  forall p, P = noone p -> exists q, q' = noone q /\ lts p a q.
Proof.
  intros P a q' Hl. induction Hl; intros p0 Heq.
  - dnoone p0 Heq. eexists. split; [ symmetry; apply noone_subst | apply lts_input ].
  - dnoone p0 Heq. eexists. split; [ reflexivity | apply lts_output ].
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

Lemma noone_not_good : forall p, ~ good_VCCS (noone p)
with gnoone_not_good : forall M, ~ good_VCCS (g (gnoone M)).
Proof.
  - destruct p; simpl; intro Hg.
    + inversion Hg; subst. destruct H0 as [H|H]; eapply noone_not_good; eassumption.
    + inversion Hg.
    + inversion Hg.
    + inversion Hg; subst; eapply noone_not_good; eassumption.
    + inversion Hg; subst; eapply noone_not_good; eassumption.
    + eapply gnoone_not_good; exact Hg.
  - destruct M; simpl; intro Hg.
    + inversion Hg.
    + inversion Hg.
    + inversion Hg.
    + inversion Hg.
    + inversion Hg.
    + inversion Hg; subst. destruct H0 as [H|H]; eapply gnoone_not_good; eassumption.
Qed.

(** ** Erasing a server is invisible to [must] *)

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

Lemma must_i_noone_l (p : proc) : p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ (noone p).
Proof. intros t Hm. apply must_noone. exact Hm. Qed.

Lemma must_i_noone_r (p : proc) : (noone p) ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ p.
Proof. intros t Hm. apply must_noone_rev. exact Hm. Qed.

(** ** Reading off the polarity of a [dual] pair *)

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

(** ** The bridge: an erased context may sit on either side of the barrier

    [must]'s pair LTS does not care how [p | r | t] is bracketed; only the
    outcome predicate does, and [noone r] can never be [good].  So [r]
    moves from the server side to the client side and back. *)

Lemma par_bridge_fwd : forall (P t : proc), P must_pass t ->
  forall p r, P = p ‖ (noone r) -> p must_pass ((noone r) ‖ t).
Proof.
  intros P t Hm. induction Hm as [ P t Ho | P t Ho Hex Hpt IHpt Het IHet Hcom IHcom ];
    intros p r Heq; subst.
  - apply m_now. apply good_par. right. exact Ho.
  - apply m_step.
    + intro Hg. inversion Hg; subst. destruct H0 as [H|H].
      * eapply noone_not_good; exact H.
      * apply Ho; exact H.
    + destruct Hex as ((x1,x2) & Hs). inversion Hs; subst.
      * inversion l; subst.
        -- exists (p2 ▷ (q2 ‖ x2)).
           eapply ParSync; [ apply dual_out_in | eassumption | apply lts_parL; eassumption ].
        -- exists (q2 ▷ (p2 ‖ x2)).
           eapply ParSync; [ apply dual_in_out | eassumption | apply lts_parL; eassumption ].
        -- exists (p2 ▷ (noone r ‖ x2)). eapply ParLeft. eassumption.
        -- exists (p ▷ (q2 ‖ x2)). eapply ParRight. apply lts_parL. eassumption.
      * exists (p ▷ (noone r ‖ x2)). eapply ParRight. apply lts_parR. eassumption.
      * inversion l1; subst.
        -- exists (p2 ▷ (noone r ‖ x2)).
           eapply ParSync; [ exact eq | eassumption | apply lts_parR; eassumption ].
        -- exists (p ▷ (q2 ‖ x2)). eapply ParRight.
           destruct (dual_shape _ _ eq) as [(a & Ha1 & Ha2)|(a & Ha1 & Ha2)]; subst;
             destruct a as (c0,v0).
           ++ eapply lts_comL; eassumption.
           ++ eapply lts_comR; eassumption.
    + intros p' Hp'. eapply (IHpt (p' ‖ noone r)); [ apply lts_parL; exact Hp' | reflexivity ].
    + intros u Hu. inversion Hu; subst.
      * destruct (lts_noone_inv _ _ _ H1) as (r1 & Hr1 & Hlr1). subst.
        eapply (IHcom (p ‖ noone r1) _ (ActOut (c,v)) (ActIn (c,v)));
          [ apply dual_out_in | apply lts_parR; apply lts_noone; exact Hlr1
          | eassumption | reflexivity ].
      * destruct (lts_noone_inv _ _ _ H2) as (r1 & Hr1 & Hlr1). subst.
        eapply (IHcom (p ‖ noone r1) _ (ActIn (c,v)) (ActOut (c,v)));
          [ apply dual_in_out | apply lts_parR; apply lts_noone; exact Hlr1
          | eassumption | reflexivity ].
      * destruct (lts_noone_inv _ _ _ H3) as (r1 & Hr1 & Hlr1). subst.
        eapply (IHpt (p ‖ noone r1)); [ apply lts_parR; apply lts_noone; exact Hlr1 | reflexivity ].
      * eapply IHet; [ eassumption | reflexivity ].
    + intros p' u mu1 mu2 Hd Hp' Hu. inversion Hu; subst.
      * destruct (lts_noone_inv _ _ _ H3) as (r1 & Hr1 & Hlr1). subst.
        destruct (dual_shape _ _ Hd) as [(a & Ha1 & Ha2)|(a & Ha1 & Ha2)]; subst.
        -- destruct a as (c0,v0).
           eapply (IHpt (p' ‖ noone r1));
             [ eapply lts_comL; [ exact Hp' | apply lts_noone; exact Hlr1 ] | reflexivity ].
        -- destruct a as (c0,v0).
           eapply (IHpt (p' ‖ noone r1));
             [ eapply lts_comR; [ apply lts_noone; exact Hlr1 | exact Hp' ] | reflexivity ].
      * eapply (IHcom (p' ‖ noone r) _ mu1 mu2);
          [ exact Hd | apply lts_parL; exact Hp' | eassumption | reflexivity ].
Qed.

Lemma par_bridge_rev : forall (p T : proc), p must_pass T ->
  forall r t, T = (noone r) ‖ t -> (p ‖ (noone r)) must_pass t.
Proof.
  intros p T Hm. induction Hm as [ p T Ho | p T Ho Hex Hpt IHpt Het IHet Hcom IHcom ];
    intros r t Heq; subst.
  - apply m_now. inversion Ho; subst. destruct H0 as [H|H].
    + exfalso. eapply noone_not_good; exact H.
    + exact H.
  - apply m_step.
    + intro Hg. apply Ho. apply good_par. right. exact Hg.
    + destruct Hex as ((x1,x2) & Hs). inversion Hs; subst.
      * exists ((x1 ‖ noone r) ▷ t). eapply ParLeft. apply lts_parL. eassumption.
      * inversion l; subst.
        -- exists ((x1 ‖ p2) ▷ q2).
           eapply ParSync; [ apply dual_out_in | apply lts_parR; eassumption | eassumption ].
        -- exists ((x1 ‖ q2) ▷ p2).
           eapply ParSync; [ apply dual_in_out | apply lts_parR; eassumption | eassumption ].
        -- exists ((x1 ‖ p2) ▷ t). eapply ParLeft. apply lts_parR. eassumption.
        -- exists ((x1 ‖ noone r) ▷ q2). eapply ParRight. eassumption.
      * inversion l2; subst.
        -- exists ((x1 ‖ p2) ▷ t). eapply ParLeft.
           destruct (dual_shape _ _ eq) as [(a & Ha1 & Ha2)|(a & Ha1 & Ha2)]; subst;
             destruct a as (c0,v0).
           ++ eapply lts_comL; eassumption.
           ++ eapply lts_comR; eassumption.
        -- exists ((x1 ‖ noone r) ▷ q2).
           eapply ParSync; [ exact eq | apply lts_parL; eassumption | eassumption ].
    + intros y Hy. inversion Hy; subst.
      * destruct (lts_noone_inv _ _ _ H2) as (r1 & Hr1 & Hlr1). subst.
        eapply (IHcom p2 (noone r1 ‖ t) (ActOut (c,v)) (ActIn (c,v)));
          [ apply dual_out_in | eassumption | apply lts_parL; apply lts_noone; exact Hlr1
          | reflexivity ].
      * destruct (lts_noone_inv _ _ _ H1) as (r1 & Hr1 & Hlr1). subst.
        eapply (IHcom q2 (noone r1 ‖ t) (ActIn (c,v)) (ActOut (c,v)));
          [ apply dual_in_out | eassumption | apply lts_parL; apply lts_noone; exact Hlr1
          | reflexivity ].
      * eapply (IHpt p2); [ exact H3 | reflexivity ].
      * destruct (lts_noone_inv _ _ _ H3) as (r1 & Hr1 & Hlr1). subst.
        eapply (IHet (noone r1 ‖ t)); [ apply lts_parL; apply lts_noone; exact Hlr1 | reflexivity ].
    + intros t' Ht'. eapply (IHet (noone r ‖ t')); [ apply lts_parR; exact Ht' | reflexivity ].
    + intros y t' mu1 mu2 Hd Hy Ht'. inversion Hy; subst.
      * eapply (IHcom p2 (noone r ‖ t') mu1 mu2);
          [ exact Hd | eassumption | apply lts_parR; exact Ht' | reflexivity ].
      * destruct (lts_noone_inv _ _ _ H3) as (r1 & Hr1 & Hlr1). subst.
        eapply (IHet (noone r1 ‖ t')); [ | reflexivity ].
        destruct (dual_shape _ _ Hd) as [(a & Ha1 & Ha2)|(a & Ha1 & Ha2)]; subst;
          destruct a as (c0,v0).
        -- eapply lts_comL; [ apply lts_noone; exact Hlr1 | exact Ht' ].
        -- eapply lts_comR; [ exact Ht' | apply lts_noone; exact Hlr1 ].
Qed.

(** ** [‖]-precongruence, with NO [Static] side condition

    Compare [VCCS_Precongruence.must_i_par_compat], which needs three of
    them and rests on [par_wt_transfer] + [par_nosync_transfer] + the
    abstraction bridge — a checkpoint's worth of lemmas.  Here the
    argument never inspects the shape of [p], [q] or [r]: erase, cross
    the bridge, apply the hypothesis at the single test [noone r ‖ t],
    cross back, un-erase. *)

Theorem must_i_par_compat_erasure : forall (p q r : proc),
  p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q -> (p ‖ r) ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ (q ‖ r).
Proof.
  intros p q r Hpq t Hm.
  apply (must_noone_rev (q ‖ r)).
  simpl. eapply par_bridge_rev; [ | reflexivity ].
  apply must_noone. apply Hpq.
  apply (must_noone_rev p).
  eapply par_bridge_fwd; [ | reflexivity ].
  apply (must_noone (p ‖ r)) in Hm. exact Hm.
Qed.

Lemma par_comm_must : forall (p q t : proc),
  (p ‖ q) must_pass t -> (q ‖ p) must_pass t.
Proof.
  intros p q t Hm. eapply must_eq_server; [ | exact Hm ]. constructor. constructor.
Qed.

Theorem must_i_par_compat_r_erasure : forall (p q q' : proc),
  q ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> (p ‖ q) ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ (p ‖ q').
Proof.
  intros p q q' Hq t Hm.
  apply par_comm_must. apply (must_i_par_compat_erasure q q' p Hq).
  apply par_comm_must. exact Hm.
Qed.

Theorem must_i_par_compat2_erasure : forall (p p' q q' : proc),
  p ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ p' -> q ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ q' -> (p ‖ q) ᴠᴄᴄꜱ⊑ₘᵤₛₜᵢ (p' ‖ q').
Proof.
  intros p p' q q' Hp Hq t Hm.
  apply (must_i_par_compat_r_erasure p' q q' Hq).
  apply (must_i_par_compat_erasure p p' q Hp). exact Hm.
Qed.


End VCCS_Erasure.
