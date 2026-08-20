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

(** * The expansion law for two guarded sums

    [g M ‖ g N ≂ₘᵤₛₜᵢ g (ext M N + ext_r N M)] — pure interleaving, with
    **no synchronisation term**.  That is the VACCS-specific part: [gproc]
    has no output constructor, so a guarded sum can never emit, so two
    guarded sums can never synchronise ([gproc_no_output] below).  VCCS's
    [int] and its five supporting lemmas simply have no counterpart here.

    (Messages are a separate story: [c!v•𝟘] is not a [gproc] at all, so a
    parallel composition involving one cannot be flattened into a sum.
    That is why VACCS's normal form is [Ѵⁿ (messages ‖ sum)] rather than a
    bare guarded sum — literally the forwarder state [p ▷ m].)

    Proved via the same light route as in VCCS: the two sides have
    *exactly* the same one-step transitions — same labels, same targets,
    not merely related ones — so a generic "same transitions ⟹ same
    [must]-behaviour" lemma closes it. *)

From Stdlib Require Import Lia.
From stdpp Require Import base.
From TestingTheory Require Import VACCS VACCS_Instance Must ActTau InputOutputActions
  gLts Bisimulation InteractionBetweenLts Testing_Predicate VACCS_Good WeakTransitions
  Subset_Act DefinitionAS Convergence VACCS_Static VACCS_Must_Characterization
  VACCS_Erasure.

Section VACCS_Expansion.

Context `{VP : VACCS_Parameters}.

(** ** Same transitions ⟹ same [must]-behaviour

    [must]'s recursive structure only ever inspects one-step transitions,
    so no relation on reached states beyond "same transition set" is
    needed anywhere. *)

Lemma must_same_lts_dir : forall (p q : proc),
  (forall p', p ⟶ p' <-> q ⟶ p') ->
  (forall mu p', p ⟶[mu] p' <-> q ⟶[mu] p') ->
  forall t, p must_pass t -> q must_pass t.
Proof.
  intros p q Htau Hext t Hm.
  revert q Htau Hext.
  induction Hm; intros q Htau Hext.
  - now apply m_now.
  - apply m_step.
    + exact nh.
    + destruct ex as ((a2,b2) & Hstep).
      inversion Hstep; subst.
      * exists (a2,b2). eapply ParLeft. apply Htau. exact l.
      * exists (q,b2). eapply ParRight. exact l.
      * exists (a2,b2). eapply (ParSync μ1 μ2); [exact eq | apply Hext; exact l1 | exact l2].
    + intros p' Hp'. apply pt. apply Htau. exact Hp'.
    + intros t' Ht'. eapply H0; [exact Ht' | exact Htau | exact Hext].
    + intros p' t' μ1 μ2 Hdual Hp' Ht'.
      eapply com; [exact Hdual | apply Hext; exact Hp' | exact Ht'].
Qed.

Lemma must_same_lts : forall (p q : proc),
  (forall p', p ⟶ p' <-> q ⟶ p') ->
  (forall mu p', p ⟶[mu] p' <-> q ⟶[mu] p') ->
  forall t, p must_pass t <-> q must_pass t.
Proof.
  intros p q Htau Hext t. split.
  - apply must_same_lts_dir; assumption.
  - apply must_same_lts_dir.
    + intro p'. symmetry. apply Htau.
    + intros mu p'. symmetry. apply Hext.
Qed.

(** ** A guarded sum never emits

    The structural fact that makes VACCS asynchronous, and the reason the
    expansion law below has no synchronisation term. *)

Lemma gproc_no_output : forall (M : gproc) (x : TypeOfActions) (q : proc),
  ~ lts (g M) (ActExt (ActOut x)) q.
Proof.
  induction M; intros x q H; inversion H; subst.
  - eapply IHM1; eassumption.
  - eapply IHM2; eassumption.
Qed.

(** ** Shifting a value binder, then substituting it, is the identity *)

Lemma subst_NewVar_Data_cancel : forall k X Y,
  subst_Data k X (NewVar_in_Data k Y) = Y.
Proof.
  intros k X [a|i]; simpl; [ reflexivity | ].
  destruct (decide (k < S i)) as [H|H]; simpl.
  - destruct (decide (S i = k)) as [E|E]; [ exfalso; lia | ].
    destruct (decide (S i < k)) as [E2|E2]; [ exfalso; lia | reflexivity ].
  - destruct (decide (i = k)) as [E|E]; [ exfalso; lia | ].
    destruct (decide (i < k)) as [E2|E2]; [ reflexivity | exfalso; lia ].
Qed.

Lemma subst_NewVar_Equation_cancel : forall k X E,
  subst_in_Equation k X (NewVar_in_Equation k E) = E.
Proof. intros k X [D1 D2]; simpl; rewrite !subst_NewVar_Data_cancel; reflexivity. Qed.

Lemma NewVar_subst_cancel : forall p k X, subst_in_proc k X (NewVar k p) = p
with gNewVar_subst_cancel : forall M k X, subst_in_gproc k X (gNewVar k M) = M.
Proof.
  - destruct p; intros k X; simpl.
    + f_equal; apply NewVar_subst_cancel.
    + reflexivity.
    + f_equal; apply NewVar_subst_cancel.
    + f_equal; [ apply subst_NewVar_Equation_cancel | apply NewVar_subst_cancel
               | apply NewVar_subst_cancel ].
    + f_equal; apply subst_NewVar_Data_cancel.
    + f_equal; apply NewVar_subst_cancel.
    + f_equal; apply gNewVar_subst_cancel.
  - destruct M; intros k X; simpl.
    + reflexivity.
    + reflexivity.
    + f_equal; apply NewVar_subst_cancel.
    + f_equal; apply NewVar_subst_cancel.
    + f_equal; apply gNewVar_subst_cancel.
Qed.

Lemma gproc_NewVar_cancel : forall N v, subst_in_gproc 0 v (gNewVar 0 N) = N.
Proof. intros N v. apply gNewVar_subst_cancel. Qed.

(** ** The interleaving

    [ext M N] lets [M]'s own guards race ahead of the untouched [N].  The
    input case must shift [N]'s value binders out of the new binder's way
    ([gNewVar 0 N]); [①] contributes nothing, exactly like [𝟘], since it
    has no transition. *)

Fixpoint ext (M N : gproc) : gproc :=
match M with
| ① => 𝟘
| 𝟘 => 𝟘
| c ? p => c ? (p ‖ (g (gNewVar 0 N)))
| 𝛕 • p => 𝛕 • (p ‖ (g N))
| gp1 + gp2 => (ext gp1 N) + (ext gp2 N)
end.

(** [N]'s guards race ahead of the untouched [M] — a *separate* function,
    not [ext] with swapped arguments, so that the wrapping order matches
    [lts_parR]'s target shape [g M ‖ c2] rather than [c2 ‖ g M]. *)

Fixpoint ext_r (N M : gproc) : gproc :=
match N with
| ① => 𝟘
| 𝟘 => 𝟘
| c ? q => c ? ((g (gNewVar 0 M)) ‖ q)
| 𝛕 • q => 𝛕 • ((g M) ‖ q)
| gq1 + gq2 => (ext_r gq1 M) + (ext_r gq2 M)
end.

(** ** [ext]/[ext_r] mirror their argument's transitions exactly *)

Lemma ext_lts_iff : forall M N a tgt, lts (g M) a tgt <-> lts (g (ext M N)) a (tgt ‖ g N).
Proof.
  induction M; intros N a tgt; simpl.
  - split; intro H; inversion H.
  - split; intro H; inversion H.
  - split; intro H.
    + inversion H; subst.
      replace (p^v ‖ N) with ((p ‖ g (gNewVar 0 N)) ^ v).
      * apply lts_input.
      * simpl. rewrite gproc_NewVar_cancel. reflexivity.
    + inversion H; subst. apply lts_input.
  - split; intro H.
    + inversion H; subst. apply lts_tau.
    + inversion H; subst. apply lts_tau.
  - split; intro H.
    + inversion H; subst.
      * eapply lts_choiceL. apply IHM1. exact H4.
      * eapply lts_choiceR. apply IHM2. exact H4.
    + inversion H; subst.
      * apply IHM1 in H4. eapply lts_choiceL. exact H4.
      * apply IHM2 in H4. eapply lts_choiceR. exact H4.
Qed.

Lemma ext_r_lts_iff : forall N M a tgt, lts (g N) a tgt <-> lts (g (ext_r N M)) a (g M ‖ tgt).
Proof.
  induction N; intros M a tgt; simpl.
  - split; intro H; inversion H.
  - split; intro H; inversion H.
  - split; intro H.
    + inversion H; subst.
      replace (M ‖ p^v) with ((g (gNewVar 0 M) ‖ p) ^ v).
      * apply lts_input.
      * simpl. rewrite gproc_NewVar_cancel. reflexivity.
    + inversion H; subst. apply lts_input.
  - split; intro H.
    + inversion H; subst. apply lts_tau.
    + inversion H; subst. apply lts_tau.
  - split; intro H.
    + inversion H; subst.
      * eapply lts_choiceL. apply IHN1. exact H4.
      * eapply lts_choiceR. apply IHN2. exact H4.
    + inversion H; subst.
      * apply IHN1 in H4. eapply lts_choiceL. exact H4.
      * apply IHN2 in H4. eapply lts_choiceR. exact H4.
Qed.

(** The "every target has this shape" corollaries, needed for the
    backward direction; proved by their own induction, since the [iff]s
    above do not themselves assert it. *)

Lemma ext_lts_shape : forall M N a tgt,
  lts (g (ext M N)) a tgt -> exists tgt', tgt = tgt' ‖ g N /\ lts (g M) a tgt'.
Proof.
  induction M; intros N a tgt H; simpl in H.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    exists (p^v). split.
    + simpl. rewrite gproc_NewVar_cancel. reflexivity.
    + apply lts_input.
  - inversion H; subst. exists p. split; [reflexivity | apply lts_tau].
  - inversion H; subst.
    + apply IHM1 in H4 as (tgt' & Heq & H4').
      exists tgt'. split; [exact Heq | apply lts_choiceL; exact H4'].
    + apply IHM2 in H4 as (tgt' & Heq & H4').
      exists tgt'. split; [exact Heq | apply lts_choiceR; exact H4'].
Qed.

Lemma ext_r_lts_shape : forall N M a tgt,
  lts (g (ext_r N M)) a tgt -> exists tgt', tgt = g M ‖ tgt' /\ lts (g N) a tgt'.
Proof.
  induction N; intros M a tgt H; simpl in H.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    exists (p^v). split.
    + simpl. rewrite gproc_NewVar_cancel. reflexivity.
    + apply lts_input.
  - inversion H; subst. exists p. split; [reflexivity | apply lts_tau].
  - inversion H; subst.
    + apply IHN1 in H4 as (tgt' & Heq & H4').
      exists tgt'. split; [exact Heq | apply lts_choiceL; exact H4'].
    + apply IHN2 in H4 as (tgt' & Heq & H4').
      exists tgt'. split; [exact Heq | apply lts_choiceR; exact H4'].
Qed.

(** ** The transition correspondence, and the law *)

Lemma expansion_lts_iff : forall M N a tgt,
  lts (g M ‖ g N) a tgt <-> lts (g (ext M N)) a tgt \/ lts (g (ext_r N M)) a tgt.
Proof.
  intros M N a tgt. split.
  - intro H. inversion H; subst.
    + exfalso. eapply gproc_no_output; eassumption.
    + exfalso. eapply gproc_no_output; eassumption.
    + left. apply ext_lts_iff. exact H4.
    + right. apply ext_r_lts_iff. exact H4.
  - intros [H|H].
    + apply ext_lts_shape in H as (tgt' & Heq & H'). subst. apply lts_parL. exact H'.
    + apply ext_r_lts_shape in H as (tgt' & Heq & H'). subst. apply lts_parR. exact H'.
Qed.

Lemma lts_choice2_iff : forall A B a tgt,
  lts (g (A + B)) a tgt <-> lts (g A) a tgt \/ lts (g B) a tgt.
Proof.
  intros A B a tgt. split.
  - intro H. inversion H; subst; [ left | right ]; assumption.
  - intros [H|H]; [ apply lts_choiceL | apply lts_choiceR ]; exact H.
Qed.

Theorem must_i_expansion : forall M N t,
  (g M ‖ g N) must_pass t <-> g (ext M N + ext_r N M) must_pass t.
Proof.
  intros M N t.
  apply must_same_lts.
  - intro p'. split.
    + intro H. apply lts_choice2_iff. apply expansion_lts_iff. exact H.
    + intro H. apply expansion_lts_iff. apply lts_choice2_iff. exact H.
  - intros mu p'. split.
    + intro H. apply lts_choice2_iff. apply expansion_lts_iff. exact H.
    + intro H. apply expansion_lts_iff. apply lts_choice2_iff. exact H.
Qed.

Corollary must_i_expansion_l : forall M N,
  (g M ‖ g N) ⊑ₘᵤₛₜᵢ g (ext M N + ext_r N M).
Proof. intros M N t Hm. apply must_i_expansion. exact Hm. Qed.

Corollary must_i_expansion_r : forall M N,
  g (ext M N + ext_r N M) ⊑ₘᵤₛₜᵢ (g M ‖ g N).
Proof. intros M N t Hm. apply must_i_expansion. exact Hm. Qed.

(** ** [gStatic] survives the construction *)

Lemma ext_gStatic : forall M N, gStatic M -> gStatic N -> gStatic (ext M N).
Proof.
  induction M; intros N HM HN; simpl; inversion HM; subst.
  - constructor.
  - constructor.
  - constructor. constructor; [ assumption | constructor; apply gStatic_gNewVar; assumption ].
  - constructor. constructor; [ assumption | constructor; assumption ].
  - constructor; [ apply IHM1 | apply IHM2 ]; assumption.
Qed.

Lemma ext_r_gStatic : forall N M, gStatic N -> gStatic M -> gStatic (ext_r N M).
Proof.
  induction N; intros M HN HM; simpl; inversion HN; subst.
  - constructor.
  - constructor.
  - constructor. constructor; [ constructor; apply gStatic_gNewVar; assumption | assumption ].
  - constructor. constructor; [ constructor; assumption | assumption ].
  - constructor; [ apply IHN1 | apply IHN2 ]; assumption.
Qed.

(** [①] is inert on the server side **in an arbitrary context** too: a
    sum's transitions never come from an [①] summand (no [lts] rule
    mentions [①]), so replacing it by [𝟘] leaves the transition relation
    *literally identical* and [must_same_lts] closes both directions at
    once.

    The context is needed for the same reason as in the merge below: the
    two rules that rewrite inside a sum preserve the rewritten summand's
    guard, and [①] and [𝟘] are not guards at all. *)

Lemma must_i_success_ctx : forall (R : gproc) (t : proc),
  (g ((gpr_success) + R)) must_pass t <-> (g ((gpr_nil) + R)) must_pass t.
Proof.
  intros R t. apply must_same_lts.
  - intro p'. split; intro H; inversion H; subst.
    + inversion H4.
    + apply lts_choiceR. assumption.
    + inversion H4.
    + apply lts_choiceR. assumption.
  - intros mu p'. split; intro H; inversion H; subst.
    + inversion H4.
    + apply lts_choiceR. assumption.
    + inversion H4.
    + apply lts_choiceR. assumption.
Qed.

Corollary must_i_success_ctx_l : forall (R : gproc),
  (g ((gpr_success) + R)) ⊑ₘᵤₛₜᵢ (g ((gpr_nil) + R)).
Proof. intros R t H. apply must_i_success_ctx. exact H. Qed.

Corollary must_i_success_ctx_r : forall (R : gproc),
  (g ((gpr_nil) + R)) ⊑ₘᵤₛₜᵢ (g ((gpr_success) + R)).
Proof. intros R t H. apply must_i_success_ctx. exact H. Qed.

End VACCS_Expansion.
